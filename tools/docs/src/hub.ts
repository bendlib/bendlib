// hub: fetch BendHub's index, names and package files into a private BEND_LIB.
// A package hash is the first 128 bits of sha256(manifest), and every manifest
// line is "<sha256> <path>", so both levels are verified before anything is cached.

import { existsSync, mkdirSync, readFileSync, writeFileSync, renameSync } from "node:fs";
import { dirname, join, resolve, sep } from "node:path";

export const HUB = process.env.BEND_HUB ?? "https://hub.bend-lang.com";

export const FETCH_TIMEOUT_MS = 30_000;

/** One hub request, bounded so a stalled hub cannot hang the build. */
export async function fetchHub(url: string, timeoutMs = FETCH_TIMEOUT_MS): Promise<Response> {
  return fetch(url, { signal: AbortSignal.timeout(timeoutMs) });
}

export type IndexEntry = { hash: string; files: Record<string, number>; bytes: number; ts: number; desc: string };
export type NameVersion = { version: string; hash: string; ts: number };
export type NameRecord = {
  name: string; owner_login: string; ts: number; dependents?: number; mentions?: number; score?: number;
  latest: { version: string; hash: string; ts: number; desc: string };
  versions: NameVersion[];
};

const HASH = /^0x[0-9a-f]{32}$/;
// PLAN F1: names are `^[a-z][a-z0-9-]{11,63}$`, versions are `a.b.c.d`.
const NAME = /^[a-z][a-z0-9-]{11,63}$/;
const VERSION = /^\d+\.\d+\.\d+\.\d+$/;

async function get(url: string, tries = 3): Promise<Response> {
  let last: unknown;
  for (let i = 0; i < tries; i++) {
    try {
      const r = await fetchHub(url);
      if (r.ok || r.status === 404 || r.status === 410) return r;
      last = new Error(`HTTP ${r.status} for ${url}`);
    } catch (e) {
      last = e;
    }
    await Bun.sleep(300 * (i + 1));
  }
  throw last instanceof Error ? last : new Error(String(last));
}

async function getJson<T>(url: string): Promise<T> {
  const r = await get(url);
  if (!r.ok) throw new Error(`HTTP ${r.status} for ${url}`);
  return (await r.json()) as T;
}

export function sha256(bytes: Uint8Array | string): string {
  return new Bun.CryptoHasher("sha256").update(bytes).digest("hex");
}

export async function fetchIndex(): Promise<IndexEntry[]> {
  const idx = await getJson<IndexEntry[]>(`${HUB}/index.json`);
  for (const e of idx) if (!HASH.test(e.hash)) throw new Error(`index.json: malformed hash ${JSON.stringify(e.hash)}`);
  return idx;
}

/** Keeps records with a well-formed name and at least one well-formed version/hash; logs and drops the rest (PLAN F1). */
export function validNameRecords(records: NameRecord[]): NameRecord[] {
  const kept: NameRecord[] = [];
  const dropped: string[] = [];
  for (const n of records) {
    const versions = (n.versions ?? []).filter((v) => VERSION.test(v.version) && HASH.test(v.hash));
    if (NAME.test(n.name) && versions.length > 0) kept.push({ ...n, versions });
    else dropped.push(n.name);
  }
  if (dropped.length) console.error(`hub: dropped ${dropped.length} invalid name record(s): ${dropped.slice(0, 5).join(", ")}`);
  return kept;
}

/** names.json lists only each name's latest version; the per-name record adds `versions`. */
export async function fetchNames(jobs = 8): Promise<NameRecord[]> {
  const list = await getJson<Omit<NameRecord, "versions">[]>(`${HUB}/names.json`);
  const named = list.filter((n) => NAME.test(n.name));  // never even request a hostile name
  if (named.length !== list.length) console.error(`hub: dropped ${list.length - named.length} name record(s) with an invalid name`);
  const out = await pool(named, jobs, async (n) => {
    const full = await getJson<NameRecord>(`${HUB}/name/${encodeURIComponent(n.name)}`);
    return { ...n, ...full, versions: full.versions ?? [{ version: n.latest.version, hash: n.latest.hash, ts: n.latest.ts }] };
  });
  return validNameRecords(out);
}

export async function pool<T, R>(items: T[], jobs: number, f: (x: T, i: number) => Promise<R>): Promise<R[]> {
  const out: R[] = new Array(items.length);
  let next = 0;
  const worker = async () => {
    while (next < items.length) {
      const i = next++;
      out[i] = await f(items[i], i);
    }
  };
  await Promise.all(Array.from({ length: Math.max(1, Math.min(jobs, items.length)) }, worker));
  return out;
}

export type ManifestLine = { sha256: string; path: string };

export function parseManifest(text: string): ManifestLine[] {
  return text.trim().split("\n").filter((l) => l !== "").map((l) => {
    const m = l.match(/^([0-9a-f]{64}) (.+)$/);
    if (m === null) throw new Error(`malformed manifest line ${JSON.stringify(l)}`);
    return { sha256: m[1], path: m[2] };
  });
}

/** True when a manifest path is relative, has no `.`/`..`/empty segment, and no control chars, quotes or angle brackets. */
export function safePath(p: string): boolean {
  if (p === "" || p.startsWith("/") || /[\x00-\x1f\x7f"'<>]/.test(p)) return false;
  return !p.split("/").some((s) => s === ".." || s === "." || s === "");
}

/** Joins `rel` under `root`, refusing anything that resolves outside `root`. */
export function underRoot(root: string, rel: string): string {
  const base = resolve(root), r = resolve(base, rel);
  if (r !== base && !r.startsWith(base + sep)) throw new Error(`path escapes ${base}: ${JSON.stringify(rel)}`);
  return r;
}

export type Cached = { hash: string; manifest: ManifestLine[]; fetched: boolean };

// The manifest copy under `<cache>/manifests/<hash>` is written last, so its presence marks a complete package.
/** Ensures `<lib>/<hash>/<path>` holds every verified file of the package. */
export async function ensurePackage(hash: string, lib: string, cache: string): Promise<Cached> {
  const mfile = join(cache, "manifests", hash);
  if (existsSync(mfile)) {
    const mbytes = readFileSync(mfile);
    if (!sha256(mbytes).startsWith(hash.slice(2))) throw new Error(`cached manifest of ${hash} is corrupt; delete ${mfile} to refetch`);
    const manifest = parseManifest(mbytes.toString("utf8"));
    for (const { path } of manifest) if (!safePath(path)) throw new Error(`cached manifest of ${hash}: unsafe path ${JSON.stringify(path)}`);
    return { hash, manifest, fetched: false };
  }
  const r = await get(`${HUB}/${hash}/manifest`);
  if (!r.ok) throw new Error(`manifest of ${hash}: HTTP ${r.status}`);
  const mbytes = new Uint8Array(await r.arrayBuffer());
  if (!sha256(mbytes).startsWith(hash.slice(2))) throw new Error(`manifest of ${hash} does not hash to the package hash`);
  const manifest = parseManifest(new TextDecoder().decode(mbytes));
  for (const { path } of manifest) if (!safePath(path)) throw new Error(`manifest of ${hash}: unsafe path ${JSON.stringify(path)}`);
  const bodies = await pool(manifest, 4, async ({ sha256: want, path }) => {
    const target = join(lib, hash, path);
    if (existsSync(target) && sha256(readFileSync(target)) === want) return null;
    const fr = await get(`${HUB}/${hash}/${path.split("/").map(encodeURIComponent).join("/")}`);
    if (!fr.ok) throw new Error(`${hash}/${path}: HTTP ${fr.status}`);
    const body = new Uint8Array(await fr.arrayBuffer());
    const got = sha256(body);
    if (got !== want) throw new Error(`${hash}/${path}: sha256 ${got} does not match manifest ${want}`);
    return body;
  });
  manifest.forEach(({ path }, i) => {
    const body = bodies[i];
    if (body === null) return;
    const target = join(lib, hash, path);
    mkdirSync(dirname(target), { recursive: true });
    writeFileSync(target + ".part", body);
    renameSync(target + ".part", target);
  });
  mkdirSync(dirname(mfile), { recursive: true });
  writeFileSync(mfile + ".part", mbytes);
  renameSync(mfile + ".part", mfile);
  return { hash, manifest, fetched: true };
}

/** Pre-seeds `<lib>/names/<name>@<version>` exactly as bend.ts's name_hash would, so loads need no network for names. */
export function seedNames(lib: string, names: NameRecord[]): void {
  for (const n of names) {
    if (!NAME.test(n.name)) continue;
    for (const v of n.versions) {
      if (!HASH.test(v.hash) || !VERSION.test(v.version)) continue;
      const at = join(lib, "names", `${n.name}@${v.version}`);
      mkdirSync(dirname(at), { recursive: true });
      writeFileSync(at, v.hash + "\n");
    }
  }
}
