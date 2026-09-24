// model: everything the renderer needs, assembled from hub metadata, extracted
// declarations, import edges and checker statuses.

import type { NameRecord } from "./hub.ts";
import type { DocDecl, FileError } from "./extract.ts";
import type { Edge, Import } from "./imports.ts";
import { worst, type FileClass, type FileStatus } from "./status.ts";
import type { License } from "./license.ts";

export type Module = {
  path: string;
  header: string | null;            // the module's top `#` comment block, when it is not a declaration's doc
  source: string | null;            // the file text for the source page, or null when it is too large
  imports: Import[];
  foreign: string[];
  decls: DocDecl[] | null;          // null when the reader could not load the file
  error: FileError | null;
  status: FileStatus | null;        // null with --no-check
  provedIn: Record<string, string>; // law local name -> file that fills it (other than this one)
  settled?: FileClass;              // an `open` LAWS file whose every open law a checking sibling proves
};

export type PkgName = { name: string; version: string; owner: string; ts: number };

export type Package = {
  hash: string; ts: number; desc: string; bytes: number;
  files: { path: string; bytes: number }[];
  names: PkgName[];
  licenses: License[];
  modules: Module[];
  deps: Edge[]; rdeps: Edge[];
  status: FileClass | null;
  counts: { laws: number; proved: number; defs: number; types: number; decls: number };
};

export type Site = {
  built: string; compiler: string; checked: boolean; partial: boolean; local: boolean;
  packages: Package[];                // display order: named first, then by recency
  byHash: Map<string, Package>;
  names: NameRecord[];
};

export const label = (p: Package) => (p.names.length > 0 ? `${p.names[0].name}@${p.names[0].version}` : shortHash(p.hash));
export const shortHash = (h: string) => h.slice(0, 10);
export const published = (p: Package) => (p.names.length > 0 ? Math.min(...p.names.map((n) => n.ts)) : p.ts);

export function namesByHash(names: NameRecord[]): Map<string, PkgName[]> {
  const m = new Map<string, PkgName[]>();
  for (const n of names) {
    for (const v of n.versions) {
      const list = m.get(v.hash) ?? [];
      list.push({ name: n.name, version: v.version, owner: n.owner_login, ts: v.ts });
      m.set(v.hash, list);
    }
  }
  return m;
}

export type Group = { key: string; latest: Package; members: Package[] };

export const versionKey = (v: string) => v.split(".").map((x) => x.padStart(8, "0")).join(".");
const newest = (a: Package, b: Package) => {
  const va = a.names[0]?.version, vb = b.names[0]?.version;
  if (va && vb && va !== vb) return versionKey(va) > versionKey(vb) ? a : b;
  return a.ts >= b.ts ? a : b;
};

/** One group per package lineage: a name, or (for anonymous uploads) the same file set and description. */
export function groupPackages(pkgs: Package[]): Group[] {
  const sig = (p: Package) => `${p.files.map((f) => f.path).sort().join("\n")}\n${p.desc}`;
  const groups = new Map<string, Group>();
  const bySig = new Map<string, string>();
  const add = (key: string, p: Package) => {
    const g = groups.get(key);
    if (g) { g.members.push(p); g.latest = newest(g.latest, p); } else groups.set(key, { key, latest: p, members: [p] });
  };
  for (const p of pkgs) if (p.names.length > 0) { add(`name:${p.names[0].name}`, p); bySig.set(sig(p), `name:${p.names[0].name}`); }
  for (const p of pkgs) if (p.names.length === 0) add(bySig.get(sig(p)) ?? `files:${sig(p)}`, p);
  for (const g of groups.values()) g.members.sort((a, b) => (newest(a, b) === a ? -1 : 1));
  return displayOrder([...groups.values()].map((g) => g.latest)).map((p) => [...groups.values()].find((g) => g.latest === p)!);
}

export function displayOrder(pkgs: Package[]): Package[] {
  return [...pkgs].sort((a, b) => {
    const na = a.names.length > 0 ? 0 : 1, nb = b.names.length > 0 ? 0 : 1;
    return na - nb || b.ts - a.ts || a.hash.localeCompare(b.hash);
  });
}

export type ApiDiff = { added: string[]; removed: string[]; changed: string[] };

// The declaration kinds that make up a package's API; effects and unsafe defs are not compared.
const API_KINDS = new Set(["def", "law", "template", "type", "ctor"]);

/** Compares two packages' APIs by `<module path>/<decl name>`; `changed` means the signature differs. */
export function apiDiff(older: Package, newer: Package): ApiDiff {
  const index = (p: Package) => {
    const m = new Map<string, string>();
    for (const mod of p.modules) for (const d of mod.decls ?? []) {
      if (API_KINDS.has(d.kind)) m.set(`${mod.path}/${d.name}`, d.signature);
    }
    return m;
  };
  const a = index(older), b = index(newer);
  const added: string[] = [], removed: string[] = [], changed: string[] = [];
  for (const [k, sig] of b) {
    if (!a.has(k)) added.push(k);
    else if (a.get(k) !== sig) changed.push(k);
  }
  for (const k of a.keys()) if (!b.has(k)) removed.push(k);
  return { added: added.sort(), removed: removed.sort(), changed: changed.sort() };
}

const esc = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");

/** The module's top `#` run with `#` and one space stripped; null when line 1 is not `#` or it documents a declaration. */
export function moduleHeader(text: string): string | null {
  const lines = text.split("\n");
  if (!lines[0]?.startsWith("#")) return null;
  let end = 0;
  while (end < lines.length && lines[end].startsWith("#")) end++;
  const after = lines[end];
  if (after !== undefined && after.trim() !== "" && !/^import\b/.test(after)) return null;
  return lines.slice(0, end).map((l) => l.replace(/^# ?/, "")).join("\n");
}

/** Lines of the def starting at `line` (1-based), up to the next top-level declaration, strings and comments blanked. */
export function defBody(text: string, line: number): string {
  const lines = text.split("\n");
  const out: string[] = [];
  for (let i = line - 1; i < lines.length; i++) {
    if (i > line - 1 && /^[^\s#]/.test(lines[i])) break;
    out.push(lines[i].replace(/"(\\.|[^"\\])*"|'(\\.|[^'\\])*'/g, '""').replace(/#.*$/, ""));
  }
  return out.join("\n");
}

/** A `?name` hole anywhere in the def's body; `bend guide` says such a hole leaves the goal open. */
export const hasHole = (body: string) => /(^|[^\w?])\?[A-Za-z_]\w*/.test(body);

/** 1-based line of `def [Alias.]<local>(` in a file that fills an imported law, or null. */
export function fillerLine(text: string, local: string): number | null {
  const re = new RegExp(`^(@unsafe\\s+)?def\\s+([A-Za-z_][\\w]*\\.)*${esc(local)}\\s*\\(`);
  const i = text.split("\n").findIndex((l) => re.test(l));
  return i < 0 ? null : i + 1;
}

const passes = (s: FileStatus | null | undefined) => s == null || s.class === "checks" || s.class === "unsafe";

/** Settles each law (proved here, proved in a checking sibling, or open), counts declarations, and sets the package status. */
export function finishPackage(p: Package, fills: Map<string, string[]>, text: (path: string) => string): void {
  const filledBy = new Map<string, string>();
  for (const [file, list] of fills) for (const f of list) if (!filledBy.has(f)) filledBy.set(f, file);
  const byPath = new Map(p.modules.map((m) => [m.path, m]));
  const c = { laws: 0, proved: 0, defs: 0, types: 0, decls: 0 };
  const effective: FileClass[] = [];
  for (const m of p.modules) {
    let unfilled = 0, rescued = 0, rescuedUnsafe = false;
    const src = m.decls ? text(m.path) : "";
    for (const d of m.decls ?? []) {
      c.decls++;
      if (d.kind === "type") { c.types++; continue; }
      if (d.kind === "ctor") continue;
      if (d.kind !== "law") { c.defs++; continue; }
      c.laws++;
      if (d.proved && d.proofLine !== undefined && hasHole(defBody(src, d.proofLine))) { d.proved = false; d.holes = true; }
      if (!d.proved && !d.holes) {
        unfilled++;
        const by = filledBy.get(`${m.path}#${d.name}`);
        if (by !== undefined && by !== m.path) {
          m.provedIn[d.name] = by;
          const fl = fillerLine(text(by), d.name);
          const holes = fl !== null && hasHole(defBody(text(by), fl));
          const st = byPath.get(by)?.status;
          if (holes) d.holes = true;
          else if (passes(st)) {
            d.proved = true;
            rescued++;
            if (st?.class === "unsafe") rescuedUnsafe = true;
          }
        }
      }
      if (d.proved) c.proved++;
    }
    const s = m.status;
    if (s === null) continue;
    const todo = s.class === "open" ? Number(s.summary.match(/^(\d+) TODO/)?.[1] ?? NaN) : NaN;
    // Checked alone, a LAWS.bend reports each law without a def as open; when that count is exactly
    // its laws proved by siblings that check, the file counts as checking for the package.
    if (s.class === "open" && todo === unfilled && rescued === unfilled && unfilled > 0) {
      m.settled = rescuedUnsafe ? "unsafe" : "checks";
      effective.push(m.settled);
    } else effective.push(s.class);
  }
  p.counts = c;
  p.status = effective.length > 0 ? worst(effective) : null;
}

export function attachEdges(pkgs: Package[], edges: Edge[]): void {
  const by = new Map(pkgs.map((p) => [p.hash, p]));
  for (const e of edges) {
    by.get(e.from)?.deps.push(e);
    by.get(e.to)?.rdeps.push(e);
  }
}
