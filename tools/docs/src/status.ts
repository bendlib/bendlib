// status: `bend <file> --check-only` per file on the pinned compiler, under a
// timeout and an address-space cap, classified and cached by (hash, compiler).

import { existsSync, readFileSync, writeFileSync, mkdirSync, renameSync } from "node:fs";
import { dirname, join } from "node:path";
import { homedir } from "node:os";
import { stripCommentsAndStrings } from "../../mathlib/lib.ts";

export const BEND = process.env.BEND_CLI ?? join(homedir(), ".bend", "bin", "bend");

export type FileClass = "checks" | "unsafe" | "open" | "fails" | "timeout";
export type FileStatus = {
  class: FileClass;
  summary: string;       // one line for badges and tables
  detail: string;        // first error block, the unsafe line, or the open-law lines
  unsafeDefs?: string[];
  exitCode: number | null;
  seconds: number;
};

/** Packages take the worst class of their files, in this order. */
export const SEVERITY: FileClass[] = ["checks", "unsafe", "open", "timeout", "fails"];

export function worst(classes: FileClass[]): FileClass {
  return classes.reduce<FileClass>((w, c) => (SEVERITY.indexOf(c) > SEVERITY.indexOf(w) ? c : w), "checks");
}

function firstBlock(out: string): string {
  const lines = out.split("\n");
  const at = lines.findIndex((l) => /^Error\b|^error\b/i.test(l.trim()));
  const from = at < 0 ? 0 : at;
  const block: string[] = [];
  for (let i = from; i < lines.length && block.length < 40; i++) {
    if (i > from && /^Error\b/.test(lines[i].trim())) break;
    block.push(lines[i]);
  }
  return block.join("\n").trim();
}

/** Classifies checker output; anything not recognised verbatim counts as `fails`. */
export function classify(out: string, exitCode: number | null, timedOut: boolean, seconds: number): FileStatus {
  const text = out.replace(/\r/g, "").trim();
  const base = { exitCode, seconds };
  if (timedOut) return { ...base, class: "timeout", summary: `no answer within ${Math.round(seconds)} s`, detail: text.slice(0, 2000) };
  if (exitCode === 0 && text === "All terms check.") return { ...base, class: "checks", summary: "All terms check.", detail: "" };
  const lines = text.split("\n");
  const rely = lines.find((l) => /^All terms check, but \d+ defs? (rely|relies) on unsafe or foreign code:?$/.test(l.trim()));
  if (exitCode === 0 && rely !== undefined) {
    const defs = unsafeDefs(lines.slice(lines.indexOf(rely) + 1));
    return { ...base, class: "unsafe", summary: rely.trim().replace(/:$/, ""), detail: text, unsafeDefs: defs };
  }
  // bend 2.0.27 reports unfinished proofs as "Error: N TODOs found." and exits 1.
  const todo = lines.find((l) => /^Error: \d+ TODOs? found\.$/.test(l.trim()));
  if (todo !== undefined && lines.every((l) => !/^Error\b/.test(l.trim()) || l === todo)) {
    return { ...base, class: "open", summary: todo.trim().replace(/^Error: /, ""), detail: text };
  }
  const block = firstBlock(text);
  const bl = block.split("\n");
  const first = (bl.find((l) => /^\s*- (message|expected)\b/.test(l)) ?? bl.find((l) => l.trim() !== "" && !/^Error:?$/.test(l.trim())) ?? "").trim();
  return { ...base, class: "fails", summary: first.slice(0, 200) || `exit code ${exitCode}`, detail: block.slice(0, 4000) };
}

function unsafeDefs(rest: string[]): string[] {
  const out: string[] = [];
  for (const l of rest) {
    const m = l.trim().match(/^- (\S+)$/);
    if (m === null) break;
    out.push(m[1]);
  }
  return out;
}

// Def names that follow an `@unsafe` token in stripped source, in source order.
function unsafeDefNames(src: string): string[] {
  const out: string[] = [];
  const lines = src.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const m = /(^|[^\w@])@unsafe\b/.exec(lines[i]);
    if (m === null) continue;
    const same = lines[i].slice(m.index + m[0].length).match(/^\s*def\s+([A-Za-z_][A-Za-z0-9_.]*)/);
    if (same !== null) { out.push(same[1]); continue; }
    for (let j = i + 1; j < lines.length; j++) {
      const t = lines[j].trim();
      if (t === "") continue;
      const d = t.match(/^(?:@unsafe\s+)?def\s+([A-Za-z_][A-Za-z0-9_.]*)/);
      if (d !== null) out.push(d[1]);
      break;
    }
  }
  return [...new Set(out)];
}

// Catches @unsafe in the package's own files only; @unsafe in a dependency is visible on that
// package's page. bend issue #1001: the checker prints a clean verdict despite an unsafe fill.
export function crossCheck(s: FileStatus, source: string): FileStatus {
  const src = stripCommentsAndStrings(source);
  if (s.class !== "checks" || !/(^|[^\w@])@unsafe\b/.test(src)) return s;
  return {
    ...s, class: "unsafe", summary: "source has @unsafe, but bend printed a clean verdict (bend issue #1001)",
    unsafeDefs: unsafeDefNames(src), detail: s.detail,
  };
}

export type CheckOptions = { bendLib: string; timeoutSec: number; memMb: number; cwd: string };

let bwrapProbe: boolean | null = null;

/** Whether per-file checks run inside bwrap; the `bwrap --version` probe runs at most once. */
export function sandboxAvailable(): boolean {
  if (bwrapProbe === null) {
    try { bwrapProbe = Bun.spawnSync(["bwrap", "--version"], { stdout: "ignore", stderr: "ignore" }).exitCode === 0; }
    catch { bwrapProbe = false; }
  }
  return bwrapProbe;
}

/** The argv `checkFile` spawns: the pinned compiler under the memory cap, inside bwrap when sandboxed. */
export function checkCommand(file: string, o: CheckOptions, sandbox: boolean): string[] {
  const cap = Math.max(256, Math.floor(o.memMb)) * 1024;
  const inner = ["bash", "-c", `ulimit -v ${cap}; exec "$0" "$1" --check-only`, BEND, file];
  if (!sandbox) return inner;
  // `--dev /dev` is required: the Bun-compiled bend aborts when / is a read-only bind without a fresh /dev.
  return ["bwrap", "--unshare-all", "--die-with-parent", "--ro-bind", "/", "/", "--tmpfs", "/tmp", "--dev", "/dev",
    "--bind", o.bendLib, o.bendLib, "--chdir", o.cwd, ...inner];
}

export async function checkFile(file: string, o: CheckOptions): Promise<FileStatus> {
  const t0 = performance.now();
  const proc = Bun.spawn(checkCommand(file, o, sandboxAvailable()), {
    cwd: o.cwd,
    env: { ...process.env, BEND_LIB: o.bendLib, BEND_NO_TELEMETRY: "1" },
    stdout: "pipe", stderr: "pipe", stdin: "ignore",
  });
  let timedOut = false;
  const timer = setTimeout(() => { timedOut = true; proc.kill("SIGKILL"); }, o.timeoutSec * 1000);
  const [so, se] = await Promise.all([new Response(proc.stdout).text(), new Response(proc.stderr).text()]);
  const code = await proc.exited;
  clearTimeout(timer);
  return classify(`${so}${se}`, timedOut ? null : code, timedOut, (performance.now() - t0) / 1000);
}

export function compilerVersion(): string {
  const p = Bun.spawnSync([BEND, "version"], { env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
  const v = new TextDecoder().decode(p.stdout).trim().match(/^bend (\S+)$/);
  if (v === null) throw new Error(`cannot read the compiler version from '${BEND} version': ${new TextDecoder().decode(p.stderr)}`);
  return v[1];
}

export type StatusCache = Record<string, FileStatus>;
export const statusKey = (hash: string, path: string, compiler: string) => `${compiler} ${hash}/${path}`;

export function readStatusCache(file: string): StatusCache {
  return existsSync(file) ? JSON.parse(readFileSync(file, "utf8")) : {};
}

export function writeStatusCache(file: string, c: StatusCache): void {
  mkdirSync(dirname(file), { recursive: true });
  writeFileSync(file + ".part", JSON.stringify(c));
  renameSync(file + ".part", file);
}

/** Namespaces of the installed compiler's Base: `Nat` from `def Nat.add`, `List` from `type List<…>`. */
export function baseNamespaces(): Set<string> {
  const p = Bun.spawnSync([BEND, "base"], { env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
  const out = new TextDecoder().decode(p.stdout);
  const names = new Set<string>(["Base"]);
  for (const m of out.matchAll(/^(?:def|law|type)\s+([A-Z][A-Za-z0-9_]*)/gm)) names.add(m[1]);
  if (names.size < 10) throw new Error(`'${BEND} base' listed only ${names.size} namespaces: ${new TextDecoder().decode(p.stderr)}`);
  return names;
}
