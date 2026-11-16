// hash: compute the BendHub content hash of a package, exactly as `bend --publish` does
// (2.0.40 bend2/main.ts cli_publish, pkg_files, pkg_read: main.ts:673-686, 838-902): the entry at
// its basename, every local import (read as bend.ts book_load reads them) at its real path from
// the entry's real directory, every foreign `.c`/`.js` a def imports (tld.i) at its path, a LICENSE
// beside any file, the README.md beside the entry (2.0.40+, at most README_MAX bytes);
// "0x" + sha256 of "sha256(content) path\n" lines, 32 hex.
// As bend does, it refuses (exit 2) an entry linked from another directory, a file whose path climbs
// out of the entry's directory or whose real path is outside it, and a README.md over README_MAX.
// usage: bun tools/mathlib/hash.ts <entry.bend>   (hash on stdout, files on stderr)
// exit: 0 printed · 2 usage (missing, non-file or linked entry, a file outside its directory, README too big)

import { createHash } from "node:crypto";
import { existsSync, readFileSync, readdirSync, realpathSync, statSync } from "node:fs";
import { basename, dirname, join, normalize, relative, resolve } from "node:path";
import { PkgError, importPaths, isHubImport } from "./lib.ts";

const USAGE = "usage: bun tools/mathlib/hash.ts <entry.bend>";
const usage = (msg: string): never => { console.error(`hash: ${msg}\n${USAGE}`); process.exit(2); };

/** The largest README.md `bend --publish` takes (2.0.40 main.ts:102, 875-878). */
export const README_MAX = 65536;

/** Whether `bend --publish` of compiler `version` ("2.0.40" or "bend 2.0.40") puts the entry's README.md in the package. */
export function publishesReadme(version: string): boolean {
  const m = /(\d+)\.(\d+)\.(\d+)/.exec(version);
  if (!m) throw new PkgError(`not a bend version: ${JSON.stringify(version)}`);
  const [a, b, c] = m.slice(1).map(Number);
  return a !== 2 ? a > 2 : b !== 0 ? b > 0 : c >= 40;
}

const sha256 = (s: string) => createHash("sha256").update(s).digest("hex");

export function hubHash(files: Record<string, string>): string {
  const lines = Object.keys(files).sort().map((p) => sha256(files[p]) + " " + p + "\n");
  return "0x" + sha256(lines.join("")).slice(0, 32);
}

// A def's foreign effect files, recorded by bend's parser as indented `import "./f.c"` lines (bend.ts:2465-2480).
const FOREIGN = /^\s+import\s+"([^"]+)"/gm;

/** Collect the files `bend <entry> --publish` would upload (local and foreign imports; hub imports stay out). */
export function packageFiles(entry: string, opts: { readme?: boolean } = {}): Record<string, string> {
  if (!existsSync(entry) || !statSync(entry).isFile()) throw new PkgError(`not a .bend file: ${entry}`);
  const realOf = (file: string): string => {
    try { return realpathSync(file); } catch { throw new PkgError(`cannot read ${file}`); }
  };
  const root = realOf(dirname(entry));
  if (dirname(realOf(entry)) !== root) throw new PkgError(`${entry} links to ${realOf(entry)}, in another directory; bend refuses to publish it`);
  if (root === "/") throw new PkgError(`${entry} is at the file system's root; bend refuses to publish it`);
  const files: Record<string, string> = {};
  // bend reads the real path, refuses one outside the entry's directory, and drops a leading BOM (main.ts:857-868).
  const read = (file: string): string => {
    const real = realOf(file);
    if (!real.startsWith(root + "/")) throw new PkgError(`${file} is outside the entry directory ${root} (its real path is ${real}); bend refuses to publish it`);
    try { return readFileSync(real, "utf8").replace(/^﻿/, ""); }
    catch { throw new PkgError(`cannot read ${file}`); }
  };
  const key = (file: string, at: string): string => {
    const k = normalize(at);
    if (k.startsWith("../") || k.startsWith("/")) {
      throw new PkgError(`${file} is outside the entry directory ${root}; bend refuses a path that climbs out of it`);
    }
    if (k.split("/").slice(0, -1).some((s) => s.toLowerCase() === "license")) {
      throw new PkgError(`${file} is in a directory named license, which bend refuses to publish`);
    }
    return k;
  };
  const add = (file: string, k: string): void => {
    if (k in files) return;
    files[k] = read(file);
    if (readdirSync(dirname(file)).includes("LICENSE")) files[join(dirname(k), "LICENSE")] = read(join(dirname(file), "LICENSE"));
  };
  // bend keys a .bend file by its real path and resolves its imports from its real directory (bend.ts:952-1019).
  const visit = (file: string): void => {
    const real = realOf(file);
    const k = file === entry ? basename(entry) : key(file, relative(root, real));
    if (k in files) return;
    add(real, k);
    const text = files[k];
    // resolve, not join: an absolute import must stay absolute, so key() refuses it as bend does.
    for (const { path } of importPaths(text)) if (!isHubImport(path)) visit(resolve(dirname(real), path));
    for (const m of text.matchAll(FOREIGN)) {
      if (!/\.(c|js)$/.test(m[1])) continue;
      const at = join(dirname(real), m[1]);
      add(at, key(at, join(relative(root, dirname(real)), m[1])));
    }
  };
  visit(entry);
  // readme: false is the rule of bend 2.0.39 and earlier, under which older releases were hashed.
  if ((opts.readme ?? true) && readdirSync(root).includes("README.md")) {
    const readme = join(root, "README.md");
    files["README.md"] = read(readme);
    const size = Buffer.byteLength(files["README.md"]);
    if (size > README_MAX) throw new PkgError(`${readme} is ${size} bytes, over ${README_MAX}, the most BendHub takes; bend refuses to publish it`);
  }
  return files;
}

if (import.meta.main) {
  const entry = process.argv[2];
  if (!entry) usage("need <entry.bend>");
  let files: Record<string, string>;
  try { files = packageFiles(entry); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
  console.log(hubHash(files));
  for (const p of Object.keys(files).sort()) console.error(`  ${p}`);
}
