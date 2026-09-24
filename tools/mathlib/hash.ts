// hash: compute the BendHub content hash of a package, exactly as `bend --publish` does
// (bend2/main.ts cli_publish + pkg_files): the entry at its basename, every local `./` import
// at its path, a LICENSE beside any file; "0x" + sha256 of "sha256(content) path\n" lines, 32 hex.

import { createHash } from "node:crypto";
import { existsSync, readFileSync } from "node:fs";
import { basename, dirname, join, normalize, relative } from "node:path";

const sha256 = (s: string) => createHash("sha256").update(s).digest("hex");

export function hubHash(files: Record<string, string>): string {
  const lines = Object.keys(files).sort().map((p) => sha256(files[p]) + " " + p + "\n");
  return "0x" + sha256(lines.join("")).slice(0, 32);
}

/** Collect the files `bend <entry> --publish` would upload (local imports only; hub imports stay out). */
export function packageFiles(entry: string): Record<string, string> {
  const root = dirname(entry);
  const files: Record<string, string> = {};
  const visit = (file: string) => {
    const key = file === entry ? basename(entry) : normalize(relative(root, file));
    if (key.startsWith("..")) throw new Error(`${file} climbs above the package root; publishing would bundle it`);
    if (key in files) return;
    const text = readFileSync(file, "utf8");
    files[key] = text;
    const lic = join(dirname(file), "LICENSE");
    if (existsSync(lic)) files[join(dirname(key), "LICENSE").replace(/^\.\//, "")] = readFileSync(lic, "utf8");
    for (const m of text.matchAll(/^import\s+(\.\.?\/\S+\.bend)\s+as\s+\w+/gm)) visit(join(dirname(file), m[1]));
  };
  visit(entry);
  return files;
}

if (import.meta.main) {
  const entry = process.argv[2];
  if (!entry) { console.error("usage: bun tools/mathlib/hash.ts <entry.bend>"); process.exit(2); }
  const files = packageFiles(entry);
  console.log(hubHash(files));
  for (const p of Object.keys(files).sort()) console.error(`  ${p}`);
}
