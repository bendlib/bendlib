// comments: lint the mechanical part of the comment policy in AGENTS.md ("Comments").
// Checks packages/**/*.bend and tools/**/*.ts (fixtures and goldens excluded).
//
// usage: bun tools/comments.ts [paths...]
// exit: 0 clean · 1 findings

import { readdirSync, readFileSync, statSync } from "node:fs";
import { join, relative } from "node:path";
import { GENERATED_MARK } from "./mathlib/lib.ts";

const ROOT = join(import.meta.dir, "..");
const TODO = /\b(TODO|FIXME|XXX|HACK)\b/;
const findings: string[] = [];

function walk(dir: string, out: string[] = []): string[] {
  for (const e of readdirSync(dir)) {
    if (["node_modules", "fixtures", "goldens", ".cache"].includes(e)) continue;
    const p = join(dir, e);
    if (statSync(p).isDirectory()) walk(p, out);
    else if (p.endsWith(".bend") || p.endsWith(".ts")) out.push(p);
  }
  return out;
}

function lintBend(file: string, lines: string[]) {
  const at = (i: number, msg: string) => findings.push(`${relative(ROOT, file)}:${i + 1}: ${msg}`);
  let i = 0, header = 0;
  while (i < lines.length && lines[i].startsWith("#")) { header++; i++; }
  if (header > 3) at(0, `module header has ${header} comment lines (max 3)`);
  for (let j = header; j < lines.length; j++) {
    const l = lines[j], t = l.trim();
    if (!t.startsWith("#")) continue;
    const text = t.replace(/^#\s?/, "");
    if (TODO.test(text)) at(j, "TODO/FIXME/XXX/HACK in a comment (open an issue instead)");
    if (/^(def|law|match|case|import|type)\b|\{==\}|^%/.test(text)) at(j, "looks like commented-out code");
    const prevIsComment = j > 0 && lines[j - 1].trim().startsWith("#");
    if (prevIsComment && !lines[j - 1].startsWith(GENERATED_MARK)) at(j, "comment blocks are limited to one line here");
    if (l.startsWith("#")) {
      if (l === GENERATED_MARK) continue;
      const next = lines.slice(j + 1).find((x) => x.trim() !== "") ?? "";
      if (!/^(law|def)\s/.test(next)) at(j, "top-level comment must be a doc line directly above a law or def");
      else if (!/^# [A-Z].*\.$/.test(l)) at(j, "doc line format is '# <Sentence ending with a period.>'");
    }
  }
}

function lintTs(file: string, lines: string[]) {
  const at = (i: number, msg: string) => findings.push(`${relative(ROOT, file)}:${i + 1}: ${msg}`);
  let i = lines[0]?.startsWith("#!") ? 1 : 0, header = 0;
  while (i < lines.length && lines[i].trim().startsWith("//")) { header++; i++; }
  if (header > 12) at(0, `file header has ${header} comment lines (max 12)`);
  let comments = 0, nonBlank = 0, run = 0;
  for (let j = i; j < lines.length; j++) {
    const t = lines[j].trim();
    if (t === "") { run = 0; continue; }
    nonBlank++;
    const full = t.startsWith("//") || t.startsWith("/*") || t.startsWith("*");
    const inline = !full && /\s\/\/\s/.test(t) && !/["'`][^"'`]*\/\/[^"'`]*["'`]/.test(t);
    if (!full && !inline) { run = 0; continue; }
    comments++;
    const text = full ? t.replace(/^(\/\/+|\/\*+|\*+)\s?/, "").replace(/\*\/$/, "") : t.slice(t.indexOf("//") + 2);
    if (TODO.test(text)) at(j, "TODO/FIXME/XXX/HACK in a comment (open an issue instead)");
    if (full && /(;|\{|\})\s*$|^\s*(const|let|if|for|return|import|await)\b/.test(text)) at(j, "looks like commented-out code");
    if (full) { run++; if (run === 3) at(j, "comment block longer than 2 lines outside the file header"); }
    if (t.startsWith("/*") && !t.endsWith("*/")) at(j, "multi-line /* */ comments are not allowed; use a one-line /** … */");
  }
  if (nonBlank >= 20 && comments / nonBlank > 0.25) at(0, `comment density ${Math.round((100 * comments) / nonBlank)}% exceeds 25% (header excluded)`);
}

const targets = process.argv.slice(2);
const expand = (p: string) => (statSync(p).isDirectory() ? walk(p) : [p]);
const files = (targets.length ? targets : [join(ROOT, "packages"), join(ROOT, "tools")]).flatMap(expand);
for (const f of files) {
  const lines = readFileSync(f, "utf8").split("\n");
  if (f.endsWith(".bend")) lintBend(f, lines); else lintTs(f, lines);
}
for (const f of findings) console.log(f);
console.log(`${findings.length} comment finding(s) in ${files.length} file(s)`);
process.exit(findings.length ? 1 : 0);
