// Shared helpers for the bend-mathlib tools (check, lint, twins, lock).
//
// These tools parse only OUR package sources, which follow strict conventions
// (PLAN.md §3.1): top-level items start at column 0, every law is a `law name:`
// block with one-line claims, immediately followed by its `def name(...)` proof.
// Third-party code is read with tools/reader (the official parser) instead.

import { readFileSync, readdirSync } from "node:fs";
import { join, basename } from "node:path";
import { homedir } from "node:os";

export const ROOT = join(import.meta.dir, "..", "..");
export const BEND = process.env.BEND_CLI ?? join(homedir(), ".bend", "bin", "bend");

export type Binder = { raw: string; name: string; mark: "" | "-" | "+" | "~"; type: string; where: boolean };
export type Law = {
  name: string; line: number; doc: string[]; binders: Binder[]; claimLines: string[]; exs: boolean;
  proof?: { line: number; args: string[]; body: string[] };
};
export type Def = { name: string; line: number; header: string; body: string[] };
export type Module = { file: string; name: string; text: string; laws: Law[]; defs: Def[]; types: { name: string; line: number }[]; imports: string[] };

// Strip `#` comments and string/char literals so scans do not match inside them.
export function stripCommentsAndStrings(src: string): string {
  let out = "";
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === "#") { while (i < src.length && src[i] !== "\n") i++; continue; }
    if (c === '"' || c === "'") {
      const q = c; out += q; i++;
      while (i < src.length && src[i] !== q && src[i] !== "\n") { if (src[i] === "\\") i++; i++; }
      out += q; i++; continue;
    }
    out += c; i++;
  }
  return out;
}

function parseBinder(line: string): Binder | null {
  const m = line.match(/^\s+for\s+([-+~]?)([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.*)$/);
  if (!m) return null;
  const rest = m[3];
  const w = rest.search(/\swhere\s/);
  return { raw: line.trim(), mark: m[1] as Binder["mark"], name: m[2], type: (w >= 0 ? rest.slice(0, w) : rest).trim(), where: w >= 0 };
}

export function parseModule(file: string, source?: string): Module {
  const text = source ?? readFileSync(file, "utf8");
  const lines = text.split("\n");
  const mod: Module = { file, name: basename(file, ".bend"), text, laws: [], defs: [], types: [], imports: [] };
  const lawByName = new Map<string, Law>();
  const docAbove = (i: number) => {
    const d: string[] = [];
    for (let j = i - 1; j >= 0 && lines[j].startsWith("#"); j--) d.unshift(lines[j].replace(/^#\s?/, ""));
    return d;
  };
  const block = (i: number) => { // indented body lines after a top-level header
    const b: string[] = [];
    for (let j = i + 1; j < lines.length && (lines[j].startsWith(" ") || lines[j] === ""); j++) b.push(lines[j]);
    while (b.length && b[b.length - 1] === "") b.pop();
    return b;
  };
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i];
    let m: RegExpMatchArray | null;
    if ((m = l.match(/^import\s+(\S+)/))) mod.imports.push(m[1]);
    else if ((m = l.match(/^law\s+([A-Za-z_][A-Za-z0-9_.]*)\s*:\s*$/))) {
      const law: Law = { name: m[1], line: i + 1, doc: docAbove(i), binders: [], claimLines: [], exs: false };
      for (const b of block(i)) {
        if (b.trim() === "") continue;
        const bd = parseBinder(b);
        if (bd) law.binders.push(bd);
        else if (/^\s+exs\s/.test(b)) law.exs = true;
        else law.claimLines.push(b.trim());
      }
      mod.laws.push(law); lawByName.set(law.name, law);
    } else if ((m = l.match(/^(?:@unsafe\s+)?def\s+([A-Za-z_][A-Za-z0-9_.]*)(\??)\s*\((.*)$/))) {
      const name = m[1];
      const law = lawByName.get(name);
      const body = block(i);
      if (law && !law.proof) {
        const args = (l.match(/^def\s+[^(]+\(([^)]*)\)/)?.[1] ?? "").split(",").map((s) => s.trim()).filter(Boolean);
        law.proof = { line: i + 1, args, body };
      } else {
        mod.defs.push({ name, line: i + 1, header: l, body });
      }
    } else if ((m = l.match(/^type\s+([A-Za-z_][A-Za-z0-9_.]*)/))) mod.types.push({ name: m[1], line: i + 1 });
  }
  return mod;
}

export function packageModules(pkgDir: string): string[] {
  const out: string[] = [];
  const walk = (dir: string) => {
    for (const e of readdirSync(dir, { withFileTypes: true })) {
      if (e.isDirectory()) walk(join(dir, e.name));
      else if (e.name.endsWith(".bend")) out.push(join(dir, e.name));
    }
  };
  walk(pkgDir);
  return out.sort();
}

// Split `{L == R : T}` at depth 0 (parens/braces/brackets). Returns null if not an equation.
export function splitEquation(claim: string): { lhs: string; rhs: string; type: string } | null {
  const s = claim.trim();
  if (!s.startsWith("{") || !s.endsWith("}")) return null;
  const inner = s.slice(1, -1);
  let depth = 0, eq = -1, colon = -1;
  for (let i = 0; i < inner.length; i++) {
    const c = inner[i];
    if ("({[".includes(c)) depth++;
    else if (")}]".includes(c)) depth--;
    else if (depth === 0 && inner.startsWith(" == ", i) && eq < 0) eq = i;
    else if (depth === 0 && inner.startsWith(" : ", i)) colon = i;
  }
  if (eq < 0 || colon < 0 || colon < eq) return null;
  return { lhs: inner.slice(0, eq).trim(), rhs: inner.slice(eq + 4, colon).trim(), type: inner.slice(colon + 3).trim() };
}

// Names defined by the pinned compiler's Base (for collision checks).
export async function baseNames(): Promise<Set<string>> {
  const p = Bun.spawnSync([BEND, "base"], { env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
  const out = new TextDecoder().decode(p.stdout);
  const names = new Set<string>();
  for (const m of out.matchAll(/^(?:def|law|type)\s+([A-Za-z_][A-Za-z0-9_.]*)/gm)) names.add(m[1]);
  for (const m of out.matchAll(/^\s+([A-Z][A-Za-z0-9_]*)\{/gm)) names.add(m[1]); // constructors
  return names;
}

export const GENERATED_MARK = "# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---";
