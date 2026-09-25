// Whole-identifier rewriting of printed Bend terms: substitute binder values and
// qualify the user's names through import aliases, never touching literals.

export class Shadowed extends Error {}

type Tok = { s: string; id: boolean };

const IDENT = /^[A-Za-z_0-9$][A-Za-z0-9_.$/]*/;
const PATH = /^\/[A-Za-z0-9_.$][A-Za-z0-9_.$\/-]*/;

function tokens(src: string): Tok[] {
  const out: Tok[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === '"' || c === "'") {
      let j = i + 1;
      while (j < src.length && src[j] !== c) j += src[j] === "\\" ? 2 : 1;
      out.push({ s: src.slice(i, j + 1), id: false });
      i = j + 1;
      continue;
    }
    const m = (c === "/" ? PATH : IDENT).exec(src.slice(i));
    if (m !== null) {
      let w = m[0];
      while (w.endsWith(".") || w.endsWith("/")) w = w.slice(0, -1);
      out.push({ s: w, id: /^[A-Za-z_$/]/.test(w) || w.startsWith("0x") });
      i += w.length;
      continue;
    }
    out.push({ s: c, id: false });
    i++;
  }
  return out;
}

/** Names bound by lambdas (`x => …`, `+x => …`) inside a printed term. */
export function lambdaBound(src: string): Set<string> {
  const ts = tokens(src);
  const out = new Set<string>();
  for (let i = 0; i < ts.length; i++) {
    if (!ts[i].id) continue;
    let j = i + 1;
    while (ts[j]?.s === " ") j++;
    if (ts[j]?.s === "=" && ts[j + 1]?.s === ">") out.add(ts[i].s);
  }
  return out;
}

export function atomic(text: string): boolean {
  return /^[A-Za-z0-9_.$'"]*$/.test(text);
}

/** Binder names in `env` become their value text (parenthesized); other identifiers go through `qualify`. */
export function rewrite(src: string, env: Map<string, string>, qualify: (id: string) => string, wrap = true): string {
  const bound = lambdaBound(src);
  for (const b of bound) if (env.has(b)) throw new Shadowed(b);
  return tokens(src).map((t) => {
    if (!t.id || bound.has(t.s)) return t.s;
    const v = env.get(t.s);
    if (v !== undefined) return !wrap || atomic(v) || v.startsWith("&") ? v : `(${v})`;
    return qualify(t.s);
  }).join("");
}

export function mentions(src: string, name: string): boolean {
  return tokens(src).some((t) => t.id && t.s === name);
}

export type TermDecl = { params: number; templates: number };

// Display polish over a printed term: template arguments regain their `~`, and a zero-argument
// def used as a call regains its `()`. Names the map does not know are left untouched.
export function showTerm(src: string, decls: Map<string, TermDecl>): string {
  const ts = tokens(src);
  const before = new Map<number, string>(), after = new Map<number, string>();
  const step = (s: string) => s === "(" || s === "[" || s === "{" ? 1 : s === ")" || s === "]" || s === "}" ? -1 : 0;
  for (let i = 0; i < ts.length; i++) {
    if (!ts[i].id) continue;
    const d = decls.get(ts[i].s);
    if (d === undefined) continue;
    let j = i + 1;
    while (ts[j]?.s === " ") j++;
    if (ts[j]?.s !== "(") {
      if (d.params === 0) after.set(i, "()");
      continue;
    }
    if (d.templates === 0) continue;
    let k = j + 1, depth = 1, arg = 0, first = true;
    while (k < ts.length && depth > 0) {
      const s = ts[k].s;
      if (first && s !== " " && s !== ")") {
        if (arg < d.templates && s !== "~") before.set(k, "~");
        first = false;
      }
      if (s === "," && depth === 1) { arg++; first = true; }
      else depth += step(s);
      k++;
    }
  }
  let out = "";
  for (let i = 0; i < ts.length; i++) {
    if (before.has(i)) out += before.get(i);
    out += ts[i].s;
    if (after.has(i)) out += after.get(i);
  }
  return out;
}

/** Splits a printed `{lhs == rhs : T}` at its top-level `==` and last top-level `:`. */
export function splitEquation(goal: string): { lhs: string; rhs: string; type: string } | null {
  const g = goal.trim();
  if (!g.startsWith("{") || !g.endsWith("}")) return null;
  const body = g.slice(1, -1);
  let depth = 0, eq = -1, colon = -1;
  for (let i = 0; i < body.length; i++) {
    const c = body[i];
    if (c === '"' || c === "'") {
      let j = i + 1;
      while (j < body.length && body[j] !== c) j += body[j] === "\\" ? 2 : 1;
      i = j;
      continue;
    }
    if ("([{".includes(c)) depth++;
    else if (")]}".includes(c)) depth--;
    else if (depth === 0 && body.startsWith(" == ", i) && eq < 0) eq = i;
    else if (depth === 0 && body.startsWith(" : ", i)) colon = i;
  }
  if (eq < 0 || colon < eq) return null;
  return { lhs: body.slice(0, eq).trim(), rhs: body.slice(eq + 4, colon).trim(), type: body.slice(colon + 3).trim() };
}
