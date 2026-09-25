// lawcheck core: load a file with @bendlib/reader, turn each law into closed
// instances, evaluate them with the checker, and shrink counterexamples.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { BendReadError, decls, load, show, type Decl, type Loaded } from "../../reader/index.ts";
import { stripCommentsAndStrings } from "../../mathlib/lib.ts";
import { bendBin, cleanCheck, evaluate, evaluateAll, locate, ModuleError, overflowed, runBatch, type Engine, type Item, type Outcome } from "./checker.ts";
import { defSpan, mutants } from "./mutate.ts";
import { mentions, rewrite, Shadowed, showTerm, splitEquation, type TermDecl } from "./terms.ts";
import { parseTy, showTy, substTy, type Ty } from "./types.ts";
import { measure, mulberry32, render, Universe, Unsupported, type Adt, type Rng, type Val } from "./values.ts";

export type Options = {
  size: number;
  maxInstances: number;
  seed: number;
  law?: string;
  impl?: string;
  jobs?: number;
  timeoutMs?: number;
  tmpDir?: string;
  maxNat?: number;
  shrink?: boolean;
  firstFail?: boolean;
  native?: boolean;
};

export type MutateOptions = Partial<Options> & { def?: string };

export type Binding = { name: string; value: string };

export type NativeDisagreement = {
  bindings: Binding[];
  engineC: "pass" | "open" | "fail";
  engineN: boolean;
  repro: string;
};

export type Counterexample = {
  bindings: Binding[];
  types: Binding[];
  claim: string;
  lhs?: { term: string; value: string };
  rhs?: { term: string; value: string };
  goal?: string;
  expected?: string;
  observed?: string;
  premises?: string[];
  original: Binding[];
  shrinkSteps: number;
};

export type LawResult = {
  name: string;
  file: string;
  line: number;
  proved: boolean;
  claim: "equation" | "predicate" | "refutation" | "witness" | "other";
  status: "pass" | "fail" | "skip" | "error";
  reason?: string;
  instances: number;
  failures: number;
  tooLarge?: number;
  native?: { checked: number; disagreements: NativeDisagreement[]; skip?: string };
  premise?: { satisfied: number; total: number };
  counterexample?: Counterexample;
};

export type Report = { schema: number; tool: "lawcheck"; version: string; bend: string; file: string; seed: number; size: number; maxInstances: number; maxNat: number; tmpDir: string; checkerRuns: number; laws: LawResult[] };

export type MutantResult = {
  id: string; def: string; op: string; line: number; before: string; after: string;
  status: "killed" | "survived" | "unknown" | "invalid"; law?: string; detail?: string;
};

export type MutateReport = {
  schema: number; tool: "lawcheck-mutate"; version: string; bend: string; file: string; impl: string | null;
  seed: number; maxInstances: number; tmpDir: string;
  defs: { name: string; mutants: MutantResult[] }[];
};

export const VERSION = "0.2.1";

class Skip extends Error {}

type Value = { name: string; ty: Ty };
type FunBinder = { name: string; args: string[]; ret: string };
type ExBinder = { name: string; ty: Ty };
type PredStmt = { params: string[]; lhs: string; rhs: string; type: string };
type PremSig = { k: "eq" } | { k: "pred"; stmt: PredStmt } | { k: "opaque" };
type Slot = { lhs: string; rhs: string; type: string };
type Plan = {
  d: Decl;
  kind: LawResult["claim"];
  claim: string;
  typeParams: string[];
  quantParams: string[];
  values: Value[];
  funs: FunBinder[];
  exs: ExBinder[];
  premises: string[];
  premiseSigs: PremSig[];
  claimSig: PremSig;
};
type Inst = { vals: Val[]; types: Map<string, string>; funs: string[] };

// Closed lambdas per instantiated signature, substituted for template function
// binders `~f` (PLAN F12/F28). Params `lc_*`; affine, so used at most once.
const CATALOG: Record<string, string[]> = {
  "Nat -> Nat": ["(lc_x => lc_x)", "(lc_x => 0n)", "(lc_x => 1n+lc_x)", "(lc_x => Nat.double(lc_x))"],
  "Nat -> Bool": ["(lc_x => True{})", "(lc_x => False{})", "(lc_x => Nat.is_le(lc_x, 1n))"],
  "Nat -> Nat -> Bool": ["(lc_x => lc_y => Nat.is_le(lc_x, lc_y))", "(lc_x => lc_y => Nat.is_eq(lc_x, lc_y))", "(lc_x => lc_y => True{})"],
  "Nat -> Nat -> Nat": ["(lc_x => lc_y => Nat.add(lc_x, lc_y))", "(lc_x => lc_y => lc_x)", "(lc_x => lc_y => lc_y)"],
  "U32 -> U32": ["(lc_x => lc_x)", "(lc_x => 0)", "(lc_x => (1 + lc_x : U32))", "(lc_x => U32.mul(lc_x, 2))"],
  "U32 -> Bool": ["(lc_x => True{})", "(lc_x => False{})", "(lc_x => U32.is_le(lc_x, 1))"],
  "U32 -> U32 -> Bool": ["(lc_x => lc_y => U32.is_le(lc_x, lc_y))", "(lc_x => lc_y => U32.is_eq(lc_x, lc_y))", "(lc_x => lc_y => True{})"],
  "U32 -> U32 -> U32": ["(lc_x => lc_y => U32.add(lc_x, lc_y))", "(lc_x => lc_y => lc_x)", "(lc_x => lc_y => lc_y)"],
};

/** Splits a printed arrow type on its top-level `->`. */
function splitArrow(t: string): string[] {
  const out: string[] = [];
  let depth = 0, start = 0;
  for (let i = 0; i < t.length; i++) {
    const c = t[i];
    if (c === "(" || c === "[" || c === "{") depth++;
    else if (c === ")" || c === "]" || c === "}") depth--;
    else if (depth === 0 && c === "-" && t[i + 1] === ">") { out.push(t.slice(start, i)); start = i + 2; i++; }
  }
  out.push(t.slice(start));
  return out;
}

function parseFun(name: string, t: string): FunBinder {
  const parts = splitArrow(t).map((s) => s.trim());
  const ret = parts.pop() ?? "";
  return { name, args: parts.map((s) => s.replace(/^@_:\s*/, "")), ret };
}

/** The printed signature with type parameters instantiated to `choice`. */
function substSig(f: FunBinder, choice: string, typeParams: string[]): string {
  const env = new Map(typeParams.map((n) => [n, choice]));
  const sub = (s: string) => s.replace(/[A-Za-z_][A-Za-z0-9_]*/g, (id) => env.get(id) ?? id);
  return [...f.args.map(sub), sub(f.ret)].join(" -> ");
}

/** Splits a printed `&name:VALUE -> BODY` sigma (a `where` premise or an `exs` witness) at its top-level arrow. */
function splitSigma(t: string): { name: string; value: string; body: string } | null {
  const m = /^&([A-Za-z_]\w*):/.exec(t);
  if (m === null) return null;
  const rest = t.slice(m[0].length);
  let depth = 0;
  for (let i = 0; i + 4 <= rest.length; i++) {
    const c = rest[i];
    if (c === "(" || c === "{" || c === "[") depth++;
    else if (c === ")" || c === "}" || c === "]") depth--;
    else if (depth === 0 && rest.startsWith(" -> ", i)) return { name: m[1], value: rest.slice(0, i), body: rest.slice(i + 4) };
  }
  return null;
}

const TYPE_CHOICES = ["U32", "Nat"];

/** Human text for an unsafe-reliance count. */
const unsafeText = (n: number) => `unsafe or foreign code (${n} def${n === 1 ? "" : "s"})`;

/** Human text for `@unsafe` found by the independent source scan. */
const unsafeFilesText = (files: string[]) => `unsafe or foreign code (@unsafe in ${files.join(", ")})`;

function tipOf(L: Loaded, key: string): string {
  const B = L.bend;
  let t = B.term_lower(L.book.tlds[key].T, 0);
  const bnd: string[] = [];
  while (t.$ === "All") { bnd.push(t.k); t = t.B; }
  return B.term_show(t, -1, bnd);
}

function universe(L: Loaded, maxNat = 30): Universe {
  const B = L.bend;
  const adts = new Map<string, Adt>();
  for (const d of decls(L, { scope: "all" })) {
    if (d.kind !== "type") continue;
    const params: string[] = [];
    let t = B.term_lower(L.book.tlds[d.name].T, 0);
    while (t.$ === "All") { params.push(t.k); t = t.B; }
    const ctors = L.book.tlds[d.name].c.map((c: any) => {
      let u = B.term_lower(c.T, 0);
      const bnd: string[] = [];
      const cparams: string[] = [];
      const fields: Ty[] = [];
      while (u.$ === "All") {
        const shown = B.term_show(u.A, -1, [...bnd]);
        if (cparams.length < params.length) cparams.push(u.k);
        else fields.push(parseTy(shown) ?? { t: "app", head: `<${shown}>`, args: [], paren: false });
        bnd.push(u.k);
        u = u.B;
      }
      return { name: c.k, params: cparams, fields };
    });
    adts.set(d.name, { name: d.name, params, ctors });
  }
  return new Universe(adts, maxNat);
}

function plan(L: Loaded, d: Decl, predicates: Map<string, PredStmt | null>, U: Universe): Plan {
  const binders = d.binders ?? [];
  const p: Plan = { d, kind: "other", claim: "", typeParams: [], quantParams: [], values: [], funs: [], exs: [], premises: [], premiseSigs: [], claimSig: { k: "opaque" } };
  const premiseNames: string[] = [];
  const isPredicateApp = (s: string) => {
    const head = applicationHead(s);
    return head !== null && predicates.has(head);
  };
  const sigOf = (s: string): PremSig => {
    if (s.trim().startsWith("{")) return { k: "eq" };
    const head = applicationHead(s);
    if (head !== null) {
      const st = predicates.get(head);
      if (st !== undefined && st !== null) return { k: "pred", stmt: st };
    }
    return { k: "opaque" };
  };
  for (const b of binders) {
    const t = b.type;
    const tmpl = b.quant === "template";
    if (tmpl && t === "Quant") { p.quantParams.push(b.name); continue; }
    if (tmpl && /^(Type|Data|Kind\(.*\))$/.test(t)) { p.typeParams.push(b.name); continue; }
    if (tmpl && t.includes("->")) { p.funs.push(parseFun(b.name, t)); continue; }
    if (tmpl && t.startsWith("{")) throw new Skip("template hypothesis");
    if (t === "Quant") p.quantParams.push(b.name);
    else if (/^(Type|Data|Kind\(.*\))$/.test(t)) p.typeParams.push(b.name);
    else if (t.startsWith("{")) { p.premises.push(t); p.premiseSigs.push(sigOf(t)); premiseNames.push(b.name); }
    else if (/^&[A-Za-z_]\w*:/.test(t)) {
      const sig = splitSigma(t);
      const ty = sig === null ? null : parseTy(sig.value);
      if (sig === null || ty === null) throw new Skip(`\`where\` premise on ${b.name}: cannot generate values of ${sig?.value ?? t}`);
      p.values.push({ name: b.name, ty });
      p.premises.push(sig.body);
      p.premiseSigs.push(sigOf(sig.body));
    }
    else if (t.includes("->")) throw new Skip(`function-typed binder ${b.name}: ${t}`);
    else if (tmpl) throw new Skip(`template binder ~${b.name}: ${t}`);
    else {
      const ty = parseTy(t);
      if (ty !== null && generable(U, substTy(ty, envTypes(p, TYPE_CHOICES[0])))) p.values.push({ name: b.name, ty });
      else if (isPredicateApp(t)) { p.premises.push(t); p.premiseSigs.push(sigOf(t)); premiseNames.push(b.name); }
      else if (ty === null) throw new Skip(`binder ${b.name}: cannot generate values of ${t}`);
      else p.values.push({ name: b.name, ty });
    }
  }
  const tip = tipOf(L, d.name);
  if (d.statement) {
    // Definitional inequality of two functions is not a counterexample (PLAN F22).
    if (splitArrow(d.statement.type).length > 1) throw new Skip("equation between functions: definitional inequality is not a counterexample");
    p.kind = "equation";
    p.claim = `{${d.statement.lhs} == ${d.statement.rhs} : ${d.statement.type}}`;
    p.claimSig = { k: "eq" };
  } else if (tip === "Empty" && p.premises.length > 0) {
    p.kind = "refutation";
    p.claim = "Empty";
  } else if (isPredicateApp(tip)) {
    p.kind = "predicate";
    p.claim = tip;
    p.claimSig = sigOf(tip);
  } else if (/^&[A-Za-z_]\w*:/.test(tip)) {
    let body = tip;
    for (;;) {
      const sig = splitSigma(body);
      if (sig === null) break;
      const ty = parseTy(sig.value);
      if (ty === null) throw new Skip(`\`exs\` witness ${sig.name}: cannot generate values of ${sig.value}`);
      p.exs.push({ name: sig.name, ty });
      body = sig.body;
    }
    p.kind = "witness";
    p.claim = body;
  } else {
    throw new Skip(`claim is not an equation or a single predicate application: ${tip}`);
  }
  for (const n of premiseNames) {
    if (n !== "_" && [p.claim, ...p.premises].some((s) => mentions(s, n))) throw new Skip(`the claim uses the premise proof ${n}`);
  }
  for (const v of p.values) {
    for (const choice of p.typeParams.length ? TYPE_CHOICES : [""]) {
      const env = envTypes(p, choice);
      try {
        U.check(substTy(v.ty, env));
      } catch (e) {
        if (e instanceof Unsupported) throw new Skip(`binder ${v.name}: no generator for type ${e.message}`);
        throw e;
      }
    }
  }
  for (const f of p.funs) {
    for (const choice of p.typeParams.length ? TYPE_CHOICES : [""]) {
      const sig = substSig(f, choice, p.typeParams);
      if (CATALOG[sig] === undefined) throw new Skip(`no catalog functions for ~${f.name}: ${sig}`);
    }
  }
  for (const e of p.exs) {
    for (const choice of p.typeParams.length ? TYPE_CHOICES : [""]) {
      try {
        U.check(substTy(e.ty, envTypes(p, choice)));
      } catch (err) {
        if (err instanceof Unsupported) throw new Skip(`\`exs\` witness ${e.name}: no generator for type ${err.message}`);
        throw err;
      }
    }
  }
  return p;
}

/** The head of `f(args)` when the whole string is that one application, else null. */
export function applicationHead(s: string): string | null {
  const m = /^([A-Za-z_\/][A-Za-z0-9_.\/$-]*)\(/.exec(s);
  if (m === null || !s.endsWith(")")) return null;
  let depth = 0;
  for (let i = m[1].length; i < s.length; i++) {
    if ("([{".includes(s[i])) depth++;
    else if (")]}".includes(s[i]) && --depth === 0 && i !== s.length - 1) return null;
  }
  return m[1];
}

/** Top-level comma-separated arguments of a whole application `head(a, b, …)`. */
function applicationArgs(s: string): string[] | null {
  const open = s.indexOf("(");
  if (open < 0 || !s.endsWith(")")) return null;
  const inner = s.slice(open + 1, -1);
  const out: string[] = [];
  let depth = 0, field = "";
  for (const ch of inner) {
    if ("([{<".includes(ch)) depth++;
    else if (")]}>".includes(ch)) depth--;
    if (ch === "," && depth === 0) { out.push(field.trim()); field = ""; }
    else field += ch;
  }
  if (field.trim() !== "") out.push(field.trim());
  return out;
}

/** The equation a `Data`-valued predicate def stands for, read from its single-statement body. */
function predicateStatement(L: Loaded, d: Decl): PredStmt | null {
  const f = L.files.find((x) => x.path === d.file);
  if (f === undefined) return null;
  const lines = f.parsed.split("\n");
  const params = [...d.signature.matchAll(/@([A-Za-z_]\w*)\s*:/g)].map((m) => m[1]);
  for (let i = d.line; i < lines.length && i <= d.line + 6; i++) {
    const line = lines[i].trim();
    if (line === "" || line.startsWith("#")) continue;
    const m = /^(\{.*\})$/.exec(line);
    if (m === null) return null;
    const eq = splitEquation(m[1]);
    return eq === null ? null : { params, ...eq };
  }
  return null;
}

/** The equation of one premise, or null when it cannot be turned into one. */
function premiseSlot(sig: PremSig, raw: string, env: Map<string, string>, qualify: (s: string) => string): Slot | null {
  if (sig.k === "opaque") return null;
  if (sig.k === "eq") return splitEquation(rewrite(raw, env, qualify));
  const args = applicationArgs(raw);
  if (args === null || args.length !== sig.stmt.params.length) return null;
  const argq = args.map((a) => rewrite(a, env, qualify));
  const pe = new Map(sig.stmt.params.map((nm, j) => [nm, argq[j]]));
  return { lhs: rewrite(sig.stmt.lhs, pe, qualify), rhs: rewrite(sig.stmt.rhs, pe, qualify), type: rewrite(sig.stmt.type, pe, qualify) };
}

const nestPair = (vs: string[]): string => vs.length <= 1 ? vs[0] : `(${vs[0]}, ${nestPair(vs.slice(1))})`;
const nestType = (ts: string[]): string => ts.length <= 1 ? ts[0] : ts.length === 2 ? `${ts[0]} & ${ts[1]}` : `${ts[0]} & (${nestType(ts.slice(1))})`;

/** Splits the checker's flattened tuple `(a, b, …)` at top-level commas. */
function splitTuple(s: string): string[] | null {
  const t = s.trim();
  if (!t.startsWith("(") || !t.endsWith(")")) return null;
  const out: string[] = [];
  let depth = 0, field = "";
  for (const ch of t.slice(1, -1)) {
    if ("([{".includes(ch)) depth++;
    else if (")]}".includes(ch)) depth--;
    if (ch === "," && depth === 0) { out.push(field.trim()); field = ""; }
    else field += ch;
  }
  out.push(field.trim());
  return out;
}

/** Components safe to compare by printed form: a Bool, a number/char/string literal. */
const trustComp = (s: string) => /^(True\{\}|False\{\}|-?\d+n|-?\d+|'[^']*'|"(?:[^"\\]|\\.)*")$/.test(s);

function generable(U: Universe, ty: Ty): boolean {
  try {
    U.check(ty);
    return true;
  } catch (e) {
    if (e instanceof Unsupported) return false;
    throw e;
  }
}

function envTypes(p: Plan, choice: string): Map<string, Ty> {
  const env = new Map<string, Ty>();
  for (const q of p.quantParams) env.set(q, { t: "q", q: "&2" });
  for (const a of p.typeParams) env.set(a, { t: "app", head: choice, args: [], paren: false });
  return env;
}

function* product(doms: Val[][], order: number[]): Generator<Val[]> {
  for (const idx of order) {
    let k = idx;
    const out: Val[] = [];
    for (let i = doms.length - 1; i >= 0; i--) { out[i] = doms[i][k % doms[i].length]; k = Math.floor(k / doms[i].length); }
    yield out;
  }
}

const CATALOG_CAP = 64;

// Full catalog product up to CATALOG_CAP; above it a seeded sample that still uses every entry of
// every binder at least once (a lexicographic prefix silently misses later entries).
function catalogCombos(perFun: string[][], r: Rng): string[][] {
  const total = perFun.reduce((n, xs) => n * xs.length, 1);
  if (total <= CATALOG_CAP) {
    let combos: string[][] = [[]];
    for (const xs of perFun) combos = combos.flatMap((acc) => xs.map((x) => [...acc, x]));
    return combos;
  }
  const seed = perFun.map((xs) => xs[0]);
  const out: string[][] = [];
  const seen = new Set<string>();
  const push = (combo: string[]) => {
    const k = combo.join("\u0000");
    if (seen.has(k) || out.length >= CATALOG_CAP) return;
    seen.add(k);
    out.push(combo);
  };
  perFun.forEach((xs, j) => { for (const x of xs) push(seed.map((s, k) => (k === j ? x : s))); });
  for (let t = 0; out.length < CATALOG_CAP && t < CATALOG_CAP * 20; t++) push(perFun.map((xs) => xs[Math.floor(r() * xs.length)]));
  return out;
}

function instances(p: Plan, U: Universe, o: Options, r: Rng): Inst[] {
  const choices = p.typeParams.length ? TYPE_CHOICES : [""];
  const ctxs: { choice: string; funs: string[] }[] = [];
  for (const choice of choices) {
    const perFun = p.funs.map((f) => CATALOG[substSig(f, choice, p.typeParams)]);
    for (const funs of catalogCombos(perFun, r)) ctxs.push({ choice, funs });
  }
  const all: Inst[] = [];
  ctxs.forEach((ctx, ci) => {
    const budget = Math.floor(o.maxInstances / ctxs.length) + (ci < o.maxInstances % ctxs.length ? 1 : 0);
    const env = envTypes(p, ctx.choice);
    const tys = p.values.map((v) => substTy(v.ty, env));
    const types = new Map(p.typeParams.map((a) => [a, ctx.choice] as [string, string]));
    const seen = new Set<string>();
    const out: Inst[] = [];
    const add = (vals: Val[]) => {
      const k = vals.map((v) => render(v)).join("|");
      if (seen.has(k) || out.length >= budget) return;
      seen.add(k);
      out.push({ vals, types, funs: ctx.funs });
    };
    const exhaustive = Math.ceil(budget * 0.6);
    for (let d = 0; d <= o.size && out.length < exhaustive; d++) {
      const doms = tys.map((t) => U.enumerate(t, d));
      const total = doms.reduce((n, x) => n * x.length, 1);
      if (total === 0) continue;
      const room = exhaustive - out.length;
      const order = total <= room
        ? Array.from({ length: total }, (_, i) => i)
        : Array.from({ length: room * 4 }, () => Math.floor(r() * total));
      for (const vals of product(doms, order)) add(vals);
    }
    for (let tries = 0; out.length < budget && tries < budget * 20; tries++) {
      add(tys.map((t) => U.random(t, Math.max(o.size, 3), r)));
    }
    all.push(...out);
  });
  return all;
}

function aliasMap(L: Loaded) {
  const nsToAlias = new Map<string, { alias: string; file: string }>();
  let k = 0;
  const imports = [`import Base`, `import ${L.file} as U`];
  for (const f of L.files) {
    if (f.namespace === "") continue;
    const alias = `LC${++k}`;
    nsToAlias.set(f.namespace, { alias, file: f.path });
    imports.push(f.namespace.startsWith("0x") ? `import ${f.namespace}.bend as ${alias}` : `import ${f.path} as ${alias}`);
  }
  const own = new Set(L.own);
  for (const d of decls(L, { scope: "own" })) own.add(d.name);
  const nss = [...nsToAlias.keys()].sort((a, b) => b.length - a.length);
  const qualify = (id: string): string => {
    if (own.has(id)) return `U.${id}`;
    for (const ns of nss) if (id.startsWith(ns + ".")) return `${nsToAlias.get(ns)!.alias}.${id.slice(ns.length + 1)}`;
    return id;
  };
  const user = userAliases(L);
  const nameOut = (id: string): string => {
    for (const ns of nss) if (id.startsWith(ns + ".") && user.has(ns)) return `${user.get(ns)}.${id.slice(ns.length + 1)}`;
    return id;
  };
  const names = (s: string) => rewrite(s, new Map(), nameOut, false);
  const back: [string, string][] = [[L.file.replace(/\.bend$/, "") + ".", ""]];
  // The batch imports a hub module by its `0x…` name, so the checker prints that name, not
  // its file path; only modules imported by absolute path need a path back-map entry (README).
  for (const [ns, { file }] of nsToAlias) if (!ns.startsWith("0x")) back.push([file.replace(/\.bend$/, "") + ".", ns + "."]);
  back.sort((a, b) => b[0].length - a[0].length);
  const display = (s: string) => names(back.reduce((acc, [from, to]) => acc.split(from).join(to), s));
  return { header: imports.join("\n") + "\n", qualify, display, nameOut };
}

/** Namespace to the alias the root file imports it under, so output reads like the user's source. */
function userAliases(L: Loaded): Map<string, string> {
  const root = L.files.find((f) => f.path === L.file);
  const out = new Map<string, string>();
  for (const line of (root?.text ?? "").split("\n")) {
    const m = /^import\s+(\S+)\s+as\s+(\S+)\s*$/.exec(line.trim());
    if (m === null) continue;
    const spec = m[1];
    const abs = spec.startsWith("/") ? spec : spec.startsWith(".") ? path.resolve(path.dirname(L.file), spec) : null;
    let f = abs === null ? L.files.find((x) => x.namespace + ".bend" === spec) : L.files.find((x) => x.path === (fs.existsSync(abs) ? fs.realpathSync(abs) : abs));
    // `name@version/rest.bend` resolves through `names/<name>@<ver>` to `0x<hash>/rest.bend` (F21),
    // so match it by the part after the hash, which the import spec does name.
    if (f === undefined && abs === null) {
      const nv = /^[^/]*@[^/]*\/(.+)$/.exec(spec);
      if (nv !== null) {
        const rest = nv[1].replace(/\.bend$/, "");
        f = L.files.find((x) => x.namespace.startsWith("0x") && x.namespace.slice(x.namespace.indexOf("/") + 1) === rest);
      }
    }
    if (f && f.namespace !== "") out.set(f.namespace, m[2]);
  }
  return out;
}

function rootFor(file: string, impl: string | undefined, tmp: string): string {
  if (impl === undefined) return file;
  const dir = path.dirname(path.resolve(file));
  const implAbs = path.resolve(impl);
  if (!fs.existsSync(implAbs)) throw new UsageError(`--impl: no such file: ${impl}`);
  const lines = fs.readFileSync(file, "utf8").split("\n");
  const locals = lines.map((l, i) => ({ i, m: /^import\s+(\.{1,2}\/\S+\.bend)(\s+as\s+\S+)?\s*$/.exec(l.trim()) })).filter((x) => x.m !== null);
  let target = locals.filter((x) => path.basename(x.m![1]) === path.basename(implAbs));
  if (target.length === 0 && locals.length === 1) target = locals;
  if (target.length !== 1) throw new UsageError(`--impl: cannot tell which import of ${file} to replace (need one local import named ${path.basename(implAbs)})`);
  for (const x of locals) {
    const abs = x === target[0] ? implAbs : path.resolve(dir, x.m![1]);
    lines[x.i] = `import ${abs}${x.m![2] ?? ""}`;
  }
  const out = path.join(tmp, "impl_" + path.basename(file));
  fs.writeFileSync(out, lines.join("\n"));
  return out;
}

/** Copy a whitespace-path root into `tmp` under a safe basename (bend import lines are unquoted). */
function safeRoot(file: string, tmp: string): string {
  const real = fs.existsSync(file) ? fs.realpathSync(file) : file;
  if (!/[\s"']/.test(real)) return file;
  if (!fs.statSync(real).isFile()) return file;
  const dir = path.dirname(real);
  const lines = fs.readFileSync(real, "utf8").split("\n");
  lines.forEach((l, i) => {
    const m = /^import\s+(\.{1,2}\/\S+\.bend)(\s+as\s+\S+)?\s*$/.exec(l.trim());
    if (m === null) return;
    const abs = path.resolve(dir, m[1]);
    lines[i] = `import ${fs.existsSync(abs) ? fs.realpathSync(abs) : abs}${m[2] ?? ""}`;
  });
  const out = path.join(tmp, `root_${path.basename(real).replace(/[^\w.-]/g, "_")}`);
  fs.writeFileSync(out, lines.join("\n"));
  return out;
}

export class UsageError extends Error {}

/** Basenames of loaded non-Base files whose comment/string-stripped source has `@unsafe`. */
function unsafeModules(L: Loaded, baseFiles: Set<string>): string[] {
  return L.files
    .filter((f) => !baseFiles.has(f.path) && /(^|[^\w@])@unsafe\b/.test(stripCommentsAndStrings(f.text)))
    .map((f) => path.basename(f.path));
}

/** Runs the checker's own validation so a rejected target fails loudly, never as `0 laws`. */
function validate(L: Loaded): void {
  try {
    L.bend.book_valid(L.book);
  } catch (e) {
    let msg: string;
    try { msg = L.bend.err_show(e); } catch { msg = String(e); }
    throw new ModuleError(msg);
  }
}

// Base has no list equality, so engine N emits this recursive one for list claims.
// It is quantity-polymorphic: a law's Quant binder reaches engine C as &2.
const LIST_EQ: Record<string, string> = {
  Nat: `def internal_list_eq_nat(q, xs: List<q, Nat>, ys: List<q, Nat>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case y <> yt:
          False{}
    case x <> xt:
      match ys:
        case Nil{}:
          False{}
        case y <> yt:
          Bool.and(Nat.is_eq(x, y), internal_list_eq_nat(q, xt, yt))
`,
  U32: `def internal_list_eq_u32(q, xs: List<q, U32>, ys: List<q, U32>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case y <> yt:
          False{}
    case x <> xt:
      match ys:
        case Nil{}:
          False{}
        case y <> yt:
          Bool.and(U32.is_eq(x, y), internal_list_eq_u32(q, xt, yt))
`,
  Bool: `def internal_list_eq_bool(q, xs: List<q, Bool>, ys: List<q, Bool>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case y <> yt:
          False{}
    case x <> xt:
      match ys:
        case Nil{}:
          False{}
        case y <> yt:
          Bool.and(U32.is_eq(Bool.to_u32(x), Bool.to_u32(y)), internal_list_eq_bool(q, xt, yt))
`,
};

/** The native equality (and any helper def) for a claim type engine N can compare. */
function nativeEq(type: string): { eq: (a: string, b: string) => string; helper?: string } | null {
  if (type === "Nat") return { eq: (a, b) => `Nat.is_eq(${a}, ${b})` };
  if (type === "U32") return { eq: (a, b) => `U32.is_eq(${a}, ${b})` };
  if (type === "Bool") return { eq: (a, b) => `U32.is_eq(Bool.to_u32(${a}), Bool.to_u32(${b}))` };
  const ty = parseTy(type);
  if (ty !== null && ty.t === "app" && ty.head === "List" && ty.args.length >= 1) {
    const q = ty.args.length >= 2 ? showTy(ty.args[0]) : "&1";
    const el = showTy(ty.args[ty.args.length - 1]);
    const helper = LIST_EQ[el];
    if (helper !== undefined) return { eq: (a, b) => `internal_list_eq_${el.toLowerCase()}(${q}, ${a}, ${b})`, helper };
  }
  return null;
}

/** Writes a minimal native harness that prints one instance's equality. */
export function nativeRepro(head: string, line: string, file: string): void {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, `${head}def main() -> IO(Unit):\n  do IO<Unit>:\n${line}\n`);
}

/** Pairs engine C outcomes with engine N bits; returns the indices that disagree (PLAN §4.2 step 6). */
export function nativeDisagreements(c: (Outcome | undefined)[], n: (boolean | undefined)[]): number[] {
  const out: number[] = [];
  for (let i = 0; i < c.length; i++) {
    const co = c[i], no = n[i];
    if (co === undefined || no === undefined) continue;
    if (co.r === "fail") { if (no) out.push(i); }
    else if (co.r === "pass" || co.r === "open") { if (!no) out.push(i); }
  }
  return out;
}

/** A copy of the root with its open-law blocks removed and local imports made absolute, for engine N. */
function nativeRoot(L: Loaded, tmp: string): string {
  const open = decls(L, { scope: "own" }).filter((d) => d.kind === "law" && !d.proved).map((d) => d.line);
  const dir = path.dirname(L.file);
  const lines = fs.readFileSync(L.file, "utf8").split("\n");
  lines.forEach((l, i) => {
    const m = /^import\s+(\.{1,2}\/\S+\.bend)(\s+as\s+\S+)?\s*$/.exec(l.trim());
    if (m === null) return;
    const abs = path.resolve(dir, m[1]);
    lines[i] = `import ${fs.existsSync(abs) ? fs.realpathSync(abs) : abs}${m[2] ?? ""}`;
  });
  const spans = open.map((ln) => {
    let end = ln - 1;
    for (let i = ln; i < lines.length; i++) {
      if (lines[i] !== "" && !/^\s/.test(lines[i])) break;
      if (lines[i].trim() !== "") end = i;
    }
    return { start: ln - 1, end };
  });
  spans.sort((a, b) => b.start - a.start);
  for (const s of spans) lines.splice(s.start, s.end - s.start + 1);
  const dirOut = path.join(tmp, "native");
  fs.mkdirSync(dirOut, { recursive: true });
  const out = path.join(dirOut, "U.bend");
  fs.writeFileSync(out, lines.join("\n"));
  return out;
}

let nativeSeq = 0;

/** Builds and runs a native engine-N harness; returns its output lines, or an error string. */
async function runNative(E: Engine, src: string): Promise<string[] | string> {
  const dir = path.join(E.dir, "native");
  fs.mkdirSync(dir, { recursive: true });
  const n = nativeSeq++;
  const file = path.join(dir, `h${n}.bend`);
  const bin = path.join(dir, `h${n}`);
  fs.writeFileSync(file, src);
  const run = async (args: string[]): Promise<{ out: string; code: number | null; timedOut: boolean }> => {
    const p = Bun.spawn(args, { env: { ...process.env, BEND_NO_TELEMETRY: "1" }, stdout: "pipe", stderr: "pipe" });
    let timedOut = false;
    const timer = setTimeout(() => { timedOut = true; p.kill(); }, E.timeoutMs);
    const [o, e] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
    const code = await p.exited;
    clearTimeout(timer);
    return { out: o + e, code, timedOut };
  };
  const b = await run([E.bend, file, "-o", bin]);
  if (b.timedOut) return `native build timed out after ${E.timeoutMs} ms`;
  if (b.code !== 0) return `native build failed: ${E.display(b.out.trim())}`;
  const r = await run([bin]);
  if (r.timedOut) return `native run timed out after ${E.timeoutMs} ms`;
  if (r.code !== 0) return `native run failed: ${E.display(r.out.trim())}`;
  return r.out.split("\n").map((l) => l.trim()).filter((l) => l !== "");
}

export async function lawcheck(file: string, o: Options): Promise<Report> {
  const abs = path.resolve(file);
  if (!fs.existsSync(abs)) throw new UsageError(`no such file: ${file}`);
  const tmp = o.tmpDir ?? fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-"));
  const root = safeRoot(rootFor(abs, o.impl, tmp), tmp);
  const L = await load(root);
  validate(L);
  const own = decls(L, { scope: "own" });
  const allDecls = decls(L, { scope: "all" });
  const predicates = new Map<string, PredStmt | null>();
  for (const d of allDecls) if (d.predicate) predicates.set(d.name, predicateStatement(L, d));
  const baseFiles = new Set(allDecls.filter((d) => d.origin === "base").map((d) => d.file));
  const U = universe(L, o.maxNat);
  const { header, qualify, display, nameOut } = aliasMap(L);
  const termDecls = new Map<string, TermDecl>();
  for (const d of allDecls) {
    if (d.kind !== "def" && d.kind !== "template") continue;
    const info: TermDecl = { params: splitArrow(d.signature).length - 1, templates: d.templates ?? 0 };
    termDecls.set(d.name, info);
    const alias = nameOut(d.name);
    if (alias !== d.name) termDecls.set(alias, info);
  }
  const E: Engine = { header, dir: tmp, bend: bendBin(), timeoutMs: o.timeoutMs ?? 120000, jobs: o.jobs ?? navigator.hardwareConcurrency, runs: 0, display, unsafe: unsafeModules(L, baseFiles) };
  const all = own.filter((d) => d.kind === "law");
  const laws = all.filter((d) => o.law === undefined || d.name === o.law);
  if (o.law !== undefined && laws.length === 0) throw new UsageError(`no law named ${o.law} in ${file}`);
  let results: LawResult[];
  if (o.firstFail) {
    results = [];
    for (const d of laws) {
      const r = await checkLaw(L, d, all.indexOf(d), o, U, predicates, E, qualify, nameOut, termDecls);
      results.push(r);
      if (r.status === "fail") break;
    }
  } else {
    results = await Promise.all(laws.map((d) => checkLaw(L, d, all.indexOf(d), o, U, predicates, E, qualify, nameOut, termDecls)));
  }
  for (const r of results) r.file = abs;
  return { schema: 1, tool: "lawcheck", version: VERSION, bend: L.source.version, file: abs, seed: o.seed, size: o.size, maxInstances: o.maxInstances, maxNat: o.maxNat ?? 30, tmpDir: tmp, checkerRuns: E.runs, laws: results };
}

async function checkLaw(L: Loaded, d: Decl, li: number, o: Options, U: Universe, predicates: Map<string, PredStmt | null>, E: Engine, qualify: (s: string) => string, nameOut: (s: string) => string, termDecls: Map<string, TermDecl>): Promise<LawResult> {
  const base: LawResult = { name: d.name, file: d.file, line: d.line, proved: d.proved === true, claim: "other", status: "skip", instances: 0, failures: 0 };
  let p: Plan;
  try {
    p = plan(L, d, predicates, U);
  } catch (e) {
    if (e instanceof Skip) return { ...base, reason: e.message };
    throw e;
  }
  base.claim = p.kind;
  const r = mulberry32(o.seed + li * 7919);
  let insts: Inst[];
  try {
    insts = instances(p, U, o, r);
  } catch (e) {
    if (e instanceof Unsupported) return { ...base, reason: `cannot generate values: ${e.message}` };
    throw e;
  }
  let n = 0;
  const texts = (inst: Inst, extra: { name: string; q: string; n: string }[] = []) => {
    const env = new Map<string, string>();
    for (const q of p.quantParams) env.set(q, "&2");
    for (const [a, t] of inst.types) env.set(a, t);
    p.values.forEach((v, i) => env.set(v.name, render(inst.vals[i], qualify)));
    p.funs.forEach((f, i) => env.set(f.name, inst.funs[i]));
    for (const e of extra) env.set(e.name, e.q);
    const denv = new Map(env);
    p.values.forEach((v, i) => denv.set(v.name, render(inst.vals[i], nameOut)));
    for (const e of extra) denv.set(e.name, e.n);
    try {
      const premises = p.premises.map((s) => rewrite(s, env, qualify));
      return {
        claim: rewrite(p.claim, env, qualify),
        claimSlot: premiseSlot(p.claimSig, p.claim, env, qualify),
        premises,
        slots: p.premises.map((s, i) => premiseSlot(p.premiseSigs[i], s, env, qualify)),
        shown: showTerm(rewrite(p.claim, denv, nameOut, false), termDecls),
        shownPremises: p.premises.map((s) => showTerm(rewrite(s, denv, nameOut, false), termDecls)),
      };
    } catch (e) {
      if (e instanceof Shadowed) throw new Skip(`binder ${e.message} is shadowed by a lambda in the claim`);
      throw e;
    }
  };
  const id = () => `lc_${li}_${n++}`;

  // Premises of many instances in one declaration: the checker normalizes the whole tuple on both
  // sides, so one run decides every component (PLAN F22).
  async function heldTuple(cands: Inst[]): Promise<{ kept: Inst[]; tooLarge: number } | null> {
    const groups: { inst: Inst; slots: Slot[] }[] = [];
    for (const c of cands) {
      const slots = texts(c).slots;
      if (slots.some((s) => s === null)) return null;
      groups.push({ inst: c, slots: slots as Slot[] });
    }
    const CHUNK = 32;
    const kept: Inst[] = [];
    for (let start = 0; start < groups.length; start += CHUNK) {
      const chunk = groups.slice(start, start + CHUNK);
      const slots = chunk.flatMap((g) => g.slots);
      const item = { id: id(), claim: `{${nestPair(slots.map((s) => s.lhs))} == ${nestPair(slots.map((s) => s.rhs))} : ${nestType(slots.map((s) => s.type))}}` };
      const { out, timedOut } = await runBatch(E, [item]);
      if (timedOut || overflowed(out)) return null;
      const loc = locate(out);
      if (loc === null) {
        if (!cleanCheck(out)) return null;
        kept.push(...chunk.map((g) => g.inst));
        continue;
      }
      if (loc.def !== item.id || loc.pointed !== "{==}") return null;
      const exp = splitTuple(loc.expected ?? ""), obs = splitTuple(loc.observed ?? "");
      if (exp === null || obs === null || exp.length !== slots.length || obs.length !== slots.length) return null;
      if (!exp.every(trustComp) || !obs.every(trustComp)) return null;
      let k = 0;
      for (const g of chunk) {
        let holds = true;
        for (let j = 0; j < g.slots.length; j++) if (exp[k + j] !== obs[k + j]) { holds = false; break; }
        if (holds) kept.push(g.inst);
        k += g.slots.length;
      }
    }
    return { kept, tooLarge: 0 };
  }

  async function holding(cands: Inst[]): Promise<{ kept: Inst[]; tooLarge: number } | string> {
    if (p.premises.length === 0) return { kept: cands, tooLarge: 0 };
    if (E.unsafe.length === 0) {
      const batched = await heldTuple(cands);
      if (batched !== null) return batched;
    }
    const items = cands.map((c) => texts(c).premises.map((claim) => ({ id: id(), claim })));
    const res = await evaluateAll(E, items.flat());
    const all = [...res.values()];
    const bad = all.find((x) => x.r === "undecidable" || x.r === "illtyped" || x.r === "error" || x.r === "unsafe");
    if (bad) return bad.r === "unsafe" ? `premise relies on ${unsafeText(bad.count)}` : `premise ${bad.r === "undecidable" ? "not decidable by evaluation" : "could not be evaluated"}: ${(bad as any).detail}`;
    if (E.unsafe.length > 0 && all.some((x) => x.r === "open")) return `premise relies on ${unsafeFilesText(E.unsafe)}`;
    let tooLarge = 0;
    const kept = cands.filter((_, i) => {
      const outs = items[i].map((it) => res.get(it.id)!);
      if (outs.some((o) => o.r === "toolarge")) { tooLarge++; return false; }
      return outs.every((it) => it.r === "pass" || it.r === "open");
    });
    return { kept, tooLarge };
  }

  // Claims of many instances in one declaration, like premises: the checker prints every failing
  // component's two sides, so one run decides the whole law (PLAN F22).
  const claimBatches = async (sat: Inst[]): Promise<{ items: Item[]; res: Map<string, Outcome> } | null> => {
    const ts = sat.map((c) => texts(c));
    if (ts.some((t) => t.claimSlot === null)) return null;
    const items = sat.map((_, i) => ({ id: id(), claim: ts[i].claim }));
    const out = new Map<string, Outcome>();
    const CHUNK = 256;
    for (let start = 0; start < items.length; start += CHUNK) {
      const chunk = items.slice(start, start + CHUNK);
      const slots = ts.slice(start, start + CHUNK).map((t) => t.claimSlot as Slot);
      const bid = id();
      const claim = `{${nestPair(slots.map((s) => s.lhs))} == ${nestPair(slots.map((s) => s.rhs))} : ${nestType(slots.map((s) => s.type))}}`;
      const { out: raw, timedOut } = await runBatch(E, [{ id: bid, claim }]);
      if (timedOut || overflowed(raw)) return null;
      const loc = locate(raw);
      if (loc === null) {
        if (!cleanCheck(raw)) return null;
        for (const it of chunk) out.set(it.id, { r: "pass" });
        continue;
      }
      if (loc.def !== bid || loc.pointed !== "{==}") return null;
      const exp = splitTuple(loc.expected ?? ""), obs = splitTuple(loc.observed ?? "");
      if (exp === null || obs === null || exp.length !== chunk.length || obs.length !== chunk.length) return null;
      if (!exp.every(trustComp) || !obs.every(trustComp)) return null;
      for (let i = 0; i < chunk.length; i++) out.set(chunk[i].id, exp[i] === obs[i] ? { r: "pass" } : { r: "fail", expected: E.display(exp[i]), observed: E.display(obs[i]) });
    }
    return { items, res: out };
  };

  const problem = (out: Outcome): LawResult | null => {
    if (out.r === "undecidable") return { ...base, status: "skip", reason: `not decidable by evaluation (${out.detail})` };
    if (out.r === "unsafe") return { ...base, status: "skip", reason: `the checker's verdict relies on ${unsafeText(out.count)}` };
    if (out.r === "open" && E.unsafe.length > 0) return { ...base, status: "skip", reason: `the checker reported open proofs and the source relies on ${unsafeFilesText(E.unsafe)}` };
    if (out.r === "illtyped") return { ...base, status: "error", reason: `a generated instance does not type-check:\n${out.detail}` };
    if (out.r === "error") return { ...base, status: "error", reason: out.detail };
    return null;
  };

  // The `exs` witness space: the generated values of each witness type, in product (capped).
  const witnessCombos = (inst: Inst): { name: string; q: string; n: string }[][] => {
    const envTy = new Map<string, Ty>();
    for (const [a, t] of inst.types) envTy.set(a, { t: "app", head: t, args: [], paren: false });
    const cap = Math.min(o.maxInstances, 64);
    const perW = p.exs.map((e) => {
      const ty = substTy(e.ty, envTy);
      const out = U.enumerate(ty, o.size).slice(0, cap);
      while (out.length < cap) out.push(U.random(ty, Math.max(o.size, 3), r));
      return out.map((v) => ({ name: e.name, q: render(v, qualify), n: render(v, nameOut) }));
    });
    const combos: { name: string; q: string; n: string }[][] = [];
    const build = (i: number, acc: { name: string; q: string; n: string }[]) => {
      if (combos.length >= cap) return;
      if (i === perW.length) { combos.push(acc); return; }
      for (const c of perW[i]) { build(i + 1, [...acc, c]); if (combos.length >= cap) return; }
    };
    build(0, []);
    return combos;
  };

  const nativeCheck = async (sat: Inst[], items: Item[], res: Map<string, Outcome>): Promise<{ checked: number; disagreements: NativeDisagreement[]; skip?: string }> => {
    const parts = items.map((it) => splitEquation(it.claim));
    const eqs = parts.map((pp) => (pp === null ? null : nativeEq(pp.type)));
    if (eqs.some((e) => e === null)) return { checked: 0, disagreements: [], skip: "claim is not an equation over Nat, U32, Bool or a list of those" };
    const nroot = nativeRoot(L, E.dir);
    const header = E.header.split(`import ${L.file} as U`).join(`import ${nroot} as U`);
    const helpers = [...new Set(eqs.map((e) => e!.helper).filter((h): h is string => h !== undefined))];
    const head = `${header}\n${helpers.join("")}`;
    const lineOf = (i: number) => `    IO.print(U32.show(Bool.to_u32(${eqs[i]!.eq(parts[i]!.lhs, parts[i]!.rhs)})))`;
    const src = `${head}def main() -> IO(Unit):\n  do IO<Unit>:\n${items.map((_, i) => lineOf(i)).join("\n")}\n`;
    const ran = await runNative(E, src);
    if (typeof ran === "string") return { checked: 0, disagreements: [], skip: ran };
    const outs = items.map((it) => res.get(it.id));
    const bits = items.map((_, i) => (ran[i] === "1" ? true : ran[i] === "0" ? false : undefined));
    const checked = outs.filter((x) => x?.r === "pass" || x?.r === "open" || x?.r === "fail").length;
    const disagreements: NativeDisagreement[] = nativeDisagreements(outs, bits).map((i) => {
      const repro = path.join(E.dir, "native", `repro_${li}_${i}.bend`);
      nativeRepro(head, lineOf(i), repro);
      return { bindings: p.values.map((v, k) => ({ name: v.name, value: render(sat[i].vals[k], nameOut) })), engineC: outs[i]!.r as "pass" | "open" | "fail", engineN: bits[i]!, repro };
    });
    return { checked, disagreements };
  };

  try {
    const held = await holding(insts);
    if (typeof held === "string") return { ...base, reason: held };
    const sat = held.kept;
    let tooLarge = held.tooLarge;
    if (tooLarge > 0) base.tooLarge = tooLarge;
    base.instances = sat.length;
    if (p.premises.length) base.premise = { satisfied: sat.length, total: insts.length };
    if (sat.length === 0) {
      if (tooLarge > 0 && tooLarge === insts.length) return { ...base, status: "skip", reason: "every instance was too large to evaluate (lower --max-nat)" };
      if (p.kind === "refutation") return { ...base, status: "pass", instances: insts.length };
      return { ...base, status: "skip", reason: `premises satisfied in 0/${insts.length} instances — law untested (vacuous in this space)` };
    }
    if (p.exs.length > 0) {
      let tried = 0;
      let missed = 0;
      for (const inst of sat) {
        const combos = witnessCombos(inst);
        tried += combos.length;
        const items = combos.map((extra) => ({ id: id(), claim: texts(inst, extra).claim }));
        const res = await evaluateAll(E, items);
        for (const out of res.values()) { const pr = problem(out); if (pr) return pr; }
        if (!items.some((it) => res.get(it.id)!.r === "pass")) missed++;
      }
      if (missed === 0) return { ...base, status: "pass" };
      return { ...base, status: "skip", reason: `no witness found in ${tried} candidates` };
    }
    let failing: { inst: Inst; out?: Outcome }[];
    let passed = 0;
    if (p.kind === "refutation") {
      failing = sat.map((inst) => ({ inst }));
    } else {
      const batched = E.unsafe.length === 0 ? await claimBatches(sat) : null;
      let items: Item[];
      let res: Map<string, Outcome>;
      if (batched !== null) {
        items = batched.items;
        res = batched.res;
      } else {
        items = sat.map((inst) => ({ id: id(), claim: texts(inst).claim }));
        // The first batch stops on the first undecidable instance, so a law the checker cannot
        // decide is skipped at once instead of once per instance (PLAN F22).
        const head = items.slice(0, 32), tail = items.slice(32);
        res = await evaluate(E, head, false, true);
        if (tail.length > 0) for (const [k, v] of await evaluateAll(E, tail)) res.set(k, v);
      }
      for (const out of res.values()) { const pr = problem(out); if (pr) return pr; }
      const outs = [...res.values()];
      passed = outs.filter((o) => o.r === "pass" || o.r === "open").length;
      const claimTooLarge = outs.filter((o) => o.r === "toolarge").length;
      if (claimTooLarge > 0) { tooLarge += claimTooLarge; base.tooLarge = tooLarge; }
      failing = sat.map((inst, i) => ({ inst, out: res.get(items[i].id)! })).filter((x) => x.out.r === "fail");
      if (o.native) base.native = await nativeCheck(sat, items, res);
    }
    base.failures = failing.length;
    if (failing.length === 0) {
      if (tooLarge > 0 && passed === 0) return { ...base, status: "skip", reason: "every instance was too large to evaluate (lower --max-nat)" };
      return { ...base, status: "pass" };
    }
    const size = (x: Inst) => x.vals.reduce((s, v) => s + measure(v), 0);
    let original: Inst;
    let cur: { inst: Inst; out?: Outcome };
    let steps = 0;
    if (o.shrink === false) {
      original = failing[0].inst;
      cur = failing[0];
    } else {
      failing.sort((a, b) => size(a.inst) - size(b.inst));
      original = failing[0].inst;
      cur = failing[0];
      for (; steps < 200; steps++) {
        const seen = new Set<string>();
        const cands: Inst[] = [];
        cur.inst.vals.forEach((v, i) => {
          for (const s of U.shrink(v)) {
            const vals = cur.inst.vals.map((w, j) => (j === i ? s : w));
            const k = vals.map((x) => render(x)).join("|");
            if (!seen.has(k)) { seen.add(k); cands.push({ vals, types: cur.inst.types, funs: cur.inst.funs }); }
          }
        });
        cands.sort((a, b) => size(a) - size(b));
        const ok = await holding(cands.slice(0, 300));
        if (typeof ok === "string" || ok.kept.length === 0) break;
        if (p.kind === "refutation") { cur = { inst: ok.kept[0] }; continue; }
        const items = ok.kept.map((inst) => ({ id: id(), claim: texts(inst).claim }));
        const res = await evaluate(E, items, true);
        const hit = items.findIndex((it) => res.get(it.id)?.r === "fail");
        if (hit < 0) break;
        cur = { inst: ok.kept[hit], out: res.get(items[hit].id) };
      }
    }
    const bind = (inst: Inst): Binding[] => [
      ...p.values.map((v, i) => ({ name: v.name, value: render(inst.vals[i], nameOut) })),
      ...p.funs.map((f, i) => ({ name: f.name, value: inst.funs[i] })),
    ];
    const t = texts(cur.inst);
    const cex: Counterexample = {
      bindings: bind(cur.inst),
      types: [...cur.inst.types].map(([name, value]) => ({ name, value })),
      claim: t.shown,
      original: bind(original),
      shrinkSteps: steps,
    };
    if (p.premises.length) cex.premises = t.shownPremises;
    if (cur.out?.r === "fail") { cex.expected = cur.out.expected; cex.observed = cur.out.observed; }
    if (o.shrink !== false && p.kind !== "refutation") {
      const hid = id();
      const g = (await evaluate(E, [{ id: hid, claim: t.claim, hole: true }])).get(hid);
      if (g?.r === "goal") {
        const eq = splitEquation(g.goal);
        const shown = p.kind === "equation" ? splitEquation(t.shown) : null;
        if (eq && shown) {
          cex.lhs = { term: shown.lhs, value: eq.lhs };
          cex.rhs = { term: shown.rhs, value: eq.rhs };
        } else cex.goal = showTerm(g.goal, termDecls);
      }
    }
    return { ...base, status: "fail", counterexample: cex };
  } catch (e) {
    if (e instanceof Skip) return { ...base, reason: e.message };
    throw e;
  }
}

/** Local `import ./x.bend` specs, in order. */
function localImports(text: string): string[] {
  const out: string[] = [];
  for (const l of text.split("\n")) {
    const m = /^import\s+(\.{1,2}\/\S+\.bend)(\s+as\s+\S+)?\s*$/.exec(l.trim());
    if (m !== null) out.push(m[1]);
  }
  return out;
}

/** Removes each named def's `defSpan` lines, so the laws it filled become open. */
function stripFills(text: string, fills: string[]): string {
  const spans = fills.map((n) => defSpan(text, n)).filter((s): s is { start: number; end: number } => s !== null);
  if (spans.length === 0) return text;
  spans.sort((a, b) => b.start - a.start);
  const lines = text.split("\n");
  for (const s of spans) lines.splice(s.start - 1, s.end - s.start + 1);
  return lines.join("\n");
}

// `text` without `fillNames`, local imports absolute from `dir` except the `--impl` one, which
// `rootFor` still needs to find and replace.
function implRootText(text: string, dir: string, fillNames: string[], implBase: string): string {
  const lines = stripFills(text, fillNames).split("\n");
  const locals = lines
    .map((l, i) => ({ i, m: /^import\s+(\.{1,2}\/\S+\.bend)(\s+as\s+\S+)?\s*$/.exec(l.trim()) }))
    .filter((x) => x.m !== null);
  const byName = locals.filter((x) => path.basename(x.m![1]) === implBase);
  const keep = byName.length === 1 ? byName[0] : byName.length === 0 && locals.length === 1 ? locals[0] : null;
  for (const x of locals) {
    if (x === keep) continue;
    const abs = path.resolve(dir, x.m![1]);
    lines[x.i] = `import ${fs.existsSync(abs) ? fs.realpathSync(abs) : abs}${x.m![2] ?? ""}`;
  }
  return lines.join("\n");
}

/** A def header (may span lines) as text. */
function headerText(lines: string[], start: number): string {
  let depth = 0;
  for (let i = start; i < lines.length; i++) {
    for (const ch of lines[i]) { if (ch === "(") depth++; else if (ch === ")") depth--; }
    if (depth === 0 && /:\s*$/.test(lines[i])) return lines.slice(start, i + 1).join("\n");
  }
  return lines[start] ?? "";
}

/** The def's parameter names, stripped of `+`/`-`/`~`, read from its source header. */
function defParams(text: string, name: string): string[] {
  const span = defSpan(text, name);
  if (span === null) return [];
  const lines = text.split("\n");
  const header = headerText(lines, span.start - 1);
  const open = header.indexOf("(");
  if (open < 0) return [];
  let d = 0, close = -1;
  for (let i = open; i < header.length; i++) {
    const ch = header[i];
    if (ch === "(" || ch === "{" || ch === "[") d++;
    else if (ch === ")" || ch === "}" || ch === "]") { d--; if (d === 0) { close = i; break; } }
  }
  if (close < 0) return [];
  const out: string[] = [];
  let depth = 0, field = "";
  const push = () => {
    let nm = "";
    let pd = 0;
    for (const ch of field) {
      if ("([{<".includes(ch)) pd++;
      else if (")]}>".includes(ch)) pd--;
      else if (ch === ":" && pd === 0) break;
      nm += ch;
    }
    nm = nm.trim().replace(/^[+\-~]\s*/, "").trim();
    if (nm !== "") out.push(nm);
  };
  for (const ch of header.slice(open + 1, close)) {
    if ("([{<".includes(ch)) depth++;
    else if (")]}>".includes(ch)) depth--;
    if (ch === "," && depth === 0) { push(); field = ""; }
    else field += ch;
  }
  push();
  return out;
}

// The checker's error text starts with `Error:` and carries the useful `- expected`/`- observed`
// and `Location:` lines; keep those, not just the header (README).
function errorDetail(msg: string): string {
  const lines = msg.split("\n").map((s) => s.trim()).filter((s) => s !== "");
  const useful = lines.filter((s) => s.startsWith("- ") || s.startsWith("Location:"));
  return (useful.length > 0 ? useful : lines).slice(0, 2).join(" ");
}

/** Runs the laws against every mutant of the target file's defs (PLAN §4.3). */
export async function mutate(file: string, o: MutateOptions): Promise<MutateReport> {
  const abs = path.resolve(file);
  if (!fs.existsSync(abs)) throw new UsageError(`no such file: ${file}`);
  const opts: Options = {
    size: o.size ?? 3, maxInstances: o.maxInstances ?? 50, seed: o.seed ?? 1,
    law: o.law, impl: o.impl, jobs: o.jobs, timeoutMs: o.timeoutMs, tmpDir: o.tmpDir, maxNat: o.maxNat,
    shrink: o.shrink, firstFail: o.firstFail,
  };
  const tmp = o.tmpDir ?? fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-mut-"));
  let target: string;
  let mode: "impl" | "in-file";
  if (o.impl !== undefined) {
    target = path.resolve(o.impl);
    if (!fs.existsSync(target)) throw new UsageError(`--impl: no such file: ${o.impl}`);
    mode = "impl";
  } else {
    const rootL = await load(abs);
    const locals = localImports(fs.readFileSync(abs, "utf8"));
    const rootDecls = decls(rootL, { scope: "own" });
    const rootLaws = new Set(rootDecls.filter((d) => d.kind === "law").map((d) => d.name));
    const hasDef = rootDecls.some((d) => (d.kind === "def" || d.kind === "template") && !rootLaws.has(d.name));
    if (locals.length === 1 && !hasDef) { target = path.resolve(path.dirname(abs), locals[0]); mode = "impl"; }
    else { target = abs; mode = "in-file"; }
  }
  const L = await load(target);
  const own = decls(L, { scope: "own" });
  const lawNames = new Set(own.filter((d) => d.kind === "law").map((d) => d.name));
  let defs = own.filter((d) => (d.kind === "def" || d.kind === "template") && !lawNames.has(d.name) && !d.predicate && !d.statement);
  if (o.def !== undefined) {
    const one = defs.filter((d) => d.name === o.def);
    if (one.length === 0) throw new UsageError(`no mutable def named ${o.def} in ${path.relative(process.cwd(), target)}`);
    defs = one;
  }
  if (defs.length === 0) throw new UsageError(`no mutable defs in ${path.relative(process.cwd(), target)}`);
  const targetText = fs.readFileSync(target, "utf8");
  const safeBase = path.basename(target).replace(/[^\w.-]/g, "_");

  // In impl mode the root is the laws file; its proof defs must be stripped too, or a mutant's
  // behaviour change only breaks a proof and is misclassified as `invalid` (README).
  const rootText = mode === "impl" ? fs.readFileSync(abs, "utf8") : targetText;
  const fillDecls = mode === "impl" ? decls(await load(abs), { scope: "own" }) : own;
  const fillNames = fillDecls.filter((d) => d.kind === "law" && d.proved).map((d) => d.name);

  const baseDir = path.join(tmp, "base");
  fs.mkdirSync(baseDir, { recursive: true });
  let baseReport: Report;
  let rootPath: string;
  if (mode === "impl") {
    rootPath = path.join(baseDir, `root_${path.basename(abs).replace(/[^\w.-]/g, "_")}`);
    fs.writeFileSync(rootPath, implRootText(rootText, path.dirname(abs), fillNames, path.basename(target)));
    baseReport = await lawcheck(rootPath, { ...opts, impl: target, tmpDir: baseDir });
  } else {
    rootPath = path.join(baseDir, safeBase);
    fs.writeFileSync(rootPath, stripFills(targetText, fillNames));
    baseReport = await lawcheck(rootPath, { ...opts, impl: undefined, tmpDir: baseDir });
  }
  if (baseReport.laws.some((l) => l.status === "fail")) throw new UsageError("the laws already fail on the unmutated code; fix those first");
  const evaluated = new Set(baseReport.laws.filter((l) => l.status === "pass").map((l) => l.name));
  if (evaluated.size === 0) {
    const idle = baseReport.laws.filter((l) => l.status !== "pass");
    const reasons = [...new Set(idle.map((l) => l.reason ?? l.status))].join("; ");
    throw new UsageError(`no law was evaluated on the unmutated code (${idle.length} skipped: ${reasons || "none"})`);
  }

  const report: MutateReport = {
    tool: "lawcheck-mutate", version: VERSION, bend: L.source.version, file: abs, schema: 1,
    impl: mode === "impl" ? target : null, seed: opts.seed, maxInstances: opts.maxInstances, tmpDir: tmp, defs: [],
  };
  // Mutants of one def run in a small pool; the global `slot()` semaphore still caps the bend
  // processes at `jobs`, so this overlaps their many short runs without oversubscribing (README).
  const pool = Math.max(1, Math.floor((opts.jobs ?? navigator.hardwareConcurrency) / 4));
  for (const d of defs) {
    const ms = mutants(targetText, d.name, defParams(targetText, d.name));
    const results: MutantResult[] = new Array(ms.length);
    const runOne = async (i: number): Promise<void> => {
      const m = ms[i];
      const dir = path.join(tmp, "mut", `${d.name}_${i}`);
      fs.mkdirSync(dir, { recursive: true });
      const mutantPath = path.join(dir, safeBase);
      fs.writeFileSync(mutantPath, mode === "in-file" ? stripFills(m.text, fillNames) : m.text);
      const runOpts: Options = { ...opts, shrink: false, firstFail: true, tmpDir: dir, impl: mode === "impl" ? mutantPath : undefined };
      const res: MutantResult = { id: m.id, def: d.name, op: m.op, line: m.line, before: m.before, after: m.after, status: "survived" };
      try {
        const rep = mode === "impl" ? await lawcheck(rootPath, runOpts) : await lawcheck(mutantPath, runOpts);
        const fail = rep.laws.find((l) => l.status === "fail");
        if (fail) { res.status = "killed"; res.law = fail.name; }
        else {
          const undecided = rep.laws.find((l) => evaluated.has(l.name) && l.status !== "pass");
          const missed = [...evaluated].find((n) => !rep.laws.some((l) => l.name === n));
          if (undecided !== undefined) { res.status = "unknown"; res.detail = (undecided.reason ?? undecided.status).split("\n")[0]; }
          else if (missed !== undefined) { res.status = "unknown"; res.detail = `law ${missed} not evaluated`; }
        }
      } catch (e) {
        if (e instanceof ModuleError || e instanceof BendReadError) { res.status = "invalid"; res.detail = errorDetail(e.message); }
        else throw e;
      }
      results[i] = res;
    };
    let next = 0;
    const worker = async () => { for (;;) { const i = next++; if (i >= ms.length) return; await runOne(i); } };
    await Promise.all(Array.from({ length: Math.min(pool, ms.length) }, worker));
    report.defs.push({ name: d.name, mutants: results });
  }
  return report;
}
