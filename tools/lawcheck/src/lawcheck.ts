// lawcheck core: load a file with @bendlib/reader, turn each law into closed
// instances, evaluate them with the checker, and shrink counterexamples.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { BendReadError, decls, load, show, type Decl, type Loaded } from "../../reader/index.ts";
import { stripCommentsAndStrings } from "../../mathlib/lib.ts";
import { bendBin, evaluate, evaluateAll, ModuleError, type Engine, type Item, type Outcome } from "./checker.ts";
import { defSpan, mutants } from "./mutate.ts";
import { mentions, rewrite, Shadowed, splitEquation } from "./terms.ts";
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
};

export type MutateOptions = Partial<Options> & { def?: string };

export type Binding = { name: string; value: string };

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
  claim: "equation" | "predicate" | "refutation" | "other";
  status: "pass" | "fail" | "skip" | "error";
  reason?: string;
  instances: number;
  failures: number;
  tooLarge?: number;
  premise?: { satisfied: number; total: number };
  counterexample?: Counterexample;
};

export type Report = { tool: "lawcheck"; version: string; bend: string; file: string; seed: number; size: number; maxInstances: number; tmpDir: string; checkerRuns: number; laws: LawResult[] };

export type MutantResult = {
  id: string; def: string; op: string; line: number; before: string; after: string;
  status: "killed" | "survived" | "invalid" | "error"; law?: string; detail?: string;
};

export type MutateReport = {
  tool: "lawcheck-mutate"; version: string; bend: string; file: string; impl: string | null;
  seed: number; maxInstances: number; tmpDir: string;
  defs: { name: string; mutants: MutantResult[] }[];
};

export const VERSION = "0.2.0";

class Skip extends Error {}

type Value = { name: string; ty: Ty };
type FunBinder = { name: string; args: string[]; ret: string };
type Plan = {
  d: Decl;
  kind: LawResult["claim"];
  claim: string;
  typeParams: string[];
  quantParams: string[];
  values: Value[];
  funs: FunBinder[];
  premises: string[];
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

function plan(L: Loaded, d: Decl, predicates: Set<string>, U: Universe): Plan {
  const binders = d.binders ?? [];
  const p: Plan = { d, kind: "other", claim: "", typeParams: [], quantParams: [], values: [], funs: [], premises: [] };
  const premiseNames: string[] = [];
  const isPredicateApp = (s: string) => {
    const head = applicationHead(s);
    return head !== null && predicates.has(head);
  };
  for (const b of binders) {
    const t = b.type;
    const tmpl = b.quant === "template";
    if (tmpl && t === "Quant") { p.quantParams.push(b.name); continue; }
    if (tmpl && /^(Type|Data|Kind\(.*\))$/.test(t)) { p.typeParams.push(b.name); continue; }
    if (tmpl && t.includes("->")) { p.funs.push(parseFun(b.name, t)); continue; }
    if (tmpl && t.startsWith("{")) throw new Skip("template hypothesis (v0.3)");
    if (t === "Quant") p.quantParams.push(b.name);
    else if (/^(Type|Data|Kind\(.*\))$/.test(t)) p.typeParams.push(b.name);
    else if (t.startsWith("{")) { p.premises.push(t); premiseNames.push(b.name); }
    else if (/^&[A-Za-z_]\w*:/.test(t)) throw new Skip(`\`where\` premise on ${b.name} (v0.2)`);
    else if (t.includes("->")) throw new Skip(`function-typed binder ${b.name}: ${t} (v0.2)`);
    else if (tmpl) throw new Skip(`template binder ~${b.name}: ${t} (v0.2)`);
    else {
      const ty = parseTy(t);
      if (ty !== null && generable(U, substTy(ty, envTypes(p, TYPE_CHOICES[0])))) p.values.push({ name: b.name, ty });
      else if (isPredicateApp(t)) { p.premises.push(t); premiseNames.push(b.name); }
      else if (ty === null) throw new Skip(`binder ${b.name}: cannot generate values of ${t}`);
      else p.values.push({ name: b.name, ty });
    }
  }
  const tip = tipOf(L, d.name);
  if (d.statement) {
    p.kind = "equation";
    p.claim = `{${d.statement.lhs} == ${d.statement.rhs} : ${d.statement.type}}`;
  } else if (tip === "Empty" && p.premises.length > 0) {
    p.kind = "refutation";
    p.claim = "Empty";
  } else if (isPredicateApp(tip)) {
    p.kind = "predicate";
    p.claim = tip;
  } else if (/^&[A-Za-z_]\w*:/.test(tip)) {
    throw new Skip(`\`exs\` witness claim (v0.2)`);
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

function instances(p: Plan, U: Universe, o: Options, r: Rng): Inst[] {
  const choices = p.typeParams.length ? TYPE_CHOICES : [""];
  const ctxs: { choice: string; funs: string[] }[] = [];
  for (const choice of choices) {
    const perFun = p.funs.map((f) => CATALOG[substSig(f, choice, p.typeParams)]);
    const combos: string[][] = [];
    const build = (i: number, acc: string[]) => {
      if (combos.length >= 8) return;
      if (i === perFun.length) { combos.push(acc); return; }
      for (const cand of perFun[i]) { build(i + 1, [...acc, cand]); if (combos.length >= 8) return; }
    };
    build(0, []);
    for (const funs of combos) ctxs.push({ choice, funs });
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
    const f = abs === null ? L.files.find((x) => x.namespace + ".bend" === spec) : L.files.find((x) => x.path === (fs.existsSync(abs) ? fs.realpathSync(abs) : abs));
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

export class UsageError extends Error {}

/** Basenames of loaded non-Base files whose comment/string-stripped source has `@unsafe`. */
function unsafeModules(L: Loaded, baseFiles: Set<string>): string[] {
  return L.files
    .filter((f) => !baseFiles.has(f.path) && /(^|[^\w@])@unsafe\b/.test(stripCommentsAndStrings(f.text)))
    .map((f) => path.basename(f.path));
}

export async function lawcheck(file: string, o: Options): Promise<Report> {
  const abs = path.resolve(file);
  if (!fs.existsSync(abs)) throw new UsageError(`no such file: ${file}`);
  const tmp = o.tmpDir ?? fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-"));
  const root = rootFor(abs, o.impl, tmp);
  const L = await load(root);
  const own = decls(L, { scope: "own" });
  const allDecls = decls(L, { scope: "all" });
  const predicates = new Set(allDecls.filter((d) => d.predicate).map((d) => d.name));
  const baseFiles = new Set(allDecls.filter((d) => d.origin === "base").map((d) => d.file));
  const U = universe(L, o.maxNat);
  const { header, qualify, display, nameOut } = aliasMap(L);
  const E: Engine = { header, dir: tmp, bend: bendBin(), timeoutMs: o.timeoutMs ?? 120000, jobs: o.jobs ?? navigator.hardwareConcurrency, runs: 0, display, unsafe: unsafeModules(L, baseFiles) };
  const all = own.filter((d) => d.kind === "law");
  const laws = all.filter((d) => o.law === undefined || d.name === o.law);
  if (o.law !== undefined && laws.length === 0) throw new UsageError(`no law named ${o.law} in ${file}`);
  let results: LawResult[];
  if (o.firstFail) {
    results = [];
    for (const d of laws) {
      const r = await checkLaw(L, d, all.indexOf(d), o, U, predicates, E, qualify, nameOut);
      results.push(r);
      if (r.status === "fail") break;
    }
  } else {
    results = await Promise.all(laws.map((d) => checkLaw(L, d, all.indexOf(d), o, U, predicates, E, qualify, nameOut)));
  }
  for (const r of results) r.file = abs;
  return { tool: "lawcheck", version: VERSION, bend: L.source.version, file: abs, seed: o.seed, size: o.size, maxInstances: o.maxInstances, tmpDir: tmp, checkerRuns: E.runs, laws: results };
}

async function checkLaw(L: Loaded, d: Decl, li: number, o: Options, U: Universe, predicates: Set<string>, E: Engine, qualify: (s: string) => string, nameOut: (s: string) => string): Promise<LawResult> {
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
  const texts = (inst: Inst) => {
    const env = new Map<string, string>();
    for (const q of p.quantParams) env.set(q, "&2");
    for (const [a, t] of inst.types) env.set(a, t);
    p.values.forEach((v, i) => env.set(v.name, render(inst.vals[i], qualify)));
    p.funs.forEach((f, i) => env.set(f.name, inst.funs[i]));
    const denv = new Map(env);
    p.values.forEach((v, i) => denv.set(v.name, render(inst.vals[i], nameOut)));
    try {
      return {
        claim: rewrite(p.claim, env, qualify),
        premises: p.premises.map((s) => rewrite(s, env, qualify)),
        shown: rewrite(p.claim, denv, nameOut, false),
        shownPremises: p.premises.map((s) => rewrite(s, denv, nameOut, false)),
      };
    } catch (e) {
      if (e instanceof Shadowed) throw new Skip(`binder ${e.message} is shadowed by a lambda in the claim`);
      throw e;
    }
  };
  const id = () => `lc_${li}_${n++}`;

  async function holding(cands: Inst[]): Promise<{ kept: Inst[]; tooLarge: number } | string> {
    if (p.premises.length === 0) return { kept: cands, tooLarge: 0 };
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

  const problem = (out: Outcome): LawResult | null => {
    if (out.r === "undecidable") return { ...base, status: "skip", reason: `not decidable by evaluation (${out.detail})` };
    if (out.r === "unsafe") return { ...base, status: "skip", reason: `the checker's verdict relies on ${unsafeText(out.count)}` };
    if (out.r === "open" && E.unsafe.length > 0) return { ...base, status: "skip", reason: `the checker reported open proofs and the source relies on ${unsafeFilesText(E.unsafe)}` };
    if (out.r === "illtyped") return { ...base, status: "error", reason: `a generated instance does not type-check:\n${out.detail}` };
    if (out.r === "error") return { ...base, status: "error", reason: out.detail };
    return null;
  };

  try {
    const held = await holding(insts);
    if (typeof held === "string") return { ...base, reason: held };
    const sat = held.kept;
    let tooLarge = held.tooLarge;
    if (tooLarge > 0) base.tooLarge = tooLarge;
    base.instances = sat.length;
    if (p.premises.length) base.premise = { satisfied: sat.length, total: insts.length };
    if (sat.length === 0 && p.kind === "refutation") return { ...base, status: "pass", instances: insts.length };
    if (sat.length === 0) {
      if (tooLarge > 0 && tooLarge === insts.length) return { ...base, status: "skip", reason: "every instance was too large to evaluate (lower --max-nat)" };
      return { ...base, status: "skip", reason: `premises satisfied in 0/${insts.length} instances — law untested (vacuous in this space)` };
    }
    let failing: { inst: Inst; out?: Outcome }[];
    let passed = 0;
    if (p.kind === "refutation") {
      failing = sat.map((inst) => ({ inst }));
    } else {
      const items = sat.map((inst) => ({ id: id(), claim: texts(inst).claim }));
      const res = await evaluateAll(E, items);
      for (const out of res.values()) { const pr = problem(out); if (pr) return pr; }
      const outs = [...res.values()];
      passed = outs.filter((o) => o.r === "pass" || o.r === "open").length;
      const claimTooLarge = outs.filter((o) => o.r === "toolarge").length;
      if (claimTooLarge > 0) { tooLarge += claimTooLarge; base.tooLarge = tooLarge; }
      failing = sat.map((inst, i) => ({ inst, out: res.get(items[i].id)! })).filter((x) => x.out.r === "fail");
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
        } else cex.goal = g.goal;
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
    const locals = localImports(fs.readFileSync(abs, "utf8"));
    const rootDecls = decls(await load(abs), { scope: "own" });
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
  const fillNames = mode === "in-file" ? own.filter((d) => d.kind === "law" && d.proved).map((d) => d.name) : [];
  const targetText = fs.readFileSync(target, "utf8");

  const baseDir = path.join(tmp, "base");
  fs.mkdirSync(baseDir, { recursive: true });
  let baseReport: Report;
  if (mode === "impl") {
    baseReport = await lawcheck(abs, { ...opts, impl: target, tmpDir: baseDir });
  } else {
    const basePath = path.join(baseDir, path.basename(target));
    fs.writeFileSync(basePath, stripFills(targetText, fillNames));
    baseReport = await lawcheck(basePath, { ...opts, impl: undefined, tmpDir: baseDir });
  }
  if (baseReport.laws.some((l) => l.status === "fail")) throw new UsageError("the laws already fail on the unmutated code; fix those first");

  const report: MutateReport = {
    tool: "lawcheck-mutate", version: VERSION, bend: L.source.version, file: abs,
    impl: mode === "impl" ? target : null, seed: opts.seed, maxInstances: opts.maxInstances, tmpDir: tmp, defs: [],
  };
  for (const d of defs) {
    const ms = mutants(targetText, d.name, defParams(targetText, d.name));
    const results: MutantResult[] = [];
    for (let i = 0; i < ms.length; i++) {
      const m = ms[i];
      const dir = path.join(tmp, "mut", `${d.name}_${i}`);
      fs.mkdirSync(dir, { recursive: true });
      const mutantPath = path.join(dir, path.basename(target));
      fs.writeFileSync(mutantPath, mode === "in-file" ? stripFills(m.text, fillNames) : m.text);
      const runOpts: Options = { ...opts, shrink: false, firstFail: true, tmpDir: dir, impl: mode === "impl" ? mutantPath : undefined };
      const res: MutantResult = { id: m.id, def: d.name, op: m.op, line: m.line, before: m.before, after: m.after, status: "survived" };
      try {
        const rep = mode === "impl" ? await lawcheck(abs, runOpts) : await lawcheck(mutantPath, runOpts);
        const fail = rep.laws.find((l) => l.status === "fail");
        const err = rep.laws.find((l) => l.status === "error");
        if (fail) { res.status = "killed"; res.law = fail.name; }
        else if (err) { res.status = "error"; res.detail = (err.reason ?? "").split("\n")[0]; }
      } catch (e) {
        if (e instanceof ModuleError || e instanceof BendReadError) { res.status = "invalid"; res.detail = e.message.split("\n")[0]; }
        else throw e;
      }
      results.push(res);
    }
    report.defs.push({ name: d.name, mutants: results });
  }
  return report;
}
