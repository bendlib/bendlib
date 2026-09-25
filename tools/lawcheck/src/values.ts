// Values lawcheck substitutes for binders: small-scope enumeration, seeded
// random generation, shrinking, and rendering as Bend source.

import { showTy, substTy, type Ty } from "./types.ts";

export type Val =
  | { v: "nat"; n: number }
  | { v: "u32"; n: number }
  | { v: "char"; c: string }
  | { v: "str"; s: string }
  | { v: "list"; items: Val[] }
  | { v: "pair"; a: Val; b: Val }
  | { v: "ctor"; ty: Ty; name: string; i: number; fields: Val[] };

export type Ctor = { name: string; params: string[]; fields: Ty[] };
export type Adt = { name: string; params: string[]; ctors: Ctor[] };

export class Unsupported extends Error {}

const U32_MAX = 4294967295;
const MAX_DOMAIN = 5000;
const OPAQUE = new Set(["Array", "Map", "Set", "F32", "Word", "Word.Nil", "Word.Con", "IO", "IO.OP", "App", "Image", "Event", "Chan", "File", "Socket", "Window", "Audio", "Empty", "Sigma"]);

export type Rng = () => number;

export function mulberry32(seed: number): Rng {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const pick = <T>(r: Rng, xs: T[]): T => xs[Math.floor(r() * xs.length)];
const int = (r: Rng, lo: number, hi: number) => lo + Math.floor(r() * (hi - lo + 1));

export class Universe {
  constructor(private adts: Map<string, Adt>, private maxNat = 30) {}

  private adt(ty: Ty): { adt: Adt; ctors: Ctor[] } {
    if (ty.t !== "app") throw new Unsupported(showTy(ty));
    const adt = this.adts.get(ty.head);
    if (adt === undefined || OPAQUE.has(ty.head)) throw new Unsupported(showTy(ty));
    if (adt.params.length !== ty.args.length) throw new Unsupported(showTy(ty));
    if (adt.ctors.length === 0) throw new Unsupported(`${showTy(ty)} (no constructors)`);
    const ctors = adt.ctors.map((c) => {
      const env = new Map(c.params.map((p, i) => [p, ty.args[i]] as [string, Ty]));
      return { name: c.name, params: [], fields: c.fields.map((f) => substTy(f, env)) };
    });
    return { adt, ctors };
  }

  /** Throws Unsupported naming the first type lawcheck cannot generate. */
  check(ty: Ty, seen = new Set<string>()): void {
    const k = showTy(ty);
    if (seen.has(k)) return;
    seen.add(k);
    const b = builtin(ty);
    if (b === "list") return this.check(ty.t === "app" ? ty.args[1] : ty, seen);
    if (b === "pair" && ty.t === "app") { this.check(ty.args[0], seen); this.check(ty.args[1], seen); return; }
    if (b !== null) return;
    for (const c of this.adt(ty).ctors) for (const f of c.fields) this.check(f, seen);
  }

  enumerate(ty: Ty, d: number): Val[] {
    const b = builtin(ty);
    const cap = (xs: Val[]) => xs.slice(0, MAX_DOMAIN);
    switch (b) {
      case "nat": return range(d + 1).map((n) => ({ v: "nat", n }));
      case "u32": return (d === 0 ? [0] : d === 1 ? [0, 1] : [0, 1, 2, U32_MAX]).map((n) => ({ v: "u32", n }));
      case "char": return (d === 0 ? ["a"] : ["a", "b"]).map((c) => ({ v: "char", c }));
      case "str": return ["", "a", "ab"].slice(0, d + 1).map((s) => ({ v: "str", s }));
      case "list": {
        const el = d === 0 ? [] : this.enumerate((ty as any).args[1], d - 1);
        const out: Val[] = [{ v: "list", items: [] }];
        let layer: Val[][] = [[]];
        for (let len = 1; len <= d && out.length < MAX_DOMAIN; len++) {
          const next: Val[][] = [];
          for (const xs of layer) for (const e of el) { next.push([...xs, e]); if (next.length > MAX_DOMAIN) break; }
          layer = next;
          for (const xs of layer) out.push({ v: "list", items: xs });
        }
        return cap(out);
      }
      case "pair": {
        const [A, B] = (ty as any).args as Ty[];
        const out: Val[] = [];
        for (const a of this.enumerate(A, d)) for (const bb of this.enumerate(B, d)) out.push({ v: "pair", a, b: bb });
        return cap(out);
      }
    }
    const { ctors } = this.adt(ty);
    const out: Val[] = [];
    for (const [i, c] of ctors.entries()) {
      if (c.fields.length > 0 && d === 0) continue;
      let combos: Val[][] = [[]];
      for (const f of c.fields) {
        const dom = this.enumerate(f, d - 1);
        const next: Val[][] = [];
        for (const xs of combos) for (const v of dom) { next.push([...xs, v]); if (next.length > MAX_DOMAIN) break; }
        combos = next;
      }
      for (const fields of combos) out.push({ v: "ctor", ty, name: c.name, i, fields });
    }
    return cap(out);
  }

  random(ty: Ty, size: number, r: Rng, budget = size): Val {
    switch (builtin(ty)) {
      // Half the draws stay small so shrinking is cheap and small counterexamples surface; the
      // other half reaches the full `--max-nat` bound (README, PLAN F31).
      case "nat": return { v: "nat", n: int(r, 0, r() < 0.5 ? Math.min(this.maxNat, 3 * size) : this.maxNat) };
      case "u32": return { v: "u32", n: r() < 0.5 ? pick(r, [0, 1, 2, 3, 255, 256, 65535, 2147483648, U32_MAX]) : Math.floor(r() * 2 ** 32) };
      case "char": return { v: "char", c: pick(r, ["a", "b", "c", "d", "e"]) };
      case "str": return { v: "str", s: range(int(r, 0, size)).map(() => pick(r, ["a", "b", "c"])).join("") };
      case "list": return { v: "list", items: range(int(r, 0, Math.max(size + 2, 8))).map(() => this.random((ty as any).args[1], size, r, budget - 1)) };
      case "pair": return { v: "pair", a: this.random((ty as any).args[0], size, r, budget), b: this.random((ty as any).args[1], size, r, budget) };
    }
    const { adt, ctors } = this.adt(ty);
    const rec = (c: Ctor) => c.fields.some((f) => f.t === "app" && f.head === adt.name);
    let choices = ctors;
    if (budget <= 0) {
      const base = ctors.filter((c) => !rec(c));
      if (base.length > 0) choices = base;
      else if (budget < -8) throw new Unsupported(`${showTy(ty)} (no finite value found)`);
    }
    const c = pick(r, choices);
    return { v: "ctor", ty, name: c.name, i: ctors.indexOf(c), fields: c.fields.map((f) => this.random(f, size, r, budget - 1)) };
  }

  /** Candidates strictly smaller than `x`, most aggressive first. */
  shrink(x: Val): Val[] {
    const out: Val[] = [];
    switch (x.v) {
      case "nat":
      case "u32": {
        const cands = x.v === "nat" ? [0, Math.floor(x.n / 2), x.n - 1] : [0, 1, 2, Math.floor(x.n / 2), x.n - 1];
        for (const n of new Set(cands)) if (n >= 0 && n < x.n) out.push({ v: x.v, n });
        break;
      }
      case "char": if (x.c !== "a") out.push({ v: "char", c: "a" }); break;
      case "str": {
        if (x.s !== "") out.push({ v: "str", s: "" });
        for (let i = 0; i < x.s.length; i++) out.push({ v: "str", s: x.s.slice(0, i) + x.s.slice(i + 1) });
        for (let i = 0; i < x.s.length; i++) if (x.s[i] !== "a") out.push({ v: "str", s: x.s.slice(0, i) + "a" + x.s.slice(i + 1) });
        break;
      }
      case "list": {
        const xs = x.items;
        if (xs.length > 0) out.push({ v: "list", items: [] });
        if (xs.length > 2) {
          out.push({ v: "list", items: xs.slice(0, Math.floor(xs.length / 2)) });
          out.push({ v: "list", items: xs.slice(Math.floor(xs.length / 2)) });
        }
        for (let i = 0; i < xs.length; i++) out.push({ v: "list", items: [...xs.slice(0, i), ...xs.slice(i + 1)] });
        for (let i = 0; i < xs.length; i++) for (const e of this.shrink(xs[i])) out.push({ v: "list", items: xs.map((y, j) => (j === i ? e : y)) });
        break;
      }
      case "pair":
        for (const a of this.shrink(x.a)) out.push({ ...x, a });
        for (const b of this.shrink(x.b)) out.push({ ...x, b });
        break;
      case "ctor": {
        const { ctors } = this.adt(x.ty);
        const key = showTy(x.ty);
        for (const f of x.fields) if (f.v === "ctor" && showTy(f.ty) === key) out.push(f);
        ctors.forEach((c, i) => { if (c.fields.length === 0 && i !== x.i) out.push({ v: "ctor", ty: x.ty, name: c.name, i, fields: [] }); });
        x.fields.forEach((f, i) => { for (const s of this.shrink(f)) out.push({ ...x, fields: x.fields.map((g, j) => (j === i ? s : g)) }); });
        break;
      }
    }
    return out.filter((y) => measure(y) < measure(x));
  }
}

function builtin(ty: Ty): "nat" | "u32" | "char" | "str" | "list" | "pair" | null {
  if (ty.t !== "app") return null;
  if (ty.args.length === 0) {
    if (ty.head === "Nat") return "nat";
    if (ty.head === "U32") return "u32";
    if (ty.head === "Char") return "char";
    if (ty.head === "String") return "str";
  }
  if (ty.head === "List" && ty.args.length === 2) return "list";
  if (ty.head === "Pair" && ty.args.length === 2) return "pair";
  return null;
}

const range = (n: number) => Array.from({ length: Math.max(0, n) }, (_, i) => i);

export function measure(x: Val): number {
  switch (x.v) {
    case "nat": return x.n;
    case "u32": return x.n === 0 ? 0 : Math.log2(x.n + 1);
    case "char": return x.c === "a" ? 0 : 1;
    case "str": return x.s.length * 2 + [...x.s].filter((c) => c !== "a").length;
    case "list": return x.items.reduce((s, y) => s + 1 + measure(y), 0);
    case "pair": return measure(x.a) + measure(x.b);
    case "ctor": return x.i / 1000 + x.fields.reduce((s, y) => s + 1 + measure(y), 0);
  }
}

/** Bend source for a value; `name` maps a constructor's reader name to the name to print. */
export function render(x: Val, name: (n: string) => string = (n) => n): string {
  switch (x.v) {
    case "nat": return `${x.n}n`;
    case "u32": return `${x.n}`;
    case "char": return `'${x.c}'`;
    case "str": return JSON.stringify(x.s);
    case "list": return `[${x.items.map((y) => render(y, name)).join(", ")}]`;
    case "pair": return `(${render(x.a, name)}, ${render(x.b, name)})`;
    case "ctor": return `${name(x.name)}{${x.fields.map((y) => render(y, name)).join(", ")}}`;
  }
}
