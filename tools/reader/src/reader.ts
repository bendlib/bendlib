// @bendlib/reader: load Bend 2 files with the official parser and list their
// declarations with readable signatures.
//
// Everything structural (what is declared, its name, namespace, type, which
// file it came from) comes from bend.ts itself. The reader only adds source
// positions and doc comments, found from the spans bend.ts attaches to each
// declaration's type, and cross-checked against the declaration's name.

import * as fs from "node:fs";
import * as path from "node:path";
import { bendSource, importBend, type BendSource, type SourceOptions } from "./source.ts";

export type Quant = "affine" | "reusable" | "erased" | "template";
export type Kind = "type" | "ctor" | "def" | "law" | "template" | "effect" | "unsafe";
export type Origin = "own" | "imported" | "base";

export type Binder = { name: string; quant: Quant; type: string };
export type Statement = { lhs: string; rhs: string; type: string };

export type Decl = {
  name: string;          // the name as bend.ts keys it (namespace-qualified)
  namespace: string;     // the file's namespace ("" for the root file and Base)
  kind: Kind;
  origin: Origin;
  file: string;          // absolute path of the declaring file
  line: number;          // 1-based line of the declaring keyword (def/type/law, or the ctor name)
  column: number;        // 1-based column of the same
  doc: string | null;    // contiguous `#` lines directly above, `#` and one space stripped
  signature: string;     // the declared type, printed by bend.ts's own term_show
  statement?: Statement; // when the type ends in {lhs == rhs : type}
  binders?: Binder[];    // leading `for`/parameter binders, for laws and equality-typed defs
  proved?: boolean;      // laws: whether a def fills it (in the loaded files)
  proof?: { line: number; column: number }; // laws: where the filling def starts, when in the same file
  unsafe?: boolean;      // set when the def (or law proof) is marked @unsafe / `?`
  effects?: string[];    // kind "effect": the foreign .c/.js files it imports
  templates?: number;    // number of leading `~` template binders (defs and laws)
  ctors?: string[];      // kind "type": its constructors
  type?: string;         // kind "ctor": the datatype it builds
  predicate?: boolean;   // defs/laws whose type ends in a kind (Type, Data, Kind(..)): a predicate/type family
};

const KEY_ORDER: (keyof Decl)[] = ["name", "namespace", "kind", "origin", "file", "line", "column", "doc", "signature",
  "statement", "binders", "proved", "proof", "unsafe", "effects", "templates", "predicate", "ctors", "type"];

function canon(d: Decl): Decl {
  const o: Record<string, unknown> = {};
  for (const k of KEY_ORDER) if (d[k] !== undefined) o[k] = d[k];
  return o as Decl;
}

export type SourceFile = {
  path: string;      // realpath
  namespace: string;
  text: string;      // file contents as read
  parsed: string;    // the text bend.ts parsed: import lines blanked (same offsets/lines)
};

export type Loaded = {
  bend: any;         // the bend.ts module instance
  source: BendSource;
  book: any;         // bend.ts Book
  file: string;      // realpath of the root file
  n0: number;        // book.order index where the root file's declarations start
  files: SourceFile[];
  own: string[];     // keys declared in the root file
  imported: string[];// keys declared in other non-Base files
  base: string[];    // keys declared in Base
  checked: boolean;
};

export type LoadOptions = SourceOptions & {
  bendLib?: string;  // BEND_LIB for hub packages (default: env BEND_LIB, else ~/.bend/lib as bend does)
  bendHub?: string;  // BEND_HUB override
  check?: boolean;   // also run the type checker (bend.ts book_valid); default false
  bendSrc?: BendSource; // a source already resolved with bendSource()
};

/** A load/parse/check failure, located at file:line:column when bend.ts gave a span. */
export class BendReadError extends Error {
  file: string | null;
  line: number | null;
  column: number | null;
  bendMessage: string;  // bend.ts err_show output (what `bend` itself would print)
  def: string | null;
  constructor(bendMessage: string, file: string | null, line: number | null, column: number | null, def: string | null) {
    const at = file === null ? "" : `${file}${line === null ? "" : ":" + line + (column === null ? "" : ":" + column)}: `;
    super(at + bendMessage);
    this.name = "BendReadError";
    this.bendMessage = bendMessage;
    this.file = file;
    this.line = line;
    this.column = column;
    this.def = def;
  }
}

/** The text book_load hands to parse_book: leading `import` lines blanked, so offsets and lines match the file. */
export function blankImports(text: string): string {
  const lines = text.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    if (/^import(\s.*|)$/.test(line)) {
      lines[i] = "";
      continue;
    }
    if (line !== "" && !line.startsWith("#")) {
      break;
    }
  }
  return lines.join("\n");
}

function lineCol(src: string, pos: number): { line: number; column: number } {
  const before = src.slice(0, pos);
  const line = before.split("\n").length;
  return { line, column: pos - (before.lastIndexOf("\n") + 1) + 1 };
}

function readFiles(seen: Map<string, string | null>): SourceFile[] {
  const out: SourceFile[] = [];
  for (const [p, ns] of seen) {
    if (!fs.existsSync(p)) continue;
    const text = fs.readFileSync(p, "utf8");
    out.push({ path: p, namespace: ns ?? "", text, parsed: blankImports(text) });
  }
  return out;
}

// bend.ts spans carry the parsed text, not a path; prefer the file whose namespace
// prefixes the declaration key, so byte-identical modules stay distinct.
function fileOfSrc(files: SourceFile[], src: string, key?: string): SourceFile | null {
  const matches = files.filter((f) => f.parsed === src);
  const pool = matches.length > 0 ? matches : files.filter((f) => f.text === src);
  if (key !== undefined) {
    const ns = pool.filter((f) => f.namespace !== "" && key.startsWith(f.namespace + "."));
    if (ns.length > 0) return ns.reduce((a, b) => (b.namespace.length > a.namespace.length ? b : a));
    const root = pool.find((f) => f.namespace === "");
    if (root !== undefined) return root;
  }
  return pool[0] ?? null;
}

// bend.ts spans carry the parsed text, not a path, so the file is found by text.
function toReadError(B: any, e: unknown, seen: Map<string, string | null>, root: string): BendReadError {
  if (e instanceof BendReadError) return e;
  const err = e as any;
  if (err?.$ === "Err") {
    let msg: string;
    try {
      msg = B.err_show(err);
    } catch (e2) {
      msg = "Error: " + String(err.exp) + " (err_show failed: " + String(e2) + ")";
    }
    let file: string | null = null, line: number | null = null, column: number | null = null;
    if (err.spn !== undefined) {
      const f = fileOfSrc(readFiles(seen), err.spn.src);
      if (f !== null) file = f.path;
      ({ line, column } = lineCol(err.spn.src, err.spn.beg));
    }
    if (file === null && err.def !== undefined) {
      file = root; // located by definition name only
    }
    return new BendReadError(msg, file, line, column, err.def ?? null);
  }
  if (e instanceof RangeError) {
    return new BendReadError("Error: the machine stack overflowed (" + e.message + ")", root, null, null, null);
  }
  return new BendReadError("Error: " + (e instanceof Error ? e.message : String(e)), root, null, null, null);
}

/** Loads `file` and its imports into a fresh Book via bend.ts book_load, with an isolated `seen` map. */
export async function load(file: string, opts: LoadOptions = {}): Promise<Loaded> {
  const source = opts.bendSrc ?? await bendSource(opts);
  const B = await importBend(source, { bendLib: opts.bendLib, bendHub: opts.bendHub });
  const abs = path.resolve(file);
  if (!fs.existsSync(abs)) {
    throw new BendReadError("Error:\n- message  : no such file: " + abs, abs, null, null, null);
  }
  const book = B.book_nil();
  const seen = new Map<string, string | null>();
  let n0: number;
  try {
    n0 = await B.book_load(book, abs, "", seen);
  } catch (e) {
    throw toReadError(B, e, seen, fs.realpathSync(abs));
  }
  const real = fs.realpathSync(abs);
  if (opts.check) {
    try {
      B.book_valid(book);
    } catch (e) {
      throw toReadError(B, e, seen, real);
    }
  }
  const files = readFiles(seen);
  const own: string[] = [], imported: string[] = [], base: string[] = [];
  for (const k of new Set<string>(book.order)) {
    const t = book.tlds[k];
    if (t.b === true) {
      base.push(k);
    } else if (fileOfSrc(files, t.T.s?.src ?? "\0", k)?.path === real) {
      own.push(k);
    } else {
      imported.push(k);
    }
  }
  return { bend: B, source, book, file: real, n0, files, own, imported, base, checked: opts.check === true };
}

/** Prints a bend.ts HOAS term as `bend` prints types in errors; `bnd` names the binders in scope, outermost first. */
export function show(B: any, term: any, bnd: string[] = []): string {
  return B.term_show(B.term_lower(term, bnd.length), -1, [...bnd]);
}

function quantOf(q: { $: string }, templ: boolean): Quant {
  if (templ) return "template";
  return q.$ === "None" ? "erased" : q.$ === "Many" ? "reusable" : "affine";
}

function shape(B: any, T: any, templates: number): { binders: Binder[]; tip: any; bnd: string[] } {
  let t = B.term_lower(T, 0);
  const bnd: string[] = [];
  const binders: Binder[] = [];
  while (t.$ === "All") {
    binders.push({ name: t.k, quant: quantOf(t.q, binders.length < templates), type: B.term_show(t.A, -1, [...bnd]) });
    bnd.push(t.k);
    t = t.B;
  }
  return { binders, tip: t, bnd };
}

const esc = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");

const MASK = "\u0001";

// Replaces string/char literal and `#` comment characters with a sentinel, preserving
// offsets, so a ctor scan cannot match a name printed inside a comment or literal.
function maskSource(src: string): string {
  return src.split("\n").map((line) => {
    const c = line.split("");
    let i = 0;
    while (i < c.length) {
      if (c[i] === '"' || c[i] === "'") {
        const q = c[i];
        c[i++] = MASK;
        while (i < c.length) {
          const d = c[i];
          c[i++] = MASK;
          if (d === "\\") { if (i < c.length) c[i++] = MASK; continue; }
          if (d === q) break;
        }
      } else if (c[i] === "#") {
        while (i < c.length) c[i++] = MASK;
      } else i++;
    }
    return c.join("");
  }).join("\n");
}

type Header = { kw: string; pos: number; line: number; column: number; unsafe: boolean };

function findHeader(src: string, pos: number, local: string): Header | null {
  const re = new RegExp(`(^|[\\s;])(@unsafe\\s+)?(def|type|law)\\s+${esc(local)}(?![A-Za-z0-9_.])`, "g");
  let best: Header | null = null;
  for (let m; (m = re.exec(src)) !== null;) {
    const at = m.index + m[1].length + (m[2]?.length ?? 0);
    if (at > pos) break;
    const lc = lineCol(src, at);
    // must be the first token on its line (after an optional @unsafe)
    const lineStart = src.lastIndexOf("\n", at - 1) + 1;
    const pre = src.slice(lineStart, at).trim();
    if (pre !== "" && pre !== "@unsafe") continue;
    best = { kw: m[3], pos: at, line: lc.line, column: lc.column, unsafe: m[2] !== undefined || pre === "@unsafe" };
  }
  return best;
}

function docAbove(src: string, line: number): string | null {
  const lines = src.split("\n");
  let i = line - 2;
  if (i >= 0 && lines[i].trim() === "@unsafe") i--;
  const doc: string[] = [];
  for (; i >= 0; i--) {
    const l = lines[i].trim();
    if (!l.startsWith("#")) break;
    doc.unshift(l.replace(/^#\s?/, ""));
  }
  return doc.length === 0 ? null : doc.join("\n");
}

function localName(key: string, ns: string): string {
  return ns !== "" && key.startsWith(ns + ".") ? key.slice(ns.length + 1) : key;
}

// A `type …:` body ends at the next top-level item (`def|type|law|import|@unsafe` at
// column 0) or EOF; stopping on the keyword (not column 0) admits unindented ctors.
function typeBodyEnd(src: string, headerPos: number): number {
  const nl = src.indexOf("\n", headerPos);
  let pos = nl === -1 ? src.length : nl + 1;
  while (pos < src.length) {
    const eol = src.indexOf("\n", pos);
    const stop = eol === -1 ? src.length : eol;
    if (/^(@unsafe\b|(def|type|law|import)\b)/.test(src.slice(pos, stop))) return pos;
    pos = eol === -1 ? src.length : eol + 1;
  }
  return src.length;
}

export type Scope = "own" | "all-non-base" | "all";

export function decls(L: Loaded, opts: { scope?: Scope } = {}): Decl[] {
  const scope = opts.scope ?? "own";
  const B = L.bend, book = L.book;
  const keys = scope === "own" ? L.own : scope === "all-non-base" ? [...L.imported, ...L.own] : [...L.base, ...L.imported, ...L.own];
  const wanted = new Set(keys);
  const out: Decl[] = [];
  for (const k of new Set<string>(book.order)) {
    if (!wanted.has(k)) continue;
    const t = book.tlds[k];
    const origin: Origin = t.b === true ? "base" : L.own.includes(k) ? "own" : "imported";
    const s = t.T.s;
    const f = s === undefined ? null : fileOfSrc(L.files, s.src, k);
    if (f === null) {
      throw new BendReadError(`Error: reader cannot place '${k}' in any loaded file (its type carries no usable span)`, L.file, null, null, k);
    }
    const local = localName(k, f.namespace);
    const h = findHeader(f.parsed, s.beg, local);
    if (h === null) {
      throw new BendReadError(`Error: reader found no 'def|type|law ${local}' header before offset ${s.beg}`, f.path, lineCol(f.parsed, s.beg).line, null, k);
    }
    const base = {
      name: k, namespace: f.namespace, origin, file: f.path, line: h.line, column: h.column,
      doc: docAbove(f.parsed, h.line), signature: show(B, t.T),
    };
    if (t.$ === "ADT") {
      if (h.kw !== "type") {
        throw new BendReadError(`Error: reader expected 'type ${local}', found '${h.kw}'`, f.path, h.line, h.column, k);
      }
      out.push({ ...base, kind: "type", ctors: t.c.map((c: any) => c.k) });
      // ctor types carry no span of their own; find them from the type header through
      // its body, in order, over the masked text (so a name in a comment cannot match)
      const masked = maskSource(f.parsed);
      const end = typeBodyEnd(masked, h.pos);
      let from = h.pos;
      for (const c of t.c) {
        const cl = localName(c.k, f.namespace);
        const re = new RegExp(`${esc(cl)}[ \\t]*\\{`, "g");
        re.lastIndex = from;
        let at = -1;
        for (let m; (m = re.exec(masked)) !== null;) {
          const p = m.index;
          if (p >= end) break;
          // matched when preceded, after indentation, by the header `:` or a `}` or line start
          const lineStart = masked.lastIndexOf("\n", p - 1) + 1;
          let i = p;
          while (i > lineStart && (masked[i - 1] === " " || masked[i - 1] === "\t")) i--;
          if (i === lineStart || masked[i - 1] === "}" || masked[i - 1] === ":") {
            at = p;
            break;
          }
        }
        if (at === -1) {
          throw new BendReadError(`Error: reader found no constructor '${cl}' after type ${local}`, f.path, h.line, null, c.k);
        }
        from = at + cl.length;
        const lc = lineCol(f.parsed, at);
        out.push({
          name: c.k, namespace: f.namespace, kind: "ctor", origin, file: f.path, line: lc.line, column: lc.column,
          doc: docAbove(f.parsed, lc.line), signature: show(B, c.T), type: k,
        });
      }
      continue;
    }
    const d: Decl = { ...base, kind: "def" };
    const templates = t.x ?? 0;
    const sh = shape(B, t.T, templates);
    if (h.kw === "law") {
      d.kind = "law";
      d.proved = t.v !== null;
      if (d.proved) {
        const p = findHeader(f.parsed, f.parsed.length, local);
        if (p !== null && p.kw === "def" && p.pos > h.pos) d.proof = { line: p.line, column: p.column };
      }
      d.binders = sh.binders;
    } else if (h.kw !== "def") {
      throw new BendReadError(`Error: reader expected 'def ${local}', found '${h.kw}'`, f.path, h.line, h.column, k);
    } else if (t.u === true) {
      d.kind = "unsafe";
    } else if (t.i !== undefined) {
      d.kind = "effect";
      d.effects = t.i.map((p: string) => path.resolve(p));
    } else if (templates > 0) {
      d.kind = "template";
    }
    if (t.u === true) d.unsafe = true;
    if (templates > 0) d.templates = templates;
    if (sh.tip.$ === "Typ") d.predicate = true;
    if (sh.tip.$ === "Eql") {
      d.binders = sh.binders;
      d.statement = {
        lhs: B.term_show(sh.tip.a, -1, [...sh.bnd]),
        rhs: B.term_show(sh.tip.b, -1, [...sh.bnd]),
        type: B.term_show(sh.tip.T, -1, [...sh.bnd]),
      };
    }
    out.push(d);
  }
  return out.map(canon);
}
