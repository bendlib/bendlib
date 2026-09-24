// extract: declarations of one hub file through @bendlib/reader; a load or parse
// failure becomes a per-file error record, never an exception.

import { relative } from "node:path";
import { load, decls, BendReadError, type BendSource, type Decl, type Loaded } from "../../reader/index.ts";

export type DocDecl = {
  name: string; kind: Decl["kind"]; line: number; doc: string | null; signature: string;
  statement?: { lhs: string; rhs: string; type: string };
  proved?: boolean; proofLine?: number; holes?: boolean; unsafe?: boolean; predicate?: boolean; templates?: number;
  ctors?: string[]; type?: string; effects?: string[];
};

export type FileError = { message: string; file: string | null; line: number | null };
// `fills`: laws of OTHER files in the same package that this file's imports leave proved,
// as "<path>#<local name>" (LAWS.bend declares, PROOF.bend fills).
export type FileDecls = { ok: true; decls: DocDecl[]; fills: string[]; ms: number } | { ok: false; error: FileError; ms: number };

function slim(d: Decl, pkgDir: string): DocDecl {
  const o: DocDecl = { name: d.name, kind: d.kind, line: d.line, doc: d.doc, signature: d.signature };
  if (d.statement) o.statement = d.statement;
  if (d.proved !== undefined) o.proved = d.proved;
  if (d.proof) o.proofLine = d.proof.line;
  if (d.unsafe) o.unsafe = true;
  if (d.predicate) o.predicate = true;
  if (d.templates) o.templates = d.templates;
  if (d.ctors) o.ctors = d.ctors;
  if (d.type) o.type = d.type;
  if (d.effects) o.effects = d.effects.map((e) => relative(pkgDir, e));
  return o;
}

function fills(L: Loaded, pkgDir: string): string[] {
  const local = L.files.filter((f) => f.path !== L.file && f.path.startsWith(pkgDir + "/") && f.namespace !== "")
    .sort((a, b) => b.namespace.length - a.namespace.length);
  const out: string[] = [];
  for (const k of L.imported) {
    if (L.book.tlds[k]?.v == null) continue;
    const f = local.find((x) => k.startsWith(x.namespace + "."));
    if (f !== undefined) out.push(`${relative(pkgDir, f.path)}#${k.slice(f.namespace.length + 1)}`);
  }
  return out;
}

export async function extractFile(file: string, pkgDir: string, bendLib: string, bendSrc: BendSource): Promise<FileDecls> {
  const t0 = performance.now();
  try {
    const L = await load(file, { bendLib, bendSrc });
    return { ok: true, decls: decls(L, { scope: "own" }).map((d) => slim(d, pkgDir)), fills: fills(L, pkgDir), ms: performance.now() - t0 };
  } catch (e) {
    const ms = performance.now() - t0;
    if (e instanceof BendReadError) {
      const f = e.file === null ? null : e.file.startsWith(bendLib + "/") ? e.file.slice(bendLib.length + 1) : e.file;
      return { ok: false, error: { message: e.bendMessage, file: f, line: e.line }, ms };
    }
    return { ok: false, error: { message: e instanceof Error ? `${e.name}: ${e.message}` : String(e), file: null, line: null }, ms };
  }
}
