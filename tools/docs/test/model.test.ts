// Law settlement: proofs in sibling files, ?holes, and when an `open` LAWS file
// may count as checking for its package.

import { describe, expect, test } from "bun:test";
import { defBody, fillerLine, finishPackage, hasHole, moduleHeader, type Module, type Package } from "../src/model.ts";
import type { DocDecl } from "../src/extract.ts";
import { declIds } from "../src/render.ts";
import type { FileStatus } from "../src/status.ts";

const st = (c: FileStatus["class"], summary = ""): FileStatus => ({ class: c, summary, detail: "", exitCode: 0, seconds: 0 });
const law = (name: string, proved: boolean, proofLine?: number): DocDecl =>
  ({ name, kind: "law", line: 1, doc: null, signature: "", proved, ...(proofLine ? { proofLine } : {}) });
const mod = (path: string, decls: DocDecl[], status: FileStatus | null): Module =>
  ({ path, header: null, imports: [], foreign: [], decls, error: null, status, provedIn: {} });
const pkg = (modules: Module[]): Package => ({
  hash: "0x0", ts: 0, desc: "", bytes: 0, files: [], names: [], licenses: [], modules, deps: [], rdeps: [], status: null,
  counts: { laws: 0, proved: 0, defs: 0, types: 0, decls: 0 },
});

const PROOF = "import Base\nimport ./LAWS.bend as Laws\n\ndef Laws.a():\n  {==}\n\ndef Laws.b(x):\n  match x:\n    case 0n:\n      ?TODO\n";

describe("proof bodies", () => {
  test("defBody stops at the next top-level line and blanks strings and comments", () => {
    const src = 'def f(x):\n  "?not_a_hole" # ?nor_this\n  {==}\ndef g():\n  ?TODO\n';
    expect(hasHole(defBody(src, 1))).toBe(false);
    expect(hasHole(defBody(src, 4))).toBe(true);
  });
  test("an unsafe def f?( is not a hole", () => {
    expect(hasHole(defBody("def f?(x):\n  x\n", 1))).toBe(false);
  });
  test("fillerLine finds an aliased def", () => {
    expect(fillerLine(PROOF, "a")).toBe(4);
    expect(fillerLine(PROOF, "b")).toBe(7);
    expect(fillerLine(PROOF, "c")).toBeNull();
  });
});

describe("finishPackage", () => {
  const text = (p: string) => (p === "PROOF.bend" ? PROOF : "law a:\nlaw b:\n");

  test("a law proved in a checking sibling is proved, and the LAWS file counts as checking", () => {
    const p = pkg([mod("LAWS.bend", [law("a", false)], st("open", "1 TODO found.")), mod("PROOF.bend", [], st("checks", "All terms check."))]);
    finishPackage(p, new Map([["PROOF.bend", ["LAWS.bend#a"]]]), text);
    expect(p.modules[0].decls![0].proved).toBe(true);
    expect(p.modules[0].provedIn).toEqual({ a: "PROOF.bend" });
    expect(p.modules[0].settled).toBe("checks");
    expect(p.status).toBe("checks");
    expect(p.counts).toMatchObject({ laws: 1, proved: 1 });
  });
  test("planted negative: a ?TODO in the sibling's proof keeps the law and the package open", () => {
    const p = pkg([mod("LAWS.bend", [law("a", false), law("b", false)], st("open", "2 TODOs found.")), mod("PROOF.bend", [], st("open", "1 TODO found."))]);
    finishPackage(p, new Map([["PROOF.bend", ["LAWS.bend#a", "LAWS.bend#b"]]]), text);
    expect(p.modules[0].decls!.map((d) => [d.name, d.proved, d.holes ?? false])).toEqual([["a", false, false], ["b", false, true]]);
    expect(p.modules[0].settled).toBeUndefined();
    expect(p.status).toBe("open");
  });
  test("planted negative: a sibling that times out does not prove anything", () => {
    const p = pkg([mod("LAWS.bend", [law("a", false)], st("open", "1 TODO found.")), mod("PROOF.bend", [], st("timeout"))]);
    finishPackage(p, new Map([["PROOF.bend", ["LAWS.bend#a"]]]), text);
    expect(p.modules[0].decls![0].proved).toBe(false);
    expect(p.status).toBe("timeout");
  });
  test("planted negative: more TODOs than sibling-proved laws means something else is open", () => {
    const p = pkg([mod("LAWS.bend", [law("a", false)], st("open", "3 TODOs found.")), mod("PROOF.bend", [], st("checks"))]);
    finishPackage(p, new Map([["PROOF.bend", ["LAWS.bend#a"]]]), text);
    expect(p.modules[0].decls![0].proved).toBe(true);
    expect(p.status).toBe("open");
  });
  test("a law proved in its own file with a ?hole is open", () => {
    const own = "law z:\n  {x == x : Nat}\n\ndef z():\n  ?TODO\n";
    const p = pkg([mod("m.bend", [law("z", true, 4)], st("open", "1 TODO found."))]);
    finishPackage(p, new Map(), () => own);
    expect(p.modules[0].decls![0]).toMatchObject({ proved: false, holes: true });
    expect(p.status).toBe("open");
  });
});

describe("declaration anchors", () => {
  test("a def named main does not take the <main> landmark's id; kinds disambiguate clashes", () => {
    const d = (name: string, kind: DocDecl["kind"]): DocDecl => ({ name, kind, line: 1, doc: null, signature: "" });
    const m = mod("main.bend", [d("main", "def"), d("Pair", "type"), { ...d("Pair", "ctor"), type: "Pair" }, d("hq", "def")], null);
    expect([...declIds(m).values()]).toEqual(["Pair", "Pair-ctor", "main-def", "hq-def"]);
  });
});

describe("module header", () => {
  test("a run of # lines before imports is the header, with # and one space removed", () => {
    expect(moduleHeader("# a\n# b\n\nimport Base\n")).toBe("a\nb");
  });
  test("a run directly before an import is the header", () => {
    expect(moduleHeader("# a\nimport Base")).toBe("a");
  });
  test("a run directly before a declaration is that declaration's doc, not a header", () => {
    expect(moduleHeader("# doc\ndef f() -> Nat:\n  0n\n")).toBeNull();
  });
  test("no # on line 1 means no header", () => {
    expect(moduleHeader("import Base\n# x\n")).toBeNull();
  });
  test("a bare # line becomes an empty line, which the renderer turns into a paragraph break", () => {
    expect(moduleHeader("# a\n#\n# b\n\n")).toBe("a\n\nb");
  });
});
