// Import-header parsing and package dependency edges. Headers are copied from real
// hub files; the rules mirror bend.ts book_load (2.0.27).

import { describe, expect, test } from "bun:test";
import { dependencyEdges, foreignImports, parseImports, relativeEscape } from "../src/imports.ts";

const FORMAT_BEND = `import Base
import 0xe49a3e6521e1b71e55654a885f27bcc1/parse.bend as P
import ./date.bend as D
import ./datetime.bend as DT

type Format.Error is Data:
  Unexpected{offset: Nat, char: Char}
`;

describe("parseImports", () => {
  test("reads the header of a real hub file", () => {
    const im = parseImports(FORMAT_BEND);
    expect(im.map((i) => [i.line, i.kind, i.path, i.alias])).toEqual([
      [1, "base", "Base", null],
      [2, "hash", "0xe49a3e6521e1b71e55654a885f27bcc1/parse.bend", "P"],
      [3, "relative", "./date.bend", "D"],
      [4, "relative", "./datetime.bend", "DT"],
    ]);
    expect(im[1].hash).toBe("0xe49a3e6521e1b71e55654a885f27bcc1");
    expect(im[1].target).toBe("parse.bend");
  });
  test("comments and blank lines may precede imports; the first code line ends the header", () => {
    const src = "# header\n\nimport Base\n# note\nimport bend-mathlib@0.1.0.1/nat.bend as MNat\ndef f() -> Nat:\n  0n\nimport ./late.bend as Late\n";
    const im = parseImports(src);
    expect(im.map((i) => i.kind)).toEqual(["base", "named"]);
    expect(im[1].named).toBe("bend-mathlib@0.1.0.1");
    expect(im[1].target).toBe("nat.bend");
  });
  test("foreign imports inside a def body are not package imports", () => {
    const src = 'import Base\n\ndef now() -> U32:\n  import "./effs/wire.c"\n  import "./effs/wire.js"\n';
    expect(parseImports(src).map((i) => i.kind)).toEqual(["base"]);
    expect(foreignImports(src)).toEqual(["./effs/wire.c", "./effs/wire.js"]);
  });
  test("malformed imports are kept as invalid, not dropped", () => {
    const im = parseImports("import ./x.bend\nimport Short@1.0.0.0/a.bend as A\n");
    expect(im.map((i) => i.kind)).toEqual(["invalid", "invalid"]);
  });
  test("a trailing comment after the alias is allowed, as in bend.ts", () => {
    expect(parseImports("import ./a.bend as A # why\n")[0].alias).toBe("A");
  });
});

describe("relativeEscape", () => {
  test("stays inside the package", () => {
    expect(relativeEscape("src/a/b.bend", "../../src.bend")).toBeNull();
    expect(relativeEscape("a.bend", "./lib/x.bend")).toBeNull();
  });
  test("climbing out of the package lands in another hash directory of BEND_LIB", () => {
    expect(relativeEscape("a.bend", "../0xe49a3e6521e1b71e55654a885f27bcc1/parse.bend"))
      .toEqual({ hash: "0xe49a3e6521e1b71e55654a885f27bcc1", target: "parse.bend" });
  });
});

describe("dependencyEdges", () => {
  const A = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", B = "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb", M = "0xafc61ca8b7738a6df7f28eddf80168f8";
  const pkg = (hash: string, files: Record<string, string>) => ({
    hash, files: Object.entries(files).map(([path, text]) => ({ path, imports: parseImports(text) })),
  });
  const names = (nv: string) => (nv === "bend-mathlib@0.1.0.1" ? M : null);

  test("hash imports, named imports (resolved) and escaping relative imports become edges; one per package pair", () => {
    const edges = dependencyEdges([
      pkg(A, {
        "x.bend": `import Base\nimport ${B}/lib.bend as L\nimport bend-mathlib@0.1.0.1/nat.bend as N\n`,
        "y.bend": `import ${B}/other.bend as O\nimport ./x.bend as X\n`,
      }),
      pkg(B, { "lib.bend": `import ../${A}/x.bend as X\n` }),
    ], names);
    expect(edges.map((e) => [e.from, e.to, e.named ?? null])).toEqual([
      [A, B, null], [A, M, "bend-mathlib@0.1.0.1"], [B, A, null],
    ]);
    expect(edges[0].via).toBe(`x.bend: import ${B}/lib.bend as L`);
  });
  test("planted negatives: self-imports by hash and unknown names give no edge", () => {
    const edges = dependencyEdges([
      pkg(A, { "LAWS.bend": `import ${A}/lib.bend as Self\nimport nobody-knows-this@1.0.0.0/a.bend as Q\n` }),
    ], names);
    expect(edges).toEqual([]);
  });
});
