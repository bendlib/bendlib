// Every CLI test runs the real bend compiler on the fixtures; nothing is mocked.

import { describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { rewrite, splitEquation } from "../src/terms.ts";
import { parseTy, showTy } from "../src/types.ts";

const CLI = path.join(import.meta.dir, "..", "cli.ts");
const FX = path.join(import.meta.dir, "fixtures");
const T = 180_000;

async function run(...args: string[]) {
  const p = Bun.spawn([process.execPath, CLI, ...args], { stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
  return { code: await p.exited, stdout, stderr };
}

async function runEnv(env: Record<string, string>, ...args: string[]) {
  const p = Bun.spawn([process.execPath, CLI, ...args], { stdout: "pipe", stderr: "pipe", env: { ...process.env, ...env } });
  const [stdout, stderr] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
  return { code: await p.exited, stdout, stderr };
}

async function json(...args: string[]) {
  const r = await run(...args, "--json");
  if (r.stderr !== "") throw new Error(r.stderr);
  return { code: r.code, report: JSON.parse(r.stdout) as any };
}

const law = (report: any, name: string) => {
  const l = report.laws.find((x: any) => x.name === name);
  if (!l) throw new Error(`no law ${name} in report`);
  return l;
};
const binds = (l: any) => Object.fromEntries(l.counterexample.bindings.map((b: any) => [b.name, b.value]));

// One `correct.bend` run, shared by the two tests that assert on a clean module.
let correctRun: Promise<{ code: number; report: any }> | null = null;
const correct = () => (correctRun ??= json(path.join(FX, "correct.bend")));

describe("correct implementation", () => {
  test("all four laws pass, exit 0", async () => {
    const { code, report } = await correct();
    expect(code).toBe(0);
    expect(report.laws.map((l: any) => [l.name, l.status, l.claim])).toEqual([
      ["ins_sorted", "pass", "equation"],
      ["dbl_add", "pass", "equation"],
      ["app_size", "pass", "equation"],
      ["le_dbl", "pass", "predicate"],
    ]);
    for (const l of report.laws) expect(l.instances).toBeGreaterThan(0);
    expect(law(report, "ins_sorted").premise.satisfied).toBeLessThan(law(report, "ins_sorted").premise.total);
  }, T);
});

describe("planted bugs", () => {
  test("each bug yields a minimal counterexample, exit 1", async () => {
    const { code, report } = await json(path.join(FX, "buggy.bend"));
    expect(code).toBe(1);
    expect(law(report, "ins_length").status).toBe("pass");
    const sorted = law(report, "ins_sorted");
    expect(sorted.status).toBe("fail");
    expect(binds(sorted)).toEqual({ x: "0n", xs: "[1n]" });
    expect(sorted.counterexample.lhs).toEqual({ term: "is_sorted(ins(0n, [1n]))", value: "False{}" });
    expect(sorted.counterexample.rhs).toEqual({ term: "True{}", value: "True{}" });
    const dbl = law(report, "dbl_add");
    expect(binds(dbl)).toEqual({ n: "2n" });
    expect(dbl.counterexample.lhs.value).toBe("3n");
    expect(dbl.counterexample.rhs.value).toBe("4n");
    expect([dbl.counterexample.expected, dbl.counterexample.observed]).toEqual(["3n", "4n"]);
    const app = law(report, "app_size");
    expect(binds(app)).toEqual({ xs: "Push{Blue{}, Bot{}}", ys: "Bot{}" });
    expect(app.counterexample.lhs.value).toBe("0n");
    expect(app.counterexample.rhs.value).toBe("1n");
  }, T);

  test("human output shows binders and both sides", async () => {
    const r = await run(path.join(FX, "buggy.bend"), "--law", "ins_sorted");
    expect(r.code).toBe(1);
    expect(r.stderr).toBe("");
    expect(r.stdout).toMatch(/✗ ins_sorted {2}counterexample \(shrunk/);
    expect(r.stdout).toMatch(/\n +x = 0n\n +xs = \[1n\]\n/);
    expect(r.stdout).toContain("lhs  is_sorted(ins(0n, [1n])) = False{}");
    expect(r.stdout).toContain("proves nothing about all inputs");
  }, T);

  test("shrinking reduces random Nat, list and datatype counterexamples", async () => {
    const dbl = law((await json(path.join(FX, "buggy.bend"), "--law", "dbl_add", "--size", "0", "--max-instances", "3", "--seed", "2")).report, "dbl_add");
    expect(dbl.counterexample.original).toEqual([{ name: "n", value: "7n" }]);
    expect(dbl.counterexample.shrinkSteps).toBeGreaterThan(0);
    expect(binds(dbl)).toEqual({ n: "2n" });
    const sorted = law((await json(path.join(FX, "buggy.bend"), "--law", "ins_sorted", "--size", "0", "--max-instances", "3", "--seed", "2")).report, "ins_sorted");
    expect(sorted.counterexample.original).toEqual([{ name: "x", value: "0n" }, { name: "xs", value: "[5n, 6n]" }]);
    expect(binds(sorted)).toEqual({ x: "0n", xs: "[1n]" });
    const app = law((await json(path.join(FX, "buggy.bend"), "--law", "app_size", "--size", "0", "--max-instances", "3", "--seed", "6")).report, "app_size");
    expect(app.counterexample.original).toEqual([{ name: "xs", value: "Push{Red{}, Push{Blue{}, Bot{}}}" }, { name: "ys", value: "Push{Green{}, Bot{}}" }]);
    expect(binds(app)).toEqual({ xs: "Push{Blue{}, Bot{}}", ys: "Bot{}" });
  }, T);
});

describe("claim kinds and skips", () => {
  test("template function binder is instantiated from the catalog", async () => {
    const { code, report } = await json(path.join(FX, "template.bend"));
    expect(code).toBe(0);
    expect(law(report, "twice_id").status).toBe("pass");
    expect(law(report, "add_zero").status).toBe("pass");
  }, T);

  test("template map laws: a true one passes, a false one fails on a non-identity f", async () => {
    const { code, report } = await json(path.join(FX, "templates_map.bend"), "--max-instances", "40");
    expect(code).toBe(1);
    expect(law(report, "length_map").status).toBe("pass");
    const bad = law(report, "map_id_bad");
    expect(bad.status).toBe("fail");
    const f = bad.counterexample.bindings.find((b: any) => b.name === "f");
    expect(f).toBeDefined();
    expect(f.value).not.toBe("(lc_x => lc_x)");
  }, T);

  test("predicates, refutations, premises, type parameters, unsupported binders", async () => {
    const { code, report } = await json(path.join(FX, "kinds.bend"));
    expect(code).toBe(1);
    const st = Object.fromEntries(report.laws.map((l: any) => [l.name, l.status]));
    expect(st).toEqual({
      le_half: "pass", half_le_bad: "fail", p_holds: "skip", lt_irrefl: "pass", add_ne_bad: "fail", le_trans: "pass",
      append_nil_r: "pass", reverse_id_bad: "fail", pair_swap: "pass", where_law: "pass", fn_binder: "skip", float_law: "skip",
    });
    expect(binds(law(report, "half_le_bad"))).toEqual({ n: "1n" });
    expect(law(report, "half_le_bad").counterexample.goal).toBe("{False{} == True{} : Bool}");
    expect(law(report, "p_holds").reason).toMatch(/^not decidable by evaluation/);
    expect(binds(law(report, "add_ne_bad"))).toEqual({ a: "0n", b: "0n" });
    expect(law(report, "lt_irrefl").premise.satisfied).toBe(0);
    const rev = law(report, "reverse_id_bad");
    expect(rev.counterexample.types).toEqual([{ name: "A", value: "U32" }]);
    expect(binds(rev)).toEqual({ xs: "[0, 1]" });
    expect(law(report, "where_law").premise.satisfied).toBeGreaterThan(0);
    expect(law(report, "fn_binder").reason).toMatch(/function-typed binder f/);
    expect(law(report, "float_law").reason).toMatch(/F32/);
  }, T);
});

describe("unsafe verdict", () => {
  test("a checker verdict that relies on unsafe code is not a clean pass", async () => {
    const { code, report } = await json(path.join(FX, "unsafe_pass.bend"), "--max-instances", "3");
    expect(code).toBe(0);
    const l = law(report, "zero_is_zero");
    expect(l.status).toBe("skip");
    expect(l.status).not.toBe("pass");
    expect(l.reason).toMatch(/unsafe or foreign code/);
  }, T);

  test("a clean module still reports pass", async () => {
    const { code, report } = await correct();
    expect(code).toBe(0);
    expect(report.laws.every((l: any) => l.status === "pass")).toBe(true);
  }, T);

  test("an open law alongside @unsafe is not a clean pass", async () => {
    const { code, report } = await json(path.join(FX, "unsafe_open.bend"), "--max-instances", "3", "--jobs", "4");
    expect(code).toBe(0);
    const l = law(report, "zero_is_zero");
    expect(l.status).toBe("skip");
    expect(l.status).not.toBe("pass");
    expect(l.reason).toMatch(/unsafe or foreign code/);
  }, T);
});

describe("where premises and exs witnesses", () => {
  test("where drops failing instances; a false where law fails; exs searches for a witness", async () => {
    const { code, report } = await json(path.join(FX, "where_exs.bend"), "--max-instances", "40", "--jobs", "4");
    expect(code).toBe(1);
    expect(report.laws.map((l: any) => [l.name, l.status])).toEqual([
      ["where_true", "pass"], ["where_false", "fail"], ["exs_found", "pass"], ["exs_missing", "skip"],
    ]);
    const wt = law(report, "where_true");
    expect(wt.premise.satisfied).toBeGreaterThan(0);
    expect(wt.premise.satisfied).toBeLessThan(wt.premise.total);
    expect(binds(law(report, "where_false"))).toEqual({ n: "0n", m: "0n" });
    expect(law(report, "exs_found").claim).toBe("witness");
    expect(law(report, "exs_missing").reason).toMatch(/^no witness found in \d+ candidates$/);
  }, T);
});

describe("too-large instances and --max-nat", () => {
  test("overflowing instances are dropped, not errors; a small counterexample still fails", async () => {
    const { code, report } = await json(path.join(FX, "pow.bend"), "--max-instances", "40");
    expect(code).toBe(1);
    expect(law(report, "pow_add").status).toBe("pass");
    const wrong = law(report, "pow_add_wrong");
    expect(wrong.status).toBe("fail");
    expect(wrong.counterexample).toBeDefined();
  }, T);

  test("--max-nat bounds random Nats so nothing overflows", async () => {
    const { code, report } = await json(path.join(FX, "pow.bend"), "--law", "pow_add", "--max-nat", "3");
    expect(code).toBe(0);
    const l = law(report, "pow_add");
    expect(l.status).toBe("pass");
    expect(l.tooLarge ?? 0).toBe(0);
  }, T);
});

describe("imports and --impl", () => {
  test("laws over an imported module print the user's alias", async () => {
    const { code, report } = await json(path.join(FX, "laws_lib.bend"));
    expect(code).toBe(1);
    expect(binds(law(report, "app_size"))).toEqual({ xs: "M.Push{0n, M.Bot{}}", ys: "M.Bot{}" });
    expect(law(report, "app_bot").counterexample.observed).toBe("M.Push{0n, M.Bot{}}");
  }, T);

  test("--impl swaps the implementation", async () => {
    const { code, report } = await json(path.join(FX, "laws_lib.bend"), "--impl", path.join(FX, "lib_ok.bend"));
    expect(code).toBe(0);
    expect(report.laws.map((l: any) => l.status)).toEqual(["pass", "pass"]);
  }, T);

  test("hash imports (a name@version spec and a direct 0x hash) resolve to a local 0x<hash> copy", async () => {
    const hash = "deadbeefdeadbeefdeadbeefdeadbeef";
    const lib = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-bendlib-"));
    fs.mkdirSync(path.join(lib, "names"), { recursive: true });
    fs.mkdirSync(path.join(lib, `0x${hash}`), { recursive: true });
    fs.writeFileSync(path.join(lib, "names", "lawcheck-testpkg@1.2.3.4"), `0x${hash}\n`);
    fs.writeFileSync(path.join(lib, `0x${hash}`, "lib.bend"), [
      "import Base",
      "",
      "type Color is Data:",
      "  Red{}",
      "  Green{}",
      "",
      "def pick(c: Color) -> Nat:",
      "  match c:",
      "    case Red{}:",
      "      0n",
      "    case Green{}:",
      "      1n",
      "",
    ].join("\n"));
    const writeRoot = (kind: string, importLine: string) => {
      const dir = fs.mkdtempSync(path.join(os.tmpdir(), `lawcheck-hashroot-${kind}-`));
      const file = path.join(dir, "root.bend");
      fs.writeFileSync(file, [
        "import Base",
        importLine,
        "",
        "law pick_le_one:",
        "  for c: H.Color",
        "  {Nat.is_le(H.pick(c), 1n) == True{} : Bool}",
        "",
        "law pick_bad:",
        "  for c: H.Color",
        "  {H.pick(c) == 0n : Nat}",
        "",
      ].join("\n"));
      return file;
    };
    const roots = [
      writeRoot("named", "import lawcheck-testpkg@1.2.3.4/lib.bend as H"),
      writeRoot("hash", `import 0x${hash}/lib.bend as H`),
    ];
    for (const root of roots) {
      const r = await runEnv({ BEND_LIB: lib }, root, "--native", "--jobs", "4", "--max-instances", "6", "--json");
      expect(r.stderr).toBe("");
      expect(r.code).toBe(1);
      const rep = JSON.parse(r.stdout);
      const ok = rep.laws.find((l: any) => l.name === "pick_le_one");
      expect(ok.status).toBe("pass");
      expect(ok.native.checked).toBeGreaterThan(0);
      expect(ok.native.disagreements).toEqual([]);
      const bad = rep.laws.find((l: any) => l.name === "pick_bad");
      expect(bad.status).toBe("fail");
      expect(bad.native.checked).toBeGreaterThan(0);
      expect(bad.native.disagreements).toEqual([]);
      expect(r.stdout).not.toContain(hash);
      expect(bad.counterexample.bindings).toEqual([{ name: "c", value: "H.Green{}" }]);
      expect(bad.counterexample.lhs.term).toBe("H.pick(H.Green{})");
    }
  }, T);

  test("nested hash imports (a name@version module importing another) resolve hermetically", async () => {
    const depHash = "feedfacefeedfacefeedfacefeedface";
    const kernelHash = "deadbeefdeadbeefdeadbeefdeadbeef";
    const lib = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-bendlib-"));
    fs.mkdirSync(path.join(lib, "names"), { recursive: true });
    fs.mkdirSync(path.join(lib, `0x${depHash}`), { recursive: true });
    fs.mkdirSync(path.join(lib, `0x${kernelHash}`), { recursive: true });
    fs.writeFileSync(path.join(lib, "names", "lawcheck-dep@2.0.0.0"), `0x${depHash}\n`);
    fs.writeFileSync(path.join(lib, "names", "lawcheck-kernel@1.2.3.4"), `0x${kernelHash}\n`);
    fs.writeFileSync(path.join(lib, `0x${depHash}`, "base.bend"), [
      "import Base",
      "",
      "type Color is Data:",
      "  Red{}",
      "  Green{}",
      "",
      "def pick(c: Color) -> Nat:",
      "  match c:",
      "    case Red{}:",
      "      0n",
      "    case Green{}:",
      "      1n",
      "",
    ].join("\n"));
    fs.writeFileSync(path.join(lib, `0x${kernelHash}`, "kernel.bend"), [
      "import Base",
      "import lawcheck-dep@2.0.0.0/base.bend as D",
      "",
      "def pick_red() -> Nat:",
      "  D.pick(D.Red{})",
      "",
    ].join("\n"));
    const writeRoot = (kind: string, importLine: string) => {
      const dir = fs.mkdtempSync(path.join(os.tmpdir(), `lawcheck-nested-${kind}-`));
      const file = path.join(dir, "root.bend");
      fs.writeFileSync(file, [
        "import Base",
        importLine,
        "",
        "law pick_red_zero:",
        "  {H.pick_red() == 0n : Nat}",
        "",
        "law pick_red_one:",
        "  {H.pick_red() == 1n : Nat}",
        "",
      ].join("\n"));
      return file;
    };
    const roots = [
      writeRoot("named", "import lawcheck-kernel@1.2.3.4/kernel.bend as H"),
      writeRoot("hash", `import 0x${kernelHash}/kernel.bend as H`),
    ];
    for (const root of roots) {
      const r = await runEnv({ BEND_LIB: lib }, root, "--native", "--jobs", "4", "--max-instances", "6", "--json");
      expect(r.stderr).toBe("");
      expect(r.code).toBe(1);
      const rep = JSON.parse(r.stdout);
      const ok = rep.laws.find((l: any) => l.name === "pick_red_zero");
      expect(ok.status).toBe("pass");
      expect(ok.native.checked).toBeGreaterThan(0);
      expect(ok.native.disagreements).toEqual([]);
      const bad = rep.laws.find((l: any) => l.name === "pick_red_one");
      expect(bad.status).toBe("fail");
      expect(bad.native.checked).toBeGreaterThan(0);
      expect(bad.native.disagreements).toEqual([]);
      expect(bad.counterexample.expected).toBe("0n");
      expect(bad.counterexample.observed).toBe("1n");
      expect(bad.counterexample.lhs).toEqual({ term: "H.pick_red", value: "0n" });
      // Neither the root's module nor the nested dependency may leak its hash into the readback.
      expect(r.stdout).not.toContain(kernelHash);
      expect(r.stdout).not.toContain(depHash);
    }
  }, T);
});

describe("errors", () => {
  test("syntax error: clean located message, exit 2", async () => {
    const r = await run(path.join(FX, "syntax_error.bend"));
    expect(r.code).toBe(2);
    expect(r.stdout).toBe("");
    expect(r.stderr).toContain("lawcheck: cannot load");
    expect(r.stderr).toContain("syntax_error.bend:5:9");
    expect(r.stderr).not.toMatch(/\n\s+at /);
  }, T);

  test("module that does not type-check: exit 2", async () => {
    const r = await run(path.join(FX, "type_error.bend"));
    expect(r.code).toBe(2);
    expect(r.stderr).toContain("does not type-check");
    expect(r.stderr).toContain("Location: f");
  }, T);

  test("usage errors: exit 2", async () => {
    expect((await run()).code).toBe(2);
    expect((await run(path.join(FX, "correct.bend"), "--bogus")).code).toBe(2);
    expect((await run(path.join(FX, "nope.bend"))).code).toBe(2);
    expect((await run(path.join(FX, "correct.bend"), "--law", "nope")).code).toBe(2);
    expect((await run(path.join(FX, "correct.bend"), "--size", "x")).code).toBe(2);
  }, T);
});

describe("term rewriting", () => {
  test("substitutes whole identifiers only, never inside literals", () => {
    const env = new Map([["x", "1n"], ["xs", "[2n, 3n]"], ["A", "U32"], ["a", "&2"]]);
    const q = (id: string) => (id === "ins" ? "U.ins" : id);
    expect(rewrite(`{List.length(a, A, ins(x, xs)) == 1n+x : Nat}`, env, q)).toBe(`{List.length(&2, U32, U.ins(1n, ([2n, 3n]))) == 1n+1n : Nat}`);
    expect(rewrite(`f("x", 'x', xs0, Nat.x)`, env, q)).toBe(`f("x", 'x', xs0, Nat.x)`);
  });

  test("splits a printed goal and parses printed types", () => {
    expect(splitEquation("{[3n, 5n] == [6n, 1n] : List<&2, Nat>}")).toEqual({ lhs: "[3n, 5n]", rhs: "[6n, 1n]", type: "List<&2, Nat>" });
    expect(splitEquation("{Some{(1n, 2n)} == None{} : Maybe<&2, Pair(Nat, Nat)>}")?.rhs).toBe("None{}");
    expect(showTy(parseTy("Either<a, b, List<&2, U32>, m.T>")!)).toBe("Either<a, b, List<&2, U32>, m.T>");
    expect(parseTy("@_:A -> B")).toBeNull();
  });
});
