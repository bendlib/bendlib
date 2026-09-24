// Every CLI test runs the real bend compiler on the fixtures; nothing is mocked.

import { describe, expect, test } from "bun:test";
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

describe("correct implementation", () => {
  test("all four laws pass, exit 0", async () => {
    const { code, report } = await json(path.join(FX, "correct.bend"));
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
  test("template binder is skipped, not a crash", async () => {
    const { code, report } = await json(path.join(FX, "template.bend"));
    expect(code).toBe(0);
    expect(law(report, "twice_id")).toMatchObject({ status: "skip", reason: "template binder ~f (v0.2)" });
    expect(law(report, "add_zero").status).toBe("pass");
  }, T);

  test("predicates, refutations, premises, type parameters, unsupported binders", async () => {
    const { code, report } = await json(path.join(FX, "kinds.bend"));
    expect(code).toBe(1);
    const st = Object.fromEntries(report.laws.map((l: any) => [l.name, l.status]));
    expect(st).toEqual({
      le_half: "pass", half_le_bad: "fail", p_holds: "skip", lt_irrefl: "pass", add_ne_bad: "fail", le_trans: "pass",
      append_nil_r: "pass", reverse_id_bad: "fail", pair_swap: "pass", where_law: "skip", fn_binder: "skip", float_law: "skip",
    });
    expect(binds(law(report, "half_le_bad"))).toEqual({ n: "1n" });
    expect(law(report, "half_le_bad").counterexample.goal).toBe("{False{} == True{} : Bool}");
    expect(law(report, "p_holds").reason).toMatch(/^not decidable by evaluation/);
    expect(binds(law(report, "add_ne_bad"))).toEqual({ a: "0n", b: "0n" });
    expect(law(report, "lt_irrefl").premise.satisfied).toBe(0);
    const rev = law(report, "reverse_id_bad");
    expect(rev.counterexample.types).toEqual([{ name: "A", value: "U32" }]);
    expect(binds(rev)).toEqual({ xs: "[0, 1]" });
    expect(law(report, "where_law").reason).toMatch(/where/);
    expect(law(report, "fn_binder").reason).toMatch(/function-typed binder f/);
    expect(law(report, "float_law").reason).toMatch(/F32/);
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
