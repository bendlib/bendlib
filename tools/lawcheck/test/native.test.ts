// Engine N (`--native`): real bend on the fixtures, plus injected-result logic tests.

import { describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { nativeDisagreements, nativeRepro } from "../src/lawcheck.ts";
import { bendBin } from "../src/checker.ts";

const CLI = path.join(import.meta.dir, "..", "cli.ts");
const FX = path.join(import.meta.dir, "fixtures");
const T = 240_000;

async function run(...args: string[]) {
  const p = Bun.spawn([process.execPath, CLI, ...args], { stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
  return { code: await p.exited, stdout, stderr };
}

describe("engine N (--native)", () => {
  test("both engines agree on the correct fixture", async () => {
    const r = await run(path.join(FX, "correct.bend"), "--native", "--jobs", "4", "--max-instances", "10", "--json");
    expect(r.code).toBe(0);
    expect(r.stderr).toBe("");
    const rep = JSON.parse(r.stdout);
    const dbl = rep.laws.find((l: any) => l.name === "dbl_add");
    expect(dbl.native.checked).toBe(10);
    expect(dbl.native.disagreements).toEqual([]);
    expect(rep.laws.find((l: any) => l.name === "ins_sorted").native.checked).toBeGreaterThan(0);
    // le_dbl is a predicate: not an equation, so native reports a skip, not silence.
    expect(rep.laws.find((l: any) => l.name === "le_dbl").native.skip).toBeDefined();
  }, T);

  test("list equations are compared with the emitted recursive equality", async () => {
    const r = await run(path.join(FX, "list_native.bend"), "--native", "--jobs", "4", "--max-instances", "6", "--json");
    expect(r.code).toBe(1);
    const rep = JSON.parse(r.stdout);
    const refl = rep.laws.find((l: any) => l.name === "refl");
    expect(refl.status).toBe("pass");
    expect(refl.native.checked).toBeGreaterThan(0);
    expect(refl.native.disagreements).toEqual([]);
    const allNil = rep.laws.find((l: any) => l.name === "all_nil");
    expect(allNil.status).toBe("fail");
    expect(allNil.native.checked).toBeGreaterThan(0);
    expect(allNil.native.disagreements).toEqual([]);
  }, T);

  test("both engines agree on a false law's counterexamples", async () => {
    const r = await run(path.join(FX, "buggy.bend"), "--native", "--jobs", "4", "--max-instances", "10");
    expect(r.code).toBe(1);
    expect(r.stdout).not.toContain("DISAGREE");
    expect(r.stdout).toContain("native");
  }, T);

  test("a harness that cannot build is reported as a skip, not silence", async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-native-skip-"));
    fs.writeFileSync(path.join(dir, "dep.bend"), "import Base\n\nlaw open_dep:\n  for n: Nat\n  {n == n : Nat}\n");
    fs.writeFileSync(path.join(dir, "root.bend"), "import Base\nimport ./dep.bend as D\n\nlaw uses:\n  for n: Nat\n  {n == n : Nat}\n");
    const r = await run(path.join(dir, "root.bend"), "--native", "--jobs", "4", "--max-instances", "4", "--json");
    const rep = JSON.parse(r.stdout);
    const l = rep.laws.find((x: any) => x.name === "uses");
    expect(l.native.skip).toContain("build failed");
  }, T);

  // No engine difference is known to reproduce on bend 2.0.27 (the #1026 `Bool.or`
  // construct agrees natively), so the disagreement path is tested by injection.
  test("INJECTED: the disagreement comparison flags mismatches (logic only)", () => {
    expect(nativeDisagreements([{ r: "pass" }], [true])).toEqual([]);
    expect(nativeDisagreements([{ r: "pass" }], [false])).toEqual([0]);
    expect(nativeDisagreements([{ r: "open" }], [true])).toEqual([]);
    expect(nativeDisagreements([{ r: "open" }], [false])).toEqual([0]);
    expect(nativeDisagreements([{ r: "fail", expected: "1n", observed: "2n" }], [false])).toEqual([]);
    expect(nativeDisagreements([{ r: "fail", expected: "1n", observed: "2n" }], [true])).toEqual([0]);
    expect(nativeDisagreements([undefined, { r: "pass" }], [true, true])).toEqual([]);
    expect(nativeDisagreements([{ r: "pass" }, { r: "pass" }], [true, false])).toEqual([1]);
  });

  test("INJECTED: the repro writer emits a runnable harness for a flagged disagreement", async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-repro-"));
    // The injected mismatch is what nativeCheck turns into a repro file.
    expect(nativeDisagreements([{ r: "pass" }], [false])).toEqual([0]);
    const file = path.join(dir, "repro_0.bend");
    nativeRepro("import Base\n\n", "    IO.print(U32.show(Bool.to_u32(Nat.is_eq(1n, 1n))))", file);
    expect(fs.existsSync(file)).toBe(true);
    const bin = path.join(dir, "repro_0");
    const build = Bun.spawn([bendBin(), file, "-o", bin], { stdout: "pipe", stderr: "pipe" });
    expect(await build.exited).toBe(0);
    const out = Bun.spawn([bin], { stdout: "pipe", stderr: "pipe" });
    expect((await new Response(out.stdout).text()).trim()).toBe("1");
    expect(await out.exited).toBe(0);
  }, T);
});
