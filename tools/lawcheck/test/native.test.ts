// Engine N (`--native`): real bend on the fixtures, plus an injected-result logic test.

import { describe, expect, test } from "bun:test";
import * as path from "node:path";
import { nativeDisagreements } from "../src/lawcheck.ts";

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
    expect(rep.laws.find((l: any) => l.name === "le_dbl").native).toBeUndefined();
  }, T);

  test("both engines agree on a false law's counterexamples", async () => {
    const r = await run(path.join(FX, "buggy.bend"), "--native", "--jobs", "4", "--max-instances", "10");
    expect(r.code).toBe(1);
    expect(r.stdout).not.toContain("DISAGREE");
    expect(r.stdout).toContain("native");
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
});
