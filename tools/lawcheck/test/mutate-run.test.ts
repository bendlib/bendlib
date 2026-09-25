// Real-bend mutation-runner tests: the laws are checked against every mutant of
// the target file's defs; nothing is mocked.

import { describe, expect, test } from "bun:test";
import * as path from "node:path";
import { mutate } from "../src/lawcheck.ts";

const FX = path.join(import.meta.dir, "fixtures");
const T = 240_000;
const def = (rep: any, name: string) => rep.defs.find((d: any) => d.name === name);

describe("mutate runner", () => {
  test("weak laws leave survivors; some mutants are invalid", async () => {
    const rep = await mutate(path.join(FX, "mut_weak.bend"), { jobs: 4, maxInstances: 5, seed: 1, size: 3 });
    const all = rep.defs.flatMap((d: any) => d.mutants);
    expect(all.some((m: any) => m.status === "survived")).toBe(true);
    expect(all.some((m: any) => m.status === "invalid")).toBe(true);
    // The bead's app arg-swap is rejected by Bend's termination checker (not a
    // decreasing self-call), so it is invalid, not survived; `size` still survives.
    const swap = def(rep, "app").mutants.find((m: any) => m.op === "arg-swap");
    expect(swap.status).toBe("invalid");
    expect(def(rep, "size").mutants.some((m: any) => m.status === "survived")).toBe(true);
  }, T);

  test("strong laws kill every mutant of both defs", async () => {
    const rep = await mutate(path.join(FX, "mut_strong.bend"), { jobs: 4, maxInstances: 5, seed: 1, size: 3 });
    for (const name of ["app", "size"]) {
      expect(def(rep, name).mutants.filter((m: any) => m.status === "survived")).toEqual([]);
    }
  }, T);

  test("in-file mode mutates one def and kills at least one mutant", async () => {
    const rep = await mutate(path.join(FX, "correct.bend"), { def: "dbl", jobs: 4, maxInstances: 5 });
    expect(rep.defs.map((d: any) => d.name)).toEqual(["dbl"]);
    expect(rep.defs[0].mutants.some((m: any) => m.status === "killed")).toBe(true);
  }, T);

  // first_of calls the non-self helper pick; swapping pick's arguments still
  // type-checks, and the diagonal law first_of(a, a) = a does not catch it.
  test("a non-self arg-swap can genuinely survive", async () => {
    const rep = await mutate(path.join(FX, "mut_argswap.bend"), { jobs: 4, maxInstances: 5, seed: 1, size: 3 });
    const swaps = def(rep, "first_of").mutants.filter((m: any) => m.op === "arg-swap");
    expect(swaps).toHaveLength(1);
    expect(swaps[0].def).toBe("first_of");
    expect(swaps[0].status).toBe("survived");
  }, T);

  test("proofs in the laws file are stripped in impl mode, so mutants are classified by the laws", async () => {
    const rep = await mutate(path.join(FX, "mut_proved", "laws.bend"), {
      impl: path.join(FX, "mut_proved", "lib.bend"), jobs: 4, maxInstances: 20, seed: 1, size: 3,
    });
    const ms = rep.defs.flatMap((d: any) => d.mutants);
    expect(ms.filter((m: any) => m.status === "killed").length).toBeGreaterThanOrEqual(4);
    expect(ms.some((m: any) => m.status === "survived")).toBe(false);
    expect(ms.some((m: any) => m.status === "invalid")).toBe(true);
  }, T);

  test("no law evaluated on the base is a usage error, never all-survivors", async () => {
    await expect(mutate(path.join(FX, "mut_allskip.bend"), { jobs: 4, maxInstances: 5 })).rejects.toThrow(/no law was evaluated on the unmutated code/);
    await expect(mutate(path.join(FX, "mut_nolaws.bend"), { jobs: 4, maxInstances: 5 })).rejects.toThrow(/no law was evaluated on the unmutated code/);
  }, T);

  test("an invalid mutant's detail keeps the checker's expected/observed lines", async () => {
    const rep = await mutate(path.join(FX, "mut_weak.bend"), { jobs: 4, maxInstances: 5, seed: 1, size: 3 });
    const inv = rep.defs.flatMap((d: any) => d.mutants).filter((m: any) => m.status === "invalid");
    expect(inv.length).toBeGreaterThan(0);
    expect(inv.some((m: any) => (m.detail ?? "").includes("- expected"))).toBe(true);
    expect(inv.every((m: any) => m.detail !== "Error:")).toBe(true);
  }, T);
});
