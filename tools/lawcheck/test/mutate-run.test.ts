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
    const rep = await mutate(path.join(FX, "mut_weak.bend"), { maxInstances: 40, seed: 1, size: 3 });
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
    const rep = await mutate(path.join(FX, "mut_strong.bend"), { maxInstances: 40, seed: 1, size: 3 });
    for (const name of ["app", "size"]) {
      expect(def(rep, name).mutants.filter((m: any) => m.status === "survived")).toEqual([]);
    }
  }, T);

  test("in-file mode mutates one def and kills at least one mutant", async () => {
    const rep = await mutate(path.join(FX, "correct.bend"), { def: "dbl" });
    expect(rep.defs.map((d: any) => d.name)).toEqual(["dbl"]);
    expect(rep.defs[0].mutants.some((m: any) => m.status === "killed")).toBe(true);
  }, T);
});
