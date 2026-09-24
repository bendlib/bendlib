// Regression: the checker's batch size is fixed and independent of --jobs, so
// `checkerRuns` must not grow when more cores are offered (the old
// `min(50, items/jobs)` shrank batches as jobs grew and multiplied spawns).
import { expect, test } from "bun:test";
import * as path from "node:path";
import { lawcheck } from "../src/lawcheck.ts";

const FX = path.join(import.meta.dir, "fixtures");
const T = 180_000;
const runsAt = (fixture: string, jobs: number) =>
  lawcheck(path.join(FX, fixture), { maxInstances: 100, jobs, seed: 1, size: 3, shrink: false });

test("checkerRuns is decoupled from --jobs and stays low", async () => {
  const base = await runsAt("correct.bend", 4);
  const many = await runsAt("correct.bend", 16);
  expect(many.checkerRuns).toBeLessThanOrEqual(base.checkerRuns);
  expect(base.checkerRuns).toBeLessThanOrEqual(80);
}, T);

test("a false law is still caught and counted (no hidden counterexample)", async () => {
  const base = await runsAt("buggy.bend", 4);
  const many = await runsAt("buggy.bend", 16);
  expect(base.laws.some((l) => l.status === "fail")).toBe(true);
  expect(many.laws.some((l) => l.status === "fail")).toBe(true);
  expect(many.checkerRuns).toBeLessThanOrEqual(base.checkerRuns);
}, T);
