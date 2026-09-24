// Tests for the bend-mathlib tools against committed fixtures (real compiler runs).
import { expect, test } from "bun:test";
import { join } from "node:path";

const dir = import.meta.dir;
const run = (script: string, ...args: string[]) => {
  const p = Bun.spawnSync([process.execPath, join(dir, script), ...args]);
  return { code: p.exitCode, out: new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr) };
};

test("check: the good fixture is green on the pinned compiler", () => {
  const r = run("check.ts", join(dir, "fixtures/good"));
  expect(r.out).toContain("1/1 modules green");
  expect(r.code).toBe(0);
});

test("twins: the good fixture's generated section is up to date", () => {
  expect(run("twins.ts", join(dir, "fixtures/good"), "--check").code).toBe(0);
});

test("lint: the good fixture is clean, including the erasure check", () => {
  const r = run("lint.ts", join(dir, "fixtures/good"), "--erasure");
  expect(r.out).toContain("0 finding(s)");
  expect(r.code).toBe(0);
});

test("lint: every planted violation in the bad fixture is reported", () => {
  const r = run("lint.ts", join(dir, "fixtures/bad"), "--erasure");
  expect(r.code).toBe(1);
  for (const needle of [
    "must be lowercase snake_case without dots",
    "has no '#' doc line",
    "exactly one claim line (found 2)",
    "predicate 'iszero' must not match",
    "type 'tree'",
    "binder 'y' of 'Nat.add_zero_x' can be erased",
  ]) expect(r.out).toContain(needle);
});
