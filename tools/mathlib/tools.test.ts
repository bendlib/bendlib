// Tests for the bend-mathlib tools against committed fixtures (real compiler runs).
import { expect, test } from "bun:test";
import { cpSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { packageModules } from "./lib.ts";

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

test("index: the since column marks published and unpublished fixture lemmas", () => {
  const r = run("index.ts", join(dir, "fixtures/index"), "fixture-package", "0.1.0.0", "--stdout");
  expect(r.code).toBe(0);
  const rows = r.out.split("\n");
  expect(rows.find((l) => l.startsWith("| `not_not(b)` |"))?.endsWith("| 0.1.0.0 |")).toBe(true);
  expect(rows.find((l) => l.startsWith("| `and_comm(a, b)` |"))?.endsWith("| next |")).toBe(true);
  expect(r.out).toContain("Rows marked `next` are proved in this repository but not yet published: the import lines above do not contain them yet.");
});

test("index: no 'next' rows or note when every lock entry is published", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-index-"));
  cpSync(join(dir, "fixtures/index"), tmp, { recursive: true });
  const lockPath = join(tmp, "PUBLIC_API.lock");
  const lock: Record<string, { since: string | null }> = JSON.parse(readFileSync(lockPath, "utf8"));
  for (const e of Object.values(lock)) e.since = "0.1.0.0";
  writeFileSync(lockPath, JSON.stringify(lock, null, 2) + "\n");
  const r = run("index.ts", tmp, "fixture-package", "0.1.0.0", "--stdout");
  expect(r.code).toBe(0);
  expect(r.out).not.toContain("Rows marked");
  expect(r.out).not.toContain("| next |");
});

const subdir = join(dir, "fixtures/subdir");

test("packageModules recurses into subdirectories", () => {
  const rel = packageModules(subdir).map((p) => p.slice(subdir.length + 1));
  expect(rel).toEqual(["all.bend", "src/mod.bend"]);
});

test("lint reads a module in a subdirectory", () => {
  const r = run("lint.ts", subdir);
  expect(r.code).toBe(1);
  expect(r.out).toContain("src/mod.bend");
  expect(r.out).toContain("in 2 module(s)");
});

test("lock reads a module in a subdirectory", () => {
  const r = run("lock.ts", subdir, "--check");
  expect(r.code).toBe(1);
  expect(r.out).toContain("mod.add_ident");
});

test("index reads a module in a subdirectory", () => {
  const r = run("index.ts", subdir, "fixture-package", "0.1.0.0", "--stdout");
  expect(r.code).toBe(0);
  expect(r.out).toContain("## mod");
  expect(r.out).toContain("add_ident");
});

