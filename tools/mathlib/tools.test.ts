// Tests for the bend-mathlib tools against committed fixtures (real compiler runs).
import { expect, test } from "bun:test";
import { cpSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { baseNames, parseModule, packageModules } from "./lib.ts";

const dir = import.meta.dir;
const run = (script: string, ...args: string[]) => {
  const p = Bun.spawnSync([process.execPath, join(dir, script), ...args]);
  return { code: p.exitCode, out: new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr) };
};
const runWith = (env: Record<string, string>, script: string, ...args: string[]) => {
  const p = Bun.spawnSync([process.execPath, join(dir, script), ...args], { env: { ...process.env, ...env } });
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
  expect(rel).toEqual(["all.bend", "src/helper.bend", "src/inner.bend", "src/mod.bend"]);
});

test("lint reads a module in a subdirectory", () => {
  const r = run("lint.ts", subdir);
  expect(r.code).toBe(1);
  expect(r.out).toContain("src/mod.bend");
  expect(r.out).toContain("in 4 module(s)");
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

test("parseModule keeps a one-line def header as the physical line", () => {
  const m = parseModule("m.bend", "import Base\n\ndef f(a: Nat) -> Data:\n  {g(a) == True{} : Bool}\n");
  expect(m.defs[0].header).toBe("def f(a: Nat) -> Data:");
  expect(m.defs[0].body).toEqual(["  {g(a) == True{} : Bool}"]);
});

test("parseModule accumulates a multi-line def header and starts the body after it", () => {
  const m = parseModule("m.bend", "import Base\n\ndef f(\n  a: Nat\n) -> Data:\n  {g(a) == True{} : Bool}\n");
  expect(m.defs[0].header).toBe("def f(\n  a: Nat\n) -> Data:");
  expect(m.defs[0].body).toEqual(["  {g(a) == True{} : Bool}"]);
});

const multiline = join(dir, "fixtures/multiline");

test("lint flags a predicate whose -> Data is on a continuation line, and the one-line control", () => {
  const r = run("lint.ts", multiline);
  expect(r.code).toBe(1);
  expect(r.out).toContain("predicate 'multiline_pred' calls 'Frobnicate', which is not a Base function");
  expect(r.out).toContain("predicate 'single_pred' calls 'Frobnicate', which is not a Base function");
});

test("lock locks a predicate whose -> Data is on a continuation line, and the one-line control", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-multiline-"));
  cpSync(multiline, tmp, { recursive: true });
  const r = run("lock.ts", tmp, "--update");
  expect(r.code).toBe(0);
  const lock: Record<string, { kind: string }> = JSON.parse(readFileSync(join(tmp, "PUBLIC_API.lock"), "utf8"));
  expect(lock["pred.multiline_pred"]?.kind).toBe("predicate");
  expect(lock["pred.single_pred"]?.kind).toBe("predicate");
});

test("index keeps a subdir module's relative path in the generated import", () => {
  const r = run("index.ts", subdir, "fixture-package", "0.1.0.0", "--stdout");
  expect(r.out).toContain("import fixture-package@0.1.0.0/src/mod.bend as MMod");
  expect(r.out).toContain("import fixture-package@0.1.0.0/src/inner.bend as MInner");
});

test("lint --erasure checks a subdir module that imports a sibling", () => {
  const r = run("lint.ts", subdir, "--erasure");
  expect(r.out).toContain("binder 'y' of 'inner_id' can be erased");
});

test("baseNames lists the compiler's Base names", async () => {
  const b = await baseNames();
  expect(b.size).toBeGreaterThan(100);
  expect(b.has("Nat.is_le")).toBe(true);
});

test("lint fails cleanly when `bend base` is broken instead of trusting an empty Base set", () => {
  const r = runWith({ BEND_CLI: "/bin/false" }, "lint.ts", join(dir, "fixtures/good"));
  expect(r.code).not.toBe(0);
  expect(r.out).toMatch(/base' failed/);
  expect(r.out).not.toContain("0 finding(s)");
});

test("release fails cleanly for a missing absolute pkgdir (no mangled join, no EINVAL)", () => {
  const missing = join(tmpdir(), "bend-release-missing");
  const r = run("release.ts", missing, "some-package-name", "0.1.0.0");
  expect(r.code).toBe(1);
  expect(r.out).toContain(`package directory ${missing} does not exist`);
  expect(r.out).not.toContain("EINVAL");
});

test("release resolves an absolute existing pkgdir instead of mangling it", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-abs-"));
  writeFileSync(join(tmp, "m.bend"), "import Base\n");
  const r = runWith({ BEND_CLI: "/bin/false" }, "release.ts", tmp, "some-package-name", "0.1.0.0");
  expect(r.code).toBe(1);
  expect(r.out).not.toContain("does not exist");
  expect(r.out).toContain("FAIL check");
});

