// Tests for the bend-mathlib tools against committed fixtures (real compiler runs).
import { expect, test } from "bun:test";
import { createHash } from "node:crypto";
import { cpSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { hubHash, packageFiles } from "./hash.ts";
import { baseNames, BEND, parseModule, packageModules } from "./lib.ts";
import { headerVersionError, regenerateIndex } from "./release.ts";

const dir = import.meta.dir;
const run = (script: string, ...args: string[]) => {
  const p = Bun.spawnSync([process.execPath, join(dir, script), ...args]);
  return { code: p.exitCode, out: new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr) };
};
const runWith = (env: Record<string, string>, script: string, ...args: string[]) => {
  const p = Bun.spawnSync([process.execPath, join(dir, script), ...args], { env: { ...process.env, ...env } });
  return { code: p.exitCode, out: new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr) };
};
const STACK = /\n\s+at /;

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
  expect(r.code).toBe(2);
  expect(r.out).toMatch(/base' failed/);
  expect(r.out).not.toContain("0 finding(s)");
  expect(r.out).not.toMatch(STACK);
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

test("release: a climbing package is a typed usage error, exit 2, no stack", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-climb-"));
  mkdirSync(join(tmp, "pkg"));
  writeFileSync(join(tmp, "other.bend"), "import Base\n\ndef other() -> U32:\n  7\n");
  writeFileSync(join(tmp, "pkg", "all.bend"), "import Base\nimport ../other.bend as Other\n\ndef f() -> U32:\n  Other.other()\n");
  const r = run("release.ts", join(tmp, "pkg"), "some-package-name", "0.1.0.0");
  expect(r.code).toBe(2);
  expect(r.out).toContain("is outside the entry directory");
  expect(r.out).toContain("usage: release.ts <pkgdir>");
  expect(r.out).not.toMatch(STACK);
});

test("release: headerVersionError flags a stale all.bend header, accepts the target (planted pair)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-header-"));
  const entry = join(tmp, "all.bend");
  writeFileSync(entry, "# fixture-package: import fixture-package@0.1.0.0/bools.bend.\nimport Base\n");
  const err = headerVersionError(tmp, "fixture-package", "0.2.0.0");
  expect(err).toContain("names fixture-package@0.1.0.0");
  expect(err).toContain("release target is fixture-package@0.2.0.0");
  writeFileSync(entry, "# fixture-package: import fixture-package@0.2.0.0/bools.bend.\nimport Base\n");
  expect(headerVersionError(tmp, "fixture-package", "0.2.0.0")).toBeNull();
});

test("release: headerVersionError reads only the first line and only this package's version (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-header-neg-"));
  writeFileSync(join(tmp, "all.bend"), "# fixture-package: a stub.\n# import fixture-package@0.1.0.0/bools.bend in the second line.\nimport Base\n");
  expect(headerVersionError(tmp, "fixture-package", "0.2.0.0")).toBeNull();
  writeFileSync(join(tmp, "all.bend"), "# fixture-package: depends on other-package@0.1.0.0.\nimport Base\n");
  expect(headerVersionError(tmp, "fixture-package", "0.2.0.0")).toBeNull();
  writeFileSync(join(tmp, "all.bend"), "# my-fixture-package: import my-fixture-package@0.1.0.0/bools.bend.\nimport Base\n");
  expect(headerVersionError(tmp, "fixture-package", "0.2.0.0")).toBeNull();
});

test("release: the dry run fails on a stale header before any gate or hash (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-gate-"));
  mkdirSync(join(tmp, "pkg"));
  writeFileSync(join(tmp, "pkg", "all.bend"), "# fixture-package: import fixture-package@0.1.0.0/bools.bend.\nimport Base\n");
  const r = run("release.ts", join(tmp, "pkg"), "fixture-package", "0.2.0.0");
  expect(r.code).toBe(1);
  expect(r.out).toContain("names fixture-package@0.1.0.0");
  expect(r.out).not.toContain("FAIL check");
  expect(r.out).not.toContain("expected hash");
});

test("release: a correct header passes the gate and the run reaches the check gate", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-release-gate-ok-"));
  mkdirSync(join(tmp, "pkg"));
  writeFileSync(join(tmp, "pkg", "all.bend"), "# fixture-package: import fixture-package@0.2.0.0/bools.bend.\nimport Base\n");
  const r = runWith({ BEND_CLI: "/bin/false" }, "release.ts", join(tmp, "pkg"), "fixture-package", "0.2.0.0");
  expect(r.code).toBe(1);
  expect(r.out).not.toContain("release target is");
  expect(r.out).toContain("FAIL check");
});

test("release: lock --freeze leaves README stale until regenerateIndex runs (the post-freeze path)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-index-regen-"));
  cpSync(join(dir, "fixtures/index"), tmp, { recursive: true });
  expect(run("index.ts", tmp, "fixture-package", "0.1.0.0").code).toBe(0);
  expect(run("index.ts", tmp, "fixture-package", "0.2.0.0", "--check").code).toBe(1);
  expect(run("lock.ts", tmp, "--freeze", "0.2.0.0").code).toBe(0);
  expect(run("index.ts", tmp, "fixture-package", "0.2.0.0", "--check").code).toBe(1);
  expect(regenerateIndex(tmp, "fixture-package", "0.2.0.0").code).toBe(0);
  expect(readFileSync(join(tmp, "README.md"), "utf8")).toContain("fixture-package@0.2.0.0");
  expect(run("index.ts", tmp, "fixture-package", "0.2.0.0", "--check").code).toBe(0);
});

test("a missing or non-directory package path is a typed usage error, exit 2, no stack", () => {
  const parent = mkdtempSync(join(tmpdir(), "bend-missing-"));
  const missing = join(parent, "nope");
  const file = join(dir, "fixtures/good/list.bend");
  const cases: [string, string[]][] = [
    ["check.ts", [missing]],
    ["check.ts", [file]],
    ["lint.ts", [missing]],
    ["twins.ts", [missing, "--check"]],
    ["lock.ts", [missing, "--check"]],
    ["index.ts", [missing, "fixture-package", "0.1.0.0", "--stdout"]],
  ];
  for (const [script, args] of cases) {
    const r = run(script, ...args);
    expect(r.code).toBe(2);
    expect(r.out).toMatch(/no such package directory|not a directory/);
    expect(r.out).not.toMatch(STACK);
  }
});

test("check: --max-seconds must be a positive integer", () => {
  const r = run("check.ts", join(dir, "fixtures/good"), "--max-seconds", "x");
  expect(r.code).toBe(2);
  expect(r.out).toContain("--max-seconds needs a positive integer");
  expect(r.out).not.toMatch(STACK);
});

test("index: the version must be a.b.c.d", () => {
  const r = run("index.ts", join(dir, "fixtures/index"), "fixture-package", "notaversion", "--stdout");
  expect(r.code).toBe(2);
  expect(r.out).toContain("version must be a.b.c.d");
  expect(r.out).not.toMatch(STACK);
});

test("twins: a byte-empty module is up to date, not perpetually stale", () => {
  const empty = join(dir, "fixtures/empty");
  const r = run("twins.ts", empty, "--check");
  expect(r.code).toBe(0);
  expect(r.out).toContain("twins up to date");
  expect(readFileSync(join(empty, "empty.bend"), "utf8")).toBe("");
});

const foreign = join(dir, "fixtures/foreign");
const refHash = (rec: Record<string, string>) =>
  "0x" + createHash("sha256").update(Object.keys(rec).sort()
    .map((p) => createHash("sha256").update(rec[p]).digest("hex") + " " + p + "\n").join(""))
    .digest("hex").slice(0, 32);
const foreignRecord = () => ({
  "main.bend": readFileSync(join(foreign, "main.bend"), "utf8"),
  "shout.c": readFileSync(join(foreign, "shout.c"), "utf8"),
  "sub/helper.js": readFileSync(join(foreign, "sub/helper.js"), "utf8"),
  "sub/mod.bend": readFileSync(join(foreign, "sub/mod.bend"), "utf8"),
  "LICENSE": readFileSync(join(foreign, "LICENSE"), "utf8"),
});

test("the foreign fixture is genuinely foreign to the pinned compiler", () => {
  const p = Bun.spawnSync([BEND, join(foreign, "main.bend"), "--check-only"], { env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
  expect(new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr)).toMatch(/defs? rely on unsafe or foreign code/);
});

test("packageFiles collects a def's foreign .c and .js imports at their paths", () => {
  expect(Object.keys(packageFiles(join(foreign, "main.bend"))).sort())
    .toEqual(["LICENSE", "main.bend", "shout.c", "sub/helper.js", "sub/mod.bend"]);
});

test("hash: the CLI hash covers the foreign files, computed over the exact manifest", () => {
  const r = run("hash.ts", join(foreign, "main.bend"));
  expect(r.code).toBe(0);
  expect(r.out).toContain("shout.c");
  expect(r.out).toContain("sub/helper.js");
  expect(r.out).toContain(refHash(foreignRecord()));
});

test("packageFiles: a package with no foreign files is byte-identical to before (planted negative)", () => {
  expect(hubHash(packageFiles(join(subdir, "all.bend")))).toBe("0xdfe38237eb381cd99fcdc0bc22bf893b");
  expect(hubHash(packageFiles(join(dir, "fixtures/good/list.bend")))).toBe("0x872818a5c5997957f8e2324698c1296e");
});

test("packageFiles: an indented `import` inside a comment is not a foreign file (planted negative)", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-hash-comment-"));
  writeFileSync(join(tmp, "main.bend"), 'import Base\n\ndef f(x: U32) -> IO(U32):\n  # import "./ghost.c" is only a note\n  x\n');
  expect(Object.keys(packageFiles(join(tmp, "main.bend")))).toEqual(["main.bend"]);
});

test("hash: a missing, non-file or climbing entry is a typed usage error, exit 2, no stack", () => {
  const tmp = mkdtempSync(join(tmpdir(), "bend-hash-bad-"));
  const climb = join(tmp, "pkg", "sub", "main.bend");
  mkdirSync(join(tmp, "pkg", "sub"), { recursive: true });
  writeFileSync(join(tmp, "pkg", "other.bend"), "import Base\n\ndef other() -> Nat:\n  7\n");
  writeFileSync(climb, "import Base\nimport ../other.bend as Other\n\ndef f() -> Nat:\n  Other.other()\n");
  const cases: [string, string][] = [
    ["not a .bend file", join(tmp, "nope.bend")],
    ["not a .bend file", tmp],
    ["is outside the entry directory", climb],
  ];
  for (const [needle, arg] of cases) {
    const r = run("hash.ts", arg);
    expect(r.code).toBe(2);
    expect(r.out).toContain(needle);
    expect(r.out).toContain("usage: bun tools/mathlib/hash.ts");
    expect(r.out).not.toMatch(STACK);
  }
});

