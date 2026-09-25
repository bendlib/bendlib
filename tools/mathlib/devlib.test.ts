// Tests for devlib against temp package trees (real compiler runs for the resolution test).
import { expect, test } from "bun:test";
import { mkdirSync, mkdtempSync, readlinkSync, readdirSync, realpathSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { buildDevlib, checkDevlib, hashPins } from "./devlib.ts";
import { hubHash, packageFiles } from "./hash.ts";
import { BEND } from "./lib.ts";

const dir = import.meta.dir;
const run = (script: string, ...args: string[]) => {
  const p = Bun.spawnSync([process.execPath, join(dir, script), ...args], { env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
  return { code: p.exitCode, out: new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr) };
};

const KERNEL_LIST = "import Base\n\ndef idw(x: Nat) -> Nat:\n  x\n";
const KERNEL_ALL = "import Base\nimport ./list.bend as KList\n";

function mkKernel(root: string, list = KERNEL_LIST): string {
  const d = join(root, "packages", "kernel");
  mkdirSync(d, { recursive: true });
  writeFileSync(join(d, "list.bend"), list);
  writeFileSync(join(d, "all.bend"), KERNEL_ALL);
  return hubHash(packageFiles(join(d, "all.bend")));
}

function mkConsumer(root: string, pin: string): string {
  const d = join(root, "packages", "consumer");
  mkdirSync(d, { recursive: true });
  writeFileSync(join(d, "all.bend"), `import Base\nimport ${pin}/list.bend as K\n\ndef u() -> Nat:\n  K.idw(0n)\n`);
  return d;
}

test("devlib symlinks every package at its real content hash and rebuilds from empty", () => {
  const root = mkdtempSync(join(tmpdir(), "bend-devlib-build-"));
  const hk = mkKernel(root);
  mkConsumer(root, hk);
  const { dir: devlib, packages } = buildDevlib(root);
  expect(packages.map((p) => p.name).sort()).toEqual(["consumer", "kernel"]);
  expect(readlinkSync(join(devlib, hk))).toBe(realpathSync(join(root, "packages", "kernel")));
  // a second build starts from empty, not a pile of old entries
  mkKernel(root, KERNEL_LIST + "\ndef idw2(y: Nat) -> Nat:\n  y\n");
  const again = buildDevlib(root);
  expect(readdirSync(devlib).length).toBe(again.packages.length);
});

test("devlib run resolves 0x…/list.bend for an unpublished local package (real compiler)", () => {
  const root = mkdtempSync(join(tmpdir(), "bend-devlib-run-"));
  const hk = mkKernel(root);
  const pk = mkConsumer(root, hk);
  const r = run("devlib.ts", "--root", root, "run", "--", BEND, join(pk, "all.bend"), "--check-only");
  expect(r.out).toContain("All terms check.");
  expect(r.code).toBe(0);
});

test("devlib run drives check.ts over the consumer package (acceptance form)", () => {
  const root = mkdtempSync(join(tmpdir(), "bend-devlib-check-"));
  const hk = mkKernel(root);
  const pk = mkConsumer(root, hk);
  const r = run("devlib.ts", "--root", root, "run", "--", process.execPath, join(dir, "check.ts"), pk, "--max-seconds", "30");
  expect(r.out).toContain("1/1 modules green");
  expect(r.code).toBe(0);
});

test("devlib --check is green for a matching pin, then names the stale hash after an edit (planted negative)", () => {
  const root = mkdtempSync(join(tmpdir(), "bend-devlib-stale-"));
  const hk = mkKernel(root);
  mkConsumer(root, hk);
  expect(checkDevlib(root).stale).toEqual([]);
  expect(run("devlib.ts", "--root", root, "--check").code).toBe(0);

  mkKernel(root, KERNEL_LIST + "\ndef idw2(y: Nat) -> Nat:\n  y\n");
  const now = checkDevlib(root).stale;
  expect(now.length).toBe(1);
  expect(now[0].hash).toBe(hk);
  expect(now[0].owner).toBe("kernel");
  expect(now[0].expected).not.toBe(hk);
  const r = run("devlib.ts", "--root", root, "--check");
  expect(r.code).toBe(1);
  expect(r.out).toContain(`${hk}/list.bend is stale`);
  expect(r.out).toContain(`now hashes to ${now[0].expected}`);
});

test("devlib refuses a symlinked .devlib and leaves the target untouched (write-outside guard)", () => {
  const root = mkdtempSync(join(tmpdir(), "bend-devlib-guard-"));
  mkKernel(root);
  const outside = mkdtempSync(join(tmpdir(), "bend-devlib-outside-"));
  symlinkSync(outside, join(root, ".devlib"), "dir");
  expect(() => buildDevlib(root)).toThrow(/symlinked \.devlib/);
  expect(readdirSync(outside)).toEqual([]);
  const r = run("devlib.ts", "--root", root, "--check");
  expect(r.code).toBe(2);
  expect(r.out).toContain("refusing to rebuild a symlinked .devlib");
});

test("devlib --check flags a 0x… import that is not 32 hex (planted negative)", () => {
  const root = mkdtempSync(join(tmpdir(), "bend-devlib-hex-"));
  const hk = mkKernel(root);
  mkConsumer(root, "0x123");
  const stale = checkDevlib(root).stale;
  expect(stale.length).toBe(1);
  expect(stale[0].owner).toBe("");
  const r = run("devlib.ts", "--root", root, "--check");
  expect(r.code).toBe(1);
  expect(r.out).toContain("0x123 is not 32 hex");
  expect(hk).toBeTruthy();
});

test("devlib rejects two local packages with identical content (hash collision is named)", () => {
  const root = mkdtempSync(join(tmpdir(), "bend-devlib-dup-"));
  mkKernel(root);
  const twin = join(root, "packages", "twin");
  mkdirSync(twin, { recursive: true });
  writeFileSync(join(twin, "list.bend"), KERNEL_LIST);
  writeFileSync(join(twin, "all.bend"), KERNEL_ALL);
  expect(() => buildDevlib(root)).toThrow(/content hash 0x[0-9a-f]{32} is shared by kernel and twin/);
});

test("hashPins reads imports and ignores a commented-out pin (planted negative)", () => {
  const root = mkdtempSync(join(tmpdir(), "bend-devlib-pins-"));
  const d = join(root, "packages", "p");
  mkdirSync(d, { recursive: true });
  writeFileSync(join(d, "all.bend"), "import Base\n# import 0xdeadbeefdeadbeefdeadbeefdeadbeef/list.bend as Old\nimport 0x0102030405060708090a0b0c0d0e0f10/list.bend as K\n");
  const pins = hashPins(d);
  expect(pins.map((p) => p.hash)).toEqual(["0x0102030405060708090a0b0c0d0e0f10"]);
});

test("devlib --check does not flag a hash whose path is in no local package (hub pin)", () => {
  const root = mkdtempSync(join(tmpdir(), "bend-devlib-hub-"));
  const hk = mkKernel(root);
  const d = join(root, "packages", "consumer");
  mkdirSync(d, { recursive: true });
  writeFileSync(join(d, "all.bend"), "import Base\nimport 0xffffffffffffffffffffffffffffffff/hub.bend as K\n");
  expect(checkDevlib(root).stale).toEqual([]);
  expect(run("devlib.ts", "--root", root, "--check").code).toBe(0);
  expect(hk).toBeTruthy();
});

test("devlib CLI is a typed usage error, exit 2, no stack", () => {
  const root = mkdtempSync(join(tmpdir(), "bend-devlib-usage-"));
  mkKernel(root);
  for (const args of [[], ["run"], ["run", "--"], ["--root", join(root, "nope"), "--check"], ["--root"]]) {
    const r = run("devlib.ts", ...args);
    expect(r.code).toBe(2);
    expect(r.out).toMatch(/need `run -- <cmd…>` or `--check`|--root needs a directory|no such directory|not a directory/);
    expect(r.out).not.toMatch(/\n\s+at /);
  }
});
