// Input robustness: directory targets, whitespace paths, and zero mutable defs.

import { describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

const CLI = path.join(import.meta.dir, "..", "cli.ts");
const FX = path.join(import.meta.dir, "fixtures");
const T = 240_000;

async function run(...args: string[]) {
  const p = Bun.spawn([process.execPath, CLI, ...args], { stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
  return { code: await p.exited, stdout, stderr };
}

describe("input robustness", () => {
  test("a directory target is a typed load error, never a raw stack", async () => {
    for (const args of [[], ["mutate"]]) {
      const r = await run(...args, FX, "--jobs", "4");
      expect(r.code).toBe(2);
      expect(r.stderr).toContain("cannot load");
      expect(r.stderr).toContain("EISDIR");
      expect(r.stderr).not.toMatch(/\n\s+at /);
    }
  }, T);

  test("a path with a space checks the laws", async () => {
    const r = await run(path.join(FX, "space name.bend"), "--jobs", "4", "--max-instances", "10");
    expect(r.code).toBe(0);
    expect(r.stdout).toContain("1 laws: 1 ✓ · 0 ✗ · 0 ~ · 0 !");
  }, T);

  test("a symlink to a space path checks the laws", async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lc-robust-"));
    const link = path.join(dir, "link.bend");
    fs.symlinkSync(path.join(FX, "space name.bend"), link);
    const r = await run(link, "--jobs", "4", "--max-instances", "10");
    expect(r.code).toBe(0);
    expect(r.stdout).toContain("1 laws: 1 ✓ · 0 ✗ · 0 ~ · 0 !");
  }, T);

  test("a path with a newline checks the laws", async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lc-robust-"));
    const file = path.join(dir, "line\nbreak.bend");
    fs.writeFileSync(file, "import Base\n\nlaw t:\n  for n: Nat\n  {Nat.add(n, 0n) == n : Nat}\n");
    const r = await run(file, "--jobs", "4", "--max-instances", "10");
    expect(r.code).toBe(0);
    expect(r.stdout).toContain("1 laws: 1 ✓ · 0 ✗ · 0 ~ · 0 !");
  }, T);

  test("mutate on a file with no mutable defs says so", async () => {
    const r = await run("mutate", path.join(FX, "empty.bend"), "--jobs", "4");
    expect(r.code).toBe(2);
    expect(r.stderr).toContain("no mutable defs");
    expect(r.stdout).not.toContain("survivor");
  }, T);
});
