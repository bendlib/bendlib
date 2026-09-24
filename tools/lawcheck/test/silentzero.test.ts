// A checker-rejected target must fail loudly: never `0 laws` exit 0, never `survived`.

import { describe, expect, test } from "bun:test";
import * as path from "node:path";

const CLI = path.join(import.meta.dir, "..", "cli.ts");
const FX = path.join(import.meta.dir, "fixtures");
const T = 240_000;

async function run(...args: string[]) {
  const p = Bun.spawn([process.execPath, CLI, ...args], { stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
  return { code: await p.exited, stdout, stderr };
}

describe("no silent zero-law success", () => {
  test("a checker-rejected file with no laws exits 2 with the checker error", async () => {
    const r = await run(path.join(FX, "unclosed.bend"), "--jobs", "4", "--max-instances", "10");
    expect(r.code).toBe(2);
    expect(r.stdout).toBe("");
    expect(r.stderr).toContain("does not type-check");
    expect(r.stderr).toContain("cases for Succ");
  }, T);

  test("a valid file with laws is unchanged", async () => {
    const r = await run(path.join(FX, "correct.bend"), "--jobs", "4", "--max-instances", "10");
    expect(r.code).toBe(0);
    expect(r.stdout).toContain("4 laws: 4 ✓ · 0 ✗ · 0 ~ · 0 !");
  }, T);

  test("a valid-but-empty file reports no laws and exits 0", async () => {
    const r = await run(path.join(FX, "empty.bend"), "--jobs", "4");
    expect(r.code).toBe(0);
    expect(r.stdout).toContain("0 laws: 0 ✓ · 0 ✗ · 0 ~ · 0 !");
  }, T);

  test("mutate on a rejected file errors, not survivors", async () => {
    const r = await run("mutate", path.join(FX, "unclosed.bend"), "--jobs", "4", "--max-instances", "5");
    expect(r.code).toBe(2);
    expect(r.stdout).toBe("");
    expect(r.stderr).toContain("does not type-check");
    expect(r.stderr).not.toContain("survived");
  }, T);
});
