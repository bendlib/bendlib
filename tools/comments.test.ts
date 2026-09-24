import { expect, test } from "bun:test";
import { join } from "node:path";

const run = (...files: string[]) => {
  const p = Bun.spawnSync([process.execPath, join(import.meta.dir, "comments.ts"), ...files]);
  return { code: p.exitCode, out: new TextDecoder().decode(p.stdout) };
};

test("clean fixture passes", () => {
  expect(run(join(import.meta.dir, "mathlib/fixtures/good/list.bend")).code).toBe(0);
});

test("every planted Bend violation is reported", () => {
  const r = run(join(import.meta.dir, "fixtures/comments_bad.bend"));
  expect(r.code).toBe(1);
  for (const n of ["module header has 4", "doc line format", "TODO/FIXME", "commented-out code", "limited to one line"]) expect(r.out).toContain(n);
});

test("every planted TypeScript violation is reported", () => {
  const r = run(join(import.meta.dir, "fixtures/comments_bad.ts"));
  expect(r.code).toBe(1);
  for (const n of ["longer than 2 lines", "commented-out code", "multi-line /* */", "TODO/FIXME"]) expect(r.out).toContain(n);
});
