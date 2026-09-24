// Checker-output classification. The strings are verbatim outputs of
// `bend <file> --check-only` on 2.0.27 for hub files (named in each test).

import { describe, expect, test } from "bun:test";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { BEND, checkCommand, checkFile, classify, crossCheck, sandboxAvailable, worst } from "../src/status.ts";

describe("classify", () => {
  test("exactly 'All terms check.' with exit 0 is checks", () => {
    expect(classify("All terms check.\n", 0, false, 1).class).toBe("checks");
  });
  test("planted negative: the same text with a non-zero exit is not checks", () => {
    expect(classify("All terms check.\n", 1, false, 1).class).toBe("fails");
  });
  test("the unsafe line lists its defs (0xb1a81026…/Engine.bend)", () => {
    const s = classify("All terms check, but 3 defs rely on unsafe or foreign code:\n- breed_child\n- generate_next_pop\n- evolve\n", 0, false, 1);
    expect(s.class).toBe("unsafe");
    expect(s.unsafeDefs).toEqual(["breed_child", "generate_next_pop", "evolve"]);
    expect(s.summary).toBe("All terms check, but 3 defs rely on unsafe or foreign code");
  });
  test("singular form (0x527a2a4f…/lib.bend)", () => {
    const s = classify("All terms check, but 1 def relies on unsafe or foreign code:\n- das_dennis_m1\n", 0, false, 1);
    expect(s.unsafeDefs).toEqual(["das_dennis_m1"]);
  });
  test("TODOs are open laws (0xf5a52e74…/src/LAWS.bend)", () => {
    const s = classify("Error: 5 TODOs found.\nThe code is incomplete, and not a valid proof yet.\n", 1, false, 1);
    expect(s.class).toBe("open");
    expect(s.summary).toBe("5 TODOs found.");
  });
  test("an error block is fails with its message as the summary", () => {
    const out = "Error:\n- expected : a fresh constructor name (duplicate declaration: Zero)\n- observed : '{'\nLocation:\n192 |   Minus{}\n193>|   Zero{}\n";
    const s = classify(out, 1, false, 1);
    expect(s.class).toBe("fails");
    expect(s.summary).toBe("- expected : a fresh constructor name (duplicate declaration: Zero)");
    expect(s.detail).toContain("193>|   Zero{}");
  });
  test("a kill on timeout is timeout, whatever was printed", () => {
    expect(classify("", null, true, 20.2).class).toBe("timeout");
  });
  test("package status is the worst file status", () => {
    expect(worst(["checks", "unsafe", "checks"])).toBe("unsafe");
    expect(worst(["open", "timeout", "unsafe"])).toBe("timeout");
    expect(worst(["checks", "fails", "timeout"])).toBe("fails");
    expect(worst([])).toBe("checks");
  });
});

describe("crossCheck", () => {
  const clean = () => classify("All terms check.\n", 0, false, 1);
  test("a clean verdict over @unsafe source is downgraded to unsafe (bend issue #1001)", () => {
    const s = crossCheck(clean(), "@unsafe\ndef f() -> Nat:\n  0n\n");
    expect(s.class).toBe("unsafe");
    expect(s.unsafeDefs).toEqual(["f"]);
    expect(s.summary).toBe("source has @unsafe, but bend printed a clean verdict (bend issue #1001)");
  });
  test("every def after an @unsafe is named, including the ? form", () => {
    const src = "@unsafe\ndef f() -> Nat:\n  0n\n\n@unsafe\ndef g?(x) -> Nat:\n  x\n";
    expect(crossCheck(clean(), src).unsafeDefs).toEqual(["f", "g"]);
  });
  test("planted negative: @unsafe in a comment is not counted", () => {
    expect(crossCheck(clean(), "# @unsafe\ndef f() -> Nat:\n  0n\n").class).toBe("checks");
  });
  test("planted negative: @unsafe inside a string is not counted", () => {
    expect(crossCheck(clean(), 'def f() -> String:\n  "@unsafe"\n').class).toBe("checks");
  });
  test("planted negative: @unsafe never upgrades a fails status", () => {
    const fails = classify("Error:\n- expected : a fresh constructor name (duplicate declaration: Zero)\n", 1, false, 1);
    expect(fails.class).toBe("fails");
    expect(crossCheck(fails, "@unsafe\ndef f() -> Nat:\n  0n\n").class).toBe("fails");
  });
});

describe("checkCommand", () => {
  const o = { bendLib: "/lib", timeoutSec: 20, memMb: 4096, cwd: "/pkg" };
  test("sandboxed: bwrap with a read-only root and writable BEND_LIB, inner check unchanged", () => {
    const argv = checkCommand("/lib/h/f.bend", o, true);
    expect(argv[0]).toBe("bwrap");
    expect(argv).toContain("--unshare-all");
    expect(argv).toContain("--die-with-parent");
    const ro = argv.indexOf("--ro-bind");
    expect(argv.slice(ro, ro + 3)).toEqual(["--ro-bind", "/", "/"]);
    const b = argv.indexOf("--bind");
    expect(argv.slice(b, b + 3)).toEqual(["--bind", "/lib", "/lib"]);
    const c = argv.indexOf("--chdir");
    expect(argv.slice(c, c + 2)).toEqual(["--chdir", "/pkg"]);
    expect(argv.slice(argv.indexOf("bash"))).toEqual(checkCommand("/lib/h/f.bend", o, false));
  });
  test("unsandboxed: today's argv, with the memory cap and no bwrap", () => {
    const argv = checkCommand("/lib/h/f.bend", o, false);
    expect(argv[0]).toBe("bash");
    expect(argv).not.toContain("bwrap");
    expect(argv[2]).toContain("ulimit -v 4194304");
    expect(argv.slice(-2)).toEqual([BEND, "/lib/h/f.bend"]);
  });
});

const hasBwrap = sandboxAvailable();

describe("checkFile under the sandbox", () => {
  test.skipIf(!hasBwrap)("the good fixture checks inside bwrap", async () => {
    const entry = join(import.meta.dir, "..", "..", "mathlib", "fixtures", "good", "list.bend");
    const lib = mkdtempSync(join(tmpdir(), "bend-docs-sandbox-"));
    const s = await checkFile(entry, { bendLib: lib, timeoutSec: 120, memMb: 4096, cwd: dirname(entry) });
    expect(s.class).toBe("checks");
  }, 180_000);
});
