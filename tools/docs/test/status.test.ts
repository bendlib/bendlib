// Checker-output classification. The strings are verbatim outputs of
// `bend <file> --check-only` on 2.0.27 for hub files (named in each test).

import { describe, expect, test } from "bun:test";
import { classify, worst } from "../src/status.ts";

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
