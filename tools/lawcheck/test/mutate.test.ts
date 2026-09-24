// Pure mutation-operator tests: they read fixture text with `fs` and run no process.

import { describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as path from "node:path";
import { defSpan, mutants, type Mutant } from "../src/mutate.ts";

const FX = path.join(import.meta.dir, "fixtures");
const read = (f: string) => fs.readFileSync(path.join(FX, f), "utf8");

describe("defSpan", () => {
  const text = read("lib_ok.bend");

  test("app's span is exactly its lines", () => {
    const lines = text.split("\n");
    expect(defSpan(text, "app")).toEqual({ start: 14, end: 19 });
    expect(lines[13].startsWith("def app(")).toBe(true);
    expect(lines[18]).toBe("      Push{c, app(r, ys)}");
  });

  test("a missing def is null", () => {
    expect(defSpan(text, "nope")).toBeNull();
  });
});

describe("mutants", () => {
  const text = read("lib_ok.bend");
  const app = mutants(text, "app", ["xs", "ys"]);
  const size = mutants(text, "size", ["s"]);

  test("app: exactly one arm-swap, with the two bodies exchanged", () => {
    const swaps = app.filter((m) => m.op === "arm-swap");
    expect(swaps.length).toBe(1);
    const ls = swaps[0].text.split("\n");
    const d = ls.findIndex((l) => l.startsWith("def app("));
    const i = ls.findIndex((l, k) => k > d && l.trim() === "case Bot{}:");
    expect(d).toBeGreaterThanOrEqual(0);
    expect(i).toBeGreaterThan(d);
    expect(ls[i + 1].trim()).toBe("Push{c, app(r, ys)}");
  });

  test("app: six projection mutants", () => {
    expect(app.filter((m) => m.op === "projection").length).toBe(6);
  });

  test("app: an arg-swap contains app(ys, r)", () => {
    expect(app.some((m) => m.op === "arg-swap" && m.after.includes("app(ys, r)"))).toBe(true);
  });

  test("size: a drop-succ and a literal", () => {
    expect(size.some((m) => m.op === "drop-succ" && m.after === "size(r)")).toBe(true);
    expect(size.some((m) => m.op === "literal" && m.after === "1n")).toBe(true);
  });

  test("every mutant changes only body lines, is new, and all texts are distinct", () => {
    const input = text.split("\n");
    for (const [name, list] of [["app", app], ["size", size]] as [string, Mutant[]][]) {
      const span = defSpan(text, name)!;
      const prefixLen = span.start - 1;
      const suffixLen = input.length - span.end;
      const texts = new Set<string>();
      for (const m of list) {
        expect(m.text).not.toBe(text);
        expect(texts.has(m.text)).toBe(false);
        texts.add(m.text);
        const out = m.text.split("\n");
        for (let i = 0; i < prefixLen; i++) expect(out[i]).toBe(input[i]);
        for (let i = 0; i < suffixLen; i++) expect(out[out.length - suffixLen + i]).toBe(input[input.length - suffixLen + i]);
      }
    }
  });
});
