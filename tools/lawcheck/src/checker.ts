// Engine C (PLAN F22): closed instances are proved with `{==}` by `bend --check-only`.
// The checker stops at the first failing declaration, in file order, so a batch
// is re-run from the instance after each failure.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

export type Item = { id: string; claim: string; hole?: boolean };

export type Outcome =
  | { r: "pass" }
  | { r: "fail"; expected: string; observed: string }
  | { r: "goal"; goal: string }
  | { r: "undecidable"; detail: string }
  | { r: "illtyped"; detail: string }
  | { r: "error"; detail: string };

export class ModuleError extends Error {}

export type Engine = {
  header: string;
  dir: string;
  bend: string;
  timeoutMs: number;
  jobs: number;
  runs: number;
  display: (s: string) => string;
};

export function bendBin(): string {
  if (process.env.BEND_BIN) return process.env.BEND_BIN;
  const home = path.join(os.homedir(), ".bend", "bin", "bend");
  return fs.existsSync(home) ? home : "bend";
}

let active = 0;
const waiting: (() => void)[] = [];

async function slot<T>(jobs: number, fn: () => Promise<T>): Promise<T> {
  if (active >= jobs) await new Promise<void>((res) => waiting.push(res));
  active++;
  try {
    return await fn();
  } finally {
    active--;
    waiting.shift()?.();
  }
}

let counter = 0;

async function runBatch(E: Engine, items: Item[]): Promise<{ out: string; code: number | null; timedOut: boolean }> {
  const file = path.join(E.dir, `b${counter++}.bend`);
  const src = [E.header, ...items.map((it) => `law ${it.id}:\n  ${it.claim}\n\ndef ${it.id}():\n  ${it.hole ? "?g" : "{==}"}\n`)].join("\n");
  fs.writeFileSync(file, src);
  return slot(E.jobs, async () => {
    E.runs++;
    const p = Bun.spawn([E.bend, file, "--check-only"], {
      env: { ...process.env, BEND_NO_TELEMETRY: "1" },
      stdout: "pipe",
      stderr: "pipe",
    });
    let timedOut = false;
    const timer = setTimeout(() => { timedOut = true; p.kill(); }, E.timeoutMs);
    const [o, e] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
    const code = await p.exited;
    clearTimeout(timer);
    return { out: o + e, code, timedOut };
  });
}

type Located = { def: string; expected: string | null; observed: string | null; pointed: string; text: string };

function field(lines: string[], key: string): string | null {
  const i = lines.findIndex((l) => l.startsWith(`- ${key} : `));
  if (i < 0) return null;
  const parts = [lines[i].slice(key.length + 5)];
  for (let j = i + 1; j < lines.length && !/^(- \w+ : |Context:|Location:)/.test(lines[j]); j++) parts.push(lines[j].trim());
  return parts.join(" ");
}

function locate(out: string): Located | null {
  const lines = out.split("\n");
  const li = lines.findIndex((l) => l.startsWith("Location: "));
  if (li < 0) return null;
  const errAt = lines.slice(0, li).lastIndexOf("Error:");
  const block = lines.slice(Math.max(0, errAt), li);
  const pointed = lines.slice(li + 1).find((l) => /^\s*\d+>\|/.test(l))?.replace(/^\s*\d+>\|/, "").trim() ?? "";
  return { def: lines[li].slice(10).trim(), expected: field(block, "expected"), observed: field(block, "observed"), pointed, text: lines.slice(Math.max(0, errAt)).join("\n").trim() };
}

const allChecked = (out: string) => /All terms check/.test(out) || /\d+ TODOs? found/.test(out);

/** Evaluates every item; with `stopAtFail`, returns as soon as one item genuinely fails. */
export async function evaluate(E: Engine, items: Item[], stopAtFail = false): Promise<Map<string, Outcome>> {
  const res = new Map<string, Outcome>();
  let rest = items;
  while (rest.length > 0) {
    const { out, timedOut } = await runBatch(E, rest);
    if (timedOut) {
      for (const it of rest) res.set(it.id, { r: "error", detail: `bend timed out after ${E.timeoutMs} ms` });
      break;
    }
    const loc = locate(out);
    if (loc === null) {
      const o: Outcome = allChecked(out) ? { r: "pass" } : { r: "error", detail: E.display(out.trim()) };
      for (const it of rest) res.set(it.id, o);
      break;
    }
    const idx = rest.findIndex((it) => it.id === loc.def);
    if (idx < 0) throw new ModuleError(E.display(loc.text));
    for (const it of rest.slice(0, idx)) res.set(it.id, { r: "pass" });
    const it = rest[idx];
    const expected = E.display(loc.expected ?? ""), observed = E.display(loc.observed ?? "");
    let o: Outcome;
    if (it.hole && loc.pointed === "?g") o = { r: "goal", goal: expected };
    else if (loc.pointed !== "{==}") o = { r: "illtyped", detail: E.display(loc.text) };
    else if (/non-inferrable term/.test(loc.observed ?? "")) o = { r: "undecidable", detail: `goal ${expected} is not an equation` };
    else if (loc.expected === null || loc.observed === null) o = { r: "illtyped", detail: E.display(loc.text) };
    else o = { r: "fail", expected, observed };
    res.set(it.id, o);
    if (stopAtFail && o.r === "fail") break;
    rest = rest.slice(idx + 1);
  }
  return res;
}

/** Splits items into batches and evaluates them concurrently. */
export async function evaluateAll(E: Engine, items: Item[]): Promise<Map<string, Outcome>> {
  const size = Math.max(8, Math.min(50, Math.ceil(items.length / E.jobs)));
  const chunks: Item[][] = [];
  for (let i = 0; i < items.length; i += size) chunks.push(items.slice(i, i + size));
  const maps = await Promise.all(chunks.map((c) => evaluate(E, c)));
  return new Map(maps.flatMap((m) => [...m]));
}
