#!/usr/bin/env bun
// lawcheck: search for counterexamples to the laws of a Bend 2 file before anyone
// tries to prove them, and shrink them. Passing laws are NOT proved.
// usage: bun tools/lawcheck/cli.ts <file.bend> [--impl <file>] [--size N]
//          [--max-instances N] [--seed S] [--json] [--law name] [--jobs N] [--timeout MS]
//   --impl  check the laws against another implementation: replaces the file's
//           local import with the same basename (or its only local import)
// exit: 0 no counterexample · 1 counterexample found · 2 usage, load or tool error

import * as path from "node:path";
import { BendReadError, SourceError } from "../reader/index.ts";

import { ModuleError } from "./src/checker.ts";
import { lawcheck, UsageError, type LawResult, type Options, type Report } from "./src/lawcheck.ts";

const USAGE = "usage: bun tools/lawcheck/cli.ts <file.bend> [--impl <file>] [--size N] [--max-instances N] [--seed S] [--json] [--law name] [--jobs N] [--timeout MS]";

function die(msg: string): never {
  process.stderr.write(`lawcheck: ${msg}\n`);
  process.exit(2);
}

function parseArgs(argv: string[]) {
  const o: Options & { file: string; json: boolean } = { file: "", json: false, size: 3, maxInstances: 200, seed: 1 };
  const num = (flag: string, v: string | undefined, min: number) => {
    const n = Number(v);
    if (v === undefined || !Number.isInteger(n) || n < min) die(`${flag} needs an integer ≥ ${min}\n${USAGE}`);
    return n;
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--json") o.json = true;
    else if (a === "--size") o.size = num(a, argv[++i], 0);
    else if (a === "--max-instances") o.maxInstances = num(a, argv[++i], 1);
    else if (a === "--seed") o.seed = num(a, argv[++i], 0);
    else if (a === "--jobs") o.jobs = num(a, argv[++i], 1);
    else if (a === "--timeout") o.timeoutMs = num(a, argv[++i], 1);
    else if (a === "--law" || a === "--impl") {
      const v = argv[++i];
      if (v === undefined) die(`${a} needs a value\n${USAGE}`);
      if (a === "--law") o.law = v; else o.impl = v;
    } else if (a === "-h" || a === "--help") {
      console.log(USAGE);
      process.exit(0);
    } else if (a.startsWith("-")) die(`unknown flag ${a}\n${USAGE}`);
    else if (o.file === "") o.file = a;
    else die(`one file only (got ${o.file} and ${a})\n${USAGE}`);
  }
  if (o.file === "") die(`no file given\n${USAGE}`);
  return o;
}

const MARK = { pass: "✓", fail: "✗", skip: "~", error: "!" } as const;

function human(r: Report): string {
  const w = Math.max(...r.laws.map((l) => l.name.length), 4);
  const pad = " ".repeat(w + 3);
  const out = [`lawcheck ${r.version} · ${path.relative(process.cwd(), r.file)} · bend ${r.bend} · seed ${r.seed} · size ${r.size} · ≤${r.maxInstances} instances/law`];
  for (const l of r.laws) {
    const head = `${MARK[l.status]} ${l.name.padEnd(w)}  `;
    out.push(head + lawLine(l, r));
    if (l.status === "fail" && l.counterexample) {
      const c = l.counterexample;
      for (const b of [...c.types, ...c.bindings]) out.push(`${pad}${b.name} = ${b.value}`);
      for (const pr of c.premises ?? []) out.push(`${pad}premise  ${pr}  (holds)`);
      if (c.lhs && c.rhs) {
        out.push(`${pad}lhs  ${c.lhs.term} = ${c.lhs.value}`);
        out.push(`${pad}rhs  ${c.rhs.term} = ${c.rhs.value}`);
      } else {
        out.push(`${pad}claim  ${c.claim}`);
        if (c.goal) out.push(`${pad}goal   ${c.goal}`);
      }
      if (c.expected !== undefined) out.push(`${pad}checker: expected ${c.expected} · observed ${c.observed}`);
    }
    if (l.status === "error" && l.reason?.includes("\n")) out.push(...l.reason.split("\n").slice(1).map((s) => pad + s));
  }
  const n = (s: LawResult["status"]) => r.laws.filter((l) => l.status === s).length;
  out.push(`${r.laws.length} laws: ${n("pass")} ✓ · ${n("fail")} ✗ · ${n("skip")} ~ · ${n("error")} !  (${r.checkerRuns} checker runs; batches in ${r.tmpDir})`);
  out.push("note: ✓ means no counterexample among the instances tried; it proves nothing about all inputs.");
  return out.join("\n");
}

function lawLine(l: LawResult, r: Report): string {
  const prem = l.premise ? `, premises held in ${l.premise.satisfied}/${l.premise.total}` : "";
  switch (l.status) {
    case "pass": return `${l.instances} instance${l.instances === 1 ? "" : "s"}, 0 failures (sizes ≤ ${r.size}${prem})`;
    case "skip": return `skipped: ${l.reason}`;
    case "error": return `error: ${l.reason?.split("\n")[0]}`;
    case "fail": {
      const c = l.counterexample!;
      const orig = c.shrinkSteps > 0 ? ` from ${c.original.map((b) => `${b.name} = ${b.value}`).join(", ")} in ${c.shrinkSteps} step${c.shrinkSteps === 1 ? "" : "s"}` : "";
      const kind = l.claim === "refutation" ? "all premises hold (the law says they cannot)" : "counterexample";
      return `${kind} (shrunk${orig}); ${l.failures}/${l.instances} instances failed${prem}`;
    }
  }
}

const o = parseArgs(process.argv.slice(2));
let report: Report;
try {
  report = await lawcheck(o.file, o);
} catch (e) {
  if (e instanceof UsageError) die(`${e.message}\n${USAGE}`);
  if (e instanceof BendReadError) die(`cannot load ${o.file}:\n${e.message}`);
  if (e instanceof SourceError) die(e.message);
  if (e instanceof ModuleError) die(`${o.file} does not type-check, so no instance can be evaluated:\n${e.message}`);
  throw e;
}
console.log(o.json ? JSON.stringify(report, null, 2) : human(report));
const has = (s: LawResult["status"]) => report.laws.some((l) => l.status === s);
process.exit(has("fail") ? 1 : has("error") ? 2 : 0);
