// lint: enforce bend-mathlib's permanent-API conventions (PLAN.md §3.1).
//
//   names      law/def names are lowercase snake_case, no dots, not a Base name
//   docs       every public law has a `#` doc line directly above it
//   claims     every claim is exactly one line; every law has a proof right below it
//   types      no `type` declarations (mathlib holds no nominal definitions)
//   predicates a type-level def (-> Data / -> Type) has a one-line body with no
//              `match` that calls only Base functions (so it unifies across versions)
//   erasure    (--erasure) every binder that CAN be erased is: tried in a scratch copy
// usage: bun tools/mathlib/lint.ts [pkgdir] [--erasure] [--allow-types]
// exit: 0 clean · 1 findings · 2 usage

import { cpSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, join, relative, resolve } from "node:path";
import { BEND, ROOT, baseNames, packageModules, parseModule, type Module } from "./lib.ts";

const args = process.argv.slice(2);
const pkg = resolve(args.find((a) => !a.startsWith("--")) ?? join(ROOT, "packages", "bend-mathlib"));
const doErasure = args.includes("--erasure");
const allowTypes = args.includes("--allow-types");

const findings: string[] = [];
const at = (m: Module, line: number, msg: string) => findings.push(`${relative(ROOT, m.file)}:${line}: ${msg}`);
const NAME = /^[a-z][a-z0-9_]*$/;
const base = await baseNames();
const mods = packageModules(pkg).map((f) => parseModule(f));

for (const m of mods) {
  for (const law of m.laws) {
    if (!NAME.test(law.name)) at(m, law.line, `law name '${law.name}' must be lowercase snake_case without dots`);
    if (base.has(law.name)) at(m, law.line, `law name '${law.name}' collides with Base`);
    if (!law.name.startsWith("internal_") && law.doc.length === 0) at(m, law.line, `law '${law.name}' has no '#' doc line above it`);
    if (law.claimLines.length !== 1) at(m, law.line, `law '${law.name}' must have exactly one claim line (found ${law.claimLines.length})`);
    if (!law.proof) at(m, law.line, `law '${law.name}' has no 'def ${law.name}(...)' proof directly after it`);
  }
  for (const d of m.defs) {
    if (!NAME.test(d.name)) at(m, d.line, `def name '${d.name}' must be lowercase snake_case without dots`);
    if (base.has(d.name)) at(m, d.line, `def name '${d.name}' collides with Base`);
    if (!d.name.startsWith("internal_") && /->\s*(Data|Type)\s*:\s*$/.test(d.header)) {
      const body = d.body.filter((l) => l.trim() !== "");
      if (body.length !== 1) at(m, d.line, `predicate '${d.name}' must have a one-line body`);
      const text = body.join(" ");
      if (/\bmatch\b/.test(text)) at(m, d.line, `predicate '${d.name}' must not match (it would be nominal across versions)`);
      for (const call of text.matchAll(/([A-Za-z_][A-Za-z0-9_.]*)\s*\(/g)) {
        const fn = call[1];
        if (!base.has(fn)) at(m, d.line, `predicate '${d.name}' calls '${fn}', which is not a Base function`);
      }
    }
  }
  if (!allowTypes) for (const t of m.types) at(m, t.line, `type '${t.name}': bend-mathlib holds no datatypes (use a kernel package)`);
}

if (doErasure) {
  // One scratch copy of the package; for each candidate, overwrite the module with
  // one binder erased, re-check, then restore the original text (nothing is deleted).
  const dir = mkdtempSync(join(tmpdir(), "bendlib-erasure-"));
  cpSync(pkg, dir, { recursive: true });
  for (const m of mods) {
    const lines = m.text.split("\n");
    for (const law of m.laws) {
      for (const b of law.binders) {
        if (b.mark === "-" || b.mark === "~" || /^(Type|Data|Kind\b)/.test(b.type)) continue;
        const idx = lines.findIndex((l, i) => i >= law.line && l.trim() === b.raw);
        if (idx < 0) continue;
        const mutated = lines.slice();
        mutated[idx] = mutated[idx].replace(/for\s+[+]?/, "for -");
        writeFileSync(join(dir, basename(m.file)), mutated.join("\n"));
        const p = Bun.spawnSync([BEND, join(dir, basename(m.file)), "--check-only"], { cwd: dir, env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
        const out = (new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr)).trim();
        writeFileSync(join(dir, basename(m.file)), m.text);
        if (out === "All terms check.") at(m, idx + 1, `binder '${b.name}' of '${law.name}' can be erased (write 'for -${b.name}')`);
      }
    }
  }
}

for (const f of findings) console.log(f);
console.log(`${findings.length} finding(s) in ${mods.length} module(s)${doErasure ? " (erasure checked)" : ""}`);
process.exit(findings.length === 0 ? 0 : 1);
