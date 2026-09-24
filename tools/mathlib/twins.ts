// twins: generate `<name>_sym` twins for every public equational law.
//
// Bend's rewrite `%e : P` replaces the equation's RIGHT side with its LEFT side,
// so a Mathlib-style lemma `{big == simple}` expands, and its reversed twin
// `{simple == big}` simplifies (PLAN.md §3.1.6, fact F28). Twins are appended in
// a generated trailing section of the same module, proved by Equal.sym.
//
// usage: bun tools/mathlib/twins.ts [pkgdir] [--check]
//   default: rewrite each module's generated section in place
//   --check: exit 1 if any module's generated section is out of date (CI)

import { readFileSync, writeFileSync } from "node:fs";
import { join, relative, resolve } from "node:path";
import { GENERATED_MARK, ROOT, packageModules, parseModule, splitEquation } from "./lib.ts";

const args = process.argv.slice(2);
const pkg = resolve(args.find((a) => !a.startsWith("--")) ?? join(ROOT, "packages", "bend-mathlib"));
const check = args.includes("--check");
let stale = 0;

for (const file of packageModules(pkg)) {
  const text = readFileSync(file, "utf8");
  const cut = text.indexOf(GENERATED_MARK);
  const handwritten = (cut >= 0 ? text.slice(0, cut) : text).replace(/\s+$/, "") + "\n";
  // Parse only the handwritten part so twins are never twinned.
  const mod = parseModule(file, handwritten);
  const out: string[] = [];
  for (const law of mod.laws) {
    if (law.name.startsWith("internal_") || law.name.endsWith("_sym") || law.exs || !law.proof) continue;
    if (law.binders.some((b) => b.where) || law.claimLines.length !== 1) continue;
    // A twin of a conclusion drawn from hypotheses (succ_inj, le_antisymm) is permanent noise.
    if (law.binders.some((b) => b.type.startsWith("{") || /^([a-z_][A-Za-z0-9_.]*|[A-Z])\(/.test(b.type))) continue;
    const eq = splitEquation(law.claimLines[0]);
    if (!eq) continue;
    const params = law.binders.map((b) => b.name);
    const callArgs = law.binders.map((b) => (b.mark === "~" ? "~" : "") + b.name);
    out.push(
      `# ${(law.doc[0] ?? law.name).replace(/\.$/, "")}, reversed to rewrite toward the simple side.`,
      `law ${law.name}_sym:`,
      ...law.binders.map((b) => `  ${b.raw}`),
      `  {${eq.rhs} == ${eq.lhs} : ${eq.type}}`,
      ``,
      `def ${law.name}_sym(${params.join(", ")}):`,
      `  Equal.sym(${eq.type}, ${eq.lhs}, ${eq.rhs}, ${law.name}(${callArgs.join(", ")}))`,
      ``,
    );
  }
  const next = out.length === 0 ? handwritten : handwritten + "\n" + GENERATED_MARK + "\n\n" + out.join("\n").replace(/\n+$/, "") + "\n";
  if (next !== text) {
    stale++;
    if (check) console.log(`stale: ${relative(ROOT, file)}`);
    else { writeFileSync(file, next); console.log(`updated: ${relative(ROOT, file)}`); }
  }
}
if (check && stale > 0) process.exit(1);
console.log(check ? "twins up to date" : `${stale} module(s) updated`);
