// index: generate a package's README.md (short, published with the package: bend 2.0.40 hashes and
// uploads the README beside the entry) and INDEX.md (the full lemma index, never uploaded).
// The README names no content hash: it is part of the hashed package, so its own hash cannot be in it.
// usage: bun tools/mathlib/index.ts <pkgdir> <name> <version> [--check] [--stdout] [--out=<dir>]
//   --check: exit 1 when either file differs from what would be written · --stdout: print both
//   --out=<dir>: write both there instead of into <pkgdir> (release.ts's dry run)
// exit: 0 ok · 1 stale (--check) · 2 usage (also a README over README_MAX)

import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { basename, join, relative, resolve } from "node:path";
import { PkgError, ROOT, packageModules, parseModule, readLock, readReleases } from "./lib.ts";
import { README_MAX } from "./hash.ts";

const USAGE = "usage: bun tools/mathlib/index.ts <pkgdir> <name> <version> [--check] [--stdout] [--out=<dir>]";
const usage = (msg: string): never => { console.error(`index: ${msg}\n${USAGE}`); process.exit(2); };

const [dirArg, name, version] = process.argv.slice(2).filter((a) => !a.startsWith("--"));
if (!dirArg || !name || !version) usage("need <pkgdir> <name> <version>");
if (!/^\d+\.\d+\.\d+\.\d+$/.test(version)) usage(`version must be a.b.c.d, got ${JSON.stringify(version)}`);
const dir = resolve(dirArg);
const alias = (m: string) => "M" + m[0].toUpperCase() + m.slice(1);
const cell = (s: string) => "`" + s.replace(/\|/g, "\\|") + "`";
const compiler = JSON.parse(readFileSync(join(ROOT, "toolchain.json"), "utf8")).bend.version as string;
const SITE = "https://bendlib.github.io/bendlib/";
const indexUrl = `https://github.com/bendlib/bendlib/blob/main/packages/${basename(dir)}/INDEX.md`;

// The hash of a released version comes from the ledger; the override lets the release test run off-tree.
const released = readReleases(process.env.BENDLIB_RELEASES ?? join(ROOT, "RELEASES.md"))
  .find((r) => r.name === name && r.version === version)?.hash;

// The lock records the version that first published each entry; absent or null means unreleased.
const lock = readLock(join(dir, "PUBLIC_API.lock"));
let hasNext = false;
const sinceCell = (module: string, entry: string) => {
  const since = lock[`${module}.${entry}`]?.since ?? null;
  if (since === null) hasNext = true;
  return since ?? "next";
};

// A module's scope is the first sentence of its header comment, after `<name>/<file>.bend: `.
const scopeOf = (text: string): string => {
  const head: string[] = [];
  for (const l of text.split("\n")) { if (!l.startsWith("#")) break; head.push(l.replace(/^#\s?/, "")); }
  const joined = head.join(" ").replace(/^\S+\.bend:\s*/, "");
  const first = (/^.*?\.(?=\s|$)/.exec(joined)?.[0] ?? joined).trim();
  return first.charAt(0).toUpperCase() + first.slice(1);
};

const rewriting = [
  "Rewriting: `%e : P` replaces the right side of `e` with its left side, so `name` expands the simple",
  "side into the compound one and `name_sym` simplifies the compound side.",
];
const rows: string[] = [];
const body: string[] = [];
let lemmas = 0;
let twins = 0;
let predicates = 0;
let typed = 0;
let files: string[];
try { files = packageModules(dir); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
let example = "";
for (const file of files) {
  const m = parseModule(file);
  const laws = m.laws.filter((l) => !l.name.startsWith("internal_"));
  const pub = m.defs.filter((d) => !d.name.startsWith("internal_"));
  const preds = pub.filter((d) => /->\s*(Data|Type)\s*:\s*$/.test(d.header));
  const defs = pub.filter((d) => !preds.includes(d));
  if (laws.length + pub.length === 0) continue;
  const sym = laws.filter((l) => l.name.endsWith("_sym")).length;
  lemmas += laws.length - sym;
  twins += sym;
  predicates += preds.length;
  typed += defs.length;
  const rel = relative(dir, file).replace(/\.bend$/, "");
  if (example === "" || rel === "nat") example = rel;
  rows.push(`| \`${rel}\` | ${scopeOf(m.text).replace(/\|/g, "\\|")} | ${laws.length - sym} | ${sym} | ${preds.length} | ${defs.length} |`);
  body.push(`## ${m.name}`, "", "```python", `import ${name}@${version}/${rel}.bend as ${alias(m.name)}`, "```", "");
  if (preds.length) {
    body.push("| predicate | definition | since |", "|---|---|---|");
    for (const p of preds) body.push(`| ${cell(p.header.replace(/^def\s+/, "").replace(/:\s*$/, ""))} | ${cell(p.body.map((l) => l.trim()).join(" "))} | ${sinceCell(m.name, p.name)} |`);
    body.push("");
  }
  if (defs.length) {
    body.push("| typed def | signature | meaning | since |", "|---|---|---|---|");
    for (const d of defs) body.push(`| ${cell(d.name)} | ${cell(d.header.replace(/^def\s+/, "").replace(/:\s*$/, "").replace(/\s*\n\s*/g, " "))} | ${(d.doc[0] ?? "").replace(/\|/g, "\\|")} | ${sinceCell(m.name, d.name)} |`);
    body.push("");
  }
  if (laws.length) body.push("| lemma | statement | meaning | since |", "|---|---|---|---|");
  for (const l of laws) {
    const binders = l.binders.map((b) => `${b.mark}${b.name}: ${b.type}`).join(", ");
    body.push(`| ${cell(`${l.name}(${l.binders.map((b) => (b.mark === "~" ? "~" : "") + b.name).join(", ")})`)} | ${cell(`${binders ? `∀ ${binders}. ` : ""}${l.claimLines[0]}`)} | ${(l.doc[0] ?? "").replace(/\|/g, "\\|")} | ${sinceCell(m.name, l.name)} |`);
  }
  if (laws.length) body.push("");
}
if (example === "") example = files.length ? relative(dir, files[0]).replace(/\.bend$/, "") : "all";
const totals = `${lemmas} lemmas + ${twins} generated _sym twins, ${predicates} predicates, ${typed} typed defs.`;

const readme = [
  `# ${name}`,
  "",
  `Machine-checked lemmas for Bend 2, checked with \`bend ${compiler}\`: ${lemmas} lemmas, ${twins} generated`,
  `\`_sym\` twins, ${predicates} predicates and ${typed} typed defs (theorems stated by their type, and the`,
  "functions they are about). Import a module instead of re-proving a basic fact; every statement is",
  "locked, so a later version never changes one you use.",
  "",
  "## Import",
  "",
  "```python",
  `import ${name}@${version}/${example}.bend as ${alias(example)}`,
  "```",
  "",
  `Each module imports on its own; \`all.bend\` imports them all. To pin the exact bytes, import by`,
  "content hash instead of name: `import 0x<hash>/" + example + ".bend as " + alias(example) + "`. The hash of",
  `${name}@${version} is what \`curl -s https://hub.bend-lang.com/name/${name}@${version}\` prints, what`,
  `\`bend\` stored in \`~/.bend/lib/names/${name}@${version}\` (or under \`$BEND_LIB\`) when it first resolved`,
  "the name, and the name of the directory this package was fetched into. This README cannot state it:",
  "the README is part of the package that the hash covers.",
  "",
  "## Modules",
  "",
  "| module | scope | lemmas | `_sym` twins | predicates | typed defs |",
  "|---|---|---|---|---|---|",
  ...rows,
  "",
  "## Find a lemma",
  "",
  "- A name is the shape of its statement: `add_comm`, `mul_add`, `append_assoc`, `le_trans`, `take_append_drop`.",
  "- Each law has a one-line description directly above it, so a grep in this directory shows the",
  `  description, the binders and the statement: \`grep -n -B1 -A4 '^law add_comm:' ${example}.bend\`.`,
  "- A generated `name_sym` twin states the same equation with its sides swapped: `add_zero` is",
  "  `Nat.add(x, 0n) == x`, `add_zero_sym` is `x == Nat.add(x, 0n)`.",
  ...rewriting.map((l, i) => (i === 0 ? "- " : "  ") + l),
  "- Names starting with `internal_` are proof helpers, not part of the public API.",
  "- The full index lists every lemma with its statement and the version that added it:",
  `  \`INDEX.md\` in the repository, ${indexUrl}`,
  `  and the docs site, ${SITE}name/${name}/ (search by shape: ${SITE}search.html).`,
  "",
  "## License",
  "",
  "See `LICENSE` beside this file.",
  "",
].join("\n");

const index = [
  `# ${name}: lemma index`,
  "",
  `Every lemma of ${name} with its statement, checked with \`bend ${compiler}\`.`,
  "",
  ...rewriting,
  "",
  ...(released ? [`${name}@${version} is \`${released}\`; to pin its bytes, import by hash instead of name:`, "", "```python",
    `import ${released}/${example}.bend as ${alias(example)}`, "```", ""] : []),
  ...(hasNext ? ["Rows marked `next` are proved in this repository but not yet published: the import lines below do not contain them yet.", ""] : []),
  ...body,
  `${totals} Generated by \`tools/mathlib/index.ts\`.`,
  "",
].join("\n");

const size = Buffer.byteLength(readme);
if (size > README_MAX) usage(`the README would be ${size} bytes, over ${README_MAX}, which bend refuses to publish`);
const outDir = resolve(process.argv.find((a) => a.startsWith("--out="))?.slice(6) || dir);
const targets: [string, string][] = [[join(outDir, "README.md"), readme], [join(outDir, "INDEX.md"), index]];
if (process.argv.includes("--check")) {
  const stale = targets.filter(([f, t]) => !existsSync(f) || readFileSync(f, "utf8") !== t).map(([f]) => f);
  console.log(stale.length === 0 ? "index up to date" : stale.map((f) => `stale: ${f}`).join("\n"));
  process.exit(stale.length === 0 ? 0 : 1);
}
if (process.argv.includes("--stdout")) { process.stdout.write(readme + "\n" + index); process.exit(0); }
for (const [f, t] of targets) writeFileSync(f, t);
console.log(`wrote ${targets.map(([f]) => f).join(" and ")} (${lemmas} lemmas + ${twins} twins, ${predicates} predicates; README ${size} bytes)`);
