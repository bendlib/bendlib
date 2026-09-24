// lock: PUBLIC_API.lock makes published statements append-only (PLAN.md §3.1 rule 2).
// Public entries: every law and type-level def not named internal_*. An entry with "since" set
// was published and may never change or disappear; unpublished entries follow the source.
//
// usage: bun tools/mathlib/lock.ts [pkgdir] (--check | --update | --freeze <version>)
// exit: 0 ok · 1 a published entry changed or vanished · 2 usage

import { createHash } from "node:crypto";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { PkgError, ROOT, packageModules, parseModule } from "./lib.ts";

const USAGE = "usage: bun tools/mathlib/lock.ts [pkgdir] (--check | --update | --freeze <version>)";
const usage = (msg: string): never => { console.error(`lock: ${msg}\n${USAGE}`); process.exit(2); };

type Entry = { kind: "law" | "predicate"; text: string; sha256: string; since: string | null };
const args = process.argv.slice(2);
const pkg = resolve(args.find((a, i) => !a.startsWith("--") && args[i - 1] !== "--freeze") ?? join(ROOT, "packages", "bend-mathlib"));
const mode = args.find((a) => ["--check", "--update", "--freeze"].includes(a));
if (!mode) usage("one of --check | --update | --freeze <version> is required");

const current = new Map<string, Omit<Entry, "since">>();
let files: string[];
try { files = packageModules(pkg); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
for (const file of files) {
  const mod = parseModule(file);
  const put = (name: string, kind: Entry["kind"], text: string) =>
    current.set(`${mod.name}.${name}`, { kind, text, sha256: createHash("sha256").update(text).digest("hex") });
  for (const law of mod.laws) if (!law.name.startsWith("internal_")) put(law.name, "law", [...law.binders.map((b) => b.raw), ...law.claimLines].join("\n"));
  for (const d of mod.defs) if (!d.name.startsWith("internal_") && /->\s*(Data|Type)\s*:\s*$/.test(d.header)) put(d.name, "predicate", [d.header.trim(), ...d.body.map((l) => l.trim()).filter(Boolean)].join("\n"));
}

const lockFile = join(pkg, "PUBLIC_API.lock");
const locked: Record<string, Entry> = existsSync(lockFile) ? JSON.parse(readFileSync(lockFile, "utf8")) : {};
const broken = Object.entries(locked)
  .filter(([k, e]) => e.since !== null && current.get(k)?.sha256 !== e.sha256)
  .map(([k, e]) => `${k} (published in ${e.since}) ${current.has(k) ? "changed" : "was removed"}`);
for (const b of broken) console.log(`frozen entry violated: ${b}`);
if (broken.length) process.exit(1);

if (mode === "--check") {
  const unlisted = [...current.keys()].filter((k) => !(k in locked) || (locked[k].since === null && locked[k].sha256 !== current.get(k)!.sha256));
  for (const k of unlisted) console.log(`not in lock (run --update): ${k}`);
  console.log(`${Object.keys(locked).length} entries locked, ${Object.values(locked).filter((e) => e.since).length} published`);
  process.exit(unlisted.length ? 1 : 0);
}

const next: Record<string, Entry> = {};
for (const [k, e] of Object.entries(locked)) if (e.since !== null) next[k] = e;
for (const [k, e] of current) if (!(k in next)) next[k] = { ...e, since: null };
if (mode === "--freeze") {
  const version = args[args.indexOf("--freeze") + 1];
  if (!/^\d+\.\d+\.\d+\.\d+$/.test(version ?? "")) { console.error("--freeze needs a version like 0.1.0.0"); process.exit(2); }
  for (const e of Object.values(next)) if (e.since === null) e.since = version;
}
const sorted = Object.fromEntries(Object.keys(next).sort().map((k) => [k, next[k]]));
writeFileSync(lockFile, JSON.stringify(sorted, null, 2) + "\n");
console.log(`wrote ${lockFile}: ${Object.keys(sorted).length} entries`);
