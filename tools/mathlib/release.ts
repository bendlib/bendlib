// release: run every gate, compute the package's hub hash, publish anonymously, verify the
// uploaded content from an empty cache, then attach the name (PLAN.md §3.5).
//
// usage: bun tools/mathlib/release.ts <pkgdir> <name> <version> [--publish]
//   without --publish: gates + expected hash + the exact commands (dry run)
//   with --publish: also publishes, verifies, links the name, freezes the lock, updates RELEASES.md,
//   regenerates the package README for the released version
// exit: 0 ok · 1 a gate or verification failed · 2 usage

import { appendFileSync, existsSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, relative, basename, resolve } from "node:path";
import { BEND, PkgError, ROOT, packageModules } from "./lib.ts";
import { hubHash, packageFiles } from "./hash.ts";

const USAGE = "usage: release.ts <pkgdir> <name(12-64 chars)> <a.b.c.d> [--publish]";
const usage = (msg: string): never => { console.error(`release: ${msg}\n${USAGE}`); process.exit(2); };
const env = { ...process.env, BEND_NO_TELEMETRY: "1" };
const sh = (cmd: string[], extra: Record<string, string> = {}) => {
  const p = Bun.spawnSync(cmd, { cwd: ROOT, env: { ...env, ...extra } });
  return { code: p.exitCode, out: (new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr)).trim() };
};
const fail = (msg: string): never => { console.error(`release: ${msg}`); process.exit(1); };

// The first line is the hub description and part of the permanent hash, so it must name the
// version being released; a stale `name@<v>` there would freeze the wrong description forever.
export function headerVersionError(pkg: string, name: string, version: string): string | null {
  const entry = join(pkg, "all.bend");
  if (!existsSync(entry)) return null;
  const first = readFileSync(entry, "utf8").split("\n", 1)[0] ?? "";
  const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const re = new RegExp(`(?:^|[^A-Za-z0-9-])${escaped}@(\\d+\\.\\d+\\.\\d+\\.\\d+)`, "g");
  const wrong = [...first.matchAll(re)].map((m) => m[1]).find((v) => v !== version);
  return wrong ? `${relative(ROOT, entry)}:1 names ${name}@${wrong}; the release target is ${name}@${version}` : null;
}

/** Regenerate the package README for `version`; run after `lock --freeze` so its since cells are final. */
export function regenerateIndex(pkg: string, name: string, version: string) {
  return sh([process.execPath, "tools/mathlib/index.ts", pkg, name, version]);
}

async function main(): Promise<void> {
  const [pkgArg, name, version] = process.argv.slice(2).filter((a) => !a.startsWith("--"));
  const doPublish = process.argv.includes("--publish");
  if (!pkgArg || !/^[a-z][a-z0-9-]{11,63}$/.test(name ?? "") || !/^\d+\.\d+\.\d+\.\d+$/.test(version ?? "")) {
    usage("need <pkgdir> <name(12-64 chars)> <a.b.c.d>");
  }
  const pkg = resolve(pkgArg);
  if (!existsSync(pkg)) {
    console.error(`release: package directory ${pkg} does not exist`);
    process.exit(1);
  }
  const header = headerVersionError(pkg, name, version);
  if (header) fail(header);

  const gates: [string, string[]][] = [
    ["check", [process.execPath, "tools/mathlib/check.ts", pkg]],
    ["lint", [process.execPath, "tools/mathlib/lint.ts", pkg, "--erasure"]],
    ["twins", [process.execPath, "tools/mathlib/twins.ts", pkg, "--check"]],
    ["comments", [process.execPath, "tools/comments.ts", ...["packages", "tools"].map((d) => join(ROOT, d))]],
    ["lock", [process.execPath, "tools/mathlib/lock.ts", pkg, "--check"]],
  ];
  for (const m of packageModules(pkg)) {
    gates.push(["lawcheck " + basename(m, ".bend"), [process.execPath, "tools/lawcheck/cli.ts", m, "--max-instances", "100"]]);
  }
  for (const [label, cmd] of gates) {
    const r = sh(cmd);
    console.log(`${r.code === 0 ? "ok  " : "FAIL"} ${label}`);
    if (r.code !== 0) fail(`${label} gate failed:\n${r.out}`);
  }

  const entry = join(pkg, "all.bend");
  let files: Record<string, string>;
  try { files = packageFiles(entry); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
  const expected = hubHash(files);
  console.log(`expected hash ${expected} (${Object.keys(files).length} files)`);
  const taken = await fetch(`https://hub.bend-lang.com/name/${name}@${version}`);
  if (taken.ok) fail(`${name}@${version} already exists on the hub`);

  if (!doPublish) {
    console.log(`dry run. commands:\n  bend ${relative(ROOT, entry)} --publish\n  bend link ${name}@${version} ${expected}`);
    return;
  }

  const pub = sh([BEND, entry, "--publish"]);
  const got = pub.out.match(/^(0x[0-9a-f]{32})$/m)?.[1];
  if (!got) fail(`publish did not print a hash:\n${pub.out}`);
  if (got !== expected) fail(`hub hash ${got} differs from the locally computed ${expected}`);
  console.log(`published ${got}`);

  const lib = mkdtempSync(join(tmpdir(), "bendlib-verify-"));
  const probe = join(lib, "probe.bend");
  writeFileSync(probe, `import Base\nimport ${got}/all.bend as P\n`);
  const v = sh([BEND, probe, "--check-only"], { BEND_LIB: join(lib, "lib") });
  if (v.out !== "All terms check.") fail(`fresh-cache verification of ${got} failed:\n${v.out}`);
  console.log("verified from an empty cache");

  const link = sh([BEND, "link", `${name}@${version}`, got]);
  if (link.code !== 0) fail(`bend link failed:\n${link.out}`);
  const named = (await (await fetch(`https://hub.bend-lang.com/name/${name}@${version}`)).text()).trim();
  if (named !== got) fail(`hub resolves ${name}@${version} to ${named}, expected ${got}`);
  console.log(`linked ${name}@${version} -> ${got}`);

  const freeze = sh([process.execPath, "tools/mathlib/lock.ts", pkg, "--freeze", version]);
  if (freeze.code !== 0) fail(`lock freeze failed:\n${freeze.out}`);
  // freeze rewrites the lock's since column, so the README is only correct after this step.
  const idx = regenerateIndex(pkg, name, version);
  if (idx.code !== 0) fail(`index regeneration for ${version} failed:\n${idx.out}`);
  const compiler = sh([BEND, "version"]).out;
  const rel = join(ROOT, "RELEASES.md");
  if (!existsSync(rel)) writeFileSync(rel, "# Releases\n\n| package | version | hash | compiler | date |\n|---|---|---|---|---|\n");
  appendFileSync(rel, `| ${name} | ${version} | \`${got}\` | ${compiler} | ${new Date().toISOString().slice(0, 10)} |\n`);
  console.log(`regenerated ${relative(ROOT, join(pkg, "README.md"))}; recorded in RELEASES.md; tag with: git tag ${name}-v${version}`);
}

if (import.meta.main) await main();
