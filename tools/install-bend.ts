// install-bend: install the exact Bend release pinned in toolchain.json into ~/.bend
// (or $BEND_HOME), verifying the archive's sha256. Used by CI; safe to run locally.
//
// usage: bun tools/install-bend.ts

import { createHash } from "node:crypto";
import { cpSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { homedir, tmpdir } from "node:os";
import { join } from "node:path";

const pin = JSON.parse(readFileSync(join(import.meta.dir, "..", "toolchain.json"), "utf8")).bend;
const os = process.platform === "darwin" ? "darwin" : "linux";
const arch = process.arch === "arm64" ? "arm64" : "x64";
const archive = pin.archives[`${os}-${arch}`];
if (!archive) { console.error(`no pinned archive for ${os}-${arch}`); process.exit(2); }

const url = `https://github.com/bendlang/bend/releases/download/v${pin.version}/${archive.file}`;
const res = await fetch(url);
if (!res.ok) { console.error(`download failed: ${url} (${res.status})`); process.exit(1); }
const bytes = Buffer.from(await res.arrayBuffer());
const sum = createHash("sha256").update(bytes).digest("hex");
if (sum !== archive.sha256) { console.error(`sha256 mismatch for ${archive.file}: ${sum}`); process.exit(1); }

const tmp = mkdtempSync(join(tmpdir(), "bend-install-"));
writeFileSync(join(tmp, archive.file), bytes);
const tar = Bun.spawnSync(["tar", "-xzf", join(tmp, archive.file), "-C", tmp]);
if (tar.exitCode !== 0) { console.error(new TextDecoder().decode(tar.stderr)); process.exit(1); }
const home = process.env.BEND_HOME ?? join(homedir(), ".bend");
mkdirSync(join(home, "bin"), { recursive: true });
for (const d of ["bend2", "guide"]) cpSync(join(tmp, "bend", d), join(home, d), { recursive: true, force: true });
cpSync(join(tmp, "bend", "bin", "bend"), join(home, "bin", "bend"), { force: true });
console.log(`installed bend ${pin.version} (${os}-${arch}, sha256 verified) into ${home}`);
