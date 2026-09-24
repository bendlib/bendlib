// Golden decl dumps: the cases, how a dump is normalized, and (run directly)
// regeneration. Regenerated goldens must be reviewed by hand before commit.
// usage: bun tools/reader/test/golden.ts   (rewrites test/golden/*.json)

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { decls, load, type Decl } from "../src/reader.ts";

export const REPO = path.resolve(import.meta.dir, "../../..");
export const GOLDEN = path.join(import.meta.dir, "golden");
export const HUB_PKG = "0x085d89db9ee8a21865e959816bb20e5b";

export type Case = { name: string; file: string; hub?: boolean };

export const CASES: Case[] = [
  { name: "glist", file: "research/experiments/glist.bend" },
  { name: "algebra", file: "research/experiments/lib/algebra.bend" },
  { name: "order", file: "research/experiments/v1/order.bend" },
  { name: "hub_list", file: "tools/reader/test/fixtures/hub_list.bend", hub: true },
];

export function freshBendLib(): string {
  return fs.mkdtempSync(path.join(os.tmpdir(), "bendlib-reader-lib-"));
}

export function normalize(ds: Decl[], bendLib?: string): Decl[] {
  const rel = (p: string) => bendLib !== undefined && p.startsWith(bendLib + "/")
    ? "$BEND_LIB/" + p.slice(bendLib.length + 1)
    : path.relative(REPO, p);
  return ds.map((d) => ({ ...d, file: rel(d.file), ...(d.effects ? { effects: d.effects.map(rel) } : {}) }));
}

export async function dump(c: Case): Promise<{ version: string; decls: Decl[] }> {
  const bendLib = c.hub ? fs.realpathSync(freshBendLib()) : undefined;
  const L = await load(path.join(REPO, c.file), { bendLib });
  return { version: L.source.version, decls: normalize(decls(L, { scope: "all-non-base" }), bendLib) };
}

export function goldenPath(c: Case): string {
  return path.join(GOLDEN, c.name + ".json");
}

if (import.meta.main) {
  for (const c of CASES) {
    const d = await dump(c);
    fs.writeFileSync(goldenPath(c), JSON.stringify({ bend: d.version, file: c.file, decls: d.decls }, null, 2) + "\n");
    console.log(`wrote ${path.relative(REPO, goldenPath(c))}: ${d.decls.length} decls`);
  }
}
