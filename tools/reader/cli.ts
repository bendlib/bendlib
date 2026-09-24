#!/usr/bin/env bun
// bend-reader: list the declarations of a Bend 2 file, parsed by the official
// bend.ts of the installed compiler's version.
// usage: bun tools/reader/cli.ts <file.bend> [--json] [--all] [--check]
//          [--bend-src <dir>] [--bend-lib <dir>]
//   --all       also list imported (non-Base) declarations
//   --check     also type-check (bend.ts book_valid) before listing
//   --bend-src  use a local bend checkout (else BENDLIB_BEND_SRC, else the cached tag)
//   --bend-lib  BEND_LIB for hub packages
// exit: 0 listed, 1 load/parse/check error (located on stderr), 2 usage error

import * as path from "node:path";
import { BendReadError, decls, load, type Decl } from "./src/reader.ts";
import { SourceError } from "./src/source.ts";

const USAGE = "usage: bun tools/reader/cli.ts <file.bend> [--json] [--all] [--check] [--bend-src <dir>] [--bend-lib <dir>]";

function parseArgs(argv: string[]) {
  const o = { file: "", json: false, all: false, check: false, src: undefined as string | undefined, lib: undefined as string | undefined };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--json") o.json = true;
    else if (a === "--all") o.all = true;
    else if (a === "--check") o.check = true;
    else if (a === "--bend-src" || a === "--bend-lib") {
      const v = argv[++i];
      if (v === undefined) usage(`${a} needs a directory`);
      if (a === "--bend-src") o.src = v; else o.lib = v;
    } else if (a === "-h" || a === "--help") {
      console.log(USAGE);
      process.exit(0);
    } else if (a.startsWith("-")) usage(`unknown flag ${a}`);
    else if (o.file === "") o.file = a;
    else usage(`one file only (got ${o.file} and ${a})`);
  }
  if (o.file === "") usage("no file given");
  return o;
}

function usage(msg: string): never {
  process.stderr.write(`bend-reader: ${msg}\n${USAGE}\n`);
  process.exit(2);
}

function table(ds: Decl[], cwd: string): string {
  const rows = ds.map((d) => {
    const tag = d.kind === "law" ? (d.proved ? "law" : "law?") : d.kind;
    const where = `${path.relative(cwd, d.file)}:${d.line}`;
    return [tag, d.name, where, d.signature];
  });
  const w = [0, 1, 2].map((j) => Math.max(...rows.map((r) => r[j].length), 4));
  const lines = rows.map((r) => r.map((c, j) => (j < 3 ? c.padEnd(w[j]) : c)).join("  "));
  return ["kind".padEnd(w[0]) + "  " + "name".padEnd(w[1]) + "  " + "at".padEnd(w[2]) + "  signature", ...lines].join("\n");
}

const o = parseArgs(process.argv.slice(2));
try {
  const L = await load(o.file, { src: o.src, bendLib: o.lib, check: o.check });
  const ds = decls(L, { scope: o.all ? "all-non-base" : "own" });
  if (o.json) {
    console.log(JSON.stringify({ bend: L.source.version, source: L.source.origin, file: L.file, decls: ds }, null, 2));
  } else {
    console.log(`# ${path.relative(process.cwd(), L.file)} — bend ${L.source.version} (${L.source.origin} source), ${ds.length} declarations` + (L.checked ? ", checked" : ""));
    console.log(table(ds, process.cwd()));
    console.log("# law? = open (unproved) law");
  }
} catch (e) {
  if (e instanceof BendReadError || e instanceof SourceError) {
    process.stderr.write(e.message + "\n");
    process.exit(1);
  }
  throw e;
}
