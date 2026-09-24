// imports: read a .bend file's import header the way bend.ts book_load does,
// and turn cross-package imports into package dependency edges.

import { posix } from "node:path";

export type Import = {
  line: number;          // 1-based
  raw: string;           // the trimmed source line
  path: string;          // as written ("Base" for `import Base`)
  alias: string | null;
  kind: "base" | "relative" | "hash" | "named" | "invalid";
  hash?: string;         // hash and named imports: the target package ("0x…"), once resolved
  named?: string;        // named imports: "<name>@<version>"
  target?: string;       // the imported file's path inside its package
};

const NAMED = /^([a-z][a-z0-9-]{11,63})@((?:0|[1-9][0-9]*)(?:\.(?:0|[1-9][0-9]*)){3})$/;

/** Import lines of the leading header (blank and `#` lines allowed), as bend.ts reads them. */
export function parseImports(text: string): Import[] {
  const out: Import[] = [];
  const lines = text.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    if (/^import(\s.*|)$/.test(line)) {
      const h = line.slice(6).match(/^\s+(\S+)(?:\s+as\s+([A-Za-z_][A-Za-z0-9_]*))?\s*(?:#.*)?$/);
      if (h === null || (h[2] === undefined && h[1] !== "Base")) {
        out.push({ line: i + 1, raw: line, path: h?.[1] ?? "", alias: null, kind: "invalid" });
        continue;
      }
      out.push(classify(i + 1, line, h[1], h[2] ?? null));
      continue;
    }
    if (line !== "" && !line.startsWith("#")) break;
  }
  return out;
}

function classify(line: number, raw: string, p: string, alias: string | null): Import {
  if (alias === null) return { line, raw, path: p, alias, kind: "base" };
  const rel = posix.normalize(p);
  const nv = rel.match(/^([^/]*@[^/]*)\//);
  if (nv !== null) {
    return NAMED.test(nv[1])
      ? { line, raw, path: p, alias, kind: "named", named: nv[1], target: rel.slice(nv[1].length + 1) }
      : { line, raw, path: p, alias, kind: "invalid" };
  }
  const hm = rel.match(/^(0x[0-9a-f]+)\/(.+)$/);
  if (hm !== null) return { line, raw, path: p, alias, kind: "hash", hash: hm[1], target: hm[2] };
  return { line, raw, path: p, alias, kind: "relative" };
}

// bend joins a relative import onto the file's directory inside BEND_LIB, so `../` can reach another package.
/** The package a relative import lands in when it climbs out of its own package, or null when it stays inside. */
export function relativeEscape(fromPath: string, imp: string): { hash: string; target: string } | null {
  const joined = posix.normalize(posix.join("/pkg", posix.dirname(fromPath), imp));
  if (joined.startsWith("/pkg/")) return null;
  const m = joined.match(/^\/(0x[0-9a-f]+)\/(.+)$/);
  return m === null ? { hash: "", target: joined } : { hash: m[1], target: m[2] };
}

export type Edge = { from: string; to: string; via: string; named?: string };

/** Package-level dependency edges; `resolveName` maps "<name>@<version>" to a hash (or null when unknown). */
export function dependencyEdges(
  pkgs: { hash: string; files: { path: string; imports: Import[] }[] }[],
  resolveName: (nv: string) => string | null,
): Edge[] {
  const edges = new Map<string, Edge>();
  for (const p of pkgs) {
    for (const f of p.files) {
      for (const imp of f.imports) {
        let to: string | null = null;
        let named: string | undefined;
        if (imp.kind === "hash") to = imp.hash!;
        else if (imp.kind === "named") {
          named = imp.named!;
          to = resolveName(named);
          if (to !== null) imp.hash = to;
        } else if (imp.kind === "relative") to = relativeEscape(f.path, imp.path)?.hash || null;
        if (to === null || to === p.hash) continue;
        const key = `${p.hash} ${to}`;
        if (!edges.has(key)) edges.set(key, { from: p.hash, to, via: `${f.path}: ${imp.raw}`, ...(named ? { named } : {}) });
      }
    }
  }
  return [...edges.values()];
}

/** Foreign files a def pulls in with `import "<file>"` inside its body (effects, .c/.js). */
export function foreignImports(text: string): string[] {
  const out = new Set<string>();
  for (const m of text.matchAll(/^\s+import\s+"([^"]+)"/gm)) out.add(m[1]);
  return [...out];
}
