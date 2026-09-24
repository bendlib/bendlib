// searchindex: the compact JSON the search page loads. Declarations are rows of
// [file, name, kind, anchor, doc, lhs, rhs, proved] with files and packages interned.

import { declIds, modPage } from "./render.ts";
import { label, type Site } from "./model.ts";

export type SearchIndex = {
  v: 1; built: string; compiler: string;
  p: [string, string][];                 // [label, hash]
  f: [number, string, string][];         // [package, path, module page]
  d: [number, string, string, string, string, string, string, number][]; // proved: 1 yes, 0 open, -1 not a law
};

const DOC_MAX = 160;

export function buildSearchIndex(site: Site): SearchIndex {
  const idx: SearchIndex = { v: 1, built: site.built, compiler: site.compiler, p: [], f: [], d: [] };
  site.packages.forEach((p, pi) => {
    idx.p.push([label(p), p.hash]);
    for (const m of p.modules) {
      if (m.decls === null) continue;
      const fi = idx.f.length;
      idx.f.push([pi, m.path, modPage(p.hash, m.path)]);
      const ids = declIds(m);
      for (const d of m.decls) {
        const id = ids.get(d);
        if (id === undefined) continue;
        const doc = (d.doc ?? "").replace(/\s+/g, " ").trim();
        idx.d.push([fi, d.name, d.kind, id, doc.length > DOC_MAX ? doc.slice(0, DOC_MAX - 1) + "…" : doc,
          d.statement?.lhs ?? "", d.statement?.rhs ?? "", d.kind === "law" ? (d.proved ? 1 : 0) : -1]);
      }
    }
  });
  return idx;
}
