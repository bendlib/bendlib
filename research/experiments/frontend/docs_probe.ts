// usage: BEND_SRC=<bendlang/bend checkout at the installed version> bun docs_probe.ts <file.bend>
const Bend: any = await import((process.env.BEND_SRC ?? "../bendsrc") + "/bend2/bend.ts");
const file = process.argv[2];
const book: any = (Bend as any).book_nil();
const seen = new Map<string, string | null>();
const n0 = await (Bend as any).book_load(book, file, "", seen);
let shown = 0;
for (const k of book.order) {
  const t = book.tlds[k];
  if (t.b) continue;               // skip Base
  const kind = t.$ === "ADT" ? "type" : (t.v === null ? "law(open)" : "def");
  console.log(kind.padEnd(9), k, ":", (Bend as any).term_show(t.T).slice(0, 110));
  if (++shown > 14) break;
}
console.log("namespaces:", [...seen.values()].filter(Boolean).join(", "));
