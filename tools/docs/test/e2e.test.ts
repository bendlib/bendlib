// End to end on the live hub: builds three real packages with a fresh cache (fetch,
// verify, extract, check on the installed bend) and inspects the generated site.

import { beforeAll, describe, expect, test } from "bun:test";
import { existsSync, mkdtempSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { compile, matchStatement } from "../src/shape.ts";
import type { SearchIndex } from "../src/searchindex.ts";
import { hubHash, packageFiles } from "../../mathlib/hash.ts";

const MATHLIB = "0xafc61ca8b7738a6df7f28eddf80168f8";   // bend-mathlib@0.1.0.1
const TENSORS = "0x39d8166231e68361eb37e8bef9287b8a";   // bend-tensors@0.0.0.2
const ANON = "0x6648eb78d8a978a0e437eabbfbc841cd";      // anonymous; imports 0xe49a3e65…/parse.bend
const PARSE = "0xe49a3e6521e1b71e55654a885f27bcc1";

const root = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-e2e-"));
const out = join(root, "dist");
let log = "";
const read = (p: string) => readFileSync(join(out, p), "utf8");

beforeAll(() => {
  const p = Bun.spawnSync([process.execPath, join(import.meta.dir, "..", "build.ts"),
    "--only", `bend-mathlib@0.1.0.1,bend-tensors@0.0.0.2,${ANON}`, "--out", out, "--cache", join(root, "cache"), "--jobs", "4"]);
  log = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
  if (p.exitCode !== 0) throw new Error(`build exited ${p.exitCode}:\n${log}`);
}, 600_000);

describe("three-package build from the live hub", () => {
  test("pages exist for every package, module and name", () => {
    for (const f of ["index.html", "search.html", "search-index.json", "assets/style.css", "assets/search.js", "assets/site.js",
      `pkg/${MATHLIB}/index.html`, `pkg/${MATHLIB}/nat.bend.html`, `pkg/${MATHLIB}/list.bend.html`,
      `pkg/${TENSORS}/index.html`, `pkg/${TENSORS}/bend_tensors.bend.html`,
      `pkg/${ANON}/index.html`, `pkg/${ANON}/format.bend.html`, "name/bend-mathlib/index.html", "name/bend-tensors/index.html"]) {
      expect(existsSync(join(out, f))).toBe(true);
    }
    expect(log).toContain("packages   3 (2 carry a name@version)");
    expect(log).toContain("fetch: 3 new packages fetched and verified");
  });

  test("the author page exists and the site nav links to it", () => {
    const html = read("authors.html");
    expect(html).toContain("Document your package");
    expect(html).toContain("What the site reads");
    expect(read("index.html")).toContain('href="authors.html">Authors</a>');
  });

  test("add_comm appears with its statement, doc, anchor and proved marker", () => {
    const html = read(`pkg/${MATHLIB}/nat.bend.html`);
    const at = html.indexOf('<section class="decl" id="add_comm"');
    expect(at).toBeGreaterThan(0);
    const sec = html.slice(at, html.indexOf("</section>", at));
    expect(sec).toContain("{Nat.add(n, m) == Nat.add(m, n) : Nat}");
    expect(sec).toContain("Addition is commutative: n + m = m + n.");
    expect(sec).toContain('<span class="pr pr-yes">proved</span>');
    expect(sec).toContain(`https://hub.bend-lang.com/${MATHLIB}/nat.bend`);
  });

  test("a module's header comment is rendered on its page", () => {
    expect(read(`pkg/${MATHLIB}/all.bend.html`)).toContain("machine-checked lemmas for Bend 2");
  });

  test("each declaration links to the module source page at its own line", () => {
    expect(read(`pkg/${MATHLIB}/nat.bend.src.html`)).toContain('id="L1"');
    const html = read(`pkg/${MATHLIB}/nat.bend.html`);
    const at = html.indexOf('<section class="decl" id="add_comm"');
    const sec = html.slice(at, html.indexOf("</section>", at));
    const href = sec.match(/href="([^"]*nat\.bend\.src\.html#L(\d+))"/);
    const line = sec.match(/source · line (\d+)/);
    expect(href).not.toBeNull();
    expect(line).not.toBeNull();
    expect(href![2]).toBe(line![1]);
  });

  test("llms.txt and lemmas.txt list every latest proved law as 3 tab-separated fields", () => {
    const llms = read("llms.txt");
    expect(llms).toContain("[bend-mathlib@0.1.0.1](");
    const lemmas = read("lemmas.txt");
    expect(lemmas.startsWith("# ")).toBe(true);
    const lines = lemmas.split("\n").filter((l) => l !== "" && !l.startsWith("#"));
    expect(lines.some((l) => l.startsWith("bend-mathlib@0.1.0.1/nat.bend\tadd_comm\t"))).toBe(true);
    for (const l of lines) expect(l.split("\t").length).toBe(3);
    // Expected line count = proved claim rows in search-index.json (same latest-lineage scope).
    const idx = JSON.parse(read("search-index.json")) as SearchIndex;
    expect(lines.length).toBe(idx.d.filter((r) => r[2] === "law" && r[7] === 1).length);
  });

  test("the index lists the three packages, named ones first, with statuses from the real checker", () => {
    const html = read("index.html");
    const [m, t, a] = ['bend-mathlib</a> <span class="pill">@0.1.0.1</span>', 'bend-tensors</a> <span class="pill">@0.0.0.2</span>', `${ANON.slice(0, 10)}…</a>`].map((s) => html.indexOf(`>${s}`));
    expect(m).toBeGreaterThan(0);
    expect(t).toBeGreaterThan(0);
    expect(a).toBeGreaterThan(Math.max(m, t));
    expect(read(`pkg/${MATHLIB}/index.html`)).toMatch(/<h1>bend-mathlib@0\.1\.0\.1 <span class="st st-checks">/);
    expect(read(`pkg/${TENSORS}/index.html`)).toMatch(/<h1>bend-tensors@0\.0\.0\.2 <span class="st st-unsafe">/);
  });

  test("the anonymous package shows its real hub dependency", () => {
    const html = read(`pkg/${ANON}/index.html`);
    const deps = html.slice(html.indexOf('id="deps"'), html.indexOf('id="rdeps"'));
    expect(deps).toContain(PARSE);
    expect(deps).toContain(`format.bend: import ${PARSE}/parse.bend as P`);
    expect(deps).toContain("not in this build");
  });

  test("law-shape search over the generated index finds append_nil and not nil_append", () => {
    const idx = JSON.parse(read("search-index.json")) as SearchIndex;
    const hits = (q: string) => {
      const p = compile(q);
      return idx.d.filter((r) => r[5] !== "" && matchStatement(p, r[5], r[6])).map((r) => `${idx.p[idx.f[r[0]][0]][0]}:${r[1]}`);
    };
    const h = hits("List.append(_, Nil{})");
    expect(h).toContain("bend-mathlib@0.1.0.1:append_nil");
    expect(h).not.toContain("bend-mathlib@0.1.0.1:nil_append");
    expect(hits("Nat.add(_, 0n)")).toContain("bend-mathlib@0.1.0.1:add_zero");
    expect(hits("Nat.add(_, 0n)")).not.toContain("bend-mathlib@0.1.0.1:zero_add");
    const row = idx.d.find((r) => r[1] === "append_nil" && idx.f[r[0]][1] === "list.bend")!;
    expect(existsSync(join(out, idx.f[row[0]][2]))).toBe(true);
    expect(read(idx.f[row[0]][2])).toContain(`id="${row[3]}"`);
  });

  test("every link is relative, or points at the hub or the source repository", () => {
    for (const f of ["index.html", "search.html", `pkg/${MATHLIB}/index.html`, `pkg/${MATHLIB}/nat.bend.html`, `pkg/${MATHLIB}/nat.bend.src.html`, "name/bend-mathlib/index.html"]) {
      for (const [, href] of read(f).matchAll(/(?:href|src)="([^"]*)"/g)) {
        if (/^https:\/\/(hub\.bend-lang\.com|github\.com\/bendlib\/bendlib)\b/.test(href)) continue;
        expect(href).not.toMatch(/^(\/|[a-z]+:)/);
      }
    }
  });

  test("every page carries the footer, and the compiler version", () => {
    for (const f of ["index.html", "search.html", `pkg/${ANON}/format.bend.html`]) {
      const html = read(f);
      expect(html).toContain("Community docs for BendHub packages · not affiliated with Higher Order Company · source");
      expect(html).toContain("on bend 2.0.27 only");
    }
  });
});

describe("--local preview", () => {
  test("stages an unpublished package, banners every page, and prints the package page path", () => {
    const entry = join(import.meta.dir, "..", "..", "mathlib", "fixtures", "good", "list.bend");
    const dir = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-local-"));
    const p = Bun.spawnSync([process.execPath, join(import.meta.dir, "..", "build.ts"),
      "--local", entry, "--out", dir, "--cache", join(dir, "cache")]);
    const msg = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
    if (p.exitCode !== 0) throw new Error(`build exited ${p.exitCode}:\n${msg}`);
    const hash = hubHash(packageFiles(entry));
    expect(existsSync(join(dir, "pkg", hash, "index.html"))).toBe(true);
    expect(readFileSync(join(dir, "pkg", hash, "index.html"), "utf8")).toContain("Local preview of an unpublished package — not on BendHub.");
    expect(readFileSync(join(dir, "pkg", hash, "list.bend.html"), "utf8")).toContain("Appending the empty list on the right changes nothing.");
    expect(msg).toContain(`local package page: pkg/${hash}/index.html`);
  }, 120_000);

  test("--local rejects a missing path and a directory with a typed usage error", () => {
    const dir = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-local-bad-"));
    for (const bad of [join(dir, "nope.bend"), dir]) {
      const p = Bun.spawnSync([process.execPath, join(import.meta.dir, "..", "build.ts"), "--local", bad]);
      const msg = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
      expect(p.exitCode).toBe(2);
      expect(msg).toContain(`build: --local: ${bad} is not a file`);
      expect(msg).toContain("usage: bun tools/docs/build.ts");
      expect(msg).not.toContain("ENOENT");
      expect(msg).not.toContain("EISDIR");
    }
  });
});
