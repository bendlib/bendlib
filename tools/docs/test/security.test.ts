// Hardening of untrusted hub input: HTML escaping, path containment, name validation,
// cached-manifest verification and a bounded fetch. Real code paths, no network for 1–4.

import { describe, expect, test } from "bun:test";
import { existsSync, mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, sep } from "node:path";
import { ensurePackage, fetchHub, safePath, seedNames, sha256, underRoot, validNameRecords, type NameRecord } from "../src/hub.ts";
import { modPage, encPath, renderModule, renderPackage } from "../src/render.ts";
import type { Module, Package, Site } from "../src/model.ts";

const HASH = "0x" + "a".repeat(32);

const mod = (path: string): Module => ({ path, header: null, source: null, imports: [], foreign: [], decls: [], error: null, status: null, provedIn: {} });
const pkg = (modules: Module[]): Package => ({
  hash: HASH, ts: 0, desc: "", bytes: 0, files: modules.map((m) => ({ path: m.path, bytes: 1 })),
  names: [], licenses: [], modules, deps: [], rdeps: [], status: null,
  counts: { laws: 0, proved: 0, defs: 0, types: 0, decls: 0 },
});
const site = (p: Package): Site => {
  const g = { key: `files:${p.hash}`, latest: p, members: [p] };
  return {
    built: "2026-01-01T00:00:00Z", compiler: "2.0.27", checked: true, partial: false, local: false,
    packages: [p], byHash: new Map([[p.hash, p]]), groups: [g], groupOf: new Map([[p.hash, g]]), fetchFails: [], names: [],
  };
};

describe("hub filenames cannot inject HTML", () => {
  test("a hostile module path renders escaped, not as a tag or attribute", () => {
    const tag = "a<script>alert(1)</script>.bend";
    const attr = 'x" onmouseover="alert(1).bend';
    const p = pkg([mod(tag), mod(attr)]);
    const s = site(p);
    const html = renderPackage(s, p) + renderModule(s, p, p.modules[0]) + renderModule(s, p, p.modules[1]);
    expect(html).not.toContain("<script>alert(1)</script>");
    expect(html).not.toContain('onmouseover="alert(1)');
    expect(html).toContain("&lt;script&gt;alert(1)&lt;/script&gt;");
    expect(html).toContain("onmouseover=&quot;alert(1)");
  });
});

describe("a .. module path cannot escape --out", () => {
  test("underRoot refuses traversal and safePath rejects hostile manifest paths", () => {
    const out = mkdtempSync(join(tmpdir(), "bend-docs-out-"));
    expect(() => underRoot(out, `pkg/${HASH}/../../../evil.html`)).toThrow();
    expect(() => underRoot(out, "../evil.html")).toThrow();
    expect(() => underRoot(out, "/etc/passwd")).toThrow();
    expect(underRoot(out, `pkg/${HASH}/nat.bend.html`).startsWith(out + sep)).toBe(true);
    expect(safePath("../evil.bend")).toBe(false);
    expect(safePath('x" onmouseover=".bend')).toBe(false);
    expect(safePath("a<script>.bend")).toBe(false);
    expect(safePath("a\tb.bend")).toBe(false);
    expect(safePath("list.bend")).toBe(true);
    expect(safePath("sub/dir.bend")).toBe(true);
  });
});

describe("seedNames validates names", () => {
  const rec = (name: string, version: string): NameRecord => ({
    name, owner_login: "o", ts: 0,
    latest: { version, hash: HASH, ts: 0, desc: "" },
    versions: [{ version, hash: HASH, ts: 0 }],
  });
  test("an invalid name or version writes nothing", () => {
    const lib = mkdtempSync(join(tmpdir(), "bend-docs-lib-"));
    seedNames(lib, [rec("../../escape", "1.2.3.4"), rec("BadName", "1.2.3.4"), rec("valid-package-name", "1.2.3.4/../..")]);
    expect(existsSync(join(lib, "names"))).toBe(false);
    seedNames(lib, [rec("valid-package-name", "1.2.3.4")]);
    expect(existsSync(join(lib, "names", "valid-package-name@1.2.3.4"))).toBe(true);
  });
});

describe("a torn or hostile cached manifest is not trusted", () => {
  const cacheDir = () => {
    const cache = mkdtempSync(join(tmpdir(), "bend-docs-cache-"));
    mkdirSync(join(cache, "manifests"), { recursive: true });
    return cache;
  };
  test("ensurePackage rejects a manifest that does not hash to its name", async () => {
    const cache = cacheDir();
    writeFileSync(join(cache, "manifests", HASH), "torn");
    await expect(ensurePackage(HASH, join(cache, "lib"), cache)).rejects.toThrow(/corrupt/);
  });
  test("ensurePackage rejects a valid-hash manifest with an unsafe path", async () => {
    const cache = cacheDir();
    const text = `${"0".repeat(64)} ../evil.bend\n`;
    const hash = "0x" + sha256(text).slice(0, 32);
    writeFileSync(join(cache, "manifests", hash), text);
    await expect(ensurePackage(hash, join(cache, "lib"), cache)).rejects.toThrow(/unsafe path/);
  });
});

describe("hub fetches are bounded", () => {
  test("a stalled fetch rejects within the timeout", async () => {
    const server = Bun.serve({ port: 0, fetch: () => new Promise<Response>(() => {}) });
    try {
      const t0 = performance.now();
      await expect(fetchHub(`http://127.0.0.1:${server.port}/`, 150)).rejects.toThrow();
      expect(performance.now() - t0).toBeLessThan(5000);
    } finally {
      server.stop(true);
    }
  });
});

describe("hub names are validated (PLAN F1)", () => {
  const rec = (name: string, versions: { version: string; hash: string }[]): NameRecord => ({
    name, owner_login: "o", ts: 0, latest: { version: versions[0]?.version ?? "1.0.0.0", hash: versions[0]?.hash ?? HASH, ts: 0, desc: "" },
    versions: versions.map((v) => ({ ...v, ts: 0 })),
  });
  test("planted negative: a hostile name is dropped, a valid one is kept", () => {
    const kept = validNameRecords([
      rec("../index", [{ version: "1.0.0.0", hash: HASH }]),
      rec("valid-package-name", [{ version: "1.0.0.0", hash: HASH }]),
    ]);
    expect(kept.map((n) => n.name)).toEqual(["valid-package-name"]);
  });
  test("planted negative: a record whose versions are all malformed is dropped", () => {
    expect(validNameRecords([rec("valid-package-name", [{ version: "1.0", hash: "0xzz" }])])).toEqual([]);
  });
});

describe("module paths in links are URL-encoded", () => {
  test("planted negative: # becomes %23, and / separators survive", () => {
    expect(modPage(HASH, "a#b.bend")).toBe(`pkg/${HASH}/a%23b.bend.html`);
    expect(encPath("sub/a b#c.bend")).toBe("sub/a%20b%23c.bend");
  });
  test("a rendered package page links the encoded module URL, never the raw one", () => {
    const p = pkg([mod("a#b.bend")]);
    const html = renderPackage(site(p), p);
    expect(html).toContain(`href="a%23b.bend.html"`);
    expect(html).not.toContain(`href="a#b.bend.html"`);
  });
});
