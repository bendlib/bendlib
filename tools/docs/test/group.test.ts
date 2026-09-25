// Package lineages: one index row per name, or per identical anonymous re-upload.

import { expect, test } from "bun:test";
import { groupPackages, type Package } from "../src/model.ts";

const pkg = (hash: string, ts: number, files: string[], desc: string, name?: [string, string]): Package => ({
  hash, ts, desc, bytes: 0, files: files.map((path) => ({ path, bytes: 1 })),
  names: name ? [{ name: name[0], version: name[1], owner: "o", ts }] : [],
  licenses: [], modules: [], deps: [], rdeps: [], status: null,
  counts: { laws: 0, proved: 0, defs: 0, types: 0, decls: 0 },
});

test("named versions merge and the highest version is the latest, not the newest upload", () => {
  const a = pkg("0xa", 1, ["m.bend"], "d", ["lib-one-two-three", "0.1.0.10"]);
  const b = pkg("0xb", 2, ["m.bend"], "d", ["lib-one-two-three", "0.1.0.9"]);
  const gs = groupPackages([a, b]);
  expect(gs.length).toBe(1);
  expect(gs[0].latest.hash).toBe("0xa");
  expect(gs[0].members.map((m) => m.hash)).toEqual(["0xa", "0xb"]);
});

test("anonymous re-uploads with the same files and description merge; different ones do not", () => {
  const gs = groupPackages([pkg("0x1", 1, ["x.bend"], "same"), pkg("0x2", 5, ["x.bend"], "same"), pkg("0x3", 3, ["x.bend"], "other")]);
  expect(gs.length).toBe(2);
  const g = gs.find((x) => x.members.length === 2)!;
  expect(g.latest.hash).toBe("0x2");
});

test("a named release outranks a newer identical anonymous upload", () => {
  const named = pkg("0xn", 1, ["a.bend", "LICENSE"], "d", ["named-package-x", "1.0.0.0"]);
  const anon = pkg("0xq", 5, ["LICENSE", "a.bend"], "d");
  const gs = groupPackages([named, anon]);
  expect(gs.length).toBe(1);
  expect(gs[0].latest.hash).toBe("0xn");
});

test("an anonymous upload identical to a named package joins its lineage", () => {
  const gs = groupPackages([pkg("0xn", 2, ["a.bend", "LICENSE"], "d", ["named-package-x", "1.0.0.0"]), pkg("0xq", 1, ["LICENSE", "a.bend"], "d")]);
  expect(gs.length).toBe(1);
  expect(gs[0].latest.hash).toBe("0xn");
  expect(gs[0].members.length).toBe(2);
});

test("4000 packages group well under 100 ms", () => {
  const many = Array.from({ length: 4000 }, (_, i) =>
    pkg(`0x${i.toString(16).padStart(32, "0")}`, i + 1, [`m${i}.bend`], `d${i}`, [`pkg-name-${String(i).padStart(6, "0")}`, "1.0.0.0"]));
  const t0 = performance.now();
  const gs = groupPackages(many);
  const ms = performance.now() - t0;
  expect(gs.length).toBe(4000);
  expect(ms).toBeLessThan(100);
});
