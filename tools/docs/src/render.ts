// render: static HTML pages with relative links only, so the site works under
// any path prefix (a Pages project path today, a domain root later).

import { posix } from "node:path";
import type { DocDecl } from "./extract.ts";
import type { Edge } from "./imports.ts";
import { HUB } from "./hub.ts";
import { groupPackages, label, published, shortHash, type Module, type Package, type Site } from "./model.ts";
import type { FileClass } from "./status.ts";

export const esc = (s: string) => s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]!);

export const pkgPage = (hash: string) => `pkg/${hash}/index.html`;
export const modPage = (hash: string, path: string) => `pkg/${hash}/${path}.html`;
export const namePage = (name: string) => `name/${name}/index.html`;

function rel(from: string, to: string): string {
  const r = posix.relative(posix.dirname(from), to);
  return r === "" ? posix.basename(to) : r;
}

const date = (ts: number) => new Date(ts).toISOString().slice(0, 10);

const STATUS_TEXT: Record<FileClass, string> = {
  checks: "checks", unsafe: "relies on unsafe/foreign", open: "open laws/TODOs", fails: "fails", timeout: "timeout",
};

function statusBadge(c: FileClass | null, title = ""): string {
  if (c === null) return `<span class="st st-none" title="not checked in this build">not checked</span>`;
  return `<span class="st st-${c}"${title ? ` title="${esc(title)}"` : ""}>${STATUS_TEXT[c]}</span>`;
}

const kindBadge = (k: string) => `<span class="k k-${k}">${k}</span>`;

function docHtml(doc: string | null): string {
  if (doc === null || doc.trim() === "") return "";
  const inline = (s: string) => esc(s).replace(/`([^`]+)`/g, "<code>$1</code>");
  return `<div class="doc">${doc.split(/\n\s*\n/).map((p) => `<p>${inline(p)}</p>`).join("")}</div>`;
}

export function anchor(name: string): string {
  return name.replace(/[^A-Za-z0-9_.-]/g, "-");
}

type PageOpts = { path: string; title: string; body: string; site: Site; scripts?: string[]; description?: string };

export function page(o: PageOpts): string {
  const r = (p: string) => rel(o.path, p);
  const scripts = (o.scripts ?? []).map((s) => `<script src="${r(s)}" defer></script>`).join("");
  const partial = o.site.partial ? ` · partial build (a subset of the hub): dependents and counts cover only the packages built` : "";
  return `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>${esc(o.title)}</title>
<meta name="description" content="${esc(o.description ?? "Documentation for every package on BendHub, the Bend 2 package hub.")}">
<meta name="color-scheme" content="light">
<link rel="stylesheet" href="${r("assets/style.css")}">${scripts}
</head><body>
<a class="skip" href="#main">Skip to content</a>
<header class="top"><div class="wrap">
<a class="brand" href="${r("index.html")}">~/bend-docs<span class="pill">community</span></a>
<nav aria-label="Site"><a href="${r("index.html")}">Packages</a><a href="${r("search.html")}">Search</a></nav>
<form class="hsearch" role="search" action="${r("search.html")}" method="get"><label class="vh" for="hq">Search the hub</label><input id="hq" name="q" type="search" placeholder="Search names, docs, or List.append(_, Nil{})" autocomplete="off"></form>
</div></header>
<main id="main" class="wrap">
${o.body}
</main>
<footer class="foot"><div class="wrap">
<p>Community docs for BendHub packages · not affiliated with Higher Order Company · source <a href="https://github.com/bendlib/bendlib">github.com/bendlib/bendlib</a></p>
<p>Built ${esc(o.site.built)} · statuses are <code>bend --check-only</code> results on bend ${esc(o.site.compiler)} only${o.site.checked ? "" : " (checking was skipped in this build)"}${partial}</p>
</div></footer>
</body></html>
`;
}

export function renderIndex(site: Site): string {
  const path = "index.html";
  const groups = groupPackages(site.packages);
  const rows = groups.map((g) => {
    const p = g.latest, n = p.names[0];
    const search = [label(p), p.desc, n?.owner ?? "", ...g.members.map((m) => m.hash), ...p.names.map((x) => x.name)].join(" ").toLowerCase();
    const title = n ? `${esc(n.name)}</a> <span class="pill">@${esc(n.version)}</span>` : `${esc(shortHash(p.hash))}…</a>`;
    const more = g.members.length < 2 ? "" : n
      ? ` <a class="more" href="${rel(path, namePage(n.name))}">${g.members.length} versions</a>`
      : ` <span class="more" title="${esc(g.members.map((m) => shortHash(m.hash)).join(", "))}">${g.members.length} uploads</span>`;
    return `<tr data-s="${esc(search)}">
<td class="pk"><a class="t" href="${rel(path, pkgPage(p.hash))}">${title}${more}<div class="h">${p.hash}</div></td>
<td class="ds"><div class="clamp" title="${esc(p.desc)}">${esc(p.desc) || `<span class="muted">no description</span>`}</div></td>
<td data-l="status">${statusBadge(p.status)}</td>
<td data-l="laws" class="num">${p.counts.laws}</td>
<td data-l="used by" class="num">${g.members.reduce((a, m) => a + m.rdeps.length, 0)}</td>
<td data-l="updated" class="num">${date(p.ts)}</td></tr>`;
  }).join("\n");
  const totals = groups.reduce((a, g) => ({ laws: a.laws + g.latest.counts.laws, decls: a.decls + g.latest.counts.decls }), { laws: 0, decls: 0 });
  const body = `<div id="hero"><h1>Bend Docs</h1>
<p class="sub">every <b>BendHub</b> package, documented</p>
<p class="tag">${totals.decls.toLocaleString("en")} declarations and ${totals.laws.toLocaleString("en")} laws, each package checked on bend ${esc(site.compiler)}</p>
<form class="find" role="search" action="${rel(path, "search.html")}" method="get"><label class="vh" for="fq">Search</label><input id="fq" name="q" type="search" placeholder="a name, a word of a doc, or a law shape like Nat.add(_, 0n)" autocomplete="off"><button class="btn" type="submit">find</button></form></div>
<section><h2>Packages <span class="n">${groups.length} packages · ${site.packages.length} uploads</span></h2>
<div class="filter"><label for="filter">filter</label> <input id="filter" type="search" placeholder="name, hash, owner or description" autocomplete="off"> <span id="shown" aria-live="polite"></span></div>
<div class="tablewrap"><table class="pkgs" id="pkgs">
<thead><tr><th scope="col">name / version</th><th scope="col">description</th><th scope="col">status</th><th scope="col" class="num">laws</th><th scope="col" class="num">used by</th><th scope="col" class="num">updated</th></tr></thead>
<tbody>
${rows}
</tbody></table></div></section>`;
  return page({ path, title: "Bend Docs: BendHub packages", body, site, scripts: ["assets/site.js"] });
}

// An alias spelled like a Base namespace (Nat, List, …) lets a future Base def shadow the module's (PLAN F16).
const BASE_NAMESPACES = new Set(["Nat", "U32", "F32", "Char", "String", "Bool", "Cmp", "Maybe", "Result", "List", "Array", "Map", "Set", "IO", "Word", "Pair", "Equal", "Image", "Event", "App", "File", "TCP", "UDP", "Chan", "Window", "Audio", "Either", "Sigma", "Empty", "Unit", "Base"]);

function aliasFor(path: string): string {
  const base = posix.basename(path, ".bend").replace(/[^A-Za-z0-9_]/g, "_");
  const a = base.charAt(0).toUpperCase() + base.slice(1);
  return /^[A-Za-z_]/.test(a) && !BASE_NAMESPACES.has(a) ? a : `M${a}`;
}

function edgeList(path: string, edges: Edge[], side: "from" | "to", site: Site, empty: string): string {
  if (edges.length === 0) return `<p class="muted">${empty}</p>`;
  return `<ul class="edges">${edges.map((e) => {
    const other = site.byHash.get(e[side]);
    const name = other ? label(other) : shortHash(e[side]);
    const link = other ? `<a href="${rel(path, pkgPage(other.hash))}">${esc(name)}</a>` : `<span>${esc(e[side])}</span> <span class="muted">(${site.partial ? "not in this build" : "not on the hub index"})</span>`;
    return `<li>${link} <span class="via">via <code>${esc(e.via)}</code></span></li>`;
  }).join("")}</ul>`;
}

function statusTable(path: string, p: Package): string {
  const rows = p.modules.map((m) => {
    const s = m.status;
    const detail = s && s.detail && s.class !== "checks"
      ? `<details><summary>output</summary><pre>${esc(s.detail)}</pre></details>` : "";
    const rely = s?.unsafeDefs?.length ? `<div class="muted">defs: ${s.unsafeDefs.map((d) => `<code>${esc(d)}</code>`).join(", ")}</div>` : "";
    const settled = m.settled ? `<div class="muted">Checked alone, a law without a def is a TODO; all of them are proved in files that check, so the package counts this file as ${STATUS_TEXT[m.settled]}.</div>` : "";
    return `<tr><td><a href="${rel(path, modPage(p.hash, m.path))}">${esc(m.path)}</a></td><td>${statusBadge(s?.class ?? null)}</td>
<td>${s ? esc(s.summary) : ""}${rely}${settled}${detail}</td><td class="num">${s ? s.seconds.toFixed(1) + " s" : ""}</td></tr>`;
  }).join("\n");
  return `<div class="tablewrap"><table class="files"><thead><tr><th scope="col">File</th><th scope="col">Status</th><th scope="col">Checker says</th><th scope="col" class="num">Time</th></tr></thead><tbody>${rows}</tbody></table></div>`;
}

export function renderPackage(site: Site, p: Package): string {
  const path = pkgPage(p.hash);
  const bend = p.modules.map((m) => m.path);
  const importLines = bend.map((f) => {
    const a = aliasFor(f);
    const named = p.names.map((n) => `import ${n.name}@${n.version}/${f} as ${a}`);
    return [...named, `import ${p.hash}/${f} as ${a}`].join("\n");
  }).join("\n");
  const others = p.files.filter((f) => !f.path.endsWith(".bend"));
  const namesHtml = p.names.length
    ? `<p>${p.names.map((n) => `<a href="${rel(path, namePage(n.name))}">${esc(n.name)}</a>@${esc(n.version)} by ${esc(n.owner)}`).join("; ")}</p>`
    : `<p class="muted">Anonymous package: import it by hash.</p>`;
  const g = groupPackages(site.packages).find((x) => x.members.includes(p))!;
  const siblings = g.members.filter((m) => m !== p);
  const versionsHtml = siblings.length === 0 ? "" : `<details class="vers"><summary>${g.latest === p ? "Earlier versions" : "Other versions"} (${siblings.length})</summary><ul class="edges">${siblings.map((m) =>
    `<li><a href="${rel(path, pkgPage(m.hash))}">${esc(label(m))}</a> <span class="muted">${date(m.ts)}</span>${m === g.latest ? ` <span class="pill">latest</span>` : ""}</li>`).join("")}</ul></details>`;
  const lic = p.licenses.map((l) => l.from === null
    ? `${esc(l.id)} <span class="muted">(no LICENSE file; the hub's default)</span>`
    : `${esc(l.id)} <span class="muted">(<a href="${HUB}/${p.hash}/${esc(l.from)}">${esc(l.from)}</a>)</span>`).join("<br>");
  const modules = p.modules.map((m) => {
    const c = m.decls === null ? `<span class="st st-fails">not loaded</span>` : `${m.decls.length} declarations${lawCount(m.decls)}`;
    return `<li><a href="${rel(path, modPage(p.hash, m.path))}">${esc(m.path)}</a> <span class="muted">${c}</span></li>`;
  }).join("");
  const body = `<nav class="crumbs" aria-label="Breadcrumb"><a href="${rel(path, "index.html")}">Packages</a> / ${esc(label(p))}</nav>
<h1>${esc(label(p))} ${statusBadge(p.status)}</h1>
<p class="hash"><code>${p.hash}</code></p>
<p class="lead">${esc(p.desc) || `<span class="muted">no description</span>`}</p>
${namesHtml}
${versionsHtml}
<dl class="facts"><dt>Published</dt><dd>${date(published(p))}</dd><dt>Size</dt><dd>${p.bytes.toLocaleString("en")} bytes, ${p.files.length} files</dd>
<dt>License</dt><dd>${lic}</dd><dt>Declarations</dt><dd>${p.counts.laws} laws (${p.counts.proved} proved), ${p.counts.defs} defs, ${p.counts.types} types</dd></dl>
<h2 id="import">Import</h2>
<pre class="code">${esc(importLines)}</pre>
<h2 id="modules">Modules</h2>
<ul class="mods">${modules}</ul>
${others.length ? `<h2 id="files">Other files</h2><ul class="mods">${others.map((f) => `<li><a href="${HUB}/${p.hash}/${esc(f.path)}">${esc(f.path)}</a> <span class="muted">${f.bytes.toLocaleString("en")} bytes</span></li>`).join("")}</ul>` : ""}
<h2 id="deps">Dependencies</h2>
${edgeList(path, p.deps, "to", site, "No imports from other hub packages.")}
<h2 id="rdeps">Dependents</h2>
${edgeList(path, p.rdeps, "from", site, "No package in this build imports it.")}
<h2 id="status">Status on bend ${esc(site.compiler)}</h2>
${site.checked ? statusTable(path, p) : `<p class="muted">Checking was skipped in this build (--no-check).</p>`}`;
  return page({ path, title: `${label(p)} · Bend Docs`, body, site, description: p.desc });
}

function lawCount(ds: DocDecl[]): string {
  const laws = ds.filter((d) => d.kind === "law");
  return laws.length ? `, ${laws.length} laws` : "";
}

const GROUPS: [string, string][] = [["law", "Laws"], ["type", "Types"], ["def", "Definitions"], ["template", "Templates"], ["effect", "Effects (foreign code)"], ["unsafe", "Unsafe"]];

function declHtml(p: Package, m: Module, d: DocDecl, ids: Map<DocDecl, string>, ctors: DocDecl[]): string {
  const id = ids.get(d)!;
  const src = `${HUB}/${p.hash}/${m.path}`;
  let marker = "";
  if (d.kind === "law") {
    const by = m.provedIn[d.name];
    const byLink = by ? `<a href="${rel(modPage(p.hash, m.path), modPage(p.hash, by))}">${esc(by)}</a>` : "";
    const fst = by ? p.modules.find((x) => x.path === by)?.status?.class : undefined;
    marker = d.proved
      ? `<span class="pr pr-yes">proved</span>${by ? `<span class="muted">in ${byLink}</span>` : ""}`
      : d.holes
        ? `<span class="pr pr-open">open</span><span class="muted">a ?hole is left in its proof${by ? ` in ${byLink}` : ""}</span>`
        : by
          ? `<span class="pr pr-open">open</span><span class="muted">its proof in ${byLink} does not pass the checker (${fst ? STATUS_TEXT[fst] : "not loaded"})</span>`
          : `<span class="pr pr-open">open</span><span class="muted">no def in the package proves it</span>`;
  }
  if (d.unsafe && d.kind !== "unsafe") marker += ` <span class="k k-unsafe">@unsafe</span>`;
  const stmt = d.statement
    ? `<pre class="code sig"><span class="muted">${esc(d.signature.slice(0, d.signature.lastIndexOf("{")))}</span>${esc(d.signature.slice(d.signature.lastIndexOf("{")))}</pre>`
    : `<pre class="code sig">${esc(d.signature)}</pre>`;
  const effects = d.effects?.length ? `<p class="muted">foreign: ${d.effects.map((e) => `<code>${esc(e)}</code>`).join(", ")}</p>` : "";
  const cs = ctors.length
    ? `<ul class="ctors">${ctors.map((c) => `<li id="${ids.get(c)!}"><code>${esc(c.name)}</code> <pre class="code sig">${esc(c.signature)}</pre>${docHtml(c.doc)}</li>`).join("")}</ul>` : "";
  return `<section class="decl" id="${id}" aria-labelledby="${id}-h">
<h3 id="${id}-h">${kindBadge(d.kind)} <a class="self" href="#${id}">${esc(d.name)}</a> ${marker}<a class="src" href="${src}" title="raw source on the hub; the declaration starts at line ${d.line}">source · line ${d.line}</a></h3>
${stmt}${docHtml(d.doc)}${effects}${cs}
</section>`;
}

/** Declaration anchors of a module page, in page order (the search index links to the same ids). */
export function declIds(m: Module): Map<DocDecl, string> {
  const ids = new Map<DocDecl, string>();
  // Ids the page layout itself uses; a def named `main` must not take the <main> landmark's id.
  const used = new Map<string, number>([["main", 1], ["hq", 1], ...GROUPS.map(([k]): [string, number] => [`g-${k}`, 1])]);
  const take = (d: DocDecl) => {
    const base = anchor(d.name);
    const n = used.get(base) ?? 0;
    used.set(base, n + 1);
    ids.set(d, n === 0 ? base : `${base}-${d.kind}${n > 1 ? n : ""}`);
  };
  const ctors = ctorsByType(m);
  for (const [k] of GROUPS) {
    for (const d of (m.decls ?? []).filter((x) => x.kind === k)) {
      take(d);
      if (k === "type") for (const c of ctors.get(d.name) ?? []) take(c);
    }
  }
  return ids;
}

function ctorsByType(m: Module): Map<string, DocDecl[]> {
  const out = new Map<string, DocDecl[]>();
  for (const d of m.decls ?? []) if (d.kind === "ctor" && d.type) out.set(d.type, [...(out.get(d.type) ?? []), d]);
  return out;
}

export function renderModule(site: Site, p: Package, m: Module): string {
  const path = modPage(p.hash, m.path);
  const head = `<nav class="crumbs" aria-label="Breadcrumb"><a href="${rel(path, "index.html")}">Packages</a> / <a href="${rel(path, pkgPage(p.hash))}">${esc(label(p))}</a> / ${esc(m.path)}</nav>
<h1>${esc(m.path)} ${m.status ? statusBadge(m.status.class, m.status.summary) : ""}</h1>
<p><a href="${HUB}/${p.hash}/${esc(m.path)}">raw source on the hub</a> · <code>import ${esc(p.names.length ? `${p.names[0].name}@${p.names[0].version}` : p.hash)}/${esc(m.path)} as ${aliasFor(m.path)}</code></p>`;
  const imports = m.imports.length
    ? `<details class="imps"><summary>${m.imports.length} import${m.imports.length > 1 ? "s" : ""}</summary><pre class="code">${m.imports.map((i) => esc(i.raw)).join("\n")}</pre></details>` : "";
  if (m.decls === null) {
    const e = m.error!;
    const body = `${head}${imports}<div class="err" role="alert"><p><strong>The reader could not load this file</strong>${e.file ? ` (at <code>${esc(e.file)}${e.line ? ":" + e.line : ""}</code>)` : ""}. What bend.ts says:</p><pre>${esc(e.message)}</pre></div>`;
    return page({ path, title: `${m.path} · ${label(p)} · Bend Docs`, body, site });
  }
  const ids = declIds(m);
  const ctorsOf = ctorsByType(m);
  const toc: string[] = [];
  const sections = GROUPS.map(([k, title]) => {
    const ds = m.decls!.filter((d) => d.kind === k);
    if (ds.length === 0) return "";
    toc.push(`<a href="#g-${k}">${title} <span class="muted">${ds.length}</span></a>`);
    return `<h2 id="g-${k}">${title}</h2>\n${ds.map((d) => declHtml(p, m, d, ids, k === "type" ? ctorsOf.get(d.name) ?? [] : [])).join("\n")}`;
  }).join("\n");
  const body = `${head}${imports}${toc.length ? `<nav class="toc" aria-label="Declaration kinds">${toc.join("")}</nav>` : `<p class="muted">This file declares nothing of its own.</p>`}${sections}`;
  return page({ path, title: `${m.path} · ${label(p)} · Bend Docs`, body, site });
}

export function renderName(site: Site, name: string): string {
  const path = namePage(name);
  const rec = site.names.find((n) => n.name === name)!;
  const rows = [...rec.versions].sort((a, b) => b.ts - a.ts).map((v) => {
    const p = site.byHash.get(v.hash);
    return `<tr><td>${esc(v.version)}${v.version === rec.latest.version ? ` <span class="muted">latest</span>` : ""}</td>
<td>${p ? `<a href="${rel(path, pkgPage(v.hash))}"><code>${v.hash}</code></a>` : `<code>${v.hash}</code> <span class="muted">(not in this build)</span>`}</td>
<td>${p ? statusBadge(p.status) : ""}</td><td class="num">${date(v.ts)}</td></tr>`;
  }).join("");
  const body = `<nav class="crumbs" aria-label="Breadcrumb"><a href="${rel(path, "index.html")}">Packages</a> / ${esc(name)}</nav>
<h1>${esc(name)}</h1><p class="lead">${esc(rec.latest.desc)}</p><p>Owner: ${esc(rec.owner_login)}</p>
<h2>Versions</h2><div class="tablewrap"><table class="files"><thead><tr><th scope="col">Version</th><th scope="col">Hash</th><th scope="col">Status</th><th scope="col" class="num">Named on</th></tr></thead><tbody>${rows}</tbody></table></div>`;
  return page({ path, title: `${name} · Bend Docs`, body, site, description: rec.latest.desc });
}

export function renderSearch(site: Site): string {
  const path = "search.html";
  const body = `<h1>Search</h1>
<form id="sf" class="sform" role="search" onsubmit="return false">
<label for="q">Query</label>
<input id="q" name="q" type="search" autocomplete="off" spellcheck="false" placeholder="add_comm, reverse, or List.append(_, Nil{})" aria-describedby="how">
<fieldset class="modes"><legend class="vh">Mode</legend>
<label><input type="radio" name="mode" value="auto" checked> auto</label>
<label><input type="radio" name="mode" value="text"> names &amp; docs</label>
<label><input type="radio" name="mode" value="shape"> law shape</label>
<label><input type="checkbox" id="lawsonly"> laws only</label></fieldset>
</form>
<p id="state" class="muted" aria-live="polite">Loading the index…</p>
<ol id="results" class="results"></ol>
<section id="how" class="how">
<h2>Law-shape search</h2>
<p>A query with a standalone <code>_</code>, or with brackets or <code>==</code>, is a <strong>shape</strong>. It finds every law (and every def whose type is an equation) whose statement contains that shape somewhere, on either side.</p>
<ul>
<li><code>_</code> matches one balanced sub-term: a name, a literal, a call like <code>List.append(a, A, xs, ys)</code>, or an operator term like <code>1n+m</code>. It never spans a comma, so it never matches two arguments.</li>
<li><strong>Leading arguments can be left out.</strong> <code>List.append(_, Nil{})</code> matches <code>List.append(a, A, xs, [])</code>: a call pattern with <var>k</var> arguments matches the <em>last</em> <var>k</var> arguments, because quantities and types come first in Bend.</li>
<li>Names match on a namespace suffix: <code>Csv.encode_row(_)</code> finds <code>lib.Csv.encode_row([])</code>, but <code>ode_row</code> finds nothing.</li>
<li>Write constructors either way. Queries are rewritten the way bend prints terms: <code>Nil{}</code> is <code>[]</code>, <code>Zero{}</code> is <code>0n</code>, <code>Succ{n}</code> is <code>1n+n</code>, and <code>Con{h, t}</code> is <code>h &lt;&gt; t</code> (a chain ending in <code>Nil{}</code> is a list literal).</li>
<li><code>lhs == rhs</code> matches a whole equation, and each side of the pattern must cover a whole side: <code>Nat.add(_, _) == Nat.add(_, _)</code> finds commutativity-shaped laws.</li>
<li>A bare name such as <code>List.length</code> finds every statement that mentions it.</li>
</ul>
<p>Examples: <a href="?q=List.append(_%2C%20Nil%7B%7D)">List.append(_, Nil{})</a> · <a href="?q=Nat.add(_%2C%200n)">Nat.add(_, 0n)</a> · <a href="?q=List.reverse(List.reverse(_))">List.reverse(List.reverse(_))</a> · <a href="?q=Nat.add(_%2C%20_)%20%3D%3D%20Nat.add(_%2C%20_)">Nat.add(_, _) == Nat.add(_, _)</a></p>
<h2>Names and docs</h2>
<p>Any other query searches declaration names and doc comments. Every word must appear. Exact names rank first, then prefixes, then names containing the word, then docs.</p>
<p>Statements are shown as bend ${esc(site.compiler)} prints them. The index covers ${site.packages.length} packages.</p>
</section>`;
  return page({ path, title: "Search · Bend Docs", body, site, scripts: ["assets/search.js"] });
}
