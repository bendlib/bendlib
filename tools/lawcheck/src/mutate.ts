// Pure mutation operators for lawcheck mutation mode (PLAN §4.3): given a def's
// source text, produce mutated copies by rewriting body lines only. No bend, no
// files, no processes. `defSpan` locates a def; `mutants` returns every
// first-order mutant, deduplicated and distinct from the input. Ill-typed
// mutants are expected: the runner discards what the checker rejects.

export type Op = "arm-swap" | "arm-copy" | "literal" | "drop-succ" | "drop-cons" | "arg-swap" | "projection" | "base-swap";

export type Mutant = { id: string; def: string; op: Op; line: number; before: string; after: string; text: string };

const INDENT = (s: string) => /^ */.exec(s)![0].length;
const BLANK = (s: string) => s.trim() === "";
const isCase = (s: string) => /^case\b/.test(s.trim());
const isMatch = (s: string) => /^match\b/.test(s.trim());

/** Replaces every char inside a string/char literal or after `#` with a sentinel, preserving offsets. */
function mask(line: string): string {
  const c = line.split("");
  let i = 0;
  while (i < c.length) {
    if (c[i] === '"' || c[i] === "'") {
      const q = c[i];
      c[i++] = "\u0001";
      while (i < c.length) {
        const d = c[i];
        c[i++] = "\u0001";
        if (d === "\\") { if (i < c.length) c[i++] = "\u0001"; continue; }
        if (d === q) break;
      }
    } else if (c[i] === "#") {
      while (i < c.length) c[i++] = "\u0001";
    } else i++;
  }
  return c.join("");
}

/** 0-based index of the header's last line: the first line ending in `:` at paren depth 0, or -1. */
function headerEnd(lines: string[], startIdx: number): number {
  let depth = 0;
  for (let i = startIdx; i < lines.length; i++) {
    for (const ch of lines[i]) {
      if (ch === "(") depth++;
      else if (ch === ")") depth--;
    }
    if (depth === 0 && /:\s*$/.test(lines[i])) return i;
  }
  return -1;
}

/** 1-based [start, end] lines of `def <name>(`: its header line through its last non-blank body line. */
export function defSpan(text: string, name: string): { start: number; end: number } | null {
  const lines = text.split("\n");
  const re = new RegExp(`^def\\s+${name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\(`);
  const startIdx = lines.findIndex((l) => re.test(l));
  if (startIdx < 0) return null;
  const he = headerEnd(lines, startIdx);
  if (he < 0) return null;
  let endIdx = he;
  for (let i = he + 1; i < lines.length; i++) {
    const l = lines[i];
    if (!BLANK(l) && !/^\s/.test(l)) break;
    if (!BLANK(l)) endIdx = i;
  }
  return { start: startIdx + 1, end: endIdx + 1 };
}

type Arm = { caseLine: number; bodyStart: number; bodyEnd: number };

/** Arms of the `match` at `matchIdx`, each with the trimmed [bodyStart, bodyEnd] of its case body. */
function matchArms(lines: string[], matchIdx: number, bodyEnd: number): Arm[] {
  const mIndent = INDENT(lines[matchIdx]);
  const cIndent = mIndent + 2;
  const arms: Arm[] = [];
  let i = matchIdx + 1;
  while (i <= bodyEnd) {
    const s = lines[i];
    if (BLANK(s)) { i++; continue; }
    const ind = INDENT(s);
    if (ind <= mIndent) break;
    if (ind === cIndent && isCase(s)) {
      let j = i + 1;
      let last = i;
      while (j <= bodyEnd) {
        const t = lines[j];
        if (!BLANK(t) && INDENT(t) <= cIndent) break;
        if (!BLANK(t)) last = j;
        j++;
      }
      arms.push({ caseLine: i, bodyStart: i + 1, bodyEnd: last });
      i = j;
    } else i++;
  }
  return arms;
}

type Call = { open: number; close: number };

/** `f(` calls on a masked line, including nested ones. */
function calls(masked: string): Call[] {
  const out: Call[] = [];
  for (let i = 0; i < masked.length; i++) {
    if (masked[i] !== "(") continue;
    const p = masked[i - 1];
    if (p === undefined || !/[A-Za-z0-9_.]/.test(p)) continue;
    let depth = 0, j = i;
    for (; j < masked.length; j++) {
      if (masked[j] === "(") depth++;
      else if (masked[j] === ")" && --depth === 0) break;
    }
    if (depth === 0) out.push({ open: i, close: j });
  }
  return out;
}

/** Trimmed [start, end) spans of the top-level arguments between `open` and `close` (absolute offsets). */
function argSpans(masked: string, open: number, close: number): [number, number][] {
  const spans: [number, number][] = [];
  let depth = 0, start = open + 1;
  for (let i = open + 1; i < close; i++) {
    const ch = masked[i];
    if (ch === "(" || ch === "{" || ch === "[") depth++;
    else if (ch === ")" || ch === "}" || ch === "]") depth--;
    else if (ch === "," && depth === 0) { spans.push([start, i]); start = i + 1; }
  }
  spans.push([start, close]);
  return spans.map(([s, e]) => {
    while (s < e && /\s/.test(masked[s])) s++;
    while (e > s && /\s/.test(masked[e - 1])) e--;
    return [s, e] as [number, number];
  });
}

/** Every mutant of def `name`, deduplicated, none equal to the input text. */
export function mutants(text: string, name: string, params: string[]): Mutant[] {
  const span = defSpan(text, name);
  if (span === null) return [];
  const lines = text.split("\n");
  const he = headerEnd(lines, span.start - 1);
  const bodyStart = he + 1;
  const bodyEnd = span.end - 1;
  const cands: { op: Op; lines: string[] }[] = [];
  const repl = (idx: number, line: string) => lines.map((l, k) => (k === idx ? line : l));
  const splice = (start: number, end: number, block: string[]) => [...lines.slice(0, start), ...block, ...lines.slice(end + 1)];

  // 1. arm-swap
  for (let mi = bodyStart; mi <= bodyEnd; mi++) {
    if (!isMatch(lines[mi])) continue;
    const arms = matchArms(lines, mi, bodyEnd);
    for (let i = 0; i < arms.length; i++) for (let j = i + 1; j < arms.length; j++) {
      const a = lines.slice(arms[i].bodyStart, arms[i].bodyEnd + 1);
      const b = lines.slice(arms[j].bodyStart, arms[j].bodyEnd + 1);
      if (a.length === 0 || b.length === 0 || INDENT(a[0]) !== INDENT(b[0])) continue;
      cands.push({ op: "arm-swap", lines: [...lines.slice(0, arms[i].bodyStart), ...b, ...lines.slice(arms[i].bodyEnd + 1, arms[j].bodyStart), ...a, ...lines.slice(arms[j].bodyEnd + 1)] });
    }
  }

  // 2. arm-copy
  for (let mi = bodyStart; mi <= bodyEnd; mi++) {
    if (!isMatch(lines[mi])) continue;
    const arms = matchArms(lines, mi, bodyEnd);
    for (let i = 0; i < arms.length; i++) for (let j = 0; j < arms.length; j++) {
      if (i === j) continue;
      const b = lines.slice(arms[j].bodyStart, arms[j].bodyEnd + 1);
      if (b.length === 0) continue;
      cands.push({ op: "arm-copy", lines: splice(arms[i].bodyStart, arms[i].bodyEnd, b) });
    }
  }

  const bodyLine = (fn: (idx: number, line: string, m: string) => void) => {
    for (let idx = bodyStart; idx <= bodyEnd; idx++) {
      const line = lines[idx];
      if (BLANK(line) || isCase(line) || isMatch(line)) continue;
      fn(idx, line, mask(line));
    }
  };

  // 3. literal: one mutant per standalone token occurrence.
  bodyLine((idx, line, m) => {
    for (const { re, to } of [
      { re: /(?<![A-Za-z0-9_])0n(?![A-Za-z0-9_])/g, to: "1n" },
      { re: /(?<![A-Za-z0-9_])1n(?![A-Za-z0-9_])(?!\s*\+)/g, to: "0n" },
      { re: /(?<![A-Za-z0-9_])True\{\}/g, to: "False{}" },
      { re: /(?<![A-Za-z0-9_])False\{\}/g, to: "True{}" },
    ]) {
      for (let x; (x = re.exec(m)) !== null;) cands.push({ op: "literal", lines: repl(idx, line.slice(0, x.index) + to + line.slice(x.index + x[0].length)) });
    }
  });

  // 4. drop-succ: remove each `Kn+` prefix.
  bodyLine((idx, line, m) => {
    const re = /(?<![A-Za-z0-9_])[12]n\+/g;
    for (let x; (x = re.exec(m)) !== null;) cands.push({ op: "drop-succ", lines: repl(idx, line.slice(0, x.index) + line.slice(x.index + x[0].length)) });
  });

  // 5. drop-cons: a top-level `A <> B` becomes `B`.
  bodyLine((idx, line, m) => {
    const off = line.length - line.trimStart().length;
    let depth = 0;
    for (let i = off; i < m.length; i++) {
      const ch = m[i];
      if ("([{".includes(ch)) depth++;
      else if (")]}".includes(ch)) depth--;
      else if (ch === "<" && m[i + 1] === ">" && depth === 0) {
        const b = line.slice(i + 2).trim();
        if (b !== "") cands.push({ op: "drop-cons", lines: repl(idx, " ".repeat(off) + b) });
      }
    }
  });

  // 6. arg-swap: swap each adjacent pair of top-level arguments of every call.
  bodyLine((idx, line, m) => {
    for (const { open, close } of calls(m)) {
      const spans = argSpans(m, open, close);
      for (let k = 0; k + 1 < spans.length; k++) {
        const [as, ae] = spans[k], [bs, be] = spans[k + 1];
        const ta = line.slice(as, ae), tb = line.slice(bs, be);
        if (ta === tb) continue;
        cands.push({ op: "arg-swap", lines: repl(idx, line.slice(0, as) + tb + line.slice(ae, bs) + ta + line.slice(be)) });
      }
    }
  });

  // 7. projection: replace the whole body by one line holding each parameter / constant.
  {
    let first = bodyStart;
    for (let i = bodyStart; i <= bodyEnd; i++) if (!BLANK(lines[i])) { first = i; break; }
    const ind = " ".repeat(INDENT(lines[first]));
    for (const item of [...params, "0n", "Nil{}", "True{}", "False{}"]) {
      cands.push({ op: "projection", lines: splice(bodyStart, bodyEnd, [ind + item]) });
    }
  }

  // 8. base-swap: one mutant per whole-token occurrence.
  bodyLine((idx, line, m) => {
    for (const { re, to } of [
      { re: /(?<![A-Za-z0-9_])Nat\.is_le(?![A-Za-z0-9_])/g, to: "Nat.is_lt" },
      { re: /(?<![A-Za-z0-9_])Nat\.is_lt(?![A-Za-z0-9_])/g, to: "Nat.is_le" },
      { re: /(?<![A-Za-z0-9_])Nat\.is_ge(?![A-Za-z0-9_])/g, to: "Nat.is_gt" },
      { re: /(?<![A-Za-z0-9_])Nat\.is_gt(?![A-Za-z0-9_])/g, to: "Nat.is_ge" },
      { re: /(?<![A-Za-z0-9_])Bool\.and(?![A-Za-z0-9_])/g, to: "Bool.or" },
      { re: /(?<![A-Za-z0-9_])Bool\.or(?![A-Za-z0-9_])/g, to: "Bool.and" },
      { re: /&&/g, to: "||" },
      { re: /\|\|/g, to: "&&" },
      { re: /(?<![A-Za-z0-9_])Nat\.min(?![A-Za-z0-9_])/g, to: "Nat.max" },
      { re: /(?<![A-Za-z0-9_])Nat\.max(?![A-Za-z0-9_])/g, to: "Nat.min" },
      { re: /(?<![A-Za-z0-9_])Nat\.add(?![A-Za-z0-9_])/g, to: "Nat.sub" },
    ]) {
      for (let x; (x = re.exec(m)) !== null;) cands.push({ op: "base-swap", lines: repl(idx, line.slice(0, x.index) + to + line.slice(x.index + x[0].length)) });
    }
  });

  const out: Mutant[] = [];
  const seen = new Set<string>();
  for (const c of cands) {
    const t = c.lines.join("\n");
    if (t === text || seen.has(t)) continue;
    seen.add(t);
    let li = 0;
    while (li < lines.length && li < c.lines.length && lines[li] === c.lines[li]) li++;
    out.push({ id: `${name}#${out.length}`, def: name, op: c.op, line: li + 1, before: (lines[li] ?? "").trim(), after: (c.lines[li] ?? "").trim(), text: t });
  }
  return out;
}
