// Type expressions as bend's term_show prints them (List<a, A>, Pair(Nat, Bool),
// m.T, &2): a small parser, printer and substitution. Anything else (arrows,
// equalities, dependent pairs) parses to null and the caller reports it.

export type Ty =
  | { t: "q"; q: string }
  | { t: "app"; head: string; args: Ty[]; paren: boolean };

const IDENT = /^[A-Za-z_0-9\/][A-Za-z0-9_.\/$-]*/;

export function parseTy(src: string): Ty | null {
  let i = 0;
  const ws = () => { while (src[i] === " ") i++; };
  function ty(): Ty | null {
    ws();
    if (src[i] === "&" && /[0-9]/.test(src[i + 1] ?? "")) {
      const q = src.slice(i, i + 2);
      i += 2;
      return { t: "q", q };
    }
    if (src[i] === "(") {
      i++;
      const inner = ty();
      ws();
      if (inner === null || src[i] !== ")") return null;
      i++;
      return inner;
    }
    const m = IDENT.exec(src.slice(i));
    if (m === null) return null;
    i += m[0].length;
    const open = src[i];
    if (open !== "<" && open !== "(") return { t: "app", head: m[0], args: [], paren: false };
    const close = open === "<" ? ">" : ")";
    i++;
    const args: Ty[] = [];
    for (;;) {
      const a = ty();
      if (a === null) return null;
      args.push(a);
      ws();
      if (src[i] === ",") { i++; continue; }
      if (src[i] === close) { i++; break; }
      return null;
    }
    return { t: "app", head: m[0], args, paren: open === "(" };
  }
  const r = ty();
  ws();
  return r !== null && i === src.length ? r : null;
}

export function showTy(t: Ty, rename: (head: string) => string = (h) => h): string {
  if (t.t === "q") return t.q;
  if (t.args.length === 0) return rename(t.head);
  const [o, c] = t.paren ? ["(", ")"] : ["<", ">"];
  return rename(t.head) + o + t.args.map((a) => showTy(a, rename)).join(", ") + c;
}

export function substTy(t: Ty, env: Map<string, Ty>): Ty {
  if (t.t === "q") return t;
  if (t.args.length === 0 && env.has(t.head)) return env.get(t.head)!;
  return { ...t, args: t.args.map((a) => substTy(a, env)) };
}

export const tyKey = (t: Ty) => showTy(t);
