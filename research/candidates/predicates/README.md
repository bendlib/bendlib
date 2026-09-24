# Candidate frozen predicates: mem and sorted_by
Base-only candidates for the 0.2 freeze (PLAN §3.1 rule 1b, §3.3); nothing here is published; owner
picks in D-pred (`bend-61a.19`). Files: `list_preds.bend` (defs+proofs), `v1/p.bend`, `v2/p.bend`,
`stable.bend`.

    def mem(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Data:
      {List.contains(~A, ~eq, xs, x) == True{} : Bool}
    def sorted_by(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> Data:
      {List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), List.zip(&2, A, &2, A, xs, List.tail(&2, A, xs))) == True{} : Bool}

## Laws (all proved; instantiated at `~Nat, ~Nat.is_eq` / `~Nat, ~Nat.is_le`)
- mem_cons_self: mem(x, x <> xs)
- mem_cons_of_mem: mem(x, xs) -> mem(x, y <> xs)
- not_mem_nil: mem(x, Nil{}) -> Empty
- mem_append_left: mem(x, xs) -> mem(x, append(xs, ys))
- mem_append_right: mem(x, ys) -> mem(x, append(xs, ys))
- sorted_nil: sorted_by(Nil{})
- sorted_single: sorted_by([x])
- sorted_cons_cons_intro: le(x,y), sorted_by(y<>t) -> sorted_by(x<>y<>t)
- sorted_cons_cons_elim_le: sorted_by(x<>y<>t) -> le(x,y)
- sorted_cons_cons_elim_tail: sorted_by(x<>y<>t) -> sorted_by(y<>t)
- sorted_tail: sorted_by(x<>xs) -> sorted_by(xs)

Not proved: none. Lawcheck on the statements only gives `11 laws: 9 ✓ · 0 ✗ · 2 ~ · 0 !`; the two
skipped are `sorted_cons_cons_intro` (premise `MNat.le`) and `sorted_cons_cons_elim_le` (claim
`MNat.le`), which lawcheck cannot generate/evaluate. Checker lines (last line verbatim):
- `~/.bend/bin/bend research/candidates/predicates/list_preds.bend --check-only` → `All terms check.`
- `bun tools/lawcheck/cli.ts research/candidates/predicates/list_preds.bend` → the summary above.
## Stability (F4)
`v1/p.bend` and `v2/p.bend` are byte-identical copies of the two defs; `stable.bend` imports them as
`P1`/`P2` and proves `cross_mem` / `cross_sorted` by `h`; `bend stable.bend --check-only` →
`All terms check.` The Base-only bodies do unify across versions, as F4 claims.

## Open questions for the owner (D-pred)
- Argument order `mem(x, xs)` (rv2) vs `mem(xs, x)`.
- Lint (`tools/mathlib/lint.ts ... --erasure`) reports `list_preds.bend:9: predicate 'sorted_by'
  calls 'le', which is not a Base function`; must the rule allow a predicate's own template `eq`/`le`?
- `sorted_by`'s closure `le(fst p, snd p)` consumes the linear pair twice: a lemma passing the
  `List.all` body as a value must bind that Bool erased (`-b`), else `h consumed more than once`.
  Should the frozen body destructure the pair once instead?
