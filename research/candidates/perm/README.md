# perm encodings: count-based vs inductive (decision D3)

Inputs (all Nat): `count.bend` → `bend research/candidates/perm/count.bend --check-only` = `All terms check.`,
lawcheck `7 laws: 0 ✓ · 0 ✗ · 7 ~ · 0 !`; `inductive.bend` → `All terms check.`, lawcheck
`8 laws: 7 ✓ · 0 ✗ · 1 ~ · 0 !`; `count_reuse.bend` = the F27 demo. Citations are `file:line`; "lines" is
the length of the proof `def`. This is the PLAN §3.3 candidate-selection step; the owner decides D3.

| law | count-based (`count.bend`) | inductive (`inductive.bend`) |
|---|---|---|
| perm_refl | proved, 2 lines, no helper (`:56`) | proved, 2 lines, no helper (`:176`) |
| perm_sym | proved, 2 lines, no helper (`:73`) | proved, 3 lines, `internal_apply_invert` (`:210`) |
| perm_trans | proved, 2 lines, no helper (`:85`) | proved, 4 lines, `internal_apply_app` (`:198`) |
| perm_nil | proved, 2 lines, no helper (`:63`) | not separate (definitional `{==}`) |
| perm_cons | proved, 3 lines, no helper (`:96`) | proved, 4 lines, `internal_apply_shift` (`:222`) |
| perm_swap | proved, 2 lines, `internal_bump_comm` (`:107`) | proved, 2 lines, no helper (`:185`) |
| perm_append_comm | proved, 6 lines, `internal_count_append`+`internal_bump_add` (`:116`) | proved, 2 lines, `internal_apply_rc` (`:232`) |
| perm_length | **not proved** (no def in `count.bend`) | proved, 3 lines, `internal_apply_length` (`:242`) |

Helpers: count-based 3 defs / 24 lines (`:24`, `:35`, `:42`); inductive 11 `internal_*` defs / 92 lines
(`:41`…`:162`) plus 8 public defs used by the statements or the kernel (`swap_head :8`, `swap_at :19`,
`apply :30`, `Perm :38`, `invert :101`, `shift :117`, `upto :131`, `rc :155`).

**Reusability.** count `perm` returns `Type` (`count.bend:21`), so F25 forbids a `+h` hypothesis; it is
single-use (F27): `count_reuse.bend` is rejected with `expected : p` / `observed : p (consumed more than once)`.
Inductive `Perm … -> Data` (`inductive.bend:38`) is `+h` reusable: `perm_reuse` (`:247`) proves
`Perm & Perm` from one `+h` and checks (`All terms check.`). F26 is the other side: an erased
hypothesis is unusable, a function-type one at most once.

**Genericity.** Both candidates are Nat-specific. count hardcodes `Nat.is_eq` (`count.bend:17`); a
generic form needs `A: Data` and `~eq: A -> A -> Bool` (PLAN §3.1). Inductive moves elements without
comparing them, so it generalizes to `A: Data` with `steps: List<&2, Nat>` unchanged.

**Missing law cost.** `perm_length` needs `Σ_{i<bound} count(i, xs)` plus Nat order/equality lemmas
(`is_lt(a,1+b) ↔ is_le(a,b)`, `is_eq` disjointness) that neither Base nor `packages/bend-mathlib`
provide; the inductive side proves it in 3 lines (`inductive.bend:242`). Merge sort needs length, so
this is the blocker for the count encoding.

**Sort proof needs.** count: additivity of `count` over merge (cf. `count.bend:42`) and the missing
length; single-use hypotheses force re-deriving count equalities per element. Inductive: reusable
`Perm` invariants composed with `internal_apply_app` (`inductive.bend:71`); length free; but the proof
must emit an explicit `steps` derivation, and the kernel exposes its constructors.

**Kernel freeze (F4: a `match`ing def is nominal across versions).** count freezes `bump`, `count`,
`perm` (`count.bend:5,13,21`) = 3 defs / 14 lines. Inductive freezes the 8 public defs above (all
appear in statements or define the relation); indexed datatypes are inexpressible on 2.0.27, so `Perm`
is a `Data` predicate over a derivation list (`inductive.bend:1-3`).

Lint reality (`bun tools/mathlib/lint.ts research/candidates/perm --erasure`): `count.bend` 2 findings
(only that `perm` calls `count`, i.e. it is nominal, F4); `inductive.bend` 21 (11 erasable binders —
F26 — plus 8 missing doc lines and the `Perm` name). Neither is `packages/`-ready as committed.

**Recommendation.** Freeze the inductive `Perm`: it gives reusable `+h` hypotheses and proves
`perm_length`, with its 11 proof helpers left in mathlib as ordinary lemmas. Trade-off: the inductive
kernel is larger (8 defs, derivation-list encoding, explicit step lists in proofs), while count is a
3-def kernel with terse refl/sym/trans but a single-use hypothesis and no provable length.
