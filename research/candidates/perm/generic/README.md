# perm, generic over `A: Data` (D3 evidence, 2026-09-25)

Generic step-list kernel and the sort proofs that justify freezing it. Run from the repo root with
`~/.bend/bin/bend <file> --check-only`. Expected last line:

| file | expected | shows |
|---|---|---|
| `kernel.bend` | `All terms check.` | `swap_head`, `swap_at`, `apply` generic over `-A: Data`; `Perm` over a step list; existential `perm(A, xs, ys) := Sigma<&2, &2, List<&2, Nat>, s => Perm(A, s, xs, ys)>` (Data, reusable) |
| `msort_perm.bend` | `All terms check.` | `ins_perm`, `isort_perm`, `merge_perm`, `split_perm`, `msort_perm`, `sort_perm` + `perm_refl/swap/trans/cons/move/move_rev/append_comm/append_right/append/reuse` |
| `sym_perm.bend` | `All terms check.` | `perm_sym`, `perm_length` |
| `use_generic.bend` | `All terms check.` | instances at Nat, U32, `List<&2, Nat>` |
| `isort_perm.bend`, `merge_perm.bend`, `ins_try.bend`, `merge_try.bend` | `All terms check.` | intermediate steps |
| `neg_perm.bend`, `neg_perm2.bend`, `neg_ins.bend` | fails | `[1n]` is not a perm of `[]`; a sabotaged proof is rejected |
| `xv/stable.bend` | `All terms check.` | two byte-identical mathlib copies over ONE kernel file unify at variables |
| `xvneg/stable.bend` | fails (`k2/list.apply` vs `k1/list.apply`) | two kernel copies do not: import the kernel at exactly one hash |
| `baseonly_sort*.bend`, `xvsort/` | sort-equality perm: refl/sym/trans check, but `baseonly_sort_swap` is stuck and `baseonly_sort_preorder` shows it is **wrong for preorders** | rejected |
| `baseonly_count*.bend`, `xvcount/` | count-via-zip perm decides closed cases but `baseonly_count4_refl` (refl at a variable) is stuck | rejected |

Proof-writing rules learned here: template theorems are checked only when instantiated, so each needs
a closed Nat instance in the file; `perm_trans` needs `+xs`; rebind Sigma fields (`+s = s`) before
reuse; the decreasing argument goes first; write `1n++f` when fuel is used twice; derive
`perm_append_left` from `perm_append_comm` (step indices can reach past the prefix).

Decision (PLAN §9 D3): freeze this kernel with `Perm` renamed `perm_steps`; `invert`, `shift`,
`upto`, `rc` from `../inductive.bend` become `internal_*` helpers in mathlib, not kernel defs.
