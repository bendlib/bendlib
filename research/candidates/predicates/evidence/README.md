# mem / sorted_by evidence (D-pred, 2026-09-25)

`~/.bend/bin/bend <file> --check-only` from the repo root:

| file | expected | shows |
|---|---|---|
| `isort_sorted.bend` | `All terms check.` | `ins_sorted`, `isort_sorted` (Nat) with the unchanged `sorted_by` body and a reusable `+h: sorted_by(…)` |
| `isort_sorted_neg.bend` | fails | a wrong `ins` is rejected |
| `memorder.bend` | `All terms check.` | `mem(x, xs)` and `mem(xs, x)` convert into each other by `h`; generic lemmas prove identically in both orders |
| `lamdestr.bend` | fails | a lambda cannot destructure its pair parameter on 2.0.27 |
| `foldr0.bend`, `base0.bend` | fail (`h consumed more than once`) | Base `List.all`/`foldr` bind the element affinely, so no Base-only body can use it twice; the Bool is proof-only, bound erased (F26) |
| `helperdef.bend` | `All terms check.` | only a non-Base helper def destructures once — nominal, breaks F4, rejected |

`../lint-template-params.patch`: the `tools/mathlib/lint.ts` change that lets a predicate call its
own `~` template parameters and flags uncalled non-Base references.
