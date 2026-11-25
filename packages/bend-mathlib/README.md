# bend-mathlib

Machine-checked lemmas for Bend 2, checked with `bend 2.0.40`: 491 lemmas, 360 generated
`_sym` twins, 6 predicates and 39 typed defs (theorems stated by their type, and the
functions they are about). Import a module instead of re-proving a basic fact; every statement is
locked, so a later version never changes one you use.

## Import

```python
import bend-mathlib@0.8.2.0/nat.bend as MNat
```

Each module imports on its own; `all.bend` imports them all. To pin the exact bytes, import by
content hash instead of name: `import 0x<hash>/nat.bend as MNat`. The hash of
bend-mathlib@0.8.2.0 is what `curl -s https://hub.bend-lang.com/name/bend-mathlib@0.8.2.0` prints, what
`bend` stored in `~/.bend/lib/names/bend-mathlib@0.8.2.0` (or under `$BEND_LIB`) when it first resolved
the name, and the name of the directory this package was fetched into. This README cannot state it:
the README is part of the package that the hash covers.

## Modules

| module | scope | lemmas | `_sym` twins | predicates | typed defs |
|---|---|---|---|---|---|
| `algebra` | Abstract associativity/commutativity theorems and their Nat/Bool/List instances. | 18 | 18 | 0 | 0 |
| `bool` | Bool algebra (not, and, or, xor). | 40 | 36 | 0 | 0 |
| `equal` | Equality lemmas (congruence, substitution, chains). | 4 | 2 | 0 | 0 |
| `list` | List lemmas (append, reverse, length, take, drop, map, fold, filter, zip, head, last, get, all, any, find, contains, mem, sorted_by). | 113 | 95 | 2 | 0 |
| `maybe` | Maybe monad and map laws over &2. | 15 | 15 | 0 | 0 |
| `nat` | Nat arithmetic (add, mul, sub, div, mod, min, max, pow, double) and order (le, lt, ge, gt). | 233 | 134 | 4 | 0 |
| `order` | Abstract preorder/total-order facts over a Bool comparator ~le. | 5 | 4 | 0 | 0 |
| `perm` | Step-list permutations over bendlib-kernel-list, plus sort value defs and proofs. | 0 | 0 | 0 | 30 |
| `sort` | Insertion and merge sort proved sorted over perm.bend's value defs (generic ~le). | 0 | 0 | 0 | 9 |
| `string` | String append, reverse and length, and comparison. | 27 | 24 | 0 | 0 |
| `u32` | Machine words as naturals; Word(n) and U32 operations agree with Nat arithmetic (compare, add, sub, inc, not, min, max, div, from_nat). | 36 | 32 | 0 | 0 |

## Find a lemma

- A name is the shape of its statement: `add_comm`, `mul_add`, `append_assoc`, `le_trans`, `take_append_drop`.
- Each law has a one-line description directly above it, so a grep in this directory shows the
  description, the binders and the statement: `grep -n -B1 -A4 '^law add_comm:' nat.bend`.
- A generated `name_sym` twin states the same equation with its sides swapped: `add_zero` is
  `Nat.add(x, 0n) == x`, `add_zero_sym` is `x == Nat.add(x, 0n)`.
- Rewriting: `%e : P` replaces the right side of `e` with its left side, so `name` expands the simple
  side into the compound one and `name_sym` simplifies the compound side.
- Names starting with `internal_` are proof helpers, not part of the public API.
- The full index lists every lemma with its statement and the version that added it:
  `INDEX.md` in the repository, https://github.com/bendlib/bendlib/blob/main/packages/bend-mathlib/INDEX.md
  and the docs site, https://bendlib.github.io/bendlib/name/bend-mathlib/ (search by shape: https://bendlib.github.io/bendlib/search.html).

## License

See `LICENSE` beside this file.
