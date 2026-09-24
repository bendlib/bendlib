# bendlib

The foundation library for [Bend 2](https://github.com/bendlang/bend): machine-checked facts you
import instead of re-proving, and tools that keep laws honest.

| Part | What | Status |
|---|---|---|
| [`bend-mathlib`](packages/bend-mathlib) | 119 lemmas about `Nat`, `Bool`, `List`, equality — generic, proved, zero `@unsafe` | **0.1.0.1 on BendHub** |
| [`@bendlib/reader`](tools/reader) | Reads Bend source with the official parser of your installed compiler version | working |
| [`lawcheck`](tools/lawcheck) | Finds counterexamples to laws before you try to prove them, and shrinks them | v0.1 working |
| [Bend Docs](https://bendlib.github.io/bendlib/) | API docs, checker status and law-shape search for every BendHub package | **live**, rebuilt hourly |

## Use it

![86 lines by hand vs one import and four rewrites](examples/demo/demo.gif)

```python
import bend-mathlib@0.1.0.1/nat.bend as MNat
import bend-mathlib@0.1.0.1/list.bend as MList

law my_rev:
  for xs: List<&2, U32>
  {List.reverse(&2, U32, List.reverse(&2, U32, xs)) == xs : List<&2, U32>}

def my_rev(xs):
  MList.reverse_reverse(&2, U32, xs)
```

Every lemma with its statement: [packages/bend-mathlib/README.md](packages/bend-mathlib/README.md).
By hash (content-pinned): `import 0xafc61ca8b7738a6df7f28eddf80168f8/nat.bend as MNat`.

## Principles

- **Never breaks dependents.** Published statements are append-only (`PUBLIC_API.lock`), and
  mathlib holds only definitions that stay compatible across its own versions.
- **Zero `@unsafe`.** Every module must print exactly `All terms check.` on the pinned compiler.
- **Built for AI provers too.** Mathlib-standard names, one-line statements, generated
  `_sym` twins for the rewrite direction that simplifies.

The architecture and its evidence are in [PLAN.md](PLAN.md) and [research/experiments](research/experiments).

## Develop

```sh
bun tools/install-bend.ts                          # the pinned compiler (toolchain.json)
bun test tools/                                    # tool tests
bun tools/mathlib/check.ts packages/bend-mathlib   # every module checks
bun tools/mathlib/lint.ts packages/bend-mathlib --erasure
```

Apache-2.0.
