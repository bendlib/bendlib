# bendlib

The foundation library for [Bend 2](https://github.com/bendlang/bend): machine-checked facts you
import instead of re-proving, and tools that keep laws honest.

| Part | What | Status |
|---|---|---|
| [`bend-mathlib`](packages/bend-mathlib) | Lemmas about `Nat`, `Bool`, `List`, equality — generic, proved, checked on every Bend release | 0.1 in progress |
| [`@bendlib/reader`](tools/reader) | Reads Bend source with the official parser of your installed compiler version | working |
| `lawcheck` | Finds counterexamples to laws before you try to prove them | in progress |
| Bend docs | Rendered API docs and lemma search for every BendHub package | planned |

> Not related to the hub package `bend-math-lib` (F32 numerics).

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
