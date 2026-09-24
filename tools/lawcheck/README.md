# lawcheck

`lawcheck` looks for counterexamples to the `law`s of a Bend 2 file before anyone tries to prove them, and shrinks the ones it finds. **It never proves anything.** A ✓ only means that no counterexample turned up among the instances it tried.

## Install

Download `lawcheck-<os>-<arch>` from the latest `lawcheck-v*` release at https://github.com/bendlib/bendlib/releases, `chmod +x`, and put it on PATH. It needs `bend` installed; the first run downloads the matching `bend.ts` (network).

```sh
bun tools/lawcheck/cli.ts LAWS.bend                  # every law in the file, open or proved
bun tools/lawcheck/cli.ts LAWS.bend --law ins_sorted # one law
bun tools/lawcheck/cli.ts LAWS.bend --json           # machine output
bun tools/lawcheck/cli.ts LAWS.bend --impl other.bend  # swap the file's local import for another implementation
```

Options: `--size N` sets the depth of the exhaustive small-scope phase (default 3). `--max-instances N` caps the instances per law (default 200). `--max-nat N` bounds the random `Nat`s (default 30; the exhaustive small-scope phase is unchanged). `--seed S` seeds the random phase (default 1, so runs are reproducible, including with `--law`). `--jobs N` sets how many parallel `bend` processes run (default: all cores). `--timeout MS` sets the limit for each `bend` run. `--native` also evaluates eligible instances with a compiled program and reports where it disagrees with the checker (possible compiler or runtime bug).

Exit codes: 0 means no counterexample was found. 1 means at least one counterexample was found. 2 means a usage error, a file that does not load or type-check, or a tool error.

```
✗ ins_sorted  counterexample (shrunk from x = 0n, xs = [5n, 6n] in 3 steps); 1/3 instances failed, premises held in 3/3
             x = 0n
             xs = [1n]
             premise  {is_sorted([1n]) == True{} : Bool}  (holds)
             lhs  is_sorted(ins(0n, [1n])) = False{}
             rhs  True{} = True{}
             checker: expected False{} · observed True{}
✓ dbl_add     10 instances, 0 failures (sizes ≤ 3)
~ fn_binder   skipped: function-typed binder f: @_:Nat -> Nat (v0.2)
```

## How it works

1. **Load.** `@bendlib/reader` (the official `bend.ts` parser) lists the laws, their binders and their claims, plus every datatype and its constructors.
2. **Instantiate.** Quantity parameters become `&2`. Type parameters (`Type`, `Data`, `Kind(a)`, including `~A` template type parameters) are instantiated as `U32` and then as `Nat`, and the instance budget is split between the two.
3. **Generate.** The first phase is an exhaustive small-scope search at depths 0..size, sampled once a depth no longer fits the budget. A seeded random phase then fills the budget. There are generators for `Nat`, `U32` (0, 1, 2, 4294967295 and random values), `Char`, `String`, `List`, `Pair`/`A & B`, and every datatype whose constructor fields can themselves be generated. That covers `Bool`, `Maybe`, `Result`, `Either`, `Cmp`, `Unit` and user types. Recursive fields are bounded by depth.
4. **Evaluate (engine C, PLAN F22).** Each instance becomes `law lc_i: {lhs == rhs : T}` plus `def lc_i(): {==}`, written into a batch file in a temp directory. The batch file imports the user's file by absolute path as `U` and every other non-Base module it loads as `LCk`, and it names the user's declarations through those aliases. Batches run in parallel with `bend --check-only`. The checker checks declarations in file order and stops at the first failure. lawcheck parses `Location: lc_i` and the `expected`/`observed` pair, counts every earlier instance as passed, and re-runs the batch from `lc_i+1`. A clean batch is exactly `All terms check.`; a verdict of `All terms check, but N defs rely on unsafe or foreign code:` is **not** a pass — the laws whose instances rest on `@unsafe`/foreign code are skipped, with the reliance count surfaced, so a `✓` always means the checker's own verdict was clean.
5. **Shrink.** A `Nat` shrinks toward 0, a list by dropping or shrinking elements, a datatype value to a recursive subterm, a nullary constructor, or smaller fields. All candidates for one step go into a single batch, ordered smallest first, so the checker's first failure is the best candidate.
6. **Display.** A `?g` hole on the shrunk instance makes the checker print the fully normalized goal, which gives the `lhs = …` and `rhs = …` values.

Claim kinds:
- An **equation** `{lhs == rhs : T}` is checked as described above.
- A **predicate** claim that is a single application of a `Type`/`Data`-valued def, such as `le(a, b)`, is tried with `{==}`. When its goal does not reduce to an equality, the law is reported as "not decidable by evaluation".
- **Implication premises** (a binder whose type is an equation or a predicate application, such as `for h: {is_sorted(xs) == True{} : Bool}` or `for ab: le(a, b)`) are evaluated first. An instance whose premise fails is dropped, and the output reports how many instances satisfied the premises. When no instance does, the law is reported as vacuous.
- A **refutation** (claim `Empty` with premises) fails when some instance satisfies all of its premises.

## Mutation mode

`lawcheck mutate LAWS.bend` checks the laws against every small mutant of the target's defs. A mutant is **killed** when some law finds a counterexample on it, **survived** when every law passes (the laws do not pin that change), and **invalid** when it does not type-check (discarded, never a kill). A survivor can also be an equivalent mutant (same behaviour) — check it by hand.

Operators: `arm-swap`/`arm-copy` (swap or copy `match` arm bodies), `literal` (`0n↔1n`, `True{}↔False{}`), `drop-succ` (`1n+E → E`), `drop-cons` (`A <> B → B`), `arg-swap` (swap adjacent call arguments), `projection` (replace the body with a parameter or a constant), `base-swap` (`Nat.is_le↔Nat.is_lt`, `&&↔||`, `Nat.add→Nat.sub`, …).

```sh
bun tools/lawcheck/cli.ts mutate LAWS.bend                 # all defs
bun tools/lawcheck/cli.ts mutate LAWS.bend --def app       # one def
bun tools/lawcheck/cli.ts mutate LAWS.bend --json          # machine output
```

```
$ bun tools/lawcheck/cli.ts mutate tools/lawcheck/test/fixtures/mut_weak.bend
lawcheck mutate 0.2.0 · tools/lawcheck/test/fixtures/mut_weak.bend (impl lib_ok.bend) · bend 2.0.27 · ≤50 instances/law
size  1/4 valid mutants killed · 3 survived · 6 invalid
      survived  arm-copy  line 12  1n+size(r) → 0n
      survived  drop-succ  line 12  1n+size(r) → size(r)
      survived  projection  line 8  match s: → 0n
app   3/3 valid mutants killed · 0 survived · 7 invalid
3 survivor(s): your laws do not pin these changes. A survivor can also be an equivalent mutant (same behaviour); check it by hand.
```

Exit codes: 0 no survivors · 1 at least one survivor · 2 usage, load, tool error, or an `error` mutant. A target with no mutable defs is a usage error (`no mutable defs`), never `no survivors`. A survivor shows a weakness of the laws for these operators; zero survivors does not prove the laws pin the def.

## Native comparison (`--native`)

For equation laws whose claim type is `Nat`, `U32`, or `Bool`, `--native` evaluates each instance a second way (engine N, PLAN §4.2 step 6): it emits one `main` that prints `lhs == rhs` for every instance, builds it with `bend -o`, runs it, and compares the result with the checker (engine C). Any instance where the two engines disagree is a likely compiler or runtime bug; it is reported with the instance bindings and a minimal reproduction file. Laws whose claim is not such an equation, or whose target does not build natively, are left to the checker alone.

## Known limits (v0.1)

- A law whose evaluation rests on `@unsafe` or foreign code is skipped, never passed. When the checker prints `All terms check, but N defs rely on unsafe or foreign code:` the verdict is surfaced with its reliance count; when open proofs make bend suppress that summary (`Error: N TODOs found.`), lawcheck scans the target and its non-Base imports for `@unsafe` and skips the law with a note. That scan is conservative and file-level: any `@unsafe` in those files skips a law whose verdict was suppressed, even if that law happens not to use the unsafe def.
- Function-typed template binders (`for ~f: A -> B`) are instantiated from a small catalog of closed lambdas per instantiated signature; a signature outside the catalog, a proposition-typed template binder, and a non-template function-typed binder are skipped with a reason.
- `where` premises (`for y: B where P(y)`) are evaluated like implication premises: an instance whose premise fails is dropped and the satisfied fraction is reported. An `exs` claim (`exs y: T`) is checked by searching the generated values for a witness — a witness found within the budget passes the law, otherwise the law is skipped with `no witness found in N candidates`. It is never a fail: a finite search refutes nothing. Claims that are neither an equation nor a single predicate application (such as `Either<…>`) are skipped with a reason.
- Values are kept small because the checker evaluates unary `Nat`s: random `Nat`s are drawn from `0..min(maxNat, max(6, 3·size))`, so `--max-nat` (default 30) bounds them. An instance whose evaluation overflows the checker's unary `Nat`s (such as `Nat.pow(20n, 25n)`) is dropped as too large to evaluate and reported on the law's line; it neither passes nor fails the law, and if every instance is dropped this way the law is skipped. Types with no generator (`F32`, `Array`, `Map`, `IO`, indexed families) make lawcheck skip the law and name the type.
- If the file, or anything it imports, fails to type-check, no instance can be evaluated, because bend re-checks imports (F8). lawcheck exits 2 and shows the checker's error. This includes a file with no laws at all: lawcheck validates the target up front, so a rejected file exits 2 rather than reporting `0 laws`. Open laws are fine.
- Hub imports (`0x…`) are re-imported by their hash. That path has not been exercised yet.
- A target directory is a typed load error (exit 2), never a raw stack. A target path containing whitespace is copied into the batch temp directory under a safe basename (bend `import` lines are unquoted) with its local imports rewritten to absolute realpaths; a symlink to such a path works the same way.
- Batch files are left in `$TMPDIR/lawcheck-*` (the path is printed) and are never deleted.
- lawcheck is tested only on bend 2.0.27.
