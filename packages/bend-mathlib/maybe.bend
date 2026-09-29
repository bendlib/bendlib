# bend-mathlib/maybe.bend: Maybe monad and map laws over &2.
import Base

# Left identity: binding a pure value applies the function.
law maybe_pure_bind:
  for ~A: Data
  for ~B: Data
  for -f: A -> Maybe<&2, B>
  for -x: A
  {Maybe.bind(&2, A, B, Maybe.pure(&2, A, x), f) == f(x) : Maybe<&2, B>}

def maybe_pure_bind(A, B, f, x):
  {==}

# Right identity: binding pure is the identity.
law maybe_bind_pure:
  for ~A: Data
  for m: Maybe<&2, A>
  {Maybe.bind(&2, A, A, m, x => Maybe.pure(&2, A, x)) == m : Maybe<&2, A>}

def maybe_bind_pure(A, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Bind is associative.
law maybe_bind_assoc:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for -f: A -> Maybe<&2, B>
  for -g: B -> Maybe<&2, C>
  for m: Maybe<&2, A>
  {Maybe.bind(&2, B, C, Maybe.bind(&2, A, B, m, f), g) == Maybe.bind(&2, A, C, m, x => Maybe.bind(&2, B, C, f(x), g)) : Maybe<&2, C>}

def maybe_bind_assoc(A, B, C, f, g, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Mapping a pure value is pure of the mapped value.
law maybe_map_pure:
  for ~A: Data
  for ~B: Data
  for -f: A -> B
  for -x: A
  {Maybe.map(&2, A, B, f, Maybe.pure(&2, A, x)) == Maybe.pure(&2, B, f(x)) : Maybe<&2, B>}

def maybe_map_pure(A, B, f, x):
  {==}

# Mapping a composition maps the composition.
law maybe_map_compose:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for -f: A -> B
  for -g: B -> C
  for m: Maybe<&2, A>
  {Maybe.map(&2, B, C, g, Maybe.map(&2, A, B, f, m)) == Maybe.map(&2, A, C, x => g(f(x)), m) : Maybe<&2, C>}

def maybe_map_compose(A, B, C, f, g, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Mapping the identity gives the value back.
law maybe_map_id:
  for ~A: Data
  for m: Maybe<&2, A>
  {Maybe.map(&2, A, A, x => x, m) == m : Maybe<&2, A>}

def maybe_map_id(A, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Binding a function that always fails gives None.
law maybe_bind_none:
  for ~A: Data
  for ~B: Data
  for m: Maybe<&2, A>
  {Maybe.bind(&2, A, B, m, x => None{}) == None{} : Maybe<&2, B>}

def maybe_bind_none(A, B, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Mapping is binding the function followed by pure.
law maybe_map_eq_bind:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for m: Maybe<&2, A>
  {Maybe.map(&2, A, B, f, m) == Maybe.bind(&2, A, B, m, x => Maybe.pure(&2, B, f(x))) : Maybe<&2, B>}

def maybe_map_eq_bind(A, B, f, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Mapping keeps whether a value is present.
law maybe_is_some_map:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for m: Maybe<&2, A>
  {Maybe.is_some(&2, B, Maybe.map(&2, A, B, f, m)) == Maybe.is_some(&2, A, m) : Bool}

def maybe_is_some_map(A, B, f, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Mapping keeps whether a value is absent.
law maybe_is_none_map:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for m: Maybe<&2, A>
  {Maybe.is_none(&2, B, Maybe.map(&2, A, B, f, m)) == Maybe.is_none(&2, A, m) : Bool}

def maybe_is_none_map(A, B, f, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# The default of a map, with the mapped default, is the mapped default of the original.
law maybe_default_map:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for m: Maybe<&2, A>
  for -d: A
  {Maybe.default(&2, B, Maybe.map(&2, A, B, f, m), f(d)) == f(Maybe.default(&2, A, m, d)) : B}

def maybe_default_map(A, B, f, m, d):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# None is a right identity for or.
law maybe_or_none:
  for ~A: Data
  for m: Maybe<&2, A>
  {Maybe.or(&2, A, m, None{}) == m : Maybe<&2, A>}

def maybe_or_none(A, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Or is associative.
law maybe_or_assoc:
  for ~A: Data
  for m: Maybe<&2, A>
  for -n: Maybe<&2, A>
  for -k: Maybe<&2, A>
  {Maybe.or(&2, A, Maybe.or(&2, A, m, n), k) == Maybe.or(&2, A, m, Maybe.or(&2, A, n, k)) : Maybe<&2, A>}

def maybe_or_assoc(A, m, n, k):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Binding after a map binds the composition.
law maybe_bind_map:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B
  for ~g: B -> Maybe<&2, C>
  for m: Maybe<&2, A>
  {Maybe.bind(&2, B, C, Maybe.map(&2, A, B, f, m), g) == Maybe.bind(&2, A, C, m, x => g(f(x))) : Maybe<&2, C>}

def maybe_bind_map(A, B, C, f, g, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Mapping after a bind maps inside the bound function.
law maybe_map_bind:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> Maybe<&2, B>
  for ~g: B -> C
  for m: Maybe<&2, A>
  {Maybe.map(&2, B, C, g, Maybe.bind(&2, A, B, m, f)) == Maybe.bind(&2, A, C, m, x => Maybe.map(&2, B, C, g, f(x))) : Maybe<&2, C>}

def maybe_map_bind(A, B, C, f, g, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# Left identity: binding a pure value applies the function, reversed to rewrite toward the simple side.
law maybe_pure_bind_sym:
  for ~A: Data
  for ~B: Data
  for -f: A -> Maybe<&2, B>
  for -x: A
  {f(x) == Maybe.bind(&2, A, B, Maybe.pure(&2, A, x), f) : Maybe<&2, B>}

def maybe_pure_bind_sym(A, B, f, x):
  Equal.sym(Maybe<&2, B>, Maybe.bind(&2, A, B, Maybe.pure(&2, A, x), f), f(x), maybe_pure_bind(~A, ~B, f, x))

# Right identity: binding pure is the identity, reversed to rewrite toward the simple side.
law maybe_bind_pure_sym:
  for ~A: Data
  for m: Maybe<&2, A>
  {m == Maybe.bind(&2, A, A, m, x => Maybe.pure(&2, A, x)) : Maybe<&2, A>}

def maybe_bind_pure_sym(A, m):
  Equal.sym(Maybe<&2, A>, Maybe.bind(&2, A, A, m, x => Maybe.pure(&2, A, x)), m, maybe_bind_pure(~A, m))

# Bind is associative, reversed to rewrite toward the simple side.
law maybe_bind_assoc_sym:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for -f: A -> Maybe<&2, B>
  for -g: B -> Maybe<&2, C>
  for m: Maybe<&2, A>
  {Maybe.bind(&2, A, C, m, x => Maybe.bind(&2, B, C, f(x), g)) == Maybe.bind(&2, B, C, Maybe.bind(&2, A, B, m, f), g) : Maybe<&2, C>}

def maybe_bind_assoc_sym(A, B, C, f, g, m):
  Equal.sym(Maybe<&2, C>, Maybe.bind(&2, B, C, Maybe.bind(&2, A, B, m, f), g), Maybe.bind(&2, A, C, m, x => Maybe.bind(&2, B, C, f(x), g)), maybe_bind_assoc(~A, ~B, ~C, f, g, m))

# Mapping a pure value is pure of the mapped value, reversed to rewrite toward the simple side.
law maybe_map_pure_sym:
  for ~A: Data
  for ~B: Data
  for -f: A -> B
  for -x: A
  {Maybe.pure(&2, B, f(x)) == Maybe.map(&2, A, B, f, Maybe.pure(&2, A, x)) : Maybe<&2, B>}

def maybe_map_pure_sym(A, B, f, x):
  Equal.sym(Maybe<&2, B>, Maybe.map(&2, A, B, f, Maybe.pure(&2, A, x)), Maybe.pure(&2, B, f(x)), maybe_map_pure(~A, ~B, f, x))

# Mapping a composition maps the composition, reversed to rewrite toward the simple side.
law maybe_map_compose_sym:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for -f: A -> B
  for -g: B -> C
  for m: Maybe<&2, A>
  {Maybe.map(&2, A, C, x => g(f(x)), m) == Maybe.map(&2, B, C, g, Maybe.map(&2, A, B, f, m)) : Maybe<&2, C>}

def maybe_map_compose_sym(A, B, C, f, g, m):
  Equal.sym(Maybe<&2, C>, Maybe.map(&2, B, C, g, Maybe.map(&2, A, B, f, m)), Maybe.map(&2, A, C, x => g(f(x)), m), maybe_map_compose(~A, ~B, ~C, f, g, m))

# Mapping the identity gives the value back, reversed to rewrite toward the simple side.
law maybe_map_id_sym:
  for ~A: Data
  for m: Maybe<&2, A>
  {m == Maybe.map(&2, A, A, x => x, m) : Maybe<&2, A>}

def maybe_map_id_sym(A, m):
  Equal.sym(Maybe<&2, A>, Maybe.map(&2, A, A, x => x, m), m, maybe_map_id(~A, m))

# Binding a function that always fails gives None, reversed to rewrite toward the simple side.
law maybe_bind_none_sym:
  for ~A: Data
  for ~B: Data
  for m: Maybe<&2, A>
  {None{} == Maybe.bind(&2, A, B, m, x => None{}) : Maybe<&2, B>}

def maybe_bind_none_sym(A, B, m):
  Equal.sym(Maybe<&2, B>, Maybe.bind(&2, A, B, m, x => None{}), None{}, maybe_bind_none(~A, ~B, m))

# Mapping is binding the function followed by pure, reversed to rewrite toward the simple side.
law maybe_map_eq_bind_sym:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for m: Maybe<&2, A>
  {Maybe.bind(&2, A, B, m, x => Maybe.pure(&2, B, f(x))) == Maybe.map(&2, A, B, f, m) : Maybe<&2, B>}

def maybe_map_eq_bind_sym(A, B, f, m):
  Equal.sym(Maybe<&2, B>, Maybe.map(&2, A, B, f, m), Maybe.bind(&2, A, B, m, x => Maybe.pure(&2, B, f(x))), maybe_map_eq_bind(~A, ~B, ~f, m))

# Mapping keeps whether a value is present, reversed to rewrite toward the simple side.
law maybe_is_some_map_sym:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for m: Maybe<&2, A>
  {Maybe.is_some(&2, A, m) == Maybe.is_some(&2, B, Maybe.map(&2, A, B, f, m)) : Bool}

def maybe_is_some_map_sym(A, B, f, m):
  Equal.sym(Bool, Maybe.is_some(&2, B, Maybe.map(&2, A, B, f, m)), Maybe.is_some(&2, A, m), maybe_is_some_map(~A, ~B, ~f, m))

# Mapping keeps whether a value is absent, reversed to rewrite toward the simple side.
law maybe_is_none_map_sym:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for m: Maybe<&2, A>
  {Maybe.is_none(&2, A, m) == Maybe.is_none(&2, B, Maybe.map(&2, A, B, f, m)) : Bool}

def maybe_is_none_map_sym(A, B, f, m):
  Equal.sym(Bool, Maybe.is_none(&2, B, Maybe.map(&2, A, B, f, m)), Maybe.is_none(&2, A, m), maybe_is_none_map(~A, ~B, ~f, m))

# The default of a map, with the mapped default, is the mapped default of the original, reversed to rewrite toward the simple side.
law maybe_default_map_sym:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for m: Maybe<&2, A>
  for -d: A
  {f(Maybe.default(&2, A, m, d)) == Maybe.default(&2, B, Maybe.map(&2, A, B, f, m), f(d)) : B}

def maybe_default_map_sym(A, B, f, m, d):
  Equal.sym(B, Maybe.default(&2, B, Maybe.map(&2, A, B, f, m), f(d)), f(Maybe.default(&2, A, m, d)), maybe_default_map(~A, ~B, ~f, m, d))

# None is a right identity for or, reversed to rewrite toward the simple side.
law maybe_or_none_sym:
  for ~A: Data
  for m: Maybe<&2, A>
  {m == Maybe.or(&2, A, m, None{}) : Maybe<&2, A>}

def maybe_or_none_sym(A, m):
  Equal.sym(Maybe<&2, A>, Maybe.or(&2, A, m, None{}), m, maybe_or_none(~A, m))

# Or is associative, reversed to rewrite toward the simple side.
law maybe_or_assoc_sym:
  for ~A: Data
  for m: Maybe<&2, A>
  for -n: Maybe<&2, A>
  for -k: Maybe<&2, A>
  {Maybe.or(&2, A, m, Maybe.or(&2, A, n, k)) == Maybe.or(&2, A, Maybe.or(&2, A, m, n), k) : Maybe<&2, A>}

def maybe_or_assoc_sym(A, m, n, k):
  Equal.sym(Maybe<&2, A>, Maybe.or(&2, A, Maybe.or(&2, A, m, n), k), Maybe.or(&2, A, m, Maybe.or(&2, A, n, k)), maybe_or_assoc(~A, m, n, k))

# Binding after a map binds the composition, reversed to rewrite toward the simple side.
law maybe_bind_map_sym:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B
  for ~g: B -> Maybe<&2, C>
  for m: Maybe<&2, A>
  {Maybe.bind(&2, A, C, m, x => g(f(x))) == Maybe.bind(&2, B, C, Maybe.map(&2, A, B, f, m), g) : Maybe<&2, C>}

def maybe_bind_map_sym(A, B, C, f, g, m):
  Equal.sym(Maybe<&2, C>, Maybe.bind(&2, B, C, Maybe.map(&2, A, B, f, m), g), Maybe.bind(&2, A, C, m, x => g(f(x))), maybe_bind_map(~A, ~B, ~C, ~f, ~g, m))

# Mapping after a bind maps inside the bound function, reversed to rewrite toward the simple side.
law maybe_map_bind_sym:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> Maybe<&2, B>
  for ~g: B -> C
  for m: Maybe<&2, A>
  {Maybe.bind(&2, A, C, m, x => Maybe.map(&2, B, C, g, f(x))) == Maybe.map(&2, B, C, g, Maybe.bind(&2, A, B, m, f)) : Maybe<&2, C>}

def maybe_map_bind_sym(A, B, C, f, g, m):
  Equal.sym(Maybe<&2, C>, Maybe.map(&2, B, C, g, Maybe.bind(&2, A, B, m, f)), Maybe.bind(&2, A, C, m, x => Maybe.map(&2, B, C, g, f(x))), maybe_map_bind(~A, ~B, ~C, ~f, ~g, m))
