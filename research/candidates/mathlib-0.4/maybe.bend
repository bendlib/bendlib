import Base

law maybe_pure_bind:
  for ~A: Data
  for ~B: Data
  for f: A -> Maybe<&2, B>
  for x: A
  {Maybe.bind(&2, A, B, Maybe.pure(&2, A, x), f) == f(x) : Maybe<&2, B>}

def maybe_pure_bind(A, B, f, x):
  {==}

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

law maybe_bind_assoc:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for f: A -> Maybe<&2, B>
  for g: B -> Maybe<&2, C>
  for m: Maybe<&2, A>
  {Maybe.bind(&2, B, C, Maybe.bind(&2, A, B, m, f), g) == Maybe.bind(&2, A, C, m, x => Maybe.bind(&2, B, C, f(x), g)) : Maybe<&2, C>}

def maybe_bind_assoc(A, B, C, f, g, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

law maybe_map_pure:
  for ~A: Data
  for ~B: Data
  for f: A -> B
  for x: A
  {Maybe.map(&2, A, B, f, Maybe.pure(&2, A, x)) == Maybe.pure(&2, B, f(x)) : Maybe<&2, B>}

def maybe_map_pure(A, B, f, x):
  {==}

law maybe_map_compose:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for f: A -> B
  for g: B -> C
  for m: Maybe<&2, A>
  {Maybe.map(&2, B, C, g, Maybe.map(&2, A, B, f, m)) == Maybe.map(&2, A, C, x => g(f(x)), m) : Maybe<&2, C>}

def maybe_map_compose(A, B, C, f, g, m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}
