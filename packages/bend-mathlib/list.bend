import Base
import ./nat.bend as MNat

# The empty list is a right identity for append: xs ++ [] = xs.
law append_nil:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.append(a, A, xs, Nil{}) == xs : List<a, A>}

def append_nil(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_nil(a, A, t) : {h <> List.append(a, A, t, Nil{}) == h <> _ : List<a, A>}
      {==}

# The empty list is a left identity for append: [] ++ xs = xs.
law nil_append:
  for -a: Quant
  for -A: Kind(a)
  for -xs: List<a, A>
  {List.append(a, A, Nil{}, xs) == xs : List<a, A>}

def nil_append(a, A, xs):
  {==}

# Append is associative: (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
law append_assoc:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  for -zs: List<a, A>
  {List.append(a, A, List.append(a, A, xs, ys), zs) == List.append(a, A, xs, List.append(a, A, ys, zs)) : List<a, A>}

def append_assoc(a, A, xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_assoc(a, A, t, ys, zs) : {h <> List.append(a, A, List.append(a, A, t, ys), zs) == h <> _ : List<a, A>}
      {==}

# The length of an append is the sum of the lengths.
law length_append:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  {List.length(a, A, List.append(a, A, xs, ys)) == Nat.add(List.length(a, A, xs), List.length(a, A, ys)) : Nat}

def length_append(a, A, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %length_append(a, A, t, ys) : {1n+List.length(a, A, List.append(a, A, t, ys)) == 1n+_ : Nat}
      {==}

def internal_reverse_go_append(a, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>, -acc: List<a, A>) -> {List.reverse.go(a, A, xs, List.append(a, A, ys, acc)) == List.append(a, A, List.reverse.go(a, A, xs, ys), acc) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_reverse_go_append(a, A, t, h <> ys, acc)

# The reverse accumulator loop appends the reversed list to the accumulator.
law reverse_go_spec:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -acc: List<a, A>
  {List.reverse.go(a, A, xs, acc) == List.append(a, A, List.reverse(a, A, xs), acc) : List<a, A>}

def reverse_go_spec(a, A, xs, acc):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_reverse_go_append(a, A, t, h <> Nil{}, acc)

def internal_reverse_append_go(a, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>, -acc: List<a, A>) -> {List.reverse.go(a, A, List.append(a, A, xs, ys), acc) == List.reverse.go(a, A, ys, List.reverse.go(a, A, xs, acc)) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_reverse_append_go(a, A, t, ys, h <> acc)

# Reversing an append reverses and swaps the parts: reverse (xs ++ ys) = reverse ys ++ reverse xs.
law reverse_append:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.reverse(a, A, List.append(a, A, xs, ys)) == List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)) : List<a, A>}

def reverse_append(a, A, xs, ys):
  Equal.trans(List<a, A>, List.reverse(a, A, List.append(a, A, xs, ys)), List.reverse.go(a, A, ys, List.reverse(a, A, xs)), List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)), internal_reverse_append_go(a, A, xs, ys, Nil{}), reverse_go_spec(a, A, ys, List.reverse(a, A, xs)))

def internal_reverse_go_go(a, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>) -> {List.reverse.go(a, A, List.reverse.go(a, A, xs, acc), Nil{}) == List.reverse.go(a, A, acc, xs) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_reverse_go_go(a, A, t, h <> acc)

# Reversing twice gives the list back.
law reverse_reverse:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.reverse(a, A, List.reverse(a, A, xs)) == xs : List<a, A>}

def reverse_reverse(a, A, xs):
  internal_reverse_go_go(a, A, xs, Nil{})

def internal_length_reverse_go(a, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>, +n: Nat, e: {List.length(a, A, acc) == n : Nat}) -> {List.length(a, A, List.reverse.go(a, A, xs, acc)) == Nat.add(n, List.length(a, A, xs)) : Nat}:
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(n, 0n), n, MNat.add_zero(n)) : {List.length(a, A, acc) == _ : Nat}
      e
    case h <> t:
      %Equal.sym(Nat, Nat.add(n, 1n+List.length(a, A, t)), 1n+Nat.add(n, List.length(a, A, t)), MNat.add_succ(n, List.length(a, A, t))) : {List.length(a, A, List.reverse.go(a, A, t, h <> acc)) == _ : Nat}
      internal_length_reverse_go(a, A, t, h <> acc, 1n+n, Equal.cong(Nat, Nat, k => 1n+k, List.length(a, A, acc), n, e))

# Reversing preserves the length.
law length_reverse:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.length(a, A, List.reverse(a, A, xs)) == List.length(a, A, xs) : Nat}

def length_reverse(a, A, xs):
  internal_length_reverse_go(a, A, xs, Nil{}, 0n, {==})

# A right fold over an append folds the first part onto the fold of the second.
law foldr_append:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: A -> B -> B
  for xs: List<a, A>
  for -ys: List<a, A>
  for -z: B
  {List.foldr(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) == List.foldr(~a, ~A, ~B, ~f, xs, List.foldr(~a, ~A, ~B, ~f, ys, z)) : B}

def foldr_append(a, A, B, f, xs, ys, z):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %foldr_append(~a, ~A, ~B, ~f, t, ys, z) : {f(h, List.foldr(~a, ~A, ~B, ~f, List.append(a, A, t, ys), z)) == f(h, _) : B}
      {==}

# Taking n elements and appending the rest after dropping n gives the list back.
law take_append_drop:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {List.append(a, A, List.take(a, A, xs, n), List.drop(a, A, xs, n)) == xs : List<a, A>}

def take_append_drop(a, A, xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      %take_append_drop(a, A, t, p) : {h <> List.append(a, A, List.take(a, A, t, p), List.drop(a, A, t, p)) == h <> _ : List<a, A>}
      {==}

# Mapping preserves the length.
law length_map:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.length(&1, B, List.map(~A, ~B, ~f, xs)) == List.length(&1, A, xs) : Nat}

def length_map(A, B, f, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %length_map(~A, ~B, ~f, t) : {1n+List.length(&1, B, List.map(~A, ~B, ~f, t)) == 1n+_ : Nat}
      {==}

# Mapping over an append maps each part: map f (xs ++ ys) = map f xs ++ map f ys.
law map_append:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  for -ys: List<A>
  {List.map(~A, ~B, ~f, List.append(&1, A, xs, ys)) == List.append(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, ys)) : List<B>}

def map_append(A, B, f, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %map_append(~A, ~B, ~f, t, ys) : {f(h) <> List.map(~A, ~B, ~f, List.append(&1, A, t, ys)) == f(h) <> _ : List<B>}
      {==}

# Mapping twice is mapping the composition: map g (map f xs) = map (g . f) xs.
law map_map:
  for ~A: Type
  for ~B: Type
  for ~C: Type
  for ~f: A -> B
  for ~g: B -> C
  for xs: List<A>
  {List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, xs)) == List.map(~A, ~C, ~(x => g(f(x))), xs) : List<C>}

def map_map(A, B, C, f, g, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %map_map(~A, ~B, ~C, ~f, ~g, t) : {g(f(h)) <> List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, t)) == g(f(h)) <> _ : List<C>}
      {==}

# Taking zero elements gives the empty list.
law take_zero:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.take(a, A, xs, 0n) == Nil{} : List<a, A>}

def take_zero(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# Dropping zero elements gives the list back.
law drop_zero:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.drop(a, A, xs, 0n) == xs : List<a, A>}

def drop_zero(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# Taking from the empty list gives the empty list.
law take_nil:
  for -a: Quant
  for -A: Kind(a)
  for -n: Nat
  {List.take(a, A, Nil{}, n) == Nil{} : List<a, A>}

def take_nil(a, A, n):
  {==}

# Dropping from the empty list gives the empty list.
law drop_nil:
  for -a: Quant
  for -A: Kind(a)
  for -n: Nat
  {List.drop(a, A, Nil{}, n) == Nil{} : List<a, A>}

def drop_nil(a, A, n):
  {==}

# Taking n elements leaves min(n, length) of them.
law length_take:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {List.length(a, A, List.take(a, A, xs, n)) == Nat.min(n, List.length(a, A, xs)) : Nat}

def length_take(a, A, xs, n):
  match xs n:
    case Nil{} _:
      Equal.sym(Nat, Nat.min(n, 0n), 0n, MNat.min_zero(n))
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      %length_take(a, A, t, p) : {1n+List.length(a, A, List.take(a, A, t, p)) == 1n+_ : Nat}
      {==}

# Dropping n elements leaves length - n of them.
law length_drop:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {List.length(a, A, List.drop(a, A, xs, n)) == Nat.sub(List.length(a, A, xs), n) : Nat}

def length_drop(a, A, xs, n):
  match xs n:
    case Nil{} _:
      Equal.sym(Nat, Nat.sub(0n, n), 0n, MNat.zero_sub(n))
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      length_drop(a, A, t, p)

# Taking as many elements as the list has gives the list back.
law take_length:
  for -A: Data
  for +xs: List<&2, A>
  {List.take(&2, A, xs, List.length(&2, A, xs)) == xs : List<&2, A>}

def take_length(A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %take_length(A, t) : {h <> List.take(&2, A, t, List.length(&2, A, t)) == h <> _ : List<&2, A>}
      {==}

# Dropping as many elements as the list has gives the empty list.
law drop_length:
  for -A: Data
  for +xs: List<&2, A>
  {List.drop(&2, A, xs, List.length(&2, A, xs)) == Nil{} : List<&2, A>}

def drop_length(A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      drop_length(A, t)

# Taking m from the first n is taking min(n, m).
law take_take:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for m: Nat
  {List.take(a, A, List.take(a, A, xs, n), m) == List.take(a, A, xs, Nat.min(n, m)) : List<a, A>}

def take_take(a, A, xs, n, m):
  match xs n m:
    case Nil{} _ _:
      {==}
    case h <> t 0n _:
      {==}
    case h <> t 1n+p 0n:
      {==}
    case h <> t 1n+p 1n+q:
      %take_take(a, A, t, p, q) : {h <> List.take(a, A, List.take(a, A, t, p), q) == h <> _ : List<a, A>}
      {==}

# Dropping m after dropping n is dropping n + m.
law drop_drop:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for -m: Nat
  {List.drop(a, A, List.drop(a, A, xs, n), m) == List.drop(a, A, xs, Nat.add(n, m)) : List<a, A>}

def drop_drop(a, A, xs, n, m):
  match xs n m:
    case Nil{} _ _:
      {==}
    case h <> t 0n _:
      {==}
    case h <> t 1n+p _:
      drop_drop(a, A, t, p, m)

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# The empty list is a right identity for append: xs ++ [] = xs, reversed to rewrite toward the simple side.
law append_nil_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {xs == List.append(a, A, xs, Nil{}) : List<a, A>}

def append_nil_sym(a, A, xs):
  Equal.sym(List<a, A>, List.append(a, A, xs, Nil{}), xs, append_nil(a, A, xs))

# The empty list is a left identity for append: [] ++ xs = xs, reversed to rewrite toward the simple side.
law nil_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for -xs: List<a, A>
  {xs == List.append(a, A, Nil{}, xs) : List<a, A>}

def nil_append_sym(a, A, xs):
  Equal.sym(List<a, A>, List.append(a, A, Nil{}, xs), xs, nil_append(a, A, xs))

# Append is associative: (xs ++ ys) ++ zs = xs ++ (ys ++ zs), reversed to rewrite toward the simple side.
law append_assoc_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  for -zs: List<a, A>
  {List.append(a, A, xs, List.append(a, A, ys, zs)) == List.append(a, A, List.append(a, A, xs, ys), zs) : List<a, A>}

def append_assoc_sym(a, A, xs, ys, zs):
  Equal.sym(List<a, A>, List.append(a, A, List.append(a, A, xs, ys), zs), List.append(a, A, xs, List.append(a, A, ys, zs)), append_assoc(a, A, xs, ys, zs))

# The length of an append is the sum of the lengths, reversed to rewrite toward the simple side.
law length_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  {Nat.add(List.length(a, A, xs), List.length(a, A, ys)) == List.length(a, A, List.append(a, A, xs, ys)) : Nat}

def length_append_sym(a, A, xs, ys):
  Equal.sym(Nat, List.length(a, A, List.append(a, A, xs, ys)), Nat.add(List.length(a, A, xs), List.length(a, A, ys)), length_append(a, A, xs, ys))

# The reverse accumulator loop appends the reversed list to the accumulator, reversed to rewrite toward the simple side.
law reverse_go_spec_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -acc: List<a, A>
  {List.append(a, A, List.reverse(a, A, xs), acc) == List.reverse.go(a, A, xs, acc) : List<a, A>}

def reverse_go_spec_sym(a, A, xs, acc):
  Equal.sym(List<a, A>, List.reverse.go(a, A, xs, acc), List.append(a, A, List.reverse(a, A, xs), acc), reverse_go_spec(a, A, xs, acc))

# Reversing an append reverses and swaps the parts: reverse (xs ++ ys) = reverse ys ++ reverse xs, reversed to rewrite toward the simple side.
law reverse_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)) == List.reverse(a, A, List.append(a, A, xs, ys)) : List<a, A>}

def reverse_append_sym(a, A, xs, ys):
  Equal.sym(List<a, A>, List.reverse(a, A, List.append(a, A, xs, ys)), List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)), reverse_append(a, A, xs, ys))

# Reversing twice gives the list back, reversed to rewrite toward the simple side.
law reverse_reverse_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {xs == List.reverse(a, A, List.reverse(a, A, xs)) : List<a, A>}

def reverse_reverse_sym(a, A, xs):
  Equal.sym(List<a, A>, List.reverse(a, A, List.reverse(a, A, xs)), xs, reverse_reverse(a, A, xs))

# Reversing preserves the length, reversed to rewrite toward the simple side.
law length_reverse_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.length(a, A, xs) == List.length(a, A, List.reverse(a, A, xs)) : Nat}

def length_reverse_sym(a, A, xs):
  Equal.sym(Nat, List.length(a, A, List.reverse(a, A, xs)), List.length(a, A, xs), length_reverse(a, A, xs))

# A right fold over an append folds the first part onto the fold of the second, reversed to rewrite toward the simple side.
law foldr_append_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: A -> B -> B
  for xs: List<a, A>
  for -ys: List<a, A>
  for -z: B
  {List.foldr(~a, ~A, ~B, ~f, xs, List.foldr(~a, ~A, ~B, ~f, ys, z)) == List.foldr(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) : B}

def foldr_append_sym(a, A, B, f, xs, ys, z):
  Equal.sym(B, List.foldr(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z), List.foldr(~a, ~A, ~B, ~f, xs, List.foldr(~a, ~A, ~B, ~f, ys, z)), foldr_append(~a, ~A, ~B, ~f, xs, ys, z))

# Taking n elements and appending the rest after dropping n gives the list back, reversed to rewrite toward the simple side.
law take_append_drop_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {xs == List.append(a, A, List.take(a, A, xs, n), List.drop(a, A, xs, n)) : List<a, A>}

def take_append_drop_sym(a, A, xs, n):
  Equal.sym(List<a, A>, List.append(a, A, List.take(a, A, xs, n), List.drop(a, A, xs, n)), xs, take_append_drop(a, A, xs, n))

# Mapping preserves the length, reversed to rewrite toward the simple side.
law length_map_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.length(&1, A, xs) == List.length(&1, B, List.map(~A, ~B, ~f, xs)) : Nat}

def length_map_sym(A, B, f, xs):
  Equal.sym(Nat, List.length(&1, B, List.map(~A, ~B, ~f, xs)), List.length(&1, A, xs), length_map(~A, ~B, ~f, xs))

# Mapping over an append maps each part: map f (xs ++ ys) = map f xs ++ map f ys, reversed to rewrite toward the simple side.
law map_append_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  for -ys: List<A>
  {List.append(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, ys)) == List.map(~A, ~B, ~f, List.append(&1, A, xs, ys)) : List<B>}

def map_append_sym(A, B, f, xs, ys):
  Equal.sym(List<B>, List.map(~A, ~B, ~f, List.append(&1, A, xs, ys)), List.append(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, ys)), map_append(~A, ~B, ~f, xs, ys))

# Mapping twice is mapping the composition: map g (map f xs) = map (g . f) xs, reversed to rewrite toward the simple side.
law map_map_sym:
  for ~A: Type
  for ~B: Type
  for ~C: Type
  for ~f: A -> B
  for ~g: B -> C
  for xs: List<A>
  {List.map(~A, ~C, ~(x => g(f(x))), xs) == List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, xs)) : List<C>}

def map_map_sym(A, B, C, f, g, xs):
  Equal.sym(List<C>, List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, xs)), List.map(~A, ~C, ~(x => g(f(x))), xs), map_map(~A, ~B, ~C, ~f, ~g, xs))

# Taking zero elements gives the empty list, reversed to rewrite toward the simple side.
law take_zero_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {Nil{} == List.take(a, A, xs, 0n) : List<a, A>}

def take_zero_sym(a, A, xs):
  Equal.sym(List<a, A>, List.take(a, A, xs, 0n), Nil{}, take_zero(a, A, xs))

# Dropping zero elements gives the list back, reversed to rewrite toward the simple side.
law drop_zero_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {xs == List.drop(a, A, xs, 0n) : List<a, A>}

def drop_zero_sym(a, A, xs):
  Equal.sym(List<a, A>, List.drop(a, A, xs, 0n), xs, drop_zero(a, A, xs))

# Taking from the empty list gives the empty list, reversed to rewrite toward the simple side.
law take_nil_sym:
  for -a: Quant
  for -A: Kind(a)
  for -n: Nat
  {Nil{} == List.take(a, A, Nil{}, n) : List<a, A>}

def take_nil_sym(a, A, n):
  Equal.sym(List<a, A>, List.take(a, A, Nil{}, n), Nil{}, take_nil(a, A, n))

# Dropping from the empty list gives the empty list, reversed to rewrite toward the simple side.
law drop_nil_sym:
  for -a: Quant
  for -A: Kind(a)
  for -n: Nat
  {Nil{} == List.drop(a, A, Nil{}, n) : List<a, A>}

def drop_nil_sym(a, A, n):
  Equal.sym(List<a, A>, List.drop(a, A, Nil{}, n), Nil{}, drop_nil(a, A, n))

# Taking n elements leaves min(n, length) of them, reversed to rewrite toward the simple side.
law length_take_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {Nat.min(n, List.length(a, A, xs)) == List.length(a, A, List.take(a, A, xs, n)) : Nat}

def length_take_sym(a, A, xs, n):
  Equal.sym(Nat, List.length(a, A, List.take(a, A, xs, n)), Nat.min(n, List.length(a, A, xs)), length_take(a, A, xs, n))

# Dropping n elements leaves length - n of them, reversed to rewrite toward the simple side.
law length_drop_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {Nat.sub(List.length(a, A, xs), n) == List.length(a, A, List.drop(a, A, xs, n)) : Nat}

def length_drop_sym(a, A, xs, n):
  Equal.sym(Nat, List.length(a, A, List.drop(a, A, xs, n)), Nat.sub(List.length(a, A, xs), n), length_drop(a, A, xs, n))

# Taking as many elements as the list has gives the list back, reversed to rewrite toward the simple side.
law take_length_sym:
  for -A: Data
  for +xs: List<&2, A>
  {xs == List.take(&2, A, xs, List.length(&2, A, xs)) : List<&2, A>}

def take_length_sym(A, xs):
  Equal.sym(List<&2, A>, List.take(&2, A, xs, List.length(&2, A, xs)), xs, take_length(A, xs))

# Dropping as many elements as the list has gives the empty list, reversed to rewrite toward the simple side.
law drop_length_sym:
  for -A: Data
  for +xs: List<&2, A>
  {Nil{} == List.drop(&2, A, xs, List.length(&2, A, xs)) : List<&2, A>}

def drop_length_sym(A, xs):
  Equal.sym(List<&2, A>, List.drop(&2, A, xs, List.length(&2, A, xs)), Nil{}, drop_length(A, xs))

# Taking m from the first n is taking min(n, m), reversed to rewrite toward the simple side.
law take_take_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for m: Nat
  {List.take(a, A, xs, Nat.min(n, m)) == List.take(a, A, List.take(a, A, xs, n), m) : List<a, A>}

def take_take_sym(a, A, xs, n, m):
  Equal.sym(List<a, A>, List.take(a, A, List.take(a, A, xs, n), m), List.take(a, A, xs, Nat.min(n, m)), take_take(a, A, xs, n, m))

# Dropping m after dropping n is dropping n + m, reversed to rewrite toward the simple side.
law drop_drop_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for -m: Nat
  {List.drop(a, A, xs, Nat.add(n, m)) == List.drop(a, A, List.drop(a, A, xs, n), m) : List<a, A>}

def drop_drop_sym(a, A, xs, n, m):
  Equal.sym(List<a, A>, List.drop(a, A, List.drop(a, A, xs, n), m), List.drop(a, A, xs, Nat.add(n, m)), drop_drop(a, A, xs, n, m))
