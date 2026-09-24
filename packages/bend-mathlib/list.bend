# bend-mathlib/list.bend: List lemmas (append, reverse, length, take, drop, map, fold, filter).
import Base
import ./nat.bend as MNat
import ./bool.bend as MBool

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

# Reversing the empty list gives the empty list.
law reverse_nil:
  for -a: Quant
  for -A: Kind(a)
  {List.reverse(a, A, Nil{}) == Nil{} : List<a, A>}

def reverse_nil(a, A):
  {==}

# Reversing a one-element list gives it back.
law reverse_singleton:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  {List.reverse(a, A, [x]) == [x] : List<a, A>}

def reverse_singleton(a, A, x):
  {==}

# Replicating x n times gives a list of length n.
law length_replicate:
  for -A: Data
  for n: Nat
  for -x: A
  {List.length(&2, A, List.replicate(A, n, x)) == n : Nat}

def length_replicate(A, n, x):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %length_replicate(A, p, x) : {1n+List.length(&2, A, List.replicate(A, p, x)) == 1n+_ : Nat}
      {==}

# Range(n) has length n.
law length_range:
  for n: Nat
  {List.length(&2, Nat, List.range(n)) == n : Nat}

def internal_length_range_go(+n: Nat, acc: List<&2, Nat>) -> {List.length(&2, Nat, List.range.go(n, acc)) == Nat.add(n, List.length(&2, Nat, acc)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %MNat.add_succ(p, List.length(&2, Nat, acc)) : {List.length(&2, Nat, List.range.go(p, p <> acc)) == _ : Nat}
      internal_length_range_go(p, p <> acc)

def length_range(n):
  +n = n
  %Equal.sym(Nat, List.length(&2, Nat, List.range.go(n, Nil{})), Nat.add(n, 0n), internal_length_range_go(n, Nil{})) : {_ == n : Nat}
  MNat.add_zero(n)

# Zipping two lists gives the length of the shorter one.
law length_zip:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.length(&1, A & A, List.zip(a, A, a, A, xs, ys)) == Nat.min(List.length(a, A, xs), List.length(a, A, ys)) : Nat}

def length_zip(a, A, xs, ys):
  match xs ys:
    case Nil{} _:
      {==}
    case h <> t Nil{}:
      {==}
    case h <> t y <> yt:
      %length_zip(a, A, t, yt) : {1n+List.length(&1, A & A, List.zip(a, A, a, A, t, yt)) == 1n+_ : Nat}
      {==}

# Appending after a cons: (x :: xs) ++ ys = x :: (xs ++ ys).
law append_cons:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  for -ys: List<a, A>
  {List.append(a, A, x <> xs, ys) == x <> List.append(a, A, xs, ys) : List<a, A>}

def append_cons(a, A, x, xs, ys):
  {==}

# The empty list has length zero.
law length_nil:
  for -a: Quant
  for -A: Kind(a)
  {List.length(a, A, Nil{}) == 0n : Nat}

def length_nil(a, A):
  {==}

# A cons is one longer than its tail.
law length_cons:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  {List.length(a, A, x <> xs) == 1n+List.length(a, A, xs) : Nat}

def length_cons(a, A, x, xs):
  {==}

# Concatenating an append concatenates each part: concat (xss ++ yss) = concat xss ++ concat yss.
law concat_append:
  for -a: Quant
  for -A: Kind(a)
  for xss: List<a, List<a, A>>
  for -yss: List<a, List<a, A>>
  {List.concat(a, A, List.append(a, List<a, A>, xss, yss)) == List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)) : List<a, A>}

def concat_append(a, A, xss, yss):
  match xss:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(List<a, A>, List.concat(a, A, List.append(a, List<a, A>, t, yss)), List.append(a, A, List.concat(a, A, t), List.concat(a, A, yss)), concat_append(a, A, t, yss)) : {List.append(a, A, h, _) == List.append(a, A, List.append(a, A, h, List.concat(a, A, t)), List.concat(a, A, yss)) : List<a, A>}
      Equal.sym(List<a, A>, List.append(a, A, List.append(a, A, h, List.concat(a, A, t)), List.concat(a, A, yss)), List.append(a, A, h, List.append(a, A, List.concat(a, A, t), List.concat(a, A, yss))), append_assoc(a, A, h, List.concat(a, A, t), List.concat(a, A, yss)))

# A left fold over an append folds the second part from the fold of the first.
law foldl_append:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: B -> A -> B
  for xs: List<a, A>
  for -ys: List<a, A>
  for -z: B
  {List.foldl(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) == List.foldl(~a, ~A, ~B, ~f, ys, List.foldl(~a, ~A, ~B, ~f, xs, z)) : B}

def foldl_append(a, A, B, f, xs, ys, z):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      foldl_append(~a, ~A, ~B, ~f, t, ys, f(z, h))

# Mapping commutes with reversing: map f (reverse xs) = reverse (map f xs).
law map_reverse:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.map(~A, ~B, ~f, List.reverse(&1, A, xs)) == List.reverse(&1, B, List.map(~A, ~B, ~f, xs)) : List<B>}

def internal_map_reverse_go(~A: Type, ~B: Type, ~f: A -> B, xs: List<A>, acc: List<A>) -> {List.map(~A, ~B, ~f, List.reverse.go(&1, A, xs, acc)) == List.reverse.go(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, acc)) : List<B>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      internal_map_reverse_go(~A, ~B, ~f, t, h <> acc)

def map_reverse(A, B, f, xs):
  internal_map_reverse_go(~A, ~B, ~f, xs, Nil{})

# All over an append is all over each part, joined by and.
law all_append:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  for -ys: List<a, A>
  {List.all(~a, ~A, ~f, List.append(a, A, xs, ys)) == Bool.and(List.all(~a, ~A, ~f, xs), List.all(~a, ~A, ~f, ys)) : Bool}

def all_append(a, A, f, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Bool, List.all(~a, ~A, ~f, List.append(a, A, t, ys)), Bool.and(List.all(~a, ~A, ~f, t), List.all(~a, ~A, ~f, ys)), all_append(~a, ~A, ~f, t, ys)) : {Bool.and(f(h), _) == Bool.and(Bool.and(f(h), List.all(~a, ~A, ~f, t)), List.all(~a, ~A, ~f, ys)) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(f(h), List.all(~a, ~A, ~f, t)), List.all(~a, ~A, ~f, ys)), Bool.and(f(h), Bool.and(List.all(~a, ~A, ~f, t), List.all(~a, ~A, ~f, ys))), MBool.and_assoc(f(h), List.all(~a, ~A, ~f, t), List.all(~a, ~A, ~f, ys)))

# Any over an append is any over each part, joined by or.
law any_append:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  for -ys: List<a, A>
  {List.any(~a, ~A, ~f, List.append(a, A, xs, ys)) == Bool.or(List.any(~a, ~A, ~f, xs), List.any(~a, ~A, ~f, ys)) : Bool}

def any_append(a, A, f, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Bool, List.any(~a, ~A, ~f, List.append(a, A, t, ys)), Bool.or(List.any(~a, ~A, ~f, t), List.any(~a, ~A, ~f, ys)), any_append(~a, ~A, ~f, t, ys)) : {Bool.or(f(h), _) == Bool.or(Bool.or(f(h), List.any(~a, ~A, ~f, t)), List.any(~a, ~A, ~f, ys)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(f(h), List.any(~a, ~A, ~f, t)), List.any(~a, ~A, ~f, ys)), Bool.or(f(h), Bool.or(List.any(~a, ~A, ~f, t), List.any(~a, ~A, ~f, ys))), MBool.or_assoc(f(h), List.any(~a, ~A, ~f, t), List.any(~a, ~A, ~f, ys)))

# Filtering an append filters each part.
law filter_append:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  for ys: List<&2, A>
  {List.filter(~A, ~f, List.append(&2, A, xs, ys)) == List.append(&2, A, List.filter(~A, ~f, xs), List.filter(~A, ~f, ys)) : List<&2, A>}

def internal_filter_put_append(-A: Data, h: A, r: List<&2, A>, s: List<&2, A>, b: Bool) -> {List.append(&2, A, List.filter.put(A, h, r, b), s) == List.filter.put(A, h, List.append(&2, A, r, s), b) : List<&2, A>}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def filter_append(A, f, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +ys = ys
      +t = t
      %Equal.sym(List<&2, A>, List.filter(~A, ~f, List.append(&2, A, t, ys)), List.append(&2, A, List.filter(~A, ~f, t), List.filter(~A, ~f, ys)), filter_append(~A, ~f, t, ys)) : {List.filter.put(A, h, _, f(h)) == List.append(&2, A, List.filter.put(A, h, List.filter(~A, ~f, t), f(h)), List.filter(~A, ~f, ys)) : List<&2, A>}
      Equal.sym(List<&2, A>, List.append(&2, A, List.filter.put(A, h, List.filter(~A, ~f, t), f(h)), List.filter(~A, ~f, ys)), List.filter.put(A, h, List.append(&2, A, List.filter(~A, ~f, t), List.filter(~A, ~f, ys)), f(h)), internal_filter_put_append(A, h, List.filter(~A, ~f, t), List.filter(~A, ~f, ys), f(h)))

# An append contains x iff either part does.
law contains_append:
  for ~A: Data
  for ~eq: A -> A -> Bool
  for xs: List<&2, A>
  for -ys: List<&2, A>
  for +x: A
  {List.contains(~A, ~eq, List.append(&2, A, xs, ys), x) == Bool.or(List.contains(~A, ~eq, xs, x), List.contains(~A, ~eq, ys, x)) : Bool}

def contains_append(A, eq, xs, ys, x):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Bool, List.contains(~A, ~eq, List.append(&2, A, t, ys), x), Bool.or(List.contains(~A, ~eq, t, x), List.contains(~A, ~eq, ys, x)), contains_append(~A, ~eq, t, ys, x)) : {Bool.or(eq(h, x), _) == Bool.or(Bool.or(eq(h, x), List.contains(~A, ~eq, t, x)), List.contains(~A, ~eq, ys, x)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(eq(h, x), List.contains(~A, ~eq, t, x)), List.contains(~A, ~eq, ys, x)), Bool.or(eq(h, x), Bool.or(List.contains(~A, ~eq, t, x), List.contains(~A, ~eq, ys, x))), MBool.or_assoc(eq(h, x), List.contains(~A, ~eq, t, x), List.contains(~A, ~eq, ys, x)))

# Filtering never makes a list longer.
law length_filter_le:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  {Nat.is_le(List.length(&2, A, List.filter(~A, ~f, xs)), List.length(&2, A, xs)) == True{} : Bool}

def internal_length_filter_put_le(-A: Data, h: A, r: List<&2, A>, b: Bool) -> {Nat.is_le(List.length(&2, A, List.filter.put(A, h, r, b)), 1n+List.length(&2, A, r)) == True{} : Bool}:
  match b:
    case False{}:
      MNat.le_succ(List.length(&2, A, r))
    case True{}:
      MNat.le_refl(1n+List.length(&2, A, r))

def length_filter_le(A, f, xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +t = t
      MNat.le_trans(List.length(&2, A, List.filter.put(A, h, List.filter(~A, ~f, t), f(h))), 1n+List.length(&2, A, List.filter(~A, ~f, t)), 1n+List.length(&2, A, t), internal_length_filter_put_le(A, h, List.filter(~A, ~f, t), f(h)), MNat.succ_le_succ(List.length(&2, A, List.filter(~A, ~f, t)), List.length(&2, A, t), length_filter_le(~A, ~f, t)))

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

# Reversing the empty list gives the empty list, reversed to rewrite toward the simple side.
law reverse_nil_sym:
  for -a: Quant
  for -A: Kind(a)
  {Nil{} == List.reverse(a, A, Nil{}) : List<a, A>}

def reverse_nil_sym(a, A):
  Equal.sym(List<a, A>, List.reverse(a, A, Nil{}), Nil{}, reverse_nil(a, A))

# Reversing a one-element list gives it back, reversed to rewrite toward the simple side.
law reverse_singleton_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  {[x] == List.reverse(a, A, [x]) : List<a, A>}

def reverse_singleton_sym(a, A, x):
  Equal.sym(List<a, A>, List.reverse(a, A, [x]), [x], reverse_singleton(a, A, x))

# Replicating x n times gives a list of length n, reversed to rewrite toward the simple side.
law length_replicate_sym:
  for -A: Data
  for n: Nat
  for -x: A
  {n == List.length(&2, A, List.replicate(A, n, x)) : Nat}

def length_replicate_sym(A, n, x):
  Equal.sym(Nat, List.length(&2, A, List.replicate(A, n, x)), n, length_replicate(A, n, x))

# Range(n) has length n, reversed to rewrite toward the simple side.
law length_range_sym:
  for n: Nat
  {n == List.length(&2, Nat, List.range(n)) : Nat}

def length_range_sym(n):
  Equal.sym(Nat, List.length(&2, Nat, List.range(n)), n, length_range(n))

# Zipping two lists gives the length of the shorter one, reversed to rewrite toward the simple side.
law length_zip_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {Nat.min(List.length(a, A, xs), List.length(a, A, ys)) == List.length(&1, A & A, List.zip(a, A, a, A, xs, ys)) : Nat}

def length_zip_sym(a, A, xs, ys):
  Equal.sym(Nat, List.length(&1, A & A, List.zip(a, A, a, A, xs, ys)), Nat.min(List.length(a, A, xs), List.length(a, A, ys)), length_zip(a, A, xs, ys))

# Appending after a cons: (x :: xs) ++ ys = x :: (xs ++ ys), reversed to rewrite toward the simple side.
law append_cons_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  for -ys: List<a, A>
  {x <> List.append(a, A, xs, ys) == List.append(a, A, x <> xs, ys) : List<a, A>}

def append_cons_sym(a, A, x, xs, ys):
  Equal.sym(List<a, A>, List.append(a, A, x <> xs, ys), x <> List.append(a, A, xs, ys), append_cons(a, A, x, xs, ys))

# The empty list has length zero, reversed to rewrite toward the simple side.
law length_nil_sym:
  for -a: Quant
  for -A: Kind(a)
  {0n == List.length(a, A, Nil{}) : Nat}

def length_nil_sym(a, A):
  Equal.sym(Nat, List.length(a, A, Nil{}), 0n, length_nil(a, A))

# A cons is one longer than its tail, reversed to rewrite toward the simple side.
law length_cons_sym:
  for -a: Quant
  for -A: Kind(a)
  for -x: A
  for -xs: List<a, A>
  {1n+List.length(a, A, xs) == List.length(a, A, x <> xs) : Nat}

def length_cons_sym(a, A, x, xs):
  Equal.sym(Nat, List.length(a, A, x <> xs), 1n+List.length(a, A, xs), length_cons(a, A, x, xs))

# Concatenating an append concatenates each part: concat (xss ++ yss) = concat xss ++ concat yss, reversed to rewrite toward the simple side.
law concat_append_sym:
  for -a: Quant
  for -A: Kind(a)
  for xss: List<a, List<a, A>>
  for -yss: List<a, List<a, A>>
  {List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)) == List.concat(a, A, List.append(a, List<a, A>, xss, yss)) : List<a, A>}

def concat_append_sym(a, A, xss, yss):
  Equal.sym(List<a, A>, List.concat(a, A, List.append(a, List<a, A>, xss, yss)), List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)), concat_append(a, A, xss, yss))

# A left fold over an append folds the second part from the fold of the first, reversed to rewrite toward the simple side.
law foldl_append_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: B -> A -> B
  for xs: List<a, A>
  for -ys: List<a, A>
  for -z: B
  {List.foldl(~a, ~A, ~B, ~f, ys, List.foldl(~a, ~A, ~B, ~f, xs, z)) == List.foldl(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) : B}

def foldl_append_sym(a, A, B, f, xs, ys, z):
  Equal.sym(B, List.foldl(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z), List.foldl(~a, ~A, ~B, ~f, ys, List.foldl(~a, ~A, ~B, ~f, xs, z)), foldl_append(~a, ~A, ~B, ~f, xs, ys, z))

# Mapping commutes with reversing: map f (reverse xs) = reverse (map f xs), reversed to rewrite toward the simple side.
law map_reverse_sym:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.reverse(&1, B, List.map(~A, ~B, ~f, xs)) == List.map(~A, ~B, ~f, List.reverse(&1, A, xs)) : List<B>}

def map_reverse_sym(A, B, f, xs):
  Equal.sym(List<B>, List.map(~A, ~B, ~f, List.reverse(&1, A, xs)), List.reverse(&1, B, List.map(~A, ~B, ~f, xs)), map_reverse(~A, ~B, ~f, xs))

# All over an append is all over each part, joined by and, reversed to rewrite toward the simple side.
law all_append_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  for -ys: List<a, A>
  {Bool.and(List.all(~a, ~A, ~f, xs), List.all(~a, ~A, ~f, ys)) == List.all(~a, ~A, ~f, List.append(a, A, xs, ys)) : Bool}

def all_append_sym(a, A, f, xs, ys):
  Equal.sym(Bool, List.all(~a, ~A, ~f, List.append(a, A, xs, ys)), Bool.and(List.all(~a, ~A, ~f, xs), List.all(~a, ~A, ~f, ys)), all_append(~a, ~A, ~f, xs, ys))

# Any over an append is any over each part, joined by or, reversed to rewrite toward the simple side.
law any_append_sym:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  for -ys: List<a, A>
  {Bool.or(List.any(~a, ~A, ~f, xs), List.any(~a, ~A, ~f, ys)) == List.any(~a, ~A, ~f, List.append(a, A, xs, ys)) : Bool}

def any_append_sym(a, A, f, xs, ys):
  Equal.sym(Bool, List.any(~a, ~A, ~f, List.append(a, A, xs, ys)), Bool.or(List.any(~a, ~A, ~f, xs), List.any(~a, ~A, ~f, ys)), any_append(~a, ~A, ~f, xs, ys))

# Filtering an append filters each part, reversed to rewrite toward the simple side.
law filter_append_sym:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  for ys: List<&2, A>
  {List.append(&2, A, List.filter(~A, ~f, xs), List.filter(~A, ~f, ys)) == List.filter(~A, ~f, List.append(&2, A, xs, ys)) : List<&2, A>}

def filter_append_sym(A, f, xs, ys):
  Equal.sym(List<&2, A>, List.filter(~A, ~f, List.append(&2, A, xs, ys)), List.append(&2, A, List.filter(~A, ~f, xs), List.filter(~A, ~f, ys)), filter_append(~A, ~f, xs, ys))

# An append contains x iff either part does, reversed to rewrite toward the simple side.
law contains_append_sym:
  for ~A: Data
  for ~eq: A -> A -> Bool
  for xs: List<&2, A>
  for -ys: List<&2, A>
  for +x: A
  {Bool.or(List.contains(~A, ~eq, xs, x), List.contains(~A, ~eq, ys, x)) == List.contains(~A, ~eq, List.append(&2, A, xs, ys), x) : Bool}

def contains_append_sym(A, eq, xs, ys, x):
  Equal.sym(Bool, List.contains(~A, ~eq, List.append(&2, A, xs, ys), x), Bool.or(List.contains(~A, ~eq, xs, x), List.contains(~A, ~eq, ys, x)), contains_append(~A, ~eq, xs, ys, x))

# Filtering never makes a list longer, reversed to rewrite toward the simple side.
law length_filter_le_sym:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  {True{} == Nat.is_le(List.length(&2, A, List.filter(~A, ~f, xs)), List.length(&2, A, xs)) : Bool}

def length_filter_le_sym(A, f, xs):
  Equal.sym(Bool, Nat.is_le(List.length(&2, A, List.filter(~A, ~f, xs)), List.length(&2, A, xs)), True{}, length_filter_le(~A, ~f, xs))
