import Base
import ../../../packages/bend-mathlib/nat.bend as MNat

# Increment n by one when the Bool is true.
def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case False{}:
      n
    case True{}:
      1n+n

# The number of occurrences of x in xs.
def count(+x: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +h <> t:
      bump(Nat.is_eq(x, h), count(x, t))

# Two lists are permutations when every element has the same multiplicity.
def perm(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Type:
  @x: Nat -> {count(x, xs) == count(x, ys) : Nat}

def internal_bump_comm(a: Bool, b: Bool, +n: Nat) -> {bump(a, bump(b, n)) == bump(b, bump(a, n)) : Nat}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def internal_bump_add(b: Bool, +n: Nat, +m: Nat) -> {bump(b, Nat.add(n, m)) == Nat.add(bump(b, n), m) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def internal_count_append(+x: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {count(x, List.append(&2, Nat, xs, ys)) == Nat.add(count(x, xs), count(x, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      %Equal.sym(Nat, count(x, List.append(&2, Nat, t, ys)), Nat.add(count(x, t), count(x, ys)), internal_count_append(x, t, ys)) : {bump(Nat.is_eq(x, h), _) == Nat.add(count(x, h <> t), count(x, ys)) : Nat}
      %Equal.sym(Nat, bump(Nat.is_eq(x, h), Nat.add(count(x, t), count(x, ys))), Nat.add(bump(Nat.is_eq(x, h), count(x, t)), count(x, ys)), internal_bump_add(Nat.is_eq(x, h), count(x, t), count(x, ys))) : {_ == Nat.add(count(x, h <> t), count(x, ys)) : Nat}
      {==}

# Permutation is reflexive.
law perm_refl:
  for xs: List<&2, Nat>
  perm(xs, xs)

def perm_refl(xs):
  x => {==}

# The empty list is a permutation of itself.
law perm_nil:
  perm(Nil{}, Nil{})

def perm_nil():
  x => {==}

# Permutation is symmetric.
law perm_sym:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for p: perm(xs, ys)
  perm(ys, xs)

def perm_sym(xs, ys, p):
  x => Equal.sym(Nat, count(x, xs), count(x, ys), p(x))

# Permutation is transitive.
law perm_trans:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for zs: List<&2, Nat>
  for p: perm(xs, ys)
  for q: perm(ys, zs)
  perm(xs, zs)

def perm_trans(xs, ys, zs, p, q):
  +x => Equal.trans(Nat, count(x, xs), count(x, ys), count(x, zs), p(x), q(x))

# Prepending the same element preserves permutation.
law perm_cons:
  for x: Nat
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for p: perm(xs, ys)
  perm(x <> xs, x <> ys)

def perm_cons(x, xs, ys, p):
  +z => %Equal.sym(Nat, count(z, xs), count(z, ys), p(z)) : {bump(Nat.is_eq(z, x), _) == count(z, x <> ys) : Nat}
         {==}

# Swapping the two leading elements preserves permutation.
law perm_swap:
  for x: Nat
  for y: Nat
  for t: List<&2, Nat>
  perm(x <> y <> t, y <> x <> t)

def perm_swap(x, y, t):
  +z => internal_bump_comm(Nat.is_eq(z, x), Nat.is_eq(z, y), count(z, t))

# Appending two lists commutes up to permutation.
law perm_append_comm:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  perm(List.append(&2, Nat, xs, ys), List.append(&2, Nat, ys, xs))

def perm_append_comm(xs, ys):
  +xs = xs
  +ys = ys
  +z => %Equal.sym(Nat, count(z, List.append(&2, Nat, xs, ys)), Nat.add(count(z, xs), count(z, ys)), internal_count_append(z, xs, ys)) : {_ == count(z, List.append(&2, Nat, ys, xs)) : Nat}
         %Equal.sym(Nat, count(z, List.append(&2, Nat, ys, xs)), Nat.add(count(z, ys), count(z, xs)), internal_count_append(z, ys, xs)) : {Nat.add(count(z, xs), count(z, ys)) == _ : Nat}
         MNat.add_comm(count(z, xs), count(z, ys))
