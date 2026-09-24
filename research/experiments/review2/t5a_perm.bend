import Base

def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case False{}:
      n
    case True{}:
      1n+n

def count(+x: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +h <> t:
      bump(Nat.is_eq(x, h), count(x, t))

def perm(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Type:
  @x: Nat -> {count(x, xs) == count(x, ys) : Nat}

law perm_refl:
  for xs: List<&2, Nat>
  perm(xs, xs)

def perm_refl(xs):
  x => {==}

law perm_sym:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for p: perm(xs, ys)
  perm(ys, xs)

def perm_sym(xs, ys, p):
  x => Equal.sym(Nat, count(x, xs), count(x, ys), p(x))

law perm_trans:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for zs: List<&2, Nat>
  for p: perm(xs, ys)
  for q: perm(ys, zs)
  perm(xs, zs)

def perm_trans(xs, ys, zs, p, q):
  +x => Equal.trans(Nat, count(x, xs), count(x, ys), count(x, zs), p(x), q(x))
