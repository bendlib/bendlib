# Mathlib side: perm lemmas over the generic kernel, plus insertion sort is a permutation.
import Base
import ./kernel.bend as K

def internal_shift(+s: List<&2, Nat>) -> List<&2, Nat>:
  match s:
    case Nil{}:
      Nil{}
    case +i <> rest:
      (1n+i) <> internal_shift(rest)

def internal_apply_app(-A: Data, +s1: List<&2, Nat>, +s2: List<&2, Nat>, +xs: List<&2, A>) -> {K.apply(A, List.append(&2, Nat, s1, s2), xs) == K.apply(A, s2, K.apply(A, s1, xs)) : List<&2, A>}:
  match s1:
    case Nil{}:
      {==}
    case +i <> rest:
      internal_apply_app(A, rest, s2, K.swap_at(A, i, xs))

def internal_apply_shift(-A: Data, +s: List<&2, Nat>, +x: A, +xs: List<&2, A>) -> {K.apply(A, internal_shift(s), x <> xs) == x <> K.apply(A, s, xs) : List<&2, A>}:
  match s:
    case Nil{}:
      {==}
    case +i <> rest:
      internal_apply_shift(A, rest, x, K.swap_at(A, i, xs))

# Permutation is reflexive.
def perm_refl(-A: Data, -xs: List<&2, A>) -> K.perm(A, xs, xs):
  (Nil{}, {==})

# Swapping the two leading elements is a permutation.
def perm_swap(-A: Data, -x: A, -y: A, -t: List<&2, A>) -> K.perm(A, x <> y <> t, y <> x <> t):
  (0n <> Nil{}, {==})

def internal_trans_eq(-A: Data, +s1: List<&2, Nat>, +s2: List<&2, Nat>, +xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>, e1: K.Perm(A, s1, xs, ys), e2: K.Perm(A, s2, ys, zs)) -> K.Perm(A, List.append(&2, Nat, s1, s2), xs, zs):
  %Equal.sym(List<&2, A>, K.apply(A, List.append(&2, Nat, s1, s2), xs), K.apply(A, s2, K.apply(A, s1, xs)), internal_apply_app(A, s1, s2, xs)) : {_ == zs : List<&2, A>}
  %Equal.sym(List<&2, A>, K.apply(A, s1, xs), ys, e1) : {K.apply(A, s2, _) == zs : List<&2, A>}
  e2

# Permutation is transitive.
def perm_trans(-A: Data, +xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>, h1: K.perm(A, xs, ys), h2: K.perm(A, ys, zs)) -> K.perm(A, xs, zs):
  (s1, e1) = h1
  (s2, e2) = h2
  +s1 = s1
  +s2 = s2
  (List.append(&2, Nat, s1, s2), internal_trans_eq(A, s1, s2, xs, ys, zs, e1, e2))

def internal_cons_eq(-A: Data, +s: List<&2, Nat>, +x: A, +xs: List<&2, A>, -ys: List<&2, A>, e: K.Perm(A, s, xs, ys)) -> K.Perm(A, internal_shift(s), x <> xs, x <> ys):
  %Equal.sym(List<&2, A>, K.apply(A, internal_shift(s), x <> xs), x <> K.apply(A, s, xs), internal_apply_shift(A, s, x, xs)) : {_ == x <> ys : List<&2, A>}
  %Equal.sym(List<&2, A>, K.apply(A, s, xs), ys, e) : {x <> _ == x <> ys : List<&2, A>}
  {==}

# Prepending the same element preserves permutation.
def perm_cons(-A: Data, +x: A, +xs: List<&2, A>, -ys: List<&2, A>, h: K.perm(A, xs, ys)) -> K.perm(A, x <> xs, x <> ys):
  (s, e) = h
  +s = s
  (internal_shift(s), internal_cons_eq(A, s, x, xs, ys, e))

# A Perm hypothesis in existential form is reusable.
def perm_reuse(-A: Data, -xs: List<&2, A>, -ys: List<&2, A>, +h: K.perm(A, xs, ys)) -> K.perm(A, xs, ys) & K.perm(A, xs, ys):
  (h, h)

# Insertion into a list, generic comparator (structural, Base-only branching via Bool.pick).
def ins(~A: Data, ~le: A -> A -> Bool, +x: A, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      x <> Nil{}
    case +y <> +t:
      Bool.pick(List<&2, A>, le(x, y), x <> y <> t, y <> ins(~A, ~le, x, t))

def isort(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      ins(~A, ~le, x, isort(~A, ~le, t))

def internal_ins_pick(-A: Data, b: Bool, +x: A, +y: A, +t: List<&2, A>, -r: List<&2, A>, ih: K.perm(A, x <> t, r)) -> K.perm(A, x <> y <> t, Bool.pick(List<&2, A>, b, x <> y <> t, y <> r)):
  match b:
    case True{}:
      perm_refl(A, x <> y <> t)
    case False{}:
      perm_trans(A, x <> y <> t, y <> x <> t, y <> r, perm_swap(A, x, y, t), perm_cons(A, y, x <> t, r, ih))

# Inserting x into xs permutes x <> xs.
def ins_perm(~A: Data, ~le: A -> A -> Bool, +x: A, +xs: List<&2, A>) -> K.perm(A, x <> xs, ins(~A, ~le, x, xs)):
  match xs:
    case Nil{}:
      perm_refl(A, x <> Nil{})
    case +y <> t:
      internal_ins_pick(A, le(x, y), x, y, t, ins(~A, ~le, x, t), ins_perm(~A, ~le, x, t))

# Insertion sort permutes its input.
def isort_perm(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> K.perm(A, xs, isort(~A, ~le, xs)):
  match xs:
    case Nil{}:
      perm_refl(A, Nil{})
    case +x <> t:
      perm_trans(A, x <> t, x <> isort(~A, ~le, t), isort(~A, ~le, x <> t), perm_cons(A, x, t, isort(~A, ~le, t), isort_perm(~A, ~le, t)), ins_perm(~A, ~le, x, isort(~A, ~le, t)))

# Closed instance: instantiate at Nat and at String.
def isort_perm_nat(+xs: List<&2, Nat>) -> K.perm(Nat, xs, isort(~Nat, ~Nat.is_le, xs)):
  isort_perm(~Nat, ~Nat.is_le, xs)
