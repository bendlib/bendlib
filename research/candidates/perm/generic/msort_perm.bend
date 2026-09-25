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

def internal_append_nil(-A: Data, +ys: List<&2, A>) -> {List.append(&2, A, ys, Nil{}) == ys : List<&2, A>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> t:
      %Equal.sym(List<&2, A>, List.append(&2, A, t, Nil{}), t, internal_append_nil(A, t)) : {y <> _ == y <> t : List<&2, A>}
      {==}

# Appending Nil is a permutation (steps: none).
def perm_append_nil(-A: Data, +xs: List<&2, A>) -> K.perm(A, List.append(&2, A, xs, Nil{}), xs):
  (Nil{}, internal_append_nil(A, xs))

# Moving an element from the middle to the front is a permutation.
def perm_move(-A: Data, +xs: List<&2, A>, +y: A, +t: List<&2, A>) -> K.perm(A, List.append(&2, A, xs, y <> t), y <> List.append(&2, A, xs, t)):
  match xs:
    case Nil{}:
      perm_refl(A, y <> t)
    case +x <> r:
      perm_trans(A, x <> List.append(&2, A, r, y <> t), x <> y <> List.append(&2, A, r, t), y <> x <> List.append(&2, A, r, t), perm_cons(A, x, List.append(&2, A, r, y <> t), y <> List.append(&2, A, r, t), perm_move(A, r, y, t)), perm_swap(A, x, y, List.append(&2, A, r, t)))

def merge(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs ys:
    case Nil{} _:
      ys
    case +x <> +xt Nil{}:
      x <> xt
    case +x <> +xt +y <> +yt:
      Bool.pick(List<&2, A>, le(x, y), x <> merge(~A, ~le, xt, y <> yt), y <> merge(~A, ~le, x <> xt, yt))

def internal_merge_pick(-A: Data, b: Bool, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, -m1: List<&2, A>, -m2: List<&2, A>, ih1: K.perm(A, List.append(&2, A, xt, y <> yt), m1), ih2: K.perm(A, x <> List.append(&2, A, xt, yt), m2)) -> K.perm(A, x <> List.append(&2, A, xt, y <> yt), Bool.pick(List<&2, A>, b, x <> m1, y <> m2)):
  match b:
    case True{}:
      perm_cons(A, x, List.append(&2, A, xt, y <> yt), m1, ih1)
    case False{}:
      perm_trans(A, x <> List.append(&2, A, xt, y <> yt), y <> x <> List.append(&2, A, xt, yt), y <> m2, perm_move(A, x <> xt, y, yt), perm_cons(A, y, x <> List.append(&2, A, xt, yt), m2, ih2))

# Merging permutes the concatenation.
def merge_perm(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +ys: List<&2, A>) -> K.perm(A, List.append(&2, A, xs, ys), merge(~A, ~le, xs, ys)):
  match xs ys:
    case Nil{} _:
      perm_refl(A, ys)
    case +x <> +xt Nil{}:
      perm_cons(A, x, List.append(&2, A, xt, Nil{}), xt, perm_append_nil(A, xt))
    case +x <> +xt +y <> +yt:
      internal_merge_pick(A, le(x, y), x, xt, y, yt, merge(~A, ~le, xt, y <> yt), merge(~A, ~le, x <> xt, yt), merge_perm(~A, ~le, xt, y <> yt), merge_perm(~A, ~le, x <> xt, yt))

def merge_perm_nat(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> K.perm(Nat, List.append(&2, Nat, xs, ys), merge(~Nat, ~Nat.is_le, xs, ys)):
  merge_perm(~Nat, ~Nat.is_le, xs, ys)

# Moving the front element into the middle is a permutation.
def perm_move_rev(-A: Data, +xs: List<&2, A>, +y: A, +t: List<&2, A>) -> K.perm(A, y <> List.append(&2, A, xs, t), List.append(&2, A, xs, y <> t)):
  match xs:
    case Nil{}:
      perm_refl(A, y <> t)
    case +x <> r:
      perm_trans(A, y <> x <> List.append(&2, A, r, t), x <> y <> List.append(&2, A, r, t), x <> List.append(&2, A, r, y <> t), perm_swap(A, y, x, List.append(&2, A, r, t)), perm_cons(A, x, y <> List.append(&2, A, r, t), List.append(&2, A, r, y <> t), perm_move_rev(A, r, y, t)))

# Appending commutes up to permutation (derived without symmetry).
def perm_append_comm(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>) -> K.perm(A, List.append(&2, A, xs, ys), List.append(&2, A, ys, xs)):
  match xs:
    case Nil{}:
      (Nil{}, Equal.sym(List<&2, A>, List.append(&2, A, ys, Nil{}), ys, internal_append_nil(A, ys)))
    case +x <> r:
      perm_trans(A, x <> List.append(&2, A, r, ys), x <> List.append(&2, A, ys, r), List.append(&2, A, ys, x <> r), perm_cons(A, x, List.append(&2, A, r, ys), List.append(&2, A, ys, r), perm_append_comm(A, r, ys)), perm_move_rev(A, ys, x, r))

# Permuting the right operand of an append.
def perm_append_right(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>, -zs: List<&2, A>, h: K.perm(A, ys, zs)) -> K.perm(A, List.append(&2, A, xs, ys), List.append(&2, A, xs, zs)):
  match xs:
    case Nil{}:
      h
    case +x <> r:
      perm_cons(A, x, List.append(&2, A, r, ys), List.append(&2, A, r, zs), perm_append_right(A, r, ys, zs, h))

# Permuting both operands of an append.
def perm_append(-A: Data, +xs: List<&2, A>, +xs2: List<&2, A>, +ys: List<&2, A>, -ys2: List<&2, A>, p: K.perm(A, xs, xs2), q: K.perm(A, ys, ys2)) -> K.perm(A, List.append(&2, A, xs, ys), List.append(&2, A, xs2, ys2)):
  perm_trans(A, List.append(&2, A, xs, ys), List.append(&2, A, ys, xs), List.append(&2, A, xs2, ys2), perm_append_comm(A, xs, ys), perm_trans(A, List.append(&2, A, ys, xs), List.append(&2, A, ys, xs2), List.append(&2, A, xs2, ys2), perm_append_right(A, ys, xs, xs2, p), perm_trans(A, List.append(&2, A, ys, xs2), List.append(&2, A, xs2, ys), List.append(&2, A, xs2, ys2), perm_append_comm(A, ys, xs2), perm_append_right(A, xs2, ys, ys2, q))))

def evens(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> r:
      match r:
        case Nil{}:
          x <> Nil{}
        case +y <> t:
          x <> evens(A, t)

def odds(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> r:
      match r:
        case Nil{}:
          Nil{}
        case +y <> t:
          y <> odds(A, t)

# Splitting into evens and odds is a permutation.
def split_perm(-A: Data, +xs: List<&2, A>) -> K.perm(A, xs, List.append(&2, A, evens(A, xs), odds(A, xs))):
  match xs:
    case Nil{}:
      perm_refl(A, Nil{})
    case +x <> r:
      match r:
        case Nil{}:
          perm_refl(A, x <> Nil{})
        case +y <> t:
          perm_cons(A, x, y <> t, List.append(&2, A, evens(A, t), y <> odds(A, t)), perm_trans(A, y <> t, y <> List.append(&2, A, evens(A, t), odds(A, t)), List.append(&2, A, evens(A, t), y <> odds(A, t)), perm_cons(A, y, t, List.append(&2, A, evens(A, t), odds(A, t)), split_perm(A, t)), perm_move_rev(A, evens(A, t), y, odds(A, t))))

# Merge sort with fuel (the fuel only bounds recursion; it never affects the permutation).
def msort(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +xs: List<&2, A>) -> List<&2, A>:
  match fuel:
    case 0n:
      xs
    case 1n++f:
      merge(~A, ~le, msort(~A, ~le, f, evens(A, xs)), msort(~A, ~le, f, odds(A, xs)))

# Merge sort permutes its input, for any fuel.
def msort_perm(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +xs: List<&2, A>) -> K.perm(A, xs, msort(~A, ~le, fuel, xs)):
  match fuel:
    case 0n:
      perm_refl(A, xs)
    case 1n++f:
      perm_trans(A, xs, List.append(&2, A, evens(A, xs), odds(A, xs)), msort(~A, ~le, 1n+f, xs), split_perm(A, xs), perm_trans(A, List.append(&2, A, evens(A, xs), odds(A, xs)), List.append(&2, A, msort(~A, ~le, f, evens(A, xs)), msort(~A, ~le, f, odds(A, xs))), msort(~A, ~le, 1n+f, xs), perm_append(A, evens(A, xs), msort(~A, ~le, f, evens(A, xs)), odds(A, xs), msort(~A, ~le, f, odds(A, xs)), msort_perm(~A, ~le, f, evens(A, xs)), msort_perm(~A, ~le, f, odds(A, xs))), merge_perm(~A, ~le, msort(~A, ~le, f, evens(A, xs)), msort(~A, ~le, f, odds(A, xs)))))

def sort(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> List<&2, A>:
  msort(~A, ~le, List.length(&2, A, xs), xs)

# The sort permutes its input.
def sort_perm(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> K.perm(A, xs, sort(~A, ~le, xs)):
  msort_perm(~A, ~le, List.length(&2, A, xs), xs)

def sort_perm_nat(+xs: List<&2, Nat>) -> K.perm(Nat, xs, sort(~Nat, ~Nat.is_le, xs)):
  sort_perm(~Nat, ~Nat.is_le, xs)

def sort_t() -> {sort(~Nat, ~Nat.is_le, [5n, 1n, 4n, 2n, 3n, 1n]) == [1n, 1n, 2n, 3n, 4n, 5n] : List<&2, Nat>}:
  {==}
