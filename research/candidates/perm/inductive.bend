# Candidate D3: inductive permutation over List<&2, Nat>.
# Bend 2.0.27 has no indexed datatypes (constructor rows take no result annotation), so the
# literal `type Perm(xs, ys)` is inexpressible; Perm is a recursive -> Data predicate over a derivation list.

import Base

# A derivation step `i` swaps positions i and i+1; `steps` is applied left to right.
def swap_head(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      match t:
        case Nil{}:
          x <> Nil{}
        case +y <> u:
          y <> x <> u

def swap_at(+i: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match i:
    case 0n:
      swap_head(xs)
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case +x <> t:
          x <> swap_at(p, t)

def apply(+steps: List<&2, Nat>, xs: List<&2, Nat>) -> List<&2, Nat>:
  match steps:
    case Nil{}:
      xs
    case +i <> rest:
      apply(rest, swap_at(i, xs))

# `Perm(steps, xs, ys)` is the derivable relation: steps carries xs to ys.
def Perm(+steps: List<&2, Nat>, xs: List<&2, Nat>, ys: List<&2, Nat>) -> Data:
  {apply(steps, xs) == ys : List<&2, Nat>}

def internal_swap_head_length(xs: List<&2, Nat>) -> {List.length(&2, Nat, swap_head(xs)) == List.length(&2, Nat, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      match t:
        case Nil{}:
          {==}
        case +y <> u:
          {==}

def internal_swap_at_length(+i: Nat, +xs: List<&2, Nat>) -> {List.length(&2, Nat, swap_at(i, xs)) == List.length(&2, Nat, xs) : Nat}:
  match i:
    case 0n:
      internal_swap_head_length(xs)
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case +x <> t:
          %Equal.sym(Nat, List.length(&2, Nat, swap_at(p, t)), List.length(&2, Nat, t), internal_swap_at_length(p, t)) : {1n+_ == 1n+List.length(&2, Nat, t) : Nat}
          {==}

def internal_apply_length(+s: List<&2, Nat>, +xs: List<&2, Nat>) -> {List.length(&2, Nat, apply(s, xs)) == List.length(&2, Nat, xs) : Nat}:
  match s:
    case Nil{}:
      {==}
    case +i <> rest:
      Equal.trans(Nat, List.length(&2, Nat, apply(rest, swap_at(i, xs))), List.length(&2, Nat, swap_at(i, xs)), List.length(&2, Nat, xs), internal_apply_length(rest, swap_at(i, xs)), internal_swap_at_length(i, xs))

def internal_apply_app(+s1: List<&2, Nat>, +s2: List<&2, Nat>, +xs: List<&2, Nat>) -> {apply(List.append(&2, Nat, s1, s2), xs) == apply(s2, apply(s1, xs)) : List<&2, Nat>}:
  match s1:
    case Nil{}:
      {==}
    case +i <> rest:
      internal_apply_app(rest, s2, swap_at(i, xs))

def internal_swap_head_invol(xs: List<&2, Nat>) -> {swap_head(swap_head(xs)) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      match t:
        case Nil{}:
          {==}
        case +y <> u:
          {==}

def internal_swap_at_invol(+i: Nat, +xs: List<&2, Nat>) -> {swap_at(i, swap_at(i, xs)) == xs : List<&2, Nat>}:
  match i:
    case 0n:
      internal_swap_head_invol(xs)
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case +x <> t:
          %Equal.sym(List<&2, Nat>, swap_at(p, swap_at(p, t)), t, internal_swap_at_invol(p, t)) : {x <> _ == x <> t : List<&2, Nat>}
          {==}

def invert(+s: List<&2, Nat>) -> List<&2, Nat>:
  match s:
    case Nil{}:
      Nil{}
    case +i <> rest:
      List.append(&2, Nat, invert(rest), i <> Nil{})

def internal_apply_invert(+s: List<&2, Nat>, +xs: List<&2, Nat>) -> {apply(invert(s), apply(s, xs)) == xs : List<&2, Nat>}:
  match s:
    case Nil{}:
      {==}
    case +i <> rest:
      %Equal.sym(List<&2, Nat>, apply(List.append(&2, Nat, invert(rest), i <> Nil{}), apply(rest, swap_at(i, xs))), apply(i <> Nil{}, apply(invert(rest), apply(rest, swap_at(i, xs)))), internal_apply_app(invert(rest), i <> Nil{}, apply(rest, swap_at(i, xs)))) : {_ == xs : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, apply(invert(rest), apply(rest, swap_at(i, xs))), swap_at(i, xs), internal_apply_invert(rest, swap_at(i, xs))) : {apply(i <> Nil{}, _) == xs : List<&2, Nat>}
      internal_swap_at_invol(i, xs)

def shift(+s: List<&2, Nat>) -> List<&2, Nat>:
  match s:
    case Nil{}:
      Nil{}
    case +i <> rest:
      (1n+i) <> shift(rest)

def internal_apply_shift(+s: List<&2, Nat>, +x: Nat, +xs: List<&2, Nat>) -> {apply(shift(s), x <> xs) == x <> apply(s, xs) : List<&2, Nat>}:
  match s:
    case Nil{}:
      {==}
    case +i <> rest:
      internal_apply_shift(rest, x, swap_at(i, xs))

def upto(+n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0n <> shift(upto(p))

def internal_apply_upto(+ys: List<&2, Nat>, +x: Nat, +t: List<&2, Nat>) -> {apply(upto(List.length(&2, Nat, ys)), x <> List.append(&2, Nat, ys, t)) == List.append(&2, Nat, ys, x <> t) : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> ys2:
      %Equal.sym(List<&2, Nat>, apply(shift(upto(List.length(&2, Nat, ys2))), y <> (x <> List.append(&2, Nat, ys2, t))), y <> apply(upto(List.length(&2, Nat, ys2)), x <> List.append(&2, Nat, ys2, t)), internal_apply_shift(upto(List.length(&2, Nat, ys2)), y, x <> List.append(&2, Nat, ys2, t))) : {_ == y <> List.append(&2, Nat, ys2, x <> t) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, apply(upto(List.length(&2, Nat, ys2)), x <> List.append(&2, Nat, ys2, t)), List.append(&2, Nat, ys2, x <> t), internal_apply_upto(ys2, x, t)) : {y <> _ == y <> List.append(&2, Nat, ys2, x <> t) : List<&2, Nat>}
      {==}

def internal_append_nil(+ys: List<&2, Nat>) -> {List.append(&2, Nat, ys, Nil{}) == ys : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> t:
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, t, Nil{}), t, internal_append_nil(t)) : {y <> _ == y <> t : List<&2, Nat>}
      {==}

def rc(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      List.append(&2, Nat, shift(rc(t, ys)), upto(List.length(&2, Nat, ys)))

def internal_apply_rc(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {apply(rc(xs, ys), List.append(&2, Nat, xs, ys)) == List.append(&2, Nat, ys, xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      Equal.sym(List<&2, Nat>, List.append(&2, Nat, ys, Nil{}), ys, internal_append_nil(ys))
    case +x <> t:
      %Equal.sym(List<&2, Nat>, apply(List.append(&2, Nat, shift(rc(t, ys)), upto(List.length(&2, Nat, ys))), x <> List.append(&2, Nat, t, ys)), apply(upto(List.length(&2, Nat, ys)), apply(shift(rc(t, ys)), x <> List.append(&2, Nat, t, ys))), internal_apply_app(shift(rc(t, ys)), upto(List.length(&2, Nat, ys)), x <> List.append(&2, Nat, t, ys))) : {_ == List.append(&2, Nat, ys, x <> t) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, apply(shift(rc(t, ys)), x <> List.append(&2, Nat, t, ys)), x <> apply(rc(t, ys), List.append(&2, Nat, t, ys)), internal_apply_shift(rc(t, ys), x, List.append(&2, Nat, t, ys))) : {apply(upto(List.length(&2, Nat, ys)), _) == List.append(&2, Nat, ys, x <> t) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, apply(rc(t, ys), List.append(&2, Nat, t, ys)), List.append(&2, Nat, ys, t), internal_apply_rc(t, ys)) : {apply(upto(List.length(&2, Nat, ys)), x <> _) == List.append(&2, Nat, ys, x <> t) : List<&2, Nat>}
      internal_apply_upto(ys, x, t)

law perm_refl:
  for xs: List<&2, Nat>
  Perm(Nil{}, xs, xs)

def perm_refl(xs):
  {==}

law perm_swap:
  for x: Nat
  for y: Nat
  for t: List<&2, Nat>
  Perm(0n <> Nil{}, x <> y <> t, y <> x <> t)

def perm_swap(x, y, t):
  {==}

law perm_trans:
  for s1: List<&2, Nat>
  for s2: List<&2, Nat>
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for zs: List<&2, Nat>
  for h1: Perm(s1, xs, ys)
  for h2: Perm(s2, ys, zs)
  Perm(List.append(&2, Nat, s1, s2), xs, zs)

def perm_trans(s1, s2, xs, ys, zs, h1, h2):
  %Equal.sym(List<&2, Nat>, apply(List.append(&2, Nat, s1, s2), xs), apply(s2, apply(s1, xs)), internal_apply_app(s1, s2, xs)) : {_ == zs : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, apply(s1, xs), ys, h1) : {apply(s2, _) == zs : List<&2, Nat>}
  h2

law perm_sym:
  for s: List<&2, Nat>
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for h: Perm(s, xs, ys)
  Perm(invert(s), ys, xs)

def perm_sym(s, xs, ys, h):
  %h : {apply(invert(s), _) == xs : List<&2, Nat>}
  internal_apply_invert(s, xs)

law perm_cons:
  for s: List<&2, Nat>
  for x: Nat
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for h: Perm(s, xs, ys)
  Perm(shift(s), x <> xs, x <> ys)

def perm_cons(s, x, xs, ys, h):
  %Equal.sym(List<&2, Nat>, apply(shift(s), x <> xs), x <> apply(s, xs), internal_apply_shift(s, x, xs)) : {_ == x <> ys : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, apply(s, xs), ys, h) : {x <> _ == x <> ys : List<&2, Nat>}
  {==}

law perm_append_comm:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  Perm(rc(xs, ys), List.append(&2, Nat, xs, ys), List.append(&2, Nat, ys, xs))

def perm_append_comm(xs, ys):
  internal_apply_rc(xs, ys)

law perm_length:
  for s: List<&2, Nat>
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for h: Perm(s, xs, ys)
  {List.length(&2, Nat, ys) == List.length(&2, Nat, xs) : Nat}

def perm_length(s, xs, ys, h):
  %h : {List.length(&2, Nat, _) == List.length(&2, Nat, xs) : Nat}
  internal_apply_length(s, xs)

# Reusing one Perm hypothesis twice (affine via a Data predicate) checks.
law perm_reuse:
  for s: List<&2, Nat>
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for +h: Perm(s, xs, ys)
  Perm(s, xs, ys) & Perm(s, xs, ys)

def perm_reuse(s, xs, ys, h):
  (h, h)
