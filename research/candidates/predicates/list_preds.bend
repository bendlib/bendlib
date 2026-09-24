import Base
import ../../../packages/bend-mathlib/nat.bend as MNat

# Membership in a list, as a reusable proposition.
def mem(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Data:
  {List.contains(~A, ~eq, xs, x) == True{} : Bool}

# A list is sorted by a comparator when every adjacent pair is in order.
def sorted_by(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> Data:
  {List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), List.zip(&2, A, &2, A, xs, List.tail(&2, A, xs))) == True{} : Bool}

def internal_false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def internal_is_eq_refl(x: Nat) -> {Nat.is_eq(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      internal_is_eq_refl(p)

def internal_or_of_right(a: Bool, -b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case False{}:
      hb
    case True{}:
      {==}

def internal_or_of_or(a: Bool, -b: Bool, -c: Bool, h: {Bool.or(a, b) == True{} : Bool}, k: {b == True{} : Bool} -> {c == True{} : Bool}) -> {Bool.or(a, c) == True{} : Bool}:
  match a:
    case False{}:
      k(h)
    case True{}:
      {==}

def internal_and_left(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, internal_false_ne_true(h))
    case True{}:
      {==}

def internal_and_right(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, internal_false_ne_true(h))
    case True{}:
      h

def internal_mem_append_left(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +x: Nat, h: {List.contains(~Nat, ~Nat.is_eq, xs, x) == True{} : Bool}) -> {List.contains(~Nat, ~Nat.is_eq, List.append(&2, Nat, xs, ys), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({List.contains(~Nat, ~Nat.is_eq, ys, x) == True{} : Bool}, internal_false_ne_true(h))
    case hd <> tl:
      internal_or_of_or(Nat.is_eq(hd, x), List.contains(~Nat, ~Nat.is_eq, tl, x), List.contains(~Nat, ~Nat.is_eq, List.append(&2, Nat, tl, ys), x), h, internal_mem_append_left(tl, ys, x))

def internal_mem_append_right(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +x: Nat, h: {List.contains(~Nat, ~Nat.is_eq, ys, x) == True{} : Bool}) -> {List.contains(~Nat, ~Nat.is_eq, List.append(&2, Nat, xs, ys), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case hd <> tl:
      internal_or_of_right(Nat.is_eq(hd, x), List.contains(~Nat, ~Nat.is_eq, List.append(&2, Nat, tl, ys), x), internal_mem_append_right(tl, ys, x, h))

# The head of a cons is a member of it.
law mem_cons_self:
  for x: Nat
  for xs: List<&2, Nat>
  mem(~Nat, ~Nat.is_eq, x, x <> xs)

def mem_cons_self(x, xs):
  %Equal.sym(Bool, Nat.is_eq(x, x), True{}, internal_is_eq_refl(x)) : {Bool.or(_, List.contains(~Nat, ~Nat.is_eq, xs, x)) == True{} : Bool}
  {==}

# Membership is preserved when a new head is prepended.
law mem_cons_of_mem:
  for x: Nat
  for y: Nat
  for xs: List<&2, Nat>
  for h: mem(~Nat, ~Nat.is_eq, x, xs)
  mem(~Nat, ~Nat.is_eq, x, y <> xs)

def mem_cons_of_mem(x, y, xs, h):
  +x = x
  internal_or_of_right(Nat.is_eq(y, x), List.contains(~Nat, ~Nat.is_eq, xs, x), h)

# Nothing is a member of the empty list.
law not_mem_nil:
  for x: Nat
  mem(~Nat, ~Nat.is_eq, x, Nil{}) -> Empty

def not_mem_nil(x, h):
  internal_false_ne_true(h)

# Membership on the left of an append.
law mem_append_left:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for x: Nat
  for h: mem(~Nat, ~Nat.is_eq, x, xs)
  mem(~Nat, ~Nat.is_eq, x, List.append(&2, Nat, xs, ys))

def mem_append_left(xs, ys, x, h):
  internal_mem_append_left(xs, ys, x, h)

# Membership on the right of an append.
law mem_append_right:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for x: Nat
  for h: mem(~Nat, ~Nat.is_eq, x, ys)
  mem(~Nat, ~Nat.is_eq, x, List.append(&2, Nat, xs, ys))

def mem_append_right(xs, ys, x, h):
  internal_mem_append_right(xs, ys, x, h)

# The empty list is sorted by any comparator.
law sorted_nil:
  sorted_by(~Nat, ~Nat.is_le, Nil{})

def sorted_nil():
  {==}

# A singleton list is sorted by any comparator.
law sorted_single:
  for x: Nat
  sorted_by(~Nat, ~Nat.is_le, [x])

def sorted_single(x):
  {==}

# A sorted tail with an in-order head is sorted.
law sorted_cons_cons_intro:
  for x: Nat
  for y: Nat
  for t: List<&2, Nat>
  for hxy: MNat.le(x, y)
  for hyt: sorted_by(~Nat, ~Nat.is_le, y <> t)
  sorted_by(~Nat, ~Nat.is_le, x <> y <> t)

def sorted_cons_cons_intro(x, y, t, hxy, hyt):
  %Equal.sym(Bool, Nat.is_le(x, y), True{}, hxy) : {Bool.and(_, List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), List.zip(&2, Nat, &2, Nat, y <> t, t))) == True{} : Bool}
  hyt

# The head pair of a sorted cons-cons list is in order.
law sorted_cons_cons_elim_le:
  for x: Nat
  for y: Nat
  for t: List<&2, Nat>
  for h: sorted_by(~Nat, ~Nat.is_le, x <> y <> t)
  MNat.le(x, y)

def sorted_cons_cons_elim_le(x, y, t, h):
  internal_and_left(Nat.is_le(x, y), List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), List.zip(&2, Nat, &2, Nat, y <> t, t)), h)

# The tail of a sorted cons-cons list is sorted.
law sorted_cons_cons_elim_tail:
  for x: Nat
  for y: Nat
  for t: List<&2, Nat>
  for h: sorted_by(~Nat, ~Nat.is_le, x <> y <> t)
  sorted_by(~Nat, ~Nat.is_le, y <> t)

def sorted_cons_cons_elim_tail(x, y, t, h):
  internal_and_right(Nat.is_le(x, y), List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), List.zip(&2, Nat, &2, Nat, y <> t, t)), h)

# A sorted list has a sorted tail.
law sorted_tail:
  for x: Nat
  for xs: List<&2, Nat>
  for h: sorted_by(~Nat, ~Nat.is_le, x <> xs)
  sorted_by(~Nat, ~Nat.is_le, xs)

def sorted_tail(x, xs, h):
  match xs:
    case Nil{}:
      {==}
    case y <> t:
      internal_and_right(Nat.is_le(x, y), List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), List.zip(&2, Nat, &2, Nat, y <> t, t)), h)
