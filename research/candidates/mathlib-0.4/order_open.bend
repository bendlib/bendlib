import Base
import ../../../packages/bend-mathlib/nat.bend as MNat
import ../predicates/list_preds.bend as P

law sorted_take:
  for xs: List<&2, Nat>
  for n: Nat
  for h: P.sorted_by(~Nat, ~Nat.is_le, xs)
  P.sorted_by(~Nat, ~Nat.is_le, List.take(&2, Nat, xs, n))

law sorted_drop:
  for xs: List<&2, Nat>
  for n: Nat
  for h: P.sorted_by(~Nat, ~Nat.is_le, xs)
  P.sorted_by(~Nat, ~Nat.is_le, List.drop(&2, Nat, xs, n))

law sorted_filter:
  for ~f: Nat -> Bool
  for xs: List<&2, Nat>
  for h: P.sorted_by(~Nat, ~Nat.is_le, xs)
  P.sorted_by(~Nat, ~Nat.is_le, List.filter(~Nat, ~f, xs))

law sorted_head_le_mem:
  for x: Nat
  for xs: List<&2, Nat>
  for y: Nat
  for hs: P.sorted_by(~Nat, ~Nat.is_le, x <> xs)
  for hm: P.mem(~Nat, ~Nat.is_eq, y, xs)
  MNat.le(x, y)

law sorted_le_of_mem:
  for x: Nat
  for xs: List<&2, Nat>
  for y: Nat
  for hs: P.sorted_by(~Nat, ~Nat.is_le, x <> xs)
  for hm: P.mem(~Nat, ~Nat.is_eq, y, x <> xs)
  MNat.le(x, y)

law sorted_append:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for bnd: @x: Nat -> @y: Nat -> P.mem(~Nat, ~Nat.is_eq, x, xs) -> P.mem(~Nat, ~Nat.is_eq, y, ys) -> MNat.le(x, y)
  for hx: P.sorted_by(~Nat, ~Nat.is_le, xs)
  for hy: P.sorted_by(~Nat, ~Nat.is_le, ys)
  P.sorted_by(~Nat, ~Nat.is_le, List.append(&2, Nat, xs, ys))
