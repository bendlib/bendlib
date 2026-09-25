import Base
import ./kernel.bend as K
import ./msort_perm.bend as S

def sort_perm_u32(+xs: List<&2, U32>) -> K.perm(U32, xs, S.sort(~U32, ~U32.is_le, xs)):
  S.sort_perm(~U32, ~U32.is_le, xs)

def sort_perm_nat_pairs(+xs: List<&2, List<&2, Nat>>) -> K.perm(List<&2, Nat>, xs, S.isort(~List<&2, Nat>, ~(a => b => Nat.is_le(List.length(&2, Nat, a), List.length(&2, Nat, b))), xs)):
  S.isort_perm(~List<&2, Nat>, ~(a => b => Nat.is_le(List.length(&2, Nat, a), List.length(&2, Nat, b))), xs)

def main() -> List<&2, U32>:
  S.sort(~U32, ~U32.is_le, [9, 2, 7, 2, 0])
