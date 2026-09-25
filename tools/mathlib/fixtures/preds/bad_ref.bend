import Base
import ../../../../packages/bend-mathlib/nat.bend as MNat

def bad_ref(+xs: List<&2, Nat>) -> Data:
  {List.all(~&2, ~Nat, ~MNat.le, xs) == True{} : Bool}
