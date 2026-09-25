import Base
import ./baseonly_count4.bend as C

# Refl at a variable list: does it reduce? (expected: stuck, needs induction)
def r1(xs: List<&2, Nat>) -> C.perm_count(~Nat, ~Nat.is_eq, xs, xs):
  {==}
