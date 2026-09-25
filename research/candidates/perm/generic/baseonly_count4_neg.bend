import Base
import ./baseonly_count4.bend as C

# Negative: [1n] is not a permutation of [].
def n1() -> C.perm_count(~Nat, ~Nat.is_eq, [1n], Nil{}):
  {==}

# Refl at a variable list: does it reduce? (expected: stuck, needs induction)
def r1(xs: List<&2, Nat>) -> C.perm_count(~Nat, ~Nat.is_eq, xs, xs):
  {==}
