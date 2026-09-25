import Base
import ./baseonly_sort.bend as S

# perm_swap at variables: does it reduce? (expected: stuck on List.sort fuel/merge at variables)
def perm_swap2(x: Nat, y: Nat) -> S.perm_by(~Nat, ~Nat.is_le, [x, y], [y, x]):
  {==}
