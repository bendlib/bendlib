import Base

# Base-only perm candidate: equal after Base List.sort.
def perm_by(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +ys: List<&2, A>) -> Data:
  {List.sort(~A, ~le, xs) == List.sort(~A, ~le, ys) : List<&2, A>}

def perm_refl(-xs: List<&2, Nat>) -> perm_by(~Nat, ~Nat.is_le, xs, xs):
  {==}

def perm_sym(-xs: List<&2, Nat>, -ys: List<&2, Nat>, h: perm_by(~Nat, ~Nat.is_le, xs, ys)) -> perm_by(~Nat, ~Nat.is_le, ys, xs):
  Equal.sym(List<&2, Nat>, List.sort(~Nat, ~Nat.is_le, xs), List.sort(~Nat, ~Nat.is_le, ys), h)

def perm_trans(-xs: List<&2, Nat>, -ys: List<&2, Nat>, -zs: List<&2, Nat>, h1: perm_by(~Nat, ~Nat.is_le, xs, ys), h2: perm_by(~Nat, ~Nat.is_le, ys, zs)) -> perm_by(~Nat, ~Nat.is_le, xs, zs):
  Equal.trans(List<&2, Nat>, List.sort(~Nat, ~Nat.is_le, xs), List.sort(~Nat, ~Nat.is_le, ys), List.sort(~Nat, ~Nat.is_le, zs), h1, h2)

# Reusable: an equality on Data is Data.
def perm_reuse(-xs: List<&2, Nat>, -ys: List<&2, Nat>, +h: perm_by(~Nat, ~Nat.is_le, xs, ys)) -> perm_by(~Nat, ~Nat.is_le, xs, ys) & perm_by(~Nat, ~Nat.is_le, xs, ys):
  (h, h)

# Closed instance holds.
def swap3() -> perm_by(~Nat, ~Nat.is_le, [3n, 1n, 2n], [2n, 3n, 1n]):
  {==}
