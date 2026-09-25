import Base

def perm_by(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +ys: List<&2, A>) -> Data:
  {List.sort(~A, ~le, xs) == List.sort(~A, ~le, ys) : List<&2, A>}

# Negative: under a preorder (compare by length), two permutations are NOT perm_by.
# [[1n], [2n]] and [[2n], [1n]] are permutations; stable sort keeps both orders.
def bad() -> perm_by(~List<&2, Nat>, ~(a => b => Nat.is_le(List.length(&2, Nat, a), List.length(&2, Nat, b))), [[1n], [2n]], [[2n], [1n]]):
  {==}
