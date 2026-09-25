import Base

# Base-only perm candidate: equal after Base List.sort.
def perm_by(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +ys: List<&2, A>) -> Data:
  {List.sort(~A, ~le, xs) == List.sort(~A, ~le, ys) : List<&2, A>}
