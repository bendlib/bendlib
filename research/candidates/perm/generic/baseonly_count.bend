import Base

# Attempt 1: count via filter with a template capturing x (not closed).
def count_filter(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Nat:
  List.length(&2, A, List.filter(~A, ~(y => eq(y, x)), xs))

def t1() -> {count_filter(~Nat, ~Nat.is_eq, 2n, [2n, 1n, 2n]) == 2n : Nat}:
  {==}
