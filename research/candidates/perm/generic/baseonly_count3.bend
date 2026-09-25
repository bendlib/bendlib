import Base

# count via filter whose template captures x (a def parameter).
def count(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Nat:
  List.length(&2, A, List.filter(~A, ~(y => eq(y, x)), xs))

# At a variable x.
def count_nil(x: Nat) -> {count(~Nat, ~Nat.is_eq, x, Nil{}) == 0n : Nat}:
  {==}

# Runtime use at a variable x.
def run(+x: Nat, xs: List<&2, Nat>) -> Nat:
  count(~Nat, ~Nat.is_eq, x, xs)

def main() -> Nat:
  run(2n, [2n, 1n, 2n, 5n, 2n])
