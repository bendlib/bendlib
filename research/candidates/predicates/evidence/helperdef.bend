import Base

# Non-Base variant: a user def destructures the pair once (nominal, violates F4; for evidence only).
def le_pair(~A: Data, ~le: A -> A -> Bool, p: A & A) -> Bool:
  (a, b) = p
  le(a, b)

def sorted_by(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> Data:
  {List.all(~&1, ~(A & A), ~(p => le_pair(~A, ~le, p)), List.zip(&2, A, &2, A, xs, List.tail(&2, A, xs))) == True{} : Bool}

def is_sorted(+xs: List<&2, Nat>) -> Bool:
  List.all(~&1, ~(Nat & Nat), ~(p => le_pair(~Nat, ~Nat.is_le, p)), List.zip(&2, Nat, &2, Nat, xs, List.tail(&2, Nat, xs)))

def main() -> Bool:
  is_sorted([1n, 3n, 2n])
