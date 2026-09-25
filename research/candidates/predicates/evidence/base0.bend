import Base

def sorted_by(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> Data:
  {List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), List.zip(&2, A, &2, A, xs, List.tail(&2, A, xs))) == True{} : Bool}

def is_sorted(+xs: List<&2, Nat>) -> Bool:
  List.all(~&1, ~(Nat & Nat), ~(p => Nat.is_le(Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p))), List.zip(&2, Nat, &2, Nat, xs, List.tail(&2, Nat, xs)))

def t1() -> {is_sorted([1n, 2n, 3n]) == True{} : Bool}:
  {==}

def main() -> Bool:
  is_sorted([1n, 3n, 2n])
