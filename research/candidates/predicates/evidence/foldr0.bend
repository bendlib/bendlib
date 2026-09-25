import Base

# Pair-free Base-only candidate: fold right carrying the predecessor as a Maybe.
def sorted_by(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> Data:
  {List.foldr(~&2, ~A, ~(Maybe<&2, A> -> Bool), ~(+x => k => m => Bool.and(Maybe.default(&2, Bool, Maybe.map(&2, A, Bool, y => le(y, x), m), True{}), k(Some{x}))), xs, m => True{})(None{}) == True{} : Bool}

def is_sorted(+xs: List<&2, Nat>) -> Bool:
  List.foldr(~&2, ~Nat, ~(Maybe<&2, Nat> -> Bool), ~(+x => k => m => Bool.and(Maybe.default(&2, Bool, Maybe.map(&2, Nat, Bool, y => Nat.is_le(y, x), m), True{}), k(Some{x}))), xs, m => True{})(None{})

def t1() -> {is_sorted([1n, 2n, 2n, 3n]) == True{} : Bool}:
  {==}

def t2() -> {is_sorted([1n, 3n, 2n]) == False{} : Bool}:
  {==}

def t3() -> sorted_by(~Nat, ~Nat.is_le, [0n, 4n, 9n]):
  {==}

def main() -> Bool:
  is_sorted([1n, 3n, 2n])
