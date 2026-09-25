import Base

# A plain lemma.
law add_zero:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}

def add_zero(x):
  add_zero_sym(x)

# A plain lemma, reversed to rewrite toward the simple side.
law add_zero_sym:
  for x: Nat
  {x == Nat.add(x, 0n) : Nat}

def add_zero_sym(x):
  x

# A predicate.
def le(a: Nat, b: Nat) -> Data:
  {Nat.is_le(a, b) == True{} : Bool}
