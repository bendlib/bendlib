import Base

# A non-self helper whose two arguments are swapped by the arg-swap mutant.
def pick(a: Nat, b: Nat) -> Nat:
  a

def first_of(a: Nat, b: Nat) -> Nat:
  pick(a, b)

# Diagonal law only: first_of(a, a) = a, so the swapped helper call still passes.
law first_of_diag:
  for a: Nat
  {first_of(a, a) == a : Nat}
