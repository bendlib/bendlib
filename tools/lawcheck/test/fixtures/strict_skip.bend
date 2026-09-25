import Base

law vacuous:
  for n: Nat
  for h: {Nat.is_lt(n, n) == True{} : Bool}
  {Nat.add(n, 0n) == n : Nat}
