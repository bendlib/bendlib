import Base

law pow_add:
  for a: Nat
  for m: Nat
  for n: Nat
  {Nat.pow(a, Nat.add(m, n)) == Nat.mul(Nat.pow(a, m), Nat.pow(a, n)) : Nat}

law pow_add_wrong:
  for a: Nat
  for m: Nat
  for n: Nat
  {Nat.pow(a, Nat.add(m, n)) == Nat.add(Nat.pow(a, m), Nat.pow(a, n)) : Nat}
