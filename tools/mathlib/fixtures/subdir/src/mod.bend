import Base

law add_ident:
  for -a: Nat
  {Nat.add(0n, a) == a : Nat}

def add_ident(a):
  {==}
