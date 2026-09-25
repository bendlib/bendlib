import Base

def two() -> Nat:
  2n

law two_bad:
  {Nat.add(two(), 0n) == 3n : Nat}
