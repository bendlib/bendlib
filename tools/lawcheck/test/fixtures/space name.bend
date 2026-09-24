import Base

def dbl(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      2n+dbl(p)

law dbl_add:
  for n: Nat
  {dbl(n) == Nat.add(n, n) : Nat}
