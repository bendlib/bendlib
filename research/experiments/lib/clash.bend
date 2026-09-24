import Base

law Nat.ge_refl:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}

def Nat.ge_refl(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Nat.ge_refl(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}
