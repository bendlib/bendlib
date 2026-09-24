import Base

type tree is Data:
  leaf{}

law Nat.add_zero_x:
  for x: Nat
  for y: Nat
  {Nat.add(x, 0n)
   == x : Nat}

def Nat.add_zero_x(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_zero_x(p, y) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def iszero(n: Nat) -> Data:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty
