import Base

law Nat.add_zero_r:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}

def Nat.add_zero_r(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law Nat.add_succ_r:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def Nat.add_succ_r(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_succ_r(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}
