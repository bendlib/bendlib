import Base

# can the parameter the proof MATCHES on be erased too?
law add_zero_r:
  for -x: Nat
  {Nat.add(x, 0n) == x : Nat}

def add_zero_r(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def use(x: Nat) -> &r: Nat -> {Nat.add(r, 0n) == r : Nat}:
  (x, add_zero_r(x))
