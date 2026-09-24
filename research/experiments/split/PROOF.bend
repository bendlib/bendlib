import Base
import ./LAWS.bend as Laws

def Laws.add_zero_r(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}
