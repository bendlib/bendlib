import Base

law add_succ_r:
  for x: Nat
  for -y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def add_succ_r(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

# runtime caller: y is affine, returned as a value AND passed to the lemma (erased slot)
def use_erased(x: Nat, y: Nat) -> &r: Nat -> {Nat.add(x, 1n+r) == 1n+Nat.add(x, r) : Nat}:
  (y, add_succ_r(x, y))
