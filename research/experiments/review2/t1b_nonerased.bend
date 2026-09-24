import Base

law add_succ_r2:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def add_succ_r2(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r2(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

# same caller, but y is now consumed by the lemma: expected affinity error
def use_nonerased(x: Nat, y: Nat) -> &r: Nat -> {Nat.add(x, 1n+r) == 1n+Nat.add(x, r) : Nat}:
  (y, add_succ_r2(x, y))
