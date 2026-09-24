import Base
import ./lib/algebra.bend as Alg
import ./glist.bend as GL

law add_assoc:
  for x: Nat
  for y: Nat
  for z: Nat
  {Nat.add(Nat.add(x, y), z) == Nat.add(x, Nat.add(y, z)) : Nat}

def add_assoc(x, y, z):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, y, z) : {1n+Nat.add(Nat.add(p, y), z) == 1n+_ : Nat}
      {==}

def four(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(Nat.add(a, b), c), d) == Nat.add(a, Nat.add(b, Nat.add(c, d))) : Nat}:
  Alg.reassoc4(~Nat.add, ~add_assoc, a, b, c, d)
