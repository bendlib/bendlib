import Base

law lt_twelve:
  for n: Nat
  {Nat.is_lt(n, 12n) == True{} : Bool}

law list_short:
  for xs: List<&2, Nat>
  {Nat.is_lt(List.length(&2, Nat, xs), 6n) == True{} : Bool}

law fn_eq:
  {(x => Nat.add(x, 0n)) == (x => x) : Nat -> Nat}
