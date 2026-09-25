import Base

def ev_helper(x: Nat) -> Bool:
  Nat.is_le(x, 0n)

def ev_bad(+xs: List<&2, Nat>) -> Data:
  {ev_helper(List.length(&2, Nat, xs)) == True{} : Bool}
