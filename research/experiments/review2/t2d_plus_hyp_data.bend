import Base

def le(a: Nat, b: Nat) -> Data:
  {Nat.is_le(a, b) == True{} : Bool}

def use_twice(a: Nat, b: Nat, +h: le(a, b)) -> le(a, b) & le(a, b):
  (h, h)
