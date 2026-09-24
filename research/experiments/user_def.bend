import Base
import ./v2/order.bend as O2
import ./core.bend as C

law five:
  {Nat.is_le(5n, 5n) == True{} : Bool}

def five():
  C.five_le()

def use_pred() -> O2.le(5n, 5n):
  C.five_le()
