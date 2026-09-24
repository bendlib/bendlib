import Base
import ./v1/order.bend as O

def five_le() -> O.le(5n, 5n):
  O.le_refl(5n)

def mk() -> O.tree:
  O.tnode{O.tleaf{}, 3n, O.tleaf{}}
