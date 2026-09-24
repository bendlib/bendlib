import Base
import ./helper.bend as H

# The helper is the identity on its argument.
law inner_id:
  for y: Nat
  {H.helper(y) == y : Nat}

def inner_id(y):
  {==}
