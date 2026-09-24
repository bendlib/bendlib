import Base

# is an equality proof (affine binder) usable twice inside a proof?
def use_twice_eq(a: Nat, b: Nat, h: {a == b : Nat}) -> {a == b : Nat} & {a == b : Nat}:
  (h, h)
