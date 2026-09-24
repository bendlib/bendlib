import Base

def le(a: Nat, b: Nat) -> Data:
  {Nat.is_le(a, b) == True{} : Bool}

law le_total:
  for a: Nat
  for b: Nat
  Or(le(a, b), le(b, a))

def le_total(a, b):
  match a b:
    case 0n 0n:
      Inl{{==}}
    case 0n 1n+bp:
      Inl{{==}}
    case 1n+ap 0n:
      Inr{{==}}
    case 1n+ap 1n+bp:
      le_total(ap, bp)

# reuse of a Data-valued hypothesis inside a proof
law le_dup:
  for a: Nat
  for b: Nat
  for +h: le(a, b)
  le(a, b) & le(a, b)

def le_dup(a, b, h):
  (h, h)
