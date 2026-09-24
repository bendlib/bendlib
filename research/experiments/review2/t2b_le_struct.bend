import Base

def LE(a: Nat, b: Nat) -> Type:
  match a:
    case 0n:
      Unit
    case 1n+ap:
      match b:
        case 0n:
          Empty
        case 1n+bp:
          LE(ap, bp)

law zero_LE:
  for b: Nat
  LE(0n, b)

def zero_LE(b):
  Unit{}

law LE_refl:
  for a: Nat
  LE(a, a)

def LE_refl(a):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      LE_refl(p)

law LE_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: LE(a, b)
  for bc: LE(b, c)
  LE(a, c)

def LE_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ _:
      Unit{}
    case 1n+ap 0n _:
      match ab:
    case 1n+ap 1n+bp 0n:
      match bc:
    case 1n+ap 1n+bp 1n+cp:
      LE_trans(ap, bp, cp, ab, bc)

law le_of_LE:
  for a: Nat
  for b: Nat
  for h: LE(a, b)
  {Nat.is_le(a, b) == True{} : Bool}

def le_of_LE(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      match h:
    case 1n+ap 1n+bp:
      le_of_LE(ap, bp, h)
