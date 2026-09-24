import Base

def le(a: Nat, b: Nat) -> Type:
  {Nat.is_le(a, b) == True{} : Bool}

def bdisc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : bdisc(_)
  Unit{}

law zero_le:
  for b: Nat
  le(0n, b)

def zero_le(b):
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

law le_refl:
  for a: Nat
  le(a, a)

def le_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

law le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: le(a, b)
  for bc: le(b, c)
  le(a, c)

def le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+cp:
      {==}
    case 1n+ap 0n 0n:
      Empty.absurd(le(1n+ap, 0n), false_ne_true(ab))
    case 1n+ap 0n 1n+cp:
      Empty.absurd(le(1n+ap, 1n+cp), false_ne_true(ab))
    case 1n+ap 1n+bp 0n:
      Empty.absurd(le(1n+ap, 0n), false_ne_true(bc))
    case 1n+ap 1n+bp 1n+cp:
      le_trans(ap, bp, cp, ab, bc)

# does it interoperate with user sugar?
def user(a: Nat, b: Nat, h: {(a <= b : Nat) == True{} : Bool}) -> le(a, b):
  h
