import Base

def IsZero(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

law all_zero_bad:
  for n: Nat
  IsZero(n)
