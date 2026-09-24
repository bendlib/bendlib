import Base

# A stand-in for @unsafe code: its body is opaque to the checker.
@unsafe
def zero(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      0n

law zero_is_zero:
  for n: Nat
  {zero(n) == 0n : Nat}

def zero_is_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}
