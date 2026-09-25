import Base

# Does a plain (non-template) lambda destructure its pair parameter?
def f(q: Nat & Nat) -> Bool:
  g = p => ((a, b) = p; Nat.is_le(a, b))
  g(q)

def main() -> Bool:
  f((1n, 2n))
