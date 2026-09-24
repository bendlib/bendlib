import Base

# A predicate whose result type sits on a continuation line.
def multiline_pred(
  a: Nat
) -> Data:
  {Frobnicate(a) == True{} : Bool}

# A predicate whose result type is on its header line.
def single_pred(a: Nat) -> Data:
  {Frobnicate(a) == True{} : Bool}
