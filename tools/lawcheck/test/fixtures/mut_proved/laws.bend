import Base
import ./lib.bend as L

law dbl_zero:
  {L.dbl(0n) == 0n : Nat}

def dbl_zero():
  {==}

law dbl_one:
  {L.dbl(1n) == 2n : Nat}

def dbl_one():
  {==}
