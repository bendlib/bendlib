import Base
import ./kernel.bend as K

def bad() -> K.perm(Nat, [1n, 2n], [2n, 2n]):
  (0n <> Nil{}, {==})
