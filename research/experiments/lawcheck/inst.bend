import Base
import ./buggy.bend as B

law c1:
  {List.length(&2, Nat, B.ins(0n, Nil{})) == 1n+List.length(&2, Nat, Nil{}) : Nat}

def c1():
  {==}

law c2:
  {B.ins(0n, Nil{}) == [0n] : List<&2, Nat>}

def c2():
  {==}

law c3:
  {List.length(&2, Nat, B.ins(0n, [0n])) == 1n+List.length(&2, Nat, [0n]) : Nat}

def c3():
  {==}

law c4:
  {B.ins(0n, [0n]) == [0n, 0n] : List<&2, Nat>}

def c4():
  {==}

law c5:
  {List.length(&2, Nat, B.ins(0n, [1n])) == 1n+List.length(&2, Nat, [1n]) : Nat}

def c5():
  {==}

law c6:
  {B.ins(0n, [1n]) == [0n, 1n] : List<&2, Nat>}

def c6():
  {==}

law c7:
  {List.length(&2, Nat, B.ins(0n, [0n, 1n])) == 1n+List.length(&2, Nat, [0n, 1n]) : Nat}

def c7():
  {==}

law c8:
  {B.ins(0n, [0n, 1n]) == [0n, 0n, 1n] : List<&2, Nat>}

def c8():
  {==}

law c9:
  {List.length(&2, Nat, B.ins(0n, [1n, 0n])) == 1n+List.length(&2, Nat, [1n, 0n]) : Nat}

def c9():
  {==}

law c10:
  {B.ins(0n, [0n, 1n]) == [0n, 0n, 1n] : List<&2, Nat>}

def c10():
  {==}

law c11:
  {List.length(&2, Nat, B.ins(0n, [2n, 1n])) == 1n+List.length(&2, Nat, [2n, 1n]) : Nat}

def c11():
  {==}

law c12:
  {B.ins(0n, [1n, 2n]) == [0n, 1n, 2n] : List<&2, Nat>}

def c12():
  {==}

law c13:
  {List.length(&2, Nat, B.ins(0n, [0n, 0n])) == 1n+List.length(&2, Nat, [0n, 0n]) : Nat}

def c13():
  {==}

law c14:
  {B.ins(0n, [0n, 0n]) == [0n, 0n, 0n] : List<&2, Nat>}

def c14():
  {==}

law c15:
  {List.length(&2, Nat, B.ins(0n, [1n, 2n, 0n])) == 1n+List.length(&2, Nat, [1n, 2n, 0n]) : Nat}

def c15():
  {==}

law c16:
  {B.ins(0n, [0n, 1n, 2n]) == [0n, 0n, 1n, 2n] : List<&2, Nat>}

def c16():
  {==}

law c17:
  {List.length(&2, Nat, B.ins(1n, Nil{})) == 1n+List.length(&2, Nat, Nil{}) : Nat}

def c17():
  {==}

law c18:
  {B.ins(1n, Nil{}) == [1n] : List<&2, Nat>}

def c18():
  {==}

law c19:
  {List.length(&2, Nat, B.ins(1n, [0n])) == 1n+List.length(&2, Nat, [0n]) : Nat}

def c19():
  {==}

law c20:
  {B.ins(1n, [0n]) == [0n, 1n] : List<&2, Nat>}

def c20():
  {==}

law c21:
  {List.length(&2, Nat, B.ins(1n, [1n])) == 1n+List.length(&2, Nat, [1n]) : Nat}

def c21():
  {==}

law c22:
  {B.ins(1n, [1n]) == [1n, 1n] : List<&2, Nat>}

def c22():
  {==}

law c23:
  {List.length(&2, Nat, B.ins(1n, [0n, 1n])) == 1n+List.length(&2, Nat, [0n, 1n]) : Nat}

def c23():
  {==}

law c24:
  {B.ins(1n, [0n, 1n]) == [0n, 1n, 1n] : List<&2, Nat>}

def c24():
  {==}

law c25:
  {List.length(&2, Nat, B.ins(1n, [1n, 0n])) == 1n+List.length(&2, Nat, [1n, 0n]) : Nat}

def c25():
  {==}

law c26:
  {B.ins(1n, [0n, 1n]) == [0n, 1n, 1n] : List<&2, Nat>}

def c26():
  {==}

law c27:
  {List.length(&2, Nat, B.ins(1n, [2n, 1n])) == 1n+List.length(&2, Nat, [2n, 1n]) : Nat}

def c27():
  {==}

law c28:
  {B.ins(1n, [1n, 2n]) == [1n, 1n, 2n] : List<&2, Nat>}

def c28():
  {==}

law c29:
  {List.length(&2, Nat, B.ins(1n, [0n, 0n])) == 1n+List.length(&2, Nat, [0n, 0n]) : Nat}

def c29():
  {==}

law c30:
  {B.ins(1n, [0n, 0n]) == [0n, 0n, 1n] : List<&2, Nat>}

def c30():
  {==}

law c31:
  {List.length(&2, Nat, B.ins(1n, [1n, 2n, 0n])) == 1n+List.length(&2, Nat, [1n, 2n, 0n]) : Nat}

def c31():
  {==}

law c32:
  {B.ins(1n, [0n, 1n, 2n]) == [0n, 1n, 1n, 2n] : List<&2, Nat>}

def c32():
  {==}

law c33:
  {List.length(&2, Nat, B.ins(2n, Nil{})) == 1n+List.length(&2, Nat, Nil{}) : Nat}

def c33():
  {==}

law c34:
  {B.ins(2n, Nil{}) == [2n] : List<&2, Nat>}

def c34():
  {==}

law c35:
  {List.length(&2, Nat, B.ins(2n, [0n])) == 1n+List.length(&2, Nat, [0n]) : Nat}

def c35():
  {==}

law c36:
  {B.ins(2n, [0n]) == [0n, 2n] : List<&2, Nat>}

def c36():
  {==}

law c37:
  {List.length(&2, Nat, B.ins(2n, [1n])) == 1n+List.length(&2, Nat, [1n]) : Nat}

def c37():
  {==}

law c38:
  {B.ins(2n, [1n]) == [1n, 2n] : List<&2, Nat>}

def c38():
  {==}

law c39:
  {List.length(&2, Nat, B.ins(2n, [0n, 1n])) == 1n+List.length(&2, Nat, [0n, 1n]) : Nat}

def c39():
  {==}

law c40:
  {B.ins(2n, [0n, 1n]) == [0n, 1n, 2n] : List<&2, Nat>}

def c40():
  {==}

law c41:
  {List.length(&2, Nat, B.ins(2n, [1n, 0n])) == 1n+List.length(&2, Nat, [1n, 0n]) : Nat}

def c41():
  {==}

law c42:
  {B.ins(2n, [0n, 1n]) == [0n, 1n, 2n] : List<&2, Nat>}

def c42():
  {==}

law c43:
  {List.length(&2, Nat, B.ins(2n, [2n, 1n])) == 1n+List.length(&2, Nat, [2n, 1n]) : Nat}

def c43():
  {==}

law c44:
  {B.ins(2n, [1n, 2n]) == [1n, 2n, 2n] : List<&2, Nat>}

def c44():
  {==}

law c45:
  {List.length(&2, Nat, B.ins(2n, [0n, 0n])) == 1n+List.length(&2, Nat, [0n, 0n]) : Nat}

def c45():
  {==}

law c46:
  {B.ins(2n, [0n, 0n]) == [0n, 0n, 2n] : List<&2, Nat>}

def c46():
  {==}

law c47:
  {List.length(&2, Nat, B.ins(2n, [1n, 2n, 0n])) == 1n+List.length(&2, Nat, [1n, 2n, 0n]) : Nat}

def c47():
  {==}

law c48:
  {B.ins(2n, [0n, 1n, 2n]) == [0n, 1n, 2n, 2n] : List<&2, Nat>}

def c48():
  {==}
