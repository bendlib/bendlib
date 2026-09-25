import Base
import ./algebra.bend as Alg
import ../../../packages/bend-mathlib/nat.bend as MNat
import ../../../packages/bend-mathlib/bool.bend as MBool
import ../../../packages/bend-mathlib/list.bend as MList

def internal_nat_add_assoc(x: Nat, y: Nat, z: Nat) -> {Nat.add(Nat.add(x, y), z) == Nat.add(x, Nat.add(y, z)) : Nat}:
  MNat.add_assoc(x, y, z)

def internal_nat_add_comm(x: Nat, y: Nat) -> {Nat.add(x, y) == Nat.add(y, x) : Nat}:
  MNat.add_comm(x, y)

def internal_nat_mul(x: Nat, y: Nat) -> Nat:
  Nat.mul(x, y)

def internal_nat_mul_assoc(x: Nat, y: Nat, z: Nat) -> {Nat.mul(Nat.mul(x, y), z) == Nat.mul(x, Nat.mul(y, z)) : Nat}:
  MNat.mul_assoc(x, y, z)

def internal_nat_mul_comm(x: Nat, y: Nat) -> {Nat.mul(x, y) == Nat.mul(y, x) : Nat}:
  MNat.mul_comm(x, y)

def internal_bool_and_assoc(x: Bool, y: Bool, z: Bool) -> {Bool.and(Bool.and(x, y), z) == Bool.and(x, Bool.and(y, z)) : Bool}:
  MBool.and_assoc(x, y, z)

def internal_bool_and_comm(x: Bool, y: Bool) -> {Bool.and(x, y) == Bool.and(y, x) : Bool}:
  MBool.and_comm(x, y)

def internal_bool_or_assoc(x: Bool, y: Bool, z: Bool) -> {Bool.or(Bool.or(x, y), z) == Bool.or(x, Bool.or(y, z)) : Bool}:
  MBool.or_assoc(x, y, z)

def internal_bool_or_comm(x: Bool, y: Bool) -> {Bool.or(x, y) == Bool.or(y, x) : Bool}:
  MBool.or_comm(x, y)

def internal_list_nat_append_assoc(x: List<&2, Nat>, y: List<&2, Nat>, z: List<&2, Nat>) -> {List.append(&2, Nat, List.append(&2, Nat, x, y), z) == List.append(&2, Nat, x, List.append(&2, Nat, y, z)) : List<&2, Nat>}:
  MList.append_assoc(&2, Nat, x, y, z)

law nat_add_left_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def nat_add_left_comm(a, b, c):
  Alg.op_left_comm(~Nat, ~Nat.add, ~internal_nat_add_assoc, ~internal_nat_add_comm, a, b, c)

law nat_add_right_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}

def nat_add_right_comm(a, b, c):
  Alg.op_right_comm(~Nat, ~Nat.add, ~internal_nat_add_assoc, ~internal_nat_add_comm, a, b, c)

law nat_add_four:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}

def nat_add_four(a, b, c, d):
  Alg.op_four(~Nat, ~Nat.add, ~internal_nat_add_assoc, ~internal_nat_add_comm, a, b, c, d)

law nat_mul_left_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(b, Nat.mul(a, c)) : Nat}

def nat_mul_left_comm(a, b, c):
  Alg.op_left_comm(~Nat, ~internal_nat_mul, ~internal_nat_mul_assoc, ~internal_nat_mul_comm, a, b, c)

law nat_mul_right_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(Nat.mul(a, c), b) : Nat}

def nat_mul_right_comm(a, b, c):
  Alg.op_right_comm(~Nat, ~internal_nat_mul, ~internal_nat_mul_assoc, ~internal_nat_mul_comm, a, b, c)

law nat_mul_four:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) : Nat}

def nat_mul_four(a, b, c, d):
  Alg.op_four(~Nat, ~internal_nat_mul, ~internal_nat_mul_assoc, ~internal_nat_mul_comm, a, b, c, d)

law bool_and_left_comm:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}

def bool_and_left_comm(a, b, c):
  Alg.op_left_comm(~Bool, ~Bool.and, ~internal_bool_and_assoc, ~internal_bool_and_comm, a, b, c)

law bool_and_right_comm:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(Bool.and(a, b), c) == Bool.and(Bool.and(a, c), b) : Bool}

def bool_and_right_comm(a, b, c):
  Alg.op_right_comm(~Bool, ~Bool.and, ~internal_bool_and_assoc, ~internal_bool_and_comm, a, b, c)

law bool_or_left_comm:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}

def bool_or_left_comm(a, b, c):
  Alg.op_left_comm(~Bool, ~Bool.or, ~internal_bool_or_assoc, ~internal_bool_or_comm, a, b, c)

law bool_or_right_comm:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.or(Bool.or(a, b), c) == Bool.or(Bool.or(a, c), b) : Bool}

def bool_or_right_comm(a, b, c):
  Alg.op_right_comm(~Bool, ~Bool.or, ~internal_bool_or_assoc, ~internal_bool_or_comm, a, b, c)

law list_nat_append_assoc4:
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  for +c: List<&2, Nat>
  for +d: List<&2, Nat>
  {List.append(&2, Nat, List.append(&2, Nat, List.append(&2, Nat, a, b), c), d) == List.append(&2, Nat, a, List.append(&2, Nat, b, List.append(&2, Nat, c, d))) : List<&2, Nat>}

def list_nat_append_assoc4(a, b, c, d):
  Alg.op_assoc4(~List<&2, Nat>, ~List.append(&2, Nat), ~internal_list_nat_append_assoc, a, b, c, d)
