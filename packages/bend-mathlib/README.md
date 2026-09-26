# bend-mathlib

Machine-checked lemmas for Bend 2, checked with `bend 2.0.27`.

Rewriting: `%e : P` replaces the right side of `e` with its left side, so `name` expands the simple
side into the compound one and `name_sym` simplifies the compound side.

Rows marked `next` are proved in this repository but not yet published: the import lines above do not contain them yet.

## algebra

```python
import bend-mathlib@0.3.0.0/algebra.bend as MAlgebra
```

| lemma | statement | meaning | since |
|---|---|---|---|
| `op_assoc4(~A, ~op, ~assoc, a, b, c, d)` | `∀ ~A: Data, ~op: A -> A -> A, ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}, +a: A, +b: A, +c: A, +d: A. {op(op(op(a, b), c), d) == op(a, op(b, op(c, d))) : A}` | Four-way reassociation from associativity alone. | next |
| `op_left_comm(~A, ~op, ~assoc, ~comm, a, b, c)` | `∀ ~A: Data, ~op: A -> A -> A, ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}, ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}, +a: A, +b: A, +c: A. {op(a, op(b, c)) == op(b, op(a, c)) : A}` | Left commutation from associativity and commutativity. | next |
| `op_right_comm(~A, ~op, ~assoc, ~comm, a, b, c)` | `∀ ~A: Data, ~op: A -> A -> A, ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}, ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}, +a: A, +b: A, +c: A. {op(op(a, b), c) == op(op(a, c), b) : A}` | Right commutation from associativity and commutativity. | next |
| `op_four(~A, ~op, ~assoc, ~comm, a, b, c, d)` | `∀ ~A: Data, ~op: A -> A -> A, ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}, ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}, +a: A, +b: A, +c: A, +d: A. {op(op(a, b), op(c, d)) == op(op(a, c), op(b, d)) : A}` | Middle-four interchange from associativity and commutativity. | next |
| `op_comm3(~A, ~op, ~comm, a, b, c)` | `∀ ~A: Data, ~op: A -> A -> A, ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}, +a: A, +b: A, +c: A. {op(op(a, b), c) == op(c, op(b, a)) : A}` | Three-way commutation from commutativity alone. | next |
| `nat_add_left_comm(a, b, c)` | `∀ +a: Nat, +b: Nat, +c: Nat. {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}` | Nat addition is left-commutative. | next |
| `nat_add_right_comm(a, b, c)` | `∀ +a: Nat, +b: Nat, +c: Nat. {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}` | Nat addition is right-commutative. | next |
| `nat_add_four(a, b, c, d)` | `∀ +a: Nat, +b: Nat, +c: Nat, +d: Nat. {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}` | Nat addition's middle-four interchange. | next |
| `nat_mul_left_comm(a, b, c)` | `∀ +a: Nat, +b: Nat, +c: Nat. {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(b, Nat.mul(a, c)) : Nat}` | Nat multiplication is left-commutative. | next |
| `nat_mul_right_comm(a, b, c)` | `∀ +a: Nat, +b: Nat, +c: Nat. {Nat.mul(Nat.mul(a, b), c) == Nat.mul(Nat.mul(a, c), b) : Nat}` | Nat multiplication is right-commutative. | next |
| `nat_mul_four(a, b, c, d)` | `∀ +a: Nat, +b: Nat, +c: Nat, +d: Nat. {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) : Nat}` | Nat multiplication's middle-four interchange. | next |
| `bool_and_left_comm(a, b, c)` | `∀ +a: Bool, +b: Bool, +c: Bool. {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}` | Bool and is left-commutative. | next |
| `bool_and_right_comm(a, b, c)` | `∀ +a: Bool, +b: Bool, +c: Bool. {Bool.and(Bool.and(a, b), c) == Bool.and(Bool.and(a, c), b) : Bool}` | Bool and is right-commutative. | next |
| `bool_or_left_comm(a, b, c)` | `∀ +a: Bool, +b: Bool, +c: Bool. {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}` | Bool or is left-commutative. | next |
| `bool_or_right_comm(a, b, c)` | `∀ +a: Bool, +b: Bool, +c: Bool. {Bool.or(Bool.or(a, b), c) == Bool.or(Bool.or(a, c), b) : Bool}` | Bool or is right-commutative. | next |
| `list_nat_append_assoc4(a, b, c, d)` | `∀ +a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, +d: List<&2, Nat>. {List.append(&2, Nat, List.append(&2, Nat, List.append(&2, Nat, a, b), c), d) == List.append(&2, Nat, a, List.append(&2, Nat, b, List.append(&2, Nat, c, d))) : List<&2, Nat>}` | Four-way reassociation for List append over Nat. | next |
| `foldl_op_eq_foldr_op(~B, ~op, ~assoc, ~comm, ~z, ~id, xs)` | `∀ ~B: Data, ~op: B -> B -> B, ~assoc: @x: B -> @y: B -> @z: B -> {op(op(x, y), z) == op(x, op(y, z)) : B}, ~comm: @x: B -> @y: B -> {op(x, y) == op(y, x) : B}, ~z: B, ~id: @x: B -> {op(z, x) == x : B}, +xs: List<&2, B>. {List.foldl(&2, B, B, op, xs, z) == List.foldr(&2, B, B, op, xs, z) : B}` | Folding left equals folding right for an associative, commutative operation with a left identity. | next |
| `op_assoc4_sym(~A, ~op, ~assoc, a, b, c, d)` | `∀ ~A: Data, ~op: A -> A -> A, ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}, +a: A, +b: A, +c: A, +d: A. {op(a, op(b, op(c, d))) == op(op(op(a, b), c), d) : A}` | Four-way reassociation from associativity alone, reversed to rewrite toward the simple side. | next |
| `op_left_comm_sym(~A, ~op, ~assoc, ~comm, a, b, c)` | `∀ ~A: Data, ~op: A -> A -> A, ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}, ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}, +a: A, +b: A, +c: A. {op(b, op(a, c)) == op(a, op(b, c)) : A}` | Left commutation from associativity and commutativity, reversed to rewrite toward the simple side. | next |
| `op_right_comm_sym(~A, ~op, ~assoc, ~comm, a, b, c)` | `∀ ~A: Data, ~op: A -> A -> A, ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}, ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}, +a: A, +b: A, +c: A. {op(op(a, c), b) == op(op(a, b), c) : A}` | Right commutation from associativity and commutativity, reversed to rewrite toward the simple side. | next |
| `op_four_sym(~A, ~op, ~assoc, ~comm, a, b, c, d)` | `∀ ~A: Data, ~op: A -> A -> A, ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}, ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}, +a: A, +b: A, +c: A, +d: A. {op(op(a, c), op(b, d)) == op(op(a, b), op(c, d)) : A}` | Middle-four interchange from associativity and commutativity, reversed to rewrite toward the simple side. | next |
| `op_comm3_sym(~A, ~op, ~comm, a, b, c)` | `∀ ~A: Data, ~op: A -> A -> A, ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}, +a: A, +b: A, +c: A. {op(c, op(b, a)) == op(op(a, b), c) : A}` | Three-way commutation from commutativity alone, reversed to rewrite toward the simple side. | next |
| `nat_add_left_comm_sym(a, b, c)` | `∀ +a: Nat, +b: Nat, +c: Nat. {Nat.add(b, Nat.add(a, c)) == Nat.add(a, Nat.add(b, c)) : Nat}` | Nat addition is left-commutative, reversed to rewrite toward the simple side. | next |
| `nat_add_right_comm_sym(a, b, c)` | `∀ +a: Nat, +b: Nat, +c: Nat. {Nat.add(Nat.add(a, c), b) == Nat.add(Nat.add(a, b), c) : Nat}` | Nat addition is right-commutative, reversed to rewrite toward the simple side. | next |
| `nat_add_four_sym(a, b, c, d)` | `∀ +a: Nat, +b: Nat, +c: Nat, +d: Nat. {Nat.add(Nat.add(a, c), Nat.add(b, d)) == Nat.add(Nat.add(a, b), Nat.add(c, d)) : Nat}` | Nat addition's middle-four interchange, reversed to rewrite toward the simple side. | next |
| `nat_mul_left_comm_sym(a, b, c)` | `∀ +a: Nat, +b: Nat, +c: Nat. {Nat.mul(b, Nat.mul(a, c)) == Nat.mul(a, Nat.mul(b, c)) : Nat}` | Nat multiplication is left-commutative, reversed to rewrite toward the simple side. | next |
| `nat_mul_right_comm_sym(a, b, c)` | `∀ +a: Nat, +b: Nat, +c: Nat. {Nat.mul(Nat.mul(a, c), b) == Nat.mul(Nat.mul(a, b), c) : Nat}` | Nat multiplication is right-commutative, reversed to rewrite toward the simple side. | next |
| `nat_mul_four_sym(a, b, c, d)` | `∀ +a: Nat, +b: Nat, +c: Nat, +d: Nat. {Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) == Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) : Nat}` | Nat multiplication's middle-four interchange, reversed to rewrite toward the simple side. | next |
| `bool_and_left_comm_sym(a, b, c)` | `∀ +a: Bool, +b: Bool, +c: Bool. {Bool.and(b, Bool.and(a, c)) == Bool.and(a, Bool.and(b, c)) : Bool}` | Bool and is left-commutative, reversed to rewrite toward the simple side. | next |
| `bool_and_right_comm_sym(a, b, c)` | `∀ +a: Bool, +b: Bool, +c: Bool. {Bool.and(Bool.and(a, c), b) == Bool.and(Bool.and(a, b), c) : Bool}` | Bool and is right-commutative, reversed to rewrite toward the simple side. | next |
| `bool_or_left_comm_sym(a, b, c)` | `∀ +a: Bool, +b: Bool, +c: Bool. {Bool.or(b, Bool.or(a, c)) == Bool.or(a, Bool.or(b, c)) : Bool}` | Bool or is left-commutative, reversed to rewrite toward the simple side. | next |
| `bool_or_right_comm_sym(a, b, c)` | `∀ +a: Bool, +b: Bool, +c: Bool. {Bool.or(Bool.or(a, c), b) == Bool.or(Bool.or(a, b), c) : Bool}` | Bool or is right-commutative, reversed to rewrite toward the simple side. | next |
| `list_nat_append_assoc4_sym(a, b, c, d)` | `∀ +a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, +d: List<&2, Nat>. {List.append(&2, Nat, a, List.append(&2, Nat, b, List.append(&2, Nat, c, d))) == List.append(&2, Nat, List.append(&2, Nat, List.append(&2, Nat, a, b), c), d) : List<&2, Nat>}` | Four-way reassociation for List append over Nat, reversed to rewrite toward the simple side. | next |
| `foldl_op_eq_foldr_op_sym(~B, ~op, ~assoc, ~comm, ~z, ~id, xs)` | `∀ ~B: Data, ~op: B -> B -> B, ~assoc: @x: B -> @y: B -> @z: B -> {op(op(x, y), z) == op(x, op(y, z)) : B}, ~comm: @x: B -> @y: B -> {op(x, y) == op(y, x) : B}, ~z: B, ~id: @x: B -> {op(z, x) == x : B}, +xs: List<&2, B>. {List.foldr(&2, B, B, op, xs, z) == List.foldl(&2, B, B, op, xs, z) : B}` | Folding left equals folding right for an associative, commutative operation with a left identity, reversed to rewrite toward the simple side. | next |

## bool

```python
import bend-mathlib@0.3.0.0/bool.bend as MBool
```

| lemma | statement | meaning | since |
|---|---|---|---|
| `not_not(b)` | `∀ b: Bool. {Bool.not(Bool.not(b)) == b : Bool}` | Negating a boolean twice gives it back. | 0.1.0.0 |
| `and_comm(a, b)` | `∀ a: Bool, b: Bool. {Bool.and(a, b) == Bool.and(b, a) : Bool}` | Boolean and is commutative. | 0.1.0.0 |
| `or_comm(a, b)` | `∀ a: Bool, b: Bool. {Bool.or(a, b) == Bool.or(b, a) : Bool}` | Boolean or is commutative. | 0.1.0.0 |
| `and_assoc(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}` | Boolean and is associative. | 0.1.0.0 |
| `or_assoc(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}` | Boolean or is associative. | 0.1.0.0 |
| `and_true(a)` | `∀ a: Bool. {Bool.and(a, True{}) == a : Bool}` | True is a right identity for and: a and true is a. | 0.1.0.0 |
| `true_and(a)` | `∀ -a: Bool. {Bool.and(True{}, a) == a : Bool}` | True is a left identity for and: true and a is a. | 0.1.0.0 |
| `and_false(a)` | `∀ a: Bool. {Bool.and(a, False{}) == False{} : Bool}` | False absorbs and on the right: a and false is false. | 0.1.0.0 |
| `false_and(a)` | `∀ -a: Bool. {Bool.and(False{}, a) == False{} : Bool}` | False absorbs and on the left: false and a is false. | 0.1.0.0 |
| `or_false(a)` | `∀ a: Bool. {Bool.or(a, False{}) == a : Bool}` | False is a right identity for or: a or false is a. | 0.1.0.0 |
| `false_or(a)` | `∀ -a: Bool. {Bool.or(False{}, a) == a : Bool}` | False is a left identity for or: false or a is a. | 0.1.0.0 |
| `or_true(a)` | `∀ a: Bool. {Bool.or(a, True{}) == True{} : Bool}` | True absorbs or on the right: a or true is true. | 0.1.0.0 |
| `true_or(a)` | `∀ -a: Bool. {Bool.or(True{}, a) == True{} : Bool}` | True absorbs or on the left: true or a is true. | 0.1.0.0 |
| `de_morgan_and(a, b)` | `∀ a: Bool, -b: Bool. {Bool.not(Bool.and(a, b)) == Bool.or(Bool.not(a), Bool.not(b)) : Bool}` | De Morgan: not (a and b) is (not a) or (not b). | 0.1.0.0 |
| `de_morgan_or(a, b)` | `∀ a: Bool, -b: Bool. {Bool.not(Bool.or(a, b)) == Bool.and(Bool.not(a), Bool.not(b)) : Bool}` | De Morgan: not (a or b) is (not a) and (not b). | 0.1.0.0 |
| `true_ne_false()` | `{True{} != False{} : Bool}` | True and False are different booleans. | 0.1.0.0 |
| `and_self(a)` | `∀ a: Bool. {Bool.and(a, a) == a : Bool}` | And with itself: a and a is a. | 0.2.0.0 |
| `or_self(a)` | `∀ a: Bool. {Bool.or(a, a) == a : Bool}` | Or with itself: a or a is a. | 0.2.0.0 |
| `and_not_self(a)` | `∀ a: Bool. {Bool.and(a, Bool.not(a)) == False{} : Bool}` | A boolean and its negation are never both true: a and (not a) is false. | 0.2.0.0 |
| `or_not_self(a)` | `∀ a: Bool. {Bool.or(a, Bool.not(a)) == True{} : Bool}` | A boolean or its negation is always true: a or (not a) is true. | 0.2.0.0 |
| `and_or_distrib_left(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.and(a, Bool.or(b, c)) == Bool.or(Bool.and(a, b), Bool.and(a, c)) : Bool}` | And distributes over or: a and (b or c) is (a and b) or (a and c). | 0.2.0.0 |
| `or_and_distrib_left(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.or(a, Bool.and(b, c)) == Bool.and(Bool.or(a, b), Bool.or(a, c)) : Bool}` | Or distributes over and: a or (b and c) is (a or b) and (a or c). | 0.2.0.0 |
| `and_or_absorb(a, b)` | `∀ a: Bool, -b: Bool. {Bool.and(a, Bool.or(a, b)) == a : Bool}` | Absorption: a and (a or b) is a. | 0.2.0.0 |
| `or_and_absorb(a, b)` | `∀ a: Bool, -b: Bool. {Bool.or(a, Bool.and(a, b)) == a : Bool}` | Absorption: a or (a and b) is a. | 0.2.0.0 |
| `xor_comm(a, b)` | `∀ a: Bool, b: Bool. {Bool.xor(a, b) == Bool.xor(b, a) : Bool}` | Exclusive or is commutative. | 0.2.0.0 |
| `xor_assoc(a, b, c)` | `∀ a: Bool, b: Bool, c: Bool. {Bool.xor(Bool.xor(a, b), c) == Bool.xor(a, Bool.xor(b, c)) : Bool}` | Exclusive or is associative. | 0.2.0.0 |
| `xor_self(a)` | `∀ a: Bool. {Bool.xor(a, a) == False{} : Bool}` | A boolean xor itself is false. | 0.2.0.0 |
| `xor_false(a)` | `∀ a: Bool. {Bool.xor(a, False{}) == a : Bool}` | False is an identity for xor: a xor false is a. | 0.2.0.0 |
| `xor_true(a)` | `∀ a: Bool. {Bool.xor(a, True{}) == Bool.not(a) : Bool}` | Xor with true negates: a xor true is not a. | 0.2.0.0 |
| `not_inj(a, b, h)` | `∀ a: Bool, b: Bool, h: {Bool.not(a) == Bool.not(b) : Bool}. {a == b : Bool}` | Negation is injective: not a = not b implies a = b. | 0.2.0.0 |
| `eq_true_of_ne_false(a, h)` | `∀ a: Bool, h: {a == False{} : Bool} -> Empty. {a == True{} : Bool}` | A boolean that is not false is true. | 0.2.0.0 |
| `cmp_refl(b)` | `∀ b: Bool. {Bool.cmp(b, b) == EQ{} : Cmp}` | Comparing a boolean with itself gives EQ. | next |
| `eq_of_cmp_eq(a, b, h)` | `∀ a: Bool, b: Bool, h: {Cmp.is_eq(Bool.cmp(a, b)) == True{} : Bool}. {a == b : Bool}` | Two booleans that compare EQ are equal. | next |
| `not_not_sym(b)` | `∀ b: Bool. {b == Bool.not(Bool.not(b)) : Bool}` | Negating a boolean twice gives it back, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `and_comm_sym(a, b)` | `∀ a: Bool, b: Bool. {Bool.and(b, a) == Bool.and(a, b) : Bool}` | Boolean and is commutative, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `or_comm_sym(a, b)` | `∀ a: Bool, b: Bool. {Bool.or(b, a) == Bool.or(a, b) : Bool}` | Boolean or is commutative, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `and_assoc_sym(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}` | Boolean and is associative, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `or_assoc_sym(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}` | Boolean or is associative, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `and_true_sym(a)` | `∀ a: Bool. {a == Bool.and(a, True{}) : Bool}` | True is a right identity for and: a and true is a, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `true_and_sym(a)` | `∀ -a: Bool. {a == Bool.and(True{}, a) : Bool}` | True is a left identity for and: true and a is a, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `and_false_sym(a)` | `∀ a: Bool. {False{} == Bool.and(a, False{}) : Bool}` | False absorbs and on the right: a and false is false, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `false_and_sym(a)` | `∀ -a: Bool. {False{} == Bool.and(False{}, a) : Bool}` | False absorbs and on the left: false and a is false, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `or_false_sym(a)` | `∀ a: Bool. {a == Bool.or(a, False{}) : Bool}` | False is a right identity for or: a or false is a, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `false_or_sym(a)` | `∀ -a: Bool. {a == Bool.or(False{}, a) : Bool}` | False is a left identity for or: false or a is a, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `or_true_sym(a)` | `∀ a: Bool. {True{} == Bool.or(a, True{}) : Bool}` | True absorbs or on the right: a or true is true, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `true_or_sym(a)` | `∀ -a: Bool. {True{} == Bool.or(True{}, a) : Bool}` | True absorbs or on the left: true or a is true, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `de_morgan_and_sym(a, b)` | `∀ a: Bool, -b: Bool. {Bool.or(Bool.not(a), Bool.not(b)) == Bool.not(Bool.and(a, b)) : Bool}` | De Morgan: not (a and b) is (not a) or (not b), reversed to rewrite toward the simple side. | 0.1.0.0 |
| `de_morgan_or_sym(a, b)` | `∀ a: Bool, -b: Bool. {Bool.and(Bool.not(a), Bool.not(b)) == Bool.not(Bool.or(a, b)) : Bool}` | De Morgan: not (a or b) is (not a) and (not b), reversed to rewrite toward the simple side. | 0.1.0.0 |
| `and_self_sym(a)` | `∀ a: Bool. {a == Bool.and(a, a) : Bool}` | And with itself: a and a is a, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `or_self_sym(a)` | `∀ a: Bool. {a == Bool.or(a, a) : Bool}` | Or with itself: a or a is a, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `and_not_self_sym(a)` | `∀ a: Bool. {False{} == Bool.and(a, Bool.not(a)) : Bool}` | A boolean and its negation are never both true: a and (not a) is false, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `or_not_self_sym(a)` | `∀ a: Bool. {True{} == Bool.or(a, Bool.not(a)) : Bool}` | A boolean or its negation is always true: a or (not a) is true, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `and_or_distrib_left_sym(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.or(Bool.and(a, b), Bool.and(a, c)) == Bool.and(a, Bool.or(b, c)) : Bool}` | And distributes over or: a and (b or c) is (a and b) or (a and c), reversed to rewrite toward the simple side. | 0.2.0.0 |
| `or_and_distrib_left_sym(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.and(Bool.or(a, b), Bool.or(a, c)) == Bool.or(a, Bool.and(b, c)) : Bool}` | Or distributes over and: a or (b and c) is (a or b) and (a or c), reversed to rewrite toward the simple side. | 0.2.0.0 |
| `and_or_absorb_sym(a, b)` | `∀ a: Bool, -b: Bool. {a == Bool.and(a, Bool.or(a, b)) : Bool}` | Absorption: a and (a or b) is a, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `or_and_absorb_sym(a, b)` | `∀ a: Bool, -b: Bool. {a == Bool.or(a, Bool.and(a, b)) : Bool}` | Absorption: a or (a and b) is a, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `xor_comm_sym(a, b)` | `∀ a: Bool, b: Bool. {Bool.xor(b, a) == Bool.xor(a, b) : Bool}` | Exclusive or is commutative, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `xor_assoc_sym(a, b, c)` | `∀ a: Bool, b: Bool, c: Bool. {Bool.xor(a, Bool.xor(b, c)) == Bool.xor(Bool.xor(a, b), c) : Bool}` | Exclusive or is associative, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `xor_self_sym(a)` | `∀ a: Bool. {False{} == Bool.xor(a, a) : Bool}` | A boolean xor itself is false, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `xor_false_sym(a)` | `∀ a: Bool. {a == Bool.xor(a, False{}) : Bool}` | False is an identity for xor: a xor false is a, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `xor_true_sym(a)` | `∀ a: Bool. {Bool.not(a) == Bool.xor(a, True{}) : Bool}` | Xor with true negates: a xor true is not a, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `cmp_refl_sym(b)` | `∀ b: Bool. {EQ{} == Bool.cmp(b, b) : Cmp}` | Comparing a boolean with itself gives EQ, reversed to rewrite toward the simple side. | next |

## equal

```python
import bend-mathlib@0.3.0.0/equal.bend as MEqual
```

| lemma | statement | meaning | since |
|---|---|---|---|
| `cong2(A, B, C, f, a1, a2, b1, b2, ea, eb)` | `∀ -A: Type, -B: Type, -C: Type, -f: A -> B -> C, -a1: A, -a2: A, -b1: B, -b2: B, ea: {a1 == a2 : A}, eb: {b1 == b2 : B}. {f(a1, b1) == f(a2, b2) : C}` | Applying a two-argument function to equal arguments gives equal results. | 0.1.0.0 |
| `subst(A, P, a, b, e, p)` | `∀ -A: Type, -P: A -> Type, -a: A, -b: A, e: {a == b : A}, p: P(a). P(b)` | If a equals b, any property of a is also a property of b. | 0.1.0.0 |
| `trans3(A, a, b, c, d, ab, bc, cd)` | `∀ -A: Type, -a: A, -b: A, -c: A, -d: A, ab: {a == b : A}, bc: {b == c : A}, cd: {c == d : A}. {a == d : A}` | Equality chains through three steps: a = b, b = c and c = d give a = d. | 0.1.0.0 |
| `cong_succ(a, b, e)` | `∀ -a: Nat, -b: Nat, e: {a == b : Nat}. {1n+a == 1n+b : Nat}` | Equal naturals have equal successors. | 0.1.0.0 |

## list

```python
import bend-mathlib@0.3.0.0/list.bend as MList
```

| predicate | definition | since |
|---|---|---|
| `mem(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Data` | `{List.contains(~A, ~eq, xs, x) == True{} : Bool}` | 0.3.0.0 |
| `sorted_by(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> Data` | `{List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), List.zip(&2, A, &2, A, xs, List.tail(&2, A, xs))) == True{} : Bool}` | 0.3.0.0 |

| lemma | statement | meaning | since |
|---|---|---|---|
| `append_nil(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {List.append(a, A, xs, Nil{}) == xs : List<a, A>}` | The empty list is a right identity for append: xs ++ [] = xs. | 0.1.0.0 |
| `nil_append(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), -xs: List<a, A>. {List.append(a, A, Nil{}, xs) == xs : List<a, A>}` | The empty list is a left identity for append: [] ++ xs = xs. | 0.1.0.0 |
| `append_assoc(a, A, xs, ys, zs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>, -zs: List<a, A>. {List.append(a, A, List.append(a, A, xs, ys), zs) == List.append(a, A, xs, List.append(a, A, ys, zs)) : List<a, A>}` | Append is associative: (xs ++ ys) ++ zs = xs ++ (ys ++ zs). | 0.1.0.0 |
| `length_append(a, A, xs, ys)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>. {List.length(a, A, List.append(a, A, xs, ys)) == Nat.add(List.length(a, A, xs), List.length(a, A, ys)) : Nat}` | The length of an append is the sum of the lengths. | 0.1.0.0 |
| `reverse_go_spec(a, A, xs, acc)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>. {List.reverse.go(a, A, xs, acc) == List.append(a, A, List.reverse(a, A, xs), acc) : List<a, A>}` | The reverse accumulator loop appends the reversed list to the accumulator. | 0.1.0.0 |
| `reverse_append(a, A, xs, ys)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, ys: List<a, A>. {List.reverse(a, A, List.append(a, A, xs, ys)) == List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)) : List<a, A>}` | Reversing an append reverses and swaps the parts: reverse (xs ++ ys) = reverse ys ++ reverse xs. | 0.1.0.0 |
| `reverse_reverse(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {List.reverse(a, A, List.reverse(a, A, xs)) == xs : List<a, A>}` | Reversing twice gives the list back. | 0.1.0.0 |
| `length_reverse(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {List.length(a, A, List.reverse(a, A, xs)) == List.length(a, A, xs) : Nat}` | Reversing preserves the length. | 0.1.0.0 |
| `foldr_append(~a, ~A, ~B, ~f, xs, ys, z)` | `∀ ~a: Quant, ~A: Kind(a), ~B: Type, ~f: A -> B -> B, xs: List<a, A>, -ys: List<a, A>, -z: B. {List.foldr(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) == List.foldr(~a, ~A, ~B, ~f, xs, List.foldr(~a, ~A, ~B, ~f, ys, z)) : B}` | A right fold over an append folds the first part onto the fold of the second. | 0.1.0.0 |
| `take_append_drop(a, A, xs, n)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat. {List.append(a, A, List.take(a, A, xs, n), List.drop(a, A, xs, n)) == xs : List<a, A>}` | Taking n elements and appending the rest after dropping n gives the list back. | 0.1.0.0 |
| `length_map(~A, ~B, ~f, xs)` | `∀ ~A: Type, ~B: Type, ~f: A -> B, xs: List<A>. {List.length(&1, B, List.map(~A, ~B, ~f, xs)) == List.length(&1, A, xs) : Nat}` | Mapping preserves the length. | 0.1.0.0 |
| `map_append(~A, ~B, ~f, xs, ys)` | `∀ ~A: Type, ~B: Type, ~f: A -> B, xs: List<A>, -ys: List<A>. {List.map(~A, ~B, ~f, List.append(&1, A, xs, ys)) == List.append(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, ys)) : List<B>}` | Mapping over an append maps each part: map f (xs ++ ys) = map f xs ++ map f ys. | 0.1.0.0 |
| `map_map(~A, ~B, ~C, ~f, ~g, xs)` | `∀ ~A: Type, ~B: Type, ~C: Type, ~f: A -> B, ~g: B -> C, xs: List<A>. {List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, xs)) == List.map(~A, ~C, ~(x => g(f(x))), xs) : List<C>}` | Mapping twice is mapping the composition: map g (map f xs) = map (g . f) xs. | 0.1.0.0 |
| `take_zero(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {List.take(a, A, xs, 0n) == Nil{} : List<a, A>}` | Taking zero elements gives the empty list. | 0.2.0.0 |
| `drop_zero(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {List.drop(a, A, xs, 0n) == xs : List<a, A>}` | Dropping zero elements gives the list back. | 0.2.0.0 |
| `take_nil(a, A, n)` | `∀ -a: Quant, -A: Kind(a), -n: Nat. {List.take(a, A, Nil{}, n) == Nil{} : List<a, A>}` | Taking from the empty list gives the empty list. | 0.2.0.0 |
| `drop_nil(a, A, n)` | `∀ -a: Quant, -A: Kind(a), -n: Nat. {List.drop(a, A, Nil{}, n) == Nil{} : List<a, A>}` | Dropping from the empty list gives the empty list. | 0.2.0.0 |
| `length_take(a, A, xs, n)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat. {List.length(a, A, List.take(a, A, xs, n)) == Nat.min(n, List.length(a, A, xs)) : Nat}` | Taking n elements leaves min(n, length) of them. | 0.2.0.0 |
| `length_drop(a, A, xs, n)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat. {List.length(a, A, List.drop(a, A, xs, n)) == Nat.sub(List.length(a, A, xs), n) : Nat}` | Dropping n elements leaves length - n of them. | 0.2.0.0 |
| `take_length(A, xs)` | `∀ -A: Data, +xs: List<&2, A>. {List.take(&2, A, xs, List.length(&2, A, xs)) == xs : List<&2, A>}` | Taking as many elements as the list has gives the list back. | 0.2.0.0 |
| `drop_length(A, xs)` | `∀ -A: Data, +xs: List<&2, A>. {List.drop(&2, A, xs, List.length(&2, A, xs)) == Nil{} : List<&2, A>}` | Dropping as many elements as the list has gives the empty list. | 0.2.0.0 |
| `take_take(a, A, xs, n, m)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat, m: Nat. {List.take(a, A, List.take(a, A, xs, n), m) == List.take(a, A, xs, Nat.min(n, m)) : List<a, A>}` | Taking m from the first n is taking min(n, m). | 0.2.0.0 |
| `drop_drop(a, A, xs, n, m)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat, -m: Nat. {List.drop(a, A, List.drop(a, A, xs, n), m) == List.drop(a, A, xs, Nat.add(n, m)) : List<a, A>}` | Dropping m after dropping n is dropping n + m. | 0.2.0.0 |
| `reverse_nil(a, A)` | `∀ -a: Quant, -A: Kind(a). {List.reverse(a, A, Nil{}) == Nil{} : List<a, A>}` | Reversing the empty list gives the empty list. | 0.2.0.0 |
| `reverse_singleton(a, A, x)` | `∀ -a: Quant, -A: Kind(a), -x: A. {List.reverse(a, A, [x]) == [x] : List<a, A>}` | Reversing a one-element list gives it back. | 0.2.0.0 |
| `length_replicate(A, n, x)` | `∀ -A: Data, n: Nat, -x: A. {List.length(&2, A, List.replicate(A, n, x)) == n : Nat}` | Replicating x n times gives a list of length n. | 0.2.0.0 |
| `length_range(n)` | `∀ n: Nat. {List.length(&2, Nat, List.range(n)) == n : Nat}` | Range(n) has length n. | 0.2.0.0 |
| `length_zip(a, A, xs, ys)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, ys: List<a, A>. {List.length(&1, A & A, List.zip(a, A, a, A, xs, ys)) == Nat.min(List.length(a, A, xs), List.length(a, A, ys)) : Nat}` | Zipping two lists gives the length of the shorter one. | 0.2.0.0 |
| `append_cons(a, A, x, xs, ys)` | `∀ -a: Quant, -A: Kind(a), -x: A, -xs: List<a, A>, -ys: List<a, A>. {List.append(a, A, x <> xs, ys) == x <> List.append(a, A, xs, ys) : List<a, A>}` | Appending after a cons: (x :: xs) ++ ys = x :: (xs ++ ys). | 0.2.0.0 |
| `length_nil(a, A)` | `∀ -a: Quant, -A: Kind(a). {List.length(a, A, Nil{}) == 0n : Nat}` | The empty list has length zero. | 0.2.0.0 |
| `length_cons(a, A, x, xs)` | `∀ -a: Quant, -A: Kind(a), -x: A, -xs: List<a, A>. {List.length(a, A, x <> xs) == 1n+List.length(a, A, xs) : Nat}` | A cons is one longer than its tail. | 0.2.0.0 |
| `concat_append(a, A, xss, yss)` | `∀ -a: Quant, -A: Kind(a), xss: List<a, List<a, A>>, -yss: List<a, List<a, A>>. {List.concat(a, A, List.append(a, List<a, A>, xss, yss)) == List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)) : List<a, A>}` | Concatenating an append concatenates each part: concat (xss ++ yss) = concat xss ++ concat yss. | 0.2.0.0 |
| `foldl_append(~a, ~A, ~B, ~f, xs, ys, z)` | `∀ ~a: Quant, ~A: Kind(a), ~B: Type, ~f: B -> A -> B, xs: List<a, A>, -ys: List<a, A>, -z: B. {List.foldl(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) == List.foldl(~a, ~A, ~B, ~f, ys, List.foldl(~a, ~A, ~B, ~f, xs, z)) : B}` | A left fold over an append folds the second part from the fold of the first. | 0.2.0.0 |
| `map_reverse(~A, ~B, ~f, xs)` | `∀ ~A: Type, ~B: Type, ~f: A -> B, xs: List<A>. {List.map(~A, ~B, ~f, List.reverse(&1, A, xs)) == List.reverse(&1, B, List.map(~A, ~B, ~f, xs)) : List<B>}` | Mapping commutes with reversing: map f (reverse xs) = reverse (map f xs). | 0.2.0.0 |
| `all_append(~a, ~A, ~f, xs, ys)` | `∀ ~a: Quant, ~A: Kind(a), ~f: A -> Bool, xs: List<a, A>, -ys: List<a, A>. {List.all(~a, ~A, ~f, List.append(a, A, xs, ys)) == Bool.and(List.all(~a, ~A, ~f, xs), List.all(~a, ~A, ~f, ys)) : Bool}` | All over an append is all over each part, joined by and. | 0.2.0.0 |
| `any_append(~a, ~A, ~f, xs, ys)` | `∀ ~a: Quant, ~A: Kind(a), ~f: A -> Bool, xs: List<a, A>, -ys: List<a, A>. {List.any(~a, ~A, ~f, List.append(a, A, xs, ys)) == Bool.or(List.any(~a, ~A, ~f, xs), List.any(~a, ~A, ~f, ys)) : Bool}` | Any over an append is any over each part, joined by or. | 0.2.0.0 |
| `filter_append(~A, ~f, xs, ys)` | `∀ ~A: Data, ~f: A -> Bool, xs: List<&2, A>, ys: List<&2, A>. {List.filter(~A, ~f, List.append(&2, A, xs, ys)) == List.append(&2, A, List.filter(~A, ~f, xs), List.filter(~A, ~f, ys)) : List<&2, A>}` | Filtering an append filters each part. | 0.2.0.0 |
| `contains_append(~A, ~eq, xs, ys, x)` | `∀ ~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, -ys: List<&2, A>, +x: A. {List.contains(~A, ~eq, List.append(&2, A, xs, ys), x) == Bool.or(List.contains(~A, ~eq, xs, x), List.contains(~A, ~eq, ys, x)) : Bool}` | An append contains x iff either part does. | 0.2.0.0 |
| `length_filter_le(~A, ~f, xs)` | `∀ ~A: Data, ~f: A -> Bool, xs: List<&2, A>. {Nat.is_le(List.length(&2, A, List.filter(~A, ~f, xs)), List.length(&2, A, xs)) == True{} : Bool}` | Filtering never makes a list longer. | 0.2.0.0 |
| `mem_cons_self(x, xs)` | `∀ x: Nat, -xs: List<&2, Nat>. mem(~Nat, ~Nat.is_eq, x, x <> xs)` | The head of a cons is a member of it. | 0.3.0.0 |
| `mem_cons_of_mem(x, y, xs, h)` | `∀ x: Nat, y: Nat, -xs: List<&2, Nat>, h: mem(~Nat, ~Nat.is_eq, x, xs). mem(~Nat, ~Nat.is_eq, x, y <> xs)` | Membership is preserved when a new head is prepended. | 0.3.0.0 |
| `not_mem_nil(x)` | `∀ -x: Nat. mem(~Nat, ~Nat.is_eq, x, Nil{}) -> Empty` | Nothing is a member of the empty list. | 0.3.0.0 |
| `mem_append_left(xs, ys, x, h)` | `∀ xs: List<&2, Nat>, ys: List<&2, Nat>, x: Nat, h: mem(~Nat, ~Nat.is_eq, x, xs). mem(~Nat, ~Nat.is_eq, x, List.append(&2, Nat, xs, ys))` | Membership on the left of an append. | 0.3.0.0 |
| `mem_append_right(xs, ys, x, h)` | `∀ xs: List<&2, Nat>, ys: List<&2, Nat>, x: Nat, h: mem(~Nat, ~Nat.is_eq, x, ys). mem(~Nat, ~Nat.is_eq, x, List.append(&2, Nat, xs, ys))` | Membership on the right of an append. | 0.3.0.0 |
| `sorted_nil()` | `sorted_by(~Nat, ~Nat.is_le, Nil{})` | The empty list is sorted by any comparator. | 0.3.0.0 |
| `sorted_single(x)` | `∀ -x: Nat. sorted_by(~Nat, ~Nat.is_le, [x])` | A singleton list is sorted by any comparator. | 0.3.0.0 |
| `sorted_cons_cons_intro(x, y, t, hxy, hyt)` | `∀ -x: Nat, -y: Nat, -t: List<&2, Nat>, hxy: MNat.le(x, y), hyt: sorted_by(~Nat, ~Nat.is_le, y <> t). sorted_by(~Nat, ~Nat.is_le, x <> y <> t)` | A sorted tail with an in-order head is sorted. | 0.3.0.0 |
| `sorted_cons_cons_elim_le(x, y, t, h)` | `∀ x: Nat, y: Nat, -t: List<&2, Nat>, h: sorted_by(~Nat, ~Nat.is_le, x <> y <> t). MNat.le(x, y)` | The head pair of a sorted cons-cons list is in order. | 0.3.0.0 |
| `sorted_cons_cons_elim_tail(x, y, t, h)` | `∀ x: Nat, y: Nat, -t: List<&2, Nat>, h: sorted_by(~Nat, ~Nat.is_le, x <> y <> t). sorted_by(~Nat, ~Nat.is_le, y <> t)` | The tail of a sorted cons-cons list is sorted. | 0.3.0.0 |
| `sorted_tail(x, xs, h)` | `∀ x: Nat, xs: List<&2, Nat>, h: sorted_by(~Nat, ~Nat.is_le, x <> xs). sorted_by(~Nat, ~Nat.is_le, xs)` | A sorted list has a sorted tail. | 0.3.0.0 |
| `append_nil_sym(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {xs == List.append(a, A, xs, Nil{}) : List<a, A>}` | The empty list is a right identity for append: xs ++ [] = xs, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `nil_append_sym(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), -xs: List<a, A>. {xs == List.append(a, A, Nil{}, xs) : List<a, A>}` | The empty list is a left identity for append: [] ++ xs = xs, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `append_assoc_sym(a, A, xs, ys, zs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>, -zs: List<a, A>. {List.append(a, A, xs, List.append(a, A, ys, zs)) == List.append(a, A, List.append(a, A, xs, ys), zs) : List<a, A>}` | Append is associative: (xs ++ ys) ++ zs = xs ++ (ys ++ zs), reversed to rewrite toward the simple side. | 0.1.0.0 |
| `length_append_sym(a, A, xs, ys)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>. {Nat.add(List.length(a, A, xs), List.length(a, A, ys)) == List.length(a, A, List.append(a, A, xs, ys)) : Nat}` | The length of an append is the sum of the lengths, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `reverse_go_spec_sym(a, A, xs, acc)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>. {List.append(a, A, List.reverse(a, A, xs), acc) == List.reverse.go(a, A, xs, acc) : List<a, A>}` | The reverse accumulator loop appends the reversed list to the accumulator, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `reverse_append_sym(a, A, xs, ys)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, ys: List<a, A>. {List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)) == List.reverse(a, A, List.append(a, A, xs, ys)) : List<a, A>}` | Reversing an append reverses and swaps the parts: reverse (xs ++ ys) = reverse ys ++ reverse xs, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `reverse_reverse_sym(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {xs == List.reverse(a, A, List.reverse(a, A, xs)) : List<a, A>}` | Reversing twice gives the list back, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `length_reverse_sym(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {List.length(a, A, xs) == List.length(a, A, List.reverse(a, A, xs)) : Nat}` | Reversing preserves the length, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `foldr_append_sym(~a, ~A, ~B, ~f, xs, ys, z)` | `∀ ~a: Quant, ~A: Kind(a), ~B: Type, ~f: A -> B -> B, xs: List<a, A>, -ys: List<a, A>, -z: B. {List.foldr(~a, ~A, ~B, ~f, xs, List.foldr(~a, ~A, ~B, ~f, ys, z)) == List.foldr(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) : B}` | A right fold over an append folds the first part onto the fold of the second, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `take_append_drop_sym(a, A, xs, n)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat. {xs == List.append(a, A, List.take(a, A, xs, n), List.drop(a, A, xs, n)) : List<a, A>}` | Taking n elements and appending the rest after dropping n gives the list back, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `length_map_sym(~A, ~B, ~f, xs)` | `∀ ~A: Type, ~B: Type, ~f: A -> B, xs: List<A>. {List.length(&1, A, xs) == List.length(&1, B, List.map(~A, ~B, ~f, xs)) : Nat}` | Mapping preserves the length, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `map_append_sym(~A, ~B, ~f, xs, ys)` | `∀ ~A: Type, ~B: Type, ~f: A -> B, xs: List<A>, -ys: List<A>. {List.append(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, ys)) == List.map(~A, ~B, ~f, List.append(&1, A, xs, ys)) : List<B>}` | Mapping over an append maps each part: map f (xs ++ ys) = map f xs ++ map f ys, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `map_map_sym(~A, ~B, ~C, ~f, ~g, xs)` | `∀ ~A: Type, ~B: Type, ~C: Type, ~f: A -> B, ~g: B -> C, xs: List<A>. {List.map(~A, ~C, ~(x => g(f(x))), xs) == List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, xs)) : List<C>}` | Mapping twice is mapping the composition: map g (map f xs) = map (g . f) xs, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `take_zero_sym(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {Nil{} == List.take(a, A, xs, 0n) : List<a, A>}` | Taking zero elements gives the empty list, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `drop_zero_sym(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {xs == List.drop(a, A, xs, 0n) : List<a, A>}` | Dropping zero elements gives the list back, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `take_nil_sym(a, A, n)` | `∀ -a: Quant, -A: Kind(a), -n: Nat. {Nil{} == List.take(a, A, Nil{}, n) : List<a, A>}` | Taking from the empty list gives the empty list, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `drop_nil_sym(a, A, n)` | `∀ -a: Quant, -A: Kind(a), -n: Nat. {Nil{} == List.drop(a, A, Nil{}, n) : List<a, A>}` | Dropping from the empty list gives the empty list, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `length_take_sym(a, A, xs, n)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat. {Nat.min(n, List.length(a, A, xs)) == List.length(a, A, List.take(a, A, xs, n)) : Nat}` | Taking n elements leaves min(n, length) of them, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `length_drop_sym(a, A, xs, n)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat. {Nat.sub(List.length(a, A, xs), n) == List.length(a, A, List.drop(a, A, xs, n)) : Nat}` | Dropping n elements leaves length - n of them, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `take_length_sym(A, xs)` | `∀ -A: Data, +xs: List<&2, A>. {xs == List.take(&2, A, xs, List.length(&2, A, xs)) : List<&2, A>}` | Taking as many elements as the list has gives the list back, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `drop_length_sym(A, xs)` | `∀ -A: Data, +xs: List<&2, A>. {Nil{} == List.drop(&2, A, xs, List.length(&2, A, xs)) : List<&2, A>}` | Dropping as many elements as the list has gives the empty list, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `take_take_sym(a, A, xs, n, m)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat, m: Nat. {List.take(a, A, xs, Nat.min(n, m)) == List.take(a, A, List.take(a, A, xs, n), m) : List<a, A>}` | Taking m from the first n is taking min(n, m), reversed to rewrite toward the simple side. | 0.2.0.0 |
| `drop_drop_sym(a, A, xs, n, m)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat, -m: Nat. {List.drop(a, A, xs, Nat.add(n, m)) == List.drop(a, A, List.drop(a, A, xs, n), m) : List<a, A>}` | Dropping m after dropping n is dropping n + m, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `reverse_nil_sym(a, A)` | `∀ -a: Quant, -A: Kind(a). {Nil{} == List.reverse(a, A, Nil{}) : List<a, A>}` | Reversing the empty list gives the empty list, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `reverse_singleton_sym(a, A, x)` | `∀ -a: Quant, -A: Kind(a), -x: A. {[x] == List.reverse(a, A, [x]) : List<a, A>}` | Reversing a one-element list gives it back, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `length_replicate_sym(A, n, x)` | `∀ -A: Data, n: Nat, -x: A. {n == List.length(&2, A, List.replicate(A, n, x)) : Nat}` | Replicating x n times gives a list of length n, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `length_range_sym(n)` | `∀ n: Nat. {n == List.length(&2, Nat, List.range(n)) : Nat}` | Range(n) has length n, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `length_zip_sym(a, A, xs, ys)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, ys: List<a, A>. {Nat.min(List.length(a, A, xs), List.length(a, A, ys)) == List.length(&1, A & A, List.zip(a, A, a, A, xs, ys)) : Nat}` | Zipping two lists gives the length of the shorter one, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `append_cons_sym(a, A, x, xs, ys)` | `∀ -a: Quant, -A: Kind(a), -x: A, -xs: List<a, A>, -ys: List<a, A>. {x <> List.append(a, A, xs, ys) == List.append(a, A, x <> xs, ys) : List<a, A>}` | Appending after a cons: (x :: xs) ++ ys = x :: (xs ++ ys), reversed to rewrite toward the simple side. | 0.2.0.0 |
| `length_nil_sym(a, A)` | `∀ -a: Quant, -A: Kind(a). {0n == List.length(a, A, Nil{}) : Nat}` | The empty list has length zero, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `length_cons_sym(a, A, x, xs)` | `∀ -a: Quant, -A: Kind(a), -x: A, -xs: List<a, A>. {1n+List.length(a, A, xs) == List.length(a, A, x <> xs) : Nat}` | A cons is one longer than its tail, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `concat_append_sym(a, A, xss, yss)` | `∀ -a: Quant, -A: Kind(a), xss: List<a, List<a, A>>, -yss: List<a, List<a, A>>. {List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)) == List.concat(a, A, List.append(a, List<a, A>, xss, yss)) : List<a, A>}` | Concatenating an append concatenates each part: concat (xss ++ yss) = concat xss ++ concat yss, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `foldl_append_sym(~a, ~A, ~B, ~f, xs, ys, z)` | `∀ ~a: Quant, ~A: Kind(a), ~B: Type, ~f: B -> A -> B, xs: List<a, A>, -ys: List<a, A>, -z: B. {List.foldl(~a, ~A, ~B, ~f, ys, List.foldl(~a, ~A, ~B, ~f, xs, z)) == List.foldl(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) : B}` | A left fold over an append folds the second part from the fold of the first, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `map_reverse_sym(~A, ~B, ~f, xs)` | `∀ ~A: Type, ~B: Type, ~f: A -> B, xs: List<A>. {List.reverse(&1, B, List.map(~A, ~B, ~f, xs)) == List.map(~A, ~B, ~f, List.reverse(&1, A, xs)) : List<B>}` | Mapping commutes with reversing: map f (reverse xs) = reverse (map f xs), reversed to rewrite toward the simple side. | 0.2.0.0 |
| `all_append_sym(~a, ~A, ~f, xs, ys)` | `∀ ~a: Quant, ~A: Kind(a), ~f: A -> Bool, xs: List<a, A>, -ys: List<a, A>. {Bool.and(List.all(~a, ~A, ~f, xs), List.all(~a, ~A, ~f, ys)) == List.all(~a, ~A, ~f, List.append(a, A, xs, ys)) : Bool}` | All over an append is all over each part, joined by and, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `any_append_sym(~a, ~A, ~f, xs, ys)` | `∀ ~a: Quant, ~A: Kind(a), ~f: A -> Bool, xs: List<a, A>, -ys: List<a, A>. {Bool.or(List.any(~a, ~A, ~f, xs), List.any(~a, ~A, ~f, ys)) == List.any(~a, ~A, ~f, List.append(a, A, xs, ys)) : Bool}` | Any over an append is any over each part, joined by or, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `filter_append_sym(~A, ~f, xs, ys)` | `∀ ~A: Data, ~f: A -> Bool, xs: List<&2, A>, ys: List<&2, A>. {List.append(&2, A, List.filter(~A, ~f, xs), List.filter(~A, ~f, ys)) == List.filter(~A, ~f, List.append(&2, A, xs, ys)) : List<&2, A>}` | Filtering an append filters each part, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `contains_append_sym(~A, ~eq, xs, ys, x)` | `∀ ~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, -ys: List<&2, A>, +x: A. {Bool.or(List.contains(~A, ~eq, xs, x), List.contains(~A, ~eq, ys, x)) == List.contains(~A, ~eq, List.append(&2, A, xs, ys), x) : Bool}` | An append contains x iff either part does, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `length_filter_le_sym(~A, ~f, xs)` | `∀ ~A: Data, ~f: A -> Bool, xs: List<&2, A>. {True{} == Nat.is_le(List.length(&2, A, List.filter(~A, ~f, xs)), List.length(&2, A, xs)) : Bool}` | Filtering never makes a list longer, reversed to rewrite toward the simple side. | 0.2.0.0 |

## maybe

```python
import bend-mathlib@0.3.0.0/maybe.bend as MMaybe
```

| lemma | statement | meaning | since |
|---|---|---|---|
| `maybe_pure_bind(~A, ~B, f, x)` | `∀ ~A: Data, ~B: Data, -f: A -> Maybe<&2, B>, -x: A. {Maybe.bind(&2, A, B, Maybe.pure(&2, A, x), f) == f(x) : Maybe<&2, B>}` | Left identity: binding a pure value applies the function. | next |
| `maybe_bind_pure(~A, m)` | `∀ ~A: Data, m: Maybe<&2, A>. {Maybe.bind(&2, A, A, m, x => Maybe.pure(&2, A, x)) == m : Maybe<&2, A>}` | Right identity: binding pure is the identity. | next |
| `maybe_bind_assoc(~A, ~B, ~C, f, g, m)` | `∀ ~A: Data, ~B: Data, ~C: Data, -f: A -> Maybe<&2, B>, -g: B -> Maybe<&2, C>, m: Maybe<&2, A>. {Maybe.bind(&2, B, C, Maybe.bind(&2, A, B, m, f), g) == Maybe.bind(&2, A, C, m, x => Maybe.bind(&2, B, C, f(x), g)) : Maybe<&2, C>}` | Bind is associative. | next |
| `maybe_map_pure(~A, ~B, f, x)` | `∀ ~A: Data, ~B: Data, -f: A -> B, -x: A. {Maybe.map(&2, A, B, f, Maybe.pure(&2, A, x)) == Maybe.pure(&2, B, f(x)) : Maybe<&2, B>}` | Mapping a pure value is pure of the mapped value. | next |
| `maybe_map_compose(~A, ~B, ~C, f, g, m)` | `∀ ~A: Data, ~B: Data, ~C: Data, -f: A -> B, -g: B -> C, m: Maybe<&2, A>. {Maybe.map(&2, B, C, g, Maybe.map(&2, A, B, f, m)) == Maybe.map(&2, A, C, x => g(f(x)), m) : Maybe<&2, C>}` | Mapping a composition maps the composition. | next |
| `maybe_pure_bind_sym(~A, ~B, f, x)` | `∀ ~A: Data, ~B: Data, -f: A -> Maybe<&2, B>, -x: A. {f(x) == Maybe.bind(&2, A, B, Maybe.pure(&2, A, x), f) : Maybe<&2, B>}` | Left identity: binding a pure value applies the function, reversed to rewrite toward the simple side. | next |
| `maybe_bind_pure_sym(~A, m)` | `∀ ~A: Data, m: Maybe<&2, A>. {m == Maybe.bind(&2, A, A, m, x => Maybe.pure(&2, A, x)) : Maybe<&2, A>}` | Right identity: binding pure is the identity, reversed to rewrite toward the simple side. | next |
| `maybe_bind_assoc_sym(~A, ~B, ~C, f, g, m)` | `∀ ~A: Data, ~B: Data, ~C: Data, -f: A -> Maybe<&2, B>, -g: B -> Maybe<&2, C>, m: Maybe<&2, A>. {Maybe.bind(&2, A, C, m, x => Maybe.bind(&2, B, C, f(x), g)) == Maybe.bind(&2, B, C, Maybe.bind(&2, A, B, m, f), g) : Maybe<&2, C>}` | Bind is associative, reversed to rewrite toward the simple side. | next |
| `maybe_map_pure_sym(~A, ~B, f, x)` | `∀ ~A: Data, ~B: Data, -f: A -> B, -x: A. {Maybe.pure(&2, B, f(x)) == Maybe.map(&2, A, B, f, Maybe.pure(&2, A, x)) : Maybe<&2, B>}` | Mapping a pure value is pure of the mapped value, reversed to rewrite toward the simple side. | next |
| `maybe_map_compose_sym(~A, ~B, ~C, f, g, m)` | `∀ ~A: Data, ~B: Data, ~C: Data, -f: A -> B, -g: B -> C, m: Maybe<&2, A>. {Maybe.map(&2, A, C, x => g(f(x)), m) == Maybe.map(&2, B, C, g, Maybe.map(&2, A, B, f, m)) : Maybe<&2, C>}` | Mapping a composition maps the composition, reversed to rewrite toward the simple side. | next |

## nat

```python
import bend-mathlib@0.3.0.0/nat.bend as MNat
```

| predicate | definition | since |
|---|---|---|
| `le(a: Nat, b: Nat) -> Data` | `{Nat.is_le(a, b) == True{} : Bool}` | 0.1.0.0 |
| `lt(a: Nat, b: Nat) -> Data` | `{Nat.is_lt(a, b) == True{} : Bool}` | 0.1.0.0 |
| `ge(a: Nat, b: Nat) -> Data` | `{Nat.is_ge(a, b) == True{} : Bool}` | 0.1.0.0 |
| `gt(a: Nat, b: Nat) -> Data` | `{Nat.is_gt(a, b) == True{} : Bool}` | 0.1.0.0 |

| lemma | statement | meaning | since |
|---|---|---|---|
| `add_zero(x)` | `∀ x: Nat. {Nat.add(x, 0n) == x : Nat}` | Zero is a right identity for addition: x + 0 = x. | 0.1.0.0 |
| `zero_add(x)` | `∀ -x: Nat. {Nat.add(0n, x) == x : Nat}` | Zero is a left identity for addition: 0 + x = x. | 0.1.0.0 |
| `add_succ(n, m)` | `∀ n: Nat, -m: Nat. {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}` | Adding a successor on the right: n + (m + 1) = (n + m) + 1. | 0.1.0.0 |
| `succ_add(n, m)` | `∀ -n: Nat, -m: Nat. {Nat.add(1n+n, m) == 1n+Nat.add(n, m) : Nat}` | Adding a successor on the left: (n + 1) + m = (n + m) + 1. | 0.1.0.0 |
| `add_comm(n, m)` | `∀ n: Nat, m: Nat. {Nat.add(n, m) == Nat.add(m, n) : Nat}` | Addition is commutative: n + m = m + n. | 0.1.0.0 |
| `add_assoc(a, b, c)` | `∀ a: Nat, -b: Nat, -c: Nat. {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}` | Addition is associative: (a + b) + c = a + (b + c). | 0.1.0.0 |
| `add_left_comm(a, b, c)` | `∀ a: Nat, b: Nat, -c: Nat. {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}` | Left commutativity of addition: a + (b + c) = b + (a + c). | 0.1.0.0 |
| `add_right_comm(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}` | Right commutativity of addition: (a + b) + c = (a + c) + b. | 0.1.0.0 |
| `add_add_add_comm(a, b, c, d)` | `∀ a: Nat, b: Nat, c: Nat, -d: Nat. {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}` | Four-way regrouping of a sum: (a + b) + (c + d) = (a + c) + (b + d). | 0.1.0.0 |
| `succ_inj(a, b, e)` | `∀ -a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}. {a == b : Nat}` | The successor function is injective: a + 1 = b + 1 implies a = b. | 0.1.0.0 |
| `zero_ne_succ(n)` | `∀ -n: Nat. {0n != 1n+n : Nat}` | Zero is not a successor. | 0.1.0.0 |
| `succ_ne_zero(n)` | `∀ -n: Nat. {1n+n != 0n : Nat}` | A successor is not zero. | 0.1.0.0 |
| `add_left_cancel(a, b, c, e)` | `∀ a: Nat, -b: Nat, -c: Nat, e: {Nat.add(a, b) == Nat.add(a, c) : Nat}. {b == c : Nat}` | Addition cancels on the left: a + b = a + c implies b = c. | 0.1.0.0 |
| `add_right_cancel(a, b, c, e)` | `∀ a: Nat, b: Nat, c: Nat, e: {Nat.add(a, b) == Nat.add(c, b) : Nat}. {a == c : Nat}` | Addition cancels on the right: a + b = c + b implies a = c. | 0.1.0.0 |
| `mul_zero(x)` | `∀ x: Nat. {Nat.mul(x, 0n) == 0n : Nat}` | Zero absorbs multiplication on the right: x * 0 = 0. | 0.1.0.0 |
| `zero_mul(x)` | `∀ -x: Nat. {Nat.mul(0n, x) == 0n : Nat}` | Zero absorbs multiplication on the left: 0 * x = 0. | 0.1.0.0 |
| `mul_one(x)` | `∀ x: Nat. {Nat.mul(x, 1n) == x : Nat}` | One is a right identity for multiplication: x * 1 = x. | 0.1.0.0 |
| `one_mul(x)` | `∀ x: Nat. {Nat.mul(1n, x) == x : Nat}` | One is a left identity for multiplication: 1 * x = x. | 0.1.0.0 |
| `mul_succ(n, m)` | `∀ n: Nat, m: Nat. {Nat.mul(n, 1n+m) == Nat.add(Nat.mul(n, m), n) : Nat}` | Multiplying by a successor on the right: n * (m + 1) = n * m + n. | 0.1.0.0 |
| `succ_mul(n, m)` | `∀ n: Nat, m: Nat. {Nat.mul(1n+n, m) == Nat.add(Nat.mul(n, m), m) : Nat}` | Multiplying by a successor on the left: (n + 1) * m = n * m + m. | 0.1.0.0 |
| `mul_comm(n, m)` | `∀ n: Nat, m: Nat. {Nat.mul(n, m) == Nat.mul(m, n) : Nat}` | Multiplication is commutative: n * m = m * n. | 0.1.0.0 |
| `add_mul(a, b, c)` | `∀ a: Nat, -b: Nat, c: Nat. {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}` | Multiplication distributes over addition on the right: (a + b) * c = a * c + b * c. | 0.1.0.0 |
| `mul_add(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}` | Multiplication distributes over addition on the left: a * (b + c) = a * b + a * c. | 0.1.0.0 |
| `mul_assoc(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}` | Multiplication is associative: (a * b) * c = a * (b * c). | 0.1.0.0 |
| `le_refl(a)` | `∀ a: Nat. le(a, a)` | Every natural is at most itself: a <= a. | 0.1.0.0 |
| `zero_le(b)` | `∀ b: Nat. le(0n, b)` | Zero is at most every natural: 0 <= b. | 0.1.0.0 |
| `le_succ(n)` | `∀ n: Nat. le(n, 1n+n)` | Every natural is at most its successor: n <= n + 1. | 0.1.0.0 |
| `le_add_right(n, k)` | `∀ n: Nat, k: Nat. le(n, Nat.add(n, k))` | Adding on the right never decreases a natural: n <= n + k. | 0.1.0.0 |
| `le_trans(a, b, c, ab, bc)` | `∀ a: Nat, b: Nat, c: Nat, ab: le(a, b), bc: le(b, c). le(a, c)` | The order is transitive: a <= b and b <= c imply a <= c. | 0.1.0.0 |
| `le_antisymm(a, b, ab, ba)` | `∀ a: Nat, b: Nat, ab: le(a, b), ba: le(b, a). {a == b : Nat}` | The order is antisymmetric: a <= b and b <= a imply a = b. | 0.1.0.0 |
| `le_total(a, b)` | `∀ a: Nat, b: Nat. Or(le(a, b), le(b, a))` | The order is total: a <= b or b <= a. | 0.1.0.0 |
| `le_total_d(a, b)` | `∀ a: Nat, b: Nat. Either<&2, &2, le(a, b), le(b, a)>` | The order is total, as a reusable sum: a <= b or b <= a. | 0.1.0.0 |
| `lt_irrefl(a)` | `∀ a: Nat. lt(a, a) -> Empty` | No natural is less than itself. | 0.1.0.0 |
| `lt_trans(a, b, c, ab, bc)` | `∀ a: Nat, b: Nat, c: Nat, ab: lt(a, b), bc: lt(b, c). lt(a, c)` | The strict order is transitive: a < b and b < c imply a < c. | 0.1.0.0 |
| `le_of_lt(a, b, h)` | `∀ a: Nat, b: Nat, h: lt(a, b). le(a, b)` | A strict inequality implies the weak one: a < b implies a <= b. | 0.1.0.0 |
| `le_of_ge(a, b, h)` | `∀ a: Nat, b: Nat, h: ge(a, b). le(b, a)` | Flipping a >= b gives b <= a. | 0.1.0.0 |
| `ge_of_le(a, b, h)` | `∀ a: Nat, b: Nat, h: le(b, a). ge(a, b)` | Flipping b <= a gives a >= b. | 0.1.0.0 |
| `lt_of_gt(a, b, h)` | `∀ a: Nat, b: Nat, h: gt(a, b). lt(b, a)` | Flipping a > b gives b < a. | 0.1.0.0 |
| `gt_of_lt(a, b, h)` | `∀ a: Nat, b: Nat, h: lt(b, a). gt(a, b)` | Flipping b < a gives a > b. | 0.1.0.0 |
| `sub_zero(n)` | `∀ n: Nat. {Nat.sub(n, 0n) == n : Nat}` | Subtracting zero changes nothing: n - 0 = n. | 0.2.0.0 |
| `zero_sub(n)` | `∀ n: Nat. {Nat.sub(0n, n) == 0n : Nat}` | Truncated subtraction from zero is zero: 0 - n = 0. | 0.2.0.0 |
| `sub_self(n)` | `∀ n: Nat. {Nat.sub(n, n) == 0n : Nat}` | A natural minus itself is zero: n - n = 0. | 0.2.0.0 |
| `succ_sub_succ(n, m)` | `∀ -n: Nat, -m: Nat. {Nat.sub(1n+n, 1n+m) == Nat.sub(n, m) : Nat}` | Subtracting successors: (n + 1) - (m + 1) = n - m. | 0.2.0.0 |
| `add_sub_cancel(n, m)` | `∀ n: Nat, m: Nat. {Nat.sub(Nat.add(n, m), m) == n : Nat}` | Adding then subtracting m cancels: (n + m) - m = n. | 0.2.0.0 |
| `add_sub_cancel_left(n, m)` | `∀ n: Nat, m: Nat. {Nat.sub(Nat.add(n, m), n) == m : Nat}` | Adding then subtracting n cancels: (n + m) - n = m. | 0.2.0.0 |
| `sub_add_cancel(n, m, h)` | `∀ n: Nat, m: Nat, h: le(m, n). {Nat.add(Nat.sub(n, m), m) == n : Nat}` | If m <= n, subtracting and adding m back gives n: (n - m) + m = n. | 0.2.0.0 |
| `sub_sub(n, m, k)` | `∀ n: Nat, m: Nat, k: Nat. {Nat.sub(Nat.sub(n, m), k) == Nat.sub(n, Nat.add(m, k)) : Nat}` | Subtracting twice is subtracting the sum: (n - m) - k = n - (m + k). | 0.2.0.0 |
| `sub_le(n, m)` | `∀ n: Nat, m: Nat. le(Nat.sub(n, m), n)` | Truncated subtraction never increases: n - m <= n. | 0.2.0.0 |
| `min_comm(a, b)` | `∀ a: Nat, b: Nat. {Nat.min(a, b) == Nat.min(b, a) : Nat}` | Minimum is commutative. | 0.2.0.0 |
| `max_comm(a, b)` | `∀ a: Nat, b: Nat. {Nat.max(a, b) == Nat.max(b, a) : Nat}` | Maximum is commutative. | 0.2.0.0 |
| `min_self(a)` | `∀ a: Nat. {Nat.min(a, a) == a : Nat}` | The minimum of a natural and itself is itself. | 0.2.0.0 |
| `max_self(a)` | `∀ a: Nat. {Nat.max(a, a) == a : Nat}` | The maximum of a natural and itself is itself. | 0.2.0.0 |
| `min_zero(a)` | `∀ a: Nat. {Nat.min(a, 0n) == 0n : Nat}` | The minimum with zero is zero: min(a, 0) = 0. | 0.2.0.0 |
| `zero_min(a)` | `∀ a: Nat. {Nat.min(0n, a) == 0n : Nat}` | The minimum with zero is zero: min(0, a) = 0. | 0.2.0.0 |
| `max_zero(a)` | `∀ a: Nat. {Nat.max(a, 0n) == a : Nat}` | Zero is an identity for maximum: max(a, 0) = a. | 0.2.0.0 |
| `zero_max(a)` | `∀ a: Nat. {Nat.max(0n, a) == a : Nat}` | Zero is an identity for maximum: max(0, a) = a. | 0.2.0.0 |
| `min_assoc(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.min(Nat.min(a, b), c) == Nat.min(a, Nat.min(b, c)) : Nat}` | Minimum is associative. | 0.2.0.0 |
| `max_assoc(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.max(Nat.max(a, b), c) == Nat.max(a, Nat.max(b, c)) : Nat}` | Maximum is associative. | 0.2.0.0 |
| `min_add_max(a, b)` | `∀ a: Nat, b: Nat. {Nat.add(Nat.min(a, b), Nat.max(a, b)) == Nat.add(a, b) : Nat}` | The minimum plus the maximum is the sum: min(a, b) + max(a, b) = a + b. | 0.2.0.0 |
| `min_le_left(a, b)` | `∀ a: Nat, b: Nat. le(Nat.min(a, b), a)` | The minimum is at most its left argument. | 0.2.0.0 |
| `min_le_right(a, b)` | `∀ a: Nat, b: Nat. le(Nat.min(a, b), b)` | The minimum is at most its right argument. | 0.2.0.0 |
| `le_max_left(a, b)` | `∀ a: Nat, b: Nat. le(a, Nat.max(a, b))` | The left argument is at most the maximum. | 0.2.0.0 |
| `le_max_right(a, b)` | `∀ a: Nat, b: Nat. le(b, Nat.max(a, b))` | The right argument is at most the maximum. | 0.2.0.0 |
| `pow_zero(a)` | `∀ -a: Nat. {Nat.pow(a, 0n) == 1n : Nat}` | Any natural to the power zero is one. | 0.2.0.0 |
| `pow_succ(a, n)` | `∀ -a: Nat, -n: Nat. {Nat.pow(a, 1n+n) == Nat.mul(a, Nat.pow(a, n)) : Nat}` | A power with a successor exponent: a^(n+1) = a * a^n. | 0.2.0.0 |
| `pow_one(a)` | `∀ a: Nat. {Nat.pow(a, 1n) == a : Nat}` | Any natural to the power one is itself. | 0.2.0.0 |
| `one_pow(n)` | `∀ n: Nat. {Nat.pow(1n, n) == 1n : Nat}` | One to any power is one. | 0.2.0.0 |
| `pow_add(a, m, n)` | `∀ a: Nat, m: Nat, n: Nat. {Nat.pow(a, Nat.add(m, n)) == Nat.mul(Nat.pow(a, m), Nat.pow(a, n)) : Nat}` | Exponents add under multiplication: a^(m+n) = a^m * a^n. | 0.2.0.0 |
| `double_eq_add(n)` | `∀ n: Nat. {Nat.double(n) == Nat.add(n, n) : Nat}` | Doubling is adding a natural to itself. | 0.2.0.0 |
| `is_eq_refl(n)` | `∀ n: Nat. {Nat.is_eq(n, n) == True{} : Bool}` | Every natural tests equal to itself. | 0.2.0.0 |
| `is_eq_comm(a, b)` | `∀ a: Nat, b: Nat. {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}` | The equality test is symmetric. | 0.2.0.0 |
| `eq_of_is_eq(a, b, h)` | `∀ a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}. {a == b : Nat}` | If the equality test says true, the naturals are equal. | 0.2.0.0 |
| `is_ge_eq_is_le(a, b)` | `∀ a: Nat, b: Nat. {Nat.is_ge(a, b) == Nat.is_le(b, a) : Bool}` | A >= b tests the same as b <= a. | 0.2.0.0 |
| `is_gt_eq_is_lt(a, b)` | `∀ a: Nat, b: Nat. {Nat.is_gt(a, b) == Nat.is_lt(b, a) : Bool}` | A > b tests the same as b < a. | 0.2.0.0 |
| `is_lt_eq_succ_le(a, b)` | `∀ a: Nat, b: Nat. {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}` | A < b tests the same as a + 1 <= b. | 0.2.0.0 |
| `not_is_le(a, b)` | `∀ a: Nat, b: Nat. {Bool.not(Nat.is_le(a, b)) == Nat.is_lt(b, a) : Bool}` | Not (a <= b) tests the same as b < a. | 0.2.0.0 |
| `not_is_lt(a, b)` | `∀ a: Nat, b: Nat. {Bool.not(Nat.is_lt(a, b)) == Nat.is_le(b, a) : Bool}` | Not (a < b) tests the same as b <= a. | 0.2.0.0 |
| `lt_succ_self(n)` | `∀ n: Nat. lt(n, 1n+n)` | Every natural is less than its successor: n < n + 1. | 0.2.0.0 |
| `succ_le_succ(a, b, h)` | `∀ -a: Nat, -b: Nat, h: le(a, b). le(1n+a, 1n+b)` | The successor preserves the order: a <= b implies a + 1 <= b + 1. | 0.2.0.0 |
| `le_of_succ_le_succ(a, b, h)` | `∀ -a: Nat, -b: Nat, h: le(1n+a, 1n+b). le(a, b)` | The order of successors is the order of the naturals: a + 1 <= b + 1 implies a <= b. | 0.2.0.0 |
| `lt_of_lt_of_le(a, b, c, ab, bc)` | `∀ a: Nat, b: Nat, c: Nat, ab: lt(a, b), bc: le(b, c). lt(a, c)` | A < b and b <= c imply a < c. | 0.2.0.0 |
| `lt_of_le_of_lt(a, b, c, ab, bc)` | `∀ a: Nat, b: Nat, c: Nat, ab: le(a, b), bc: lt(b, c). lt(a, c)` | A <= b and b < c imply a < c. | 0.2.0.0 |
| `add_le_add_left(a, b, k, h)` | `∀ -a: Nat, -b: Nat, k: Nat, h: le(a, b). le(Nat.add(k, a), Nat.add(k, b))` | Adding on the left preserves the order: a <= b implies k + a <= k + b. | 0.2.0.0 |
| `le_zero_eq(n, h)` | `∀ n: Nat, h: le(n, 0n). {n == 0n : Nat}` | The only natural at most zero is zero. | 0.2.0.0 |
| `lt_zero(n)` | `∀ n: Nat. lt(n, 0n) -> Empty` | No natural is less than zero. | 0.2.0.0 |
| `add_zero_sym(x)` | `∀ x: Nat. {x == Nat.add(x, 0n) : Nat}` | Zero is a right identity for addition: x + 0 = x, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `zero_add_sym(x)` | `∀ -x: Nat. {x == Nat.add(0n, x) : Nat}` | Zero is a left identity for addition: 0 + x = x, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `add_succ_sym(n, m)` | `∀ n: Nat, -m: Nat. {1n+Nat.add(n, m) == Nat.add(n, 1n+m) : Nat}` | Adding a successor on the right: n + (m + 1) = (n + m) + 1, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `succ_add_sym(n, m)` | `∀ -n: Nat, -m: Nat. {1n+Nat.add(n, m) == Nat.add(1n+n, m) : Nat}` | Adding a successor on the left: (n + 1) + m = (n + m) + 1, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `add_comm_sym(n, m)` | `∀ n: Nat, m: Nat. {Nat.add(m, n) == Nat.add(n, m) : Nat}` | Addition is commutative: n + m = m + n, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `add_assoc_sym(a, b, c)` | `∀ a: Nat, -b: Nat, -c: Nat. {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}` | Addition is associative: (a + b) + c = a + (b + c), reversed to rewrite toward the simple side. | 0.1.0.0 |
| `add_left_comm_sym(a, b, c)` | `∀ a: Nat, b: Nat, -c: Nat. {Nat.add(b, Nat.add(a, c)) == Nat.add(a, Nat.add(b, c)) : Nat}` | Left commutativity of addition: a + (b + c) = b + (a + c), reversed to rewrite toward the simple side. | 0.1.0.0 |
| `add_right_comm_sym(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.add(Nat.add(a, c), b) == Nat.add(Nat.add(a, b), c) : Nat}` | Right commutativity of addition: (a + b) + c = (a + c) + b, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `add_add_add_comm_sym(a, b, c, d)` | `∀ a: Nat, b: Nat, c: Nat, -d: Nat. {Nat.add(Nat.add(a, c), Nat.add(b, d)) == Nat.add(Nat.add(a, b), Nat.add(c, d)) : Nat}` | Four-way regrouping of a sum: (a + b) + (c + d) = (a + c) + (b + d), reversed to rewrite toward the simple side. | 0.1.0.0 |
| `mul_zero_sym(x)` | `∀ x: Nat. {0n == Nat.mul(x, 0n) : Nat}` | Zero absorbs multiplication on the right: x * 0 = 0, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `zero_mul_sym(x)` | `∀ -x: Nat. {0n == Nat.mul(0n, x) : Nat}` | Zero absorbs multiplication on the left: 0 * x = 0, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `mul_one_sym(x)` | `∀ x: Nat. {x == Nat.mul(x, 1n) : Nat}` | One is a right identity for multiplication: x * 1 = x, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `one_mul_sym(x)` | `∀ x: Nat. {x == Nat.mul(1n, x) : Nat}` | One is a left identity for multiplication: 1 * x = x, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `mul_succ_sym(n, m)` | `∀ n: Nat, m: Nat. {Nat.add(Nat.mul(n, m), n) == Nat.mul(n, 1n+m) : Nat}` | Multiplying by a successor on the right: n * (m + 1) = n * m + n, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `succ_mul_sym(n, m)` | `∀ n: Nat, m: Nat. {Nat.add(Nat.mul(n, m), m) == Nat.mul(1n+n, m) : Nat}` | Multiplying by a successor on the left: (n + 1) * m = n * m + m, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `mul_comm_sym(n, m)` | `∀ n: Nat, m: Nat. {Nat.mul(m, n) == Nat.mul(n, m) : Nat}` | Multiplication is commutative: n * m = m * n, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `add_mul_sym(a, b, c)` | `∀ a: Nat, -b: Nat, c: Nat. {Nat.add(Nat.mul(a, c), Nat.mul(b, c)) == Nat.mul(Nat.add(a, b), c) : Nat}` | Multiplication distributes over addition on the right: (a + b) * c = a * c + b * c, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `mul_add_sym(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == Nat.mul(a, Nat.add(b, c)) : Nat}` | Multiplication distributes over addition on the left: a * (b + c) = a * b + a * c, reversed to rewrite toward the simple side. | 0.1.0.0 |
| `mul_assoc_sym(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(Nat.mul(a, b), c) : Nat}` | Multiplication is associative: (a * b) * c = a * (b * c), reversed to rewrite toward the simple side. | 0.1.0.0 |
| `sub_zero_sym(n)` | `∀ n: Nat. {n == Nat.sub(n, 0n) : Nat}` | Subtracting zero changes nothing: n - 0 = n, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `zero_sub_sym(n)` | `∀ n: Nat. {0n == Nat.sub(0n, n) : Nat}` | Truncated subtraction from zero is zero: 0 - n = 0, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `sub_self_sym(n)` | `∀ n: Nat. {0n == Nat.sub(n, n) : Nat}` | A natural minus itself is zero: n - n = 0, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `succ_sub_succ_sym(n, m)` | `∀ -n: Nat, -m: Nat. {Nat.sub(n, m) == Nat.sub(1n+n, 1n+m) : Nat}` | Subtracting successors: (n + 1) - (m + 1) = n - m, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `add_sub_cancel_sym(n, m)` | `∀ n: Nat, m: Nat. {n == Nat.sub(Nat.add(n, m), m) : Nat}` | Adding then subtracting m cancels: (n + m) - m = n, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `add_sub_cancel_left_sym(n, m)` | `∀ n: Nat, m: Nat. {m == Nat.sub(Nat.add(n, m), n) : Nat}` | Adding then subtracting n cancels: (n + m) - n = m, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `sub_sub_sym(n, m, k)` | `∀ n: Nat, m: Nat, k: Nat. {Nat.sub(n, Nat.add(m, k)) == Nat.sub(Nat.sub(n, m), k) : Nat}` | Subtracting twice is subtracting the sum: (n - m) - k = n - (m + k), reversed to rewrite toward the simple side. | 0.2.0.0 |
| `min_comm_sym(a, b)` | `∀ a: Nat, b: Nat. {Nat.min(b, a) == Nat.min(a, b) : Nat}` | Minimum is commutative, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `max_comm_sym(a, b)` | `∀ a: Nat, b: Nat. {Nat.max(b, a) == Nat.max(a, b) : Nat}` | Maximum is commutative, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `min_self_sym(a)` | `∀ a: Nat. {a == Nat.min(a, a) : Nat}` | The minimum of a natural and itself is itself, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `max_self_sym(a)` | `∀ a: Nat. {a == Nat.max(a, a) : Nat}` | The maximum of a natural and itself is itself, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `min_zero_sym(a)` | `∀ a: Nat. {0n == Nat.min(a, 0n) : Nat}` | The minimum with zero is zero: min(a, 0) = 0, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `zero_min_sym(a)` | `∀ a: Nat. {0n == Nat.min(0n, a) : Nat}` | The minimum with zero is zero: min(0, a) = 0, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `max_zero_sym(a)` | `∀ a: Nat. {a == Nat.max(a, 0n) : Nat}` | Zero is an identity for maximum: max(a, 0) = a, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `zero_max_sym(a)` | `∀ a: Nat. {a == Nat.max(0n, a) : Nat}` | Zero is an identity for maximum: max(0, a) = a, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `min_assoc_sym(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.min(a, Nat.min(b, c)) == Nat.min(Nat.min(a, b), c) : Nat}` | Minimum is associative, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `max_assoc_sym(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.max(a, Nat.max(b, c)) == Nat.max(Nat.max(a, b), c) : Nat}` | Maximum is associative, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `min_add_max_sym(a, b)` | `∀ a: Nat, b: Nat. {Nat.add(a, b) == Nat.add(Nat.min(a, b), Nat.max(a, b)) : Nat}` | The minimum plus the maximum is the sum: min(a, b) + max(a, b) = a + b, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `pow_zero_sym(a)` | `∀ -a: Nat. {1n == Nat.pow(a, 0n) : Nat}` | Any natural to the power zero is one, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `pow_succ_sym(a, n)` | `∀ -a: Nat, -n: Nat. {Nat.mul(a, Nat.pow(a, n)) == Nat.pow(a, 1n+n) : Nat}` | A power with a successor exponent: a^(n+1) = a * a^n, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `pow_one_sym(a)` | `∀ a: Nat. {a == Nat.pow(a, 1n) : Nat}` | Any natural to the power one is itself, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `one_pow_sym(n)` | `∀ n: Nat. {1n == Nat.pow(1n, n) : Nat}` | One to any power is one, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `pow_add_sym(a, m, n)` | `∀ a: Nat, m: Nat, n: Nat. {Nat.mul(Nat.pow(a, m), Nat.pow(a, n)) == Nat.pow(a, Nat.add(m, n)) : Nat}` | Exponents add under multiplication: a^(m+n) = a^m * a^n, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `double_eq_add_sym(n)` | `∀ n: Nat. {Nat.add(n, n) == Nat.double(n) : Nat}` | Doubling is adding a natural to itself, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `is_eq_refl_sym(n)` | `∀ n: Nat. {True{} == Nat.is_eq(n, n) : Bool}` | Every natural tests equal to itself, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `is_eq_comm_sym(a, b)` | `∀ a: Nat, b: Nat. {Nat.is_eq(b, a) == Nat.is_eq(a, b) : Bool}` | The equality test is symmetric, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `is_ge_eq_is_le_sym(a, b)` | `∀ a: Nat, b: Nat. {Nat.is_le(b, a) == Nat.is_ge(a, b) : Bool}` | A >= b tests the same as b <= a, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `is_gt_eq_is_lt_sym(a, b)` | `∀ a: Nat, b: Nat. {Nat.is_lt(b, a) == Nat.is_gt(a, b) : Bool}` | A > b tests the same as b < a, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `is_lt_eq_succ_le_sym(a, b)` | `∀ a: Nat, b: Nat. {Nat.is_le(1n+a, b) == Nat.is_lt(a, b) : Bool}` | A < b tests the same as a + 1 <= b, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `not_is_le_sym(a, b)` | `∀ a: Nat, b: Nat. {Nat.is_lt(b, a) == Bool.not(Nat.is_le(a, b)) : Bool}` | Not (a <= b) tests the same as b < a, reversed to rewrite toward the simple side. | 0.2.0.0 |
| `not_is_lt_sym(a, b)` | `∀ a: Nat, b: Nat. {Nat.is_le(b, a) == Bool.not(Nat.is_lt(a, b)) : Bool}` | Not (a < b) tests the same as b <= a, reversed to rewrite toward the simple side. | 0.2.0.0 |

## order

```python
import bend-mathlib@0.3.0.0/order.bend as MOrder
```

| lemma | statement | meaning | since |
|---|---|---|---|
| `le_trans3(~A, ~le, ~le_trans, a, b, c, d, ab, bc, cd)` | `∀ ~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +a: A, +b: A, +c: A, +d: A, ab: {le(a, b) == True{} : Bool}, bc: {le(b, c) == True{} : Bool}, cd: {le(c, d) == True{} : Bool}. {le(a, d) == True{} : Bool}` | A chain of three comparisons composes. | next |
| `le_trans4(~A, ~le, ~le_trans, a, b, c, d, e, ab, bc, cd, de)` | `∀ ~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +a: A, +b: A, +c: A, +d: A, +e: A, ab: {le(a, b) == True{} : Bool}, bc: {le(b, c) == True{} : Bool}, cd: {le(c, d) == True{} : Bool}, de: {le(d, e) == True{} : Bool}. {le(a, e) == True{} : Bool}` | A chain of four comparisons composes. | next |
| `le_antisymm_eq(~A, ~le, ~le_antisymm, a, b, ab, ba)` | `∀ ~A: Data, ~le: A -> A -> Bool, ~le_antisymm: @x: A -> @y: A -> {le(x, y) == True{} : Bool} -> {le(y, x) == True{} : Bool} -> {x == y : A}, +a: A, +b: A, ab: {le(a, b) == True{} : Bool}, ba: {le(b, a) == True{} : Bool}. {a == b : A}` | Antisymmetry gives equality. | next |
| `le_total_true(~A, ~le, ~le_total, a, b)` | `∀ ~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {Bool.or(le(x, y), le(y, x)) == True{} : Bool}, +a: A, +b: A. {Bool.or(le(a, b), le(b, a)) == True{} : Bool}` | Totality as a Bool disjunction. | next |
| `le_total_of_not_le(~A, ~le, ~le_total, a, b, h)` | `∀ ~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {Bool.or(le(x, y), le(y, x)) == True{} : Bool}, +a: A, +b: A, h: {le(a, b) == False{} : Bool}. {le(b, a) == True{} : Bool}` | The other side of a total order holds when one side fails. | next |
| `le_total_true_sym(~A, ~le, ~le_total, a, b)` | `∀ ~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {Bool.or(le(x, y), le(y, x)) == True{} : Bool}, +a: A, +b: A. {True{} == Bool.or(le(a, b), le(b, a)) : Bool}` | Totality as a Bool disjunction, reversed to rewrite toward the simple side. | next |

## string

```python
import bend-mathlib@0.3.0.0/string.bend as MString
```

| lemma | statement | meaning | since |
|---|---|---|---|
| `append_nil(a)` | `∀ a: String. {String.append(a, SNil{}) == a : String}` | The empty string is a right identity for append: a ++ "" = a. | next |
| `nil_append(a)` | `∀ -a: String. {String.append(SNil{}, a) == a : String}` | The empty string is a left identity for append: "" ++ a = a. | next |
| `append_assoc(a, b, c)` | `∀ a: String, -b: String, -c: String. {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}` | Append is associative: (a ++ b) ++ c = a ++ (b ++ c). | next |
| `length_append(a, b)` | `∀ a: String, -b: String. {String.length(String.append(a, b)) == Nat.add(String.length(a), String.length(b)) : Nat}` | The length of an append is the sum of the lengths. | next |
| `reverse_go_spec(s, acc)` | `∀ s: String, acc: String. {String.reverse.go(s, acc) == String.append(String.reverse(s), acc) : String}` | The reverse accumulator loop appends the reversed string to the accumulator. | next |
| `reverse_append(a, b)` | `∀ a: String, b: String. {String.reverse(String.append(a, b)) == String.append(String.reverse(b), String.reverse(a)) : String}` | Reversing an append reverses and swaps the parts: reverse (a ++ b) = reverse b ++ reverse a. | next |
| `reverse_reverse(a)` | `∀ a: String. {String.reverse(String.reverse(a)) == a : String}` | Reversing twice gives the string back. | next |
| `u32_cmp_refl(x)` | `∀ x: U32. {U32.cmp(x, x) == EQ{} : Cmp}` | Comparing a U32 with itself gives EQ. | next |
| `char_cmp_refl(c)` | `∀ c: Char. {Char.cmp(c, c) == ((c, c), EQ{}) : (Char & Char) & Cmp}` | Comparing a character with itself gives EQ and hands both back. | next |
| `cmp_refl(s)` | `∀ s: String. {String.cmp(s, s) == ((s, s), EQ{}) : (String & String) & Cmp}` | Comparing a string with itself gives EQ and hands both back. | next |
| `eq_refl(s)` | `∀ s: String. {String.eq(s, s) == True{} : Bool}` | Every string is equal to itself under String.eq. | next |
| `u32_eq_of_is_eq(a, b, h)` | `∀ a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}. {a == b : U32}` | Two U32s that U32.is_eq calls equal are equal. | next |
| `char_eq_of_is_eq(a, b, h)` | `∀ a: Char, b: Char, h: {Char.is_eq(a, b) == True{} : Bool}. {a == b : Char}` | Two characters that Char.is_eq calls equal are equal. | next |
| `eq_of_eq_true(a, b, h)` | `∀ a: String, b: String, h: {String.eq(a, b) == True{} : Bool}. {a == b : String}` | Two strings that String.eq calls equal are equal. | next |
| `append_nil_sym(a)` | `∀ a: String. {a == String.append(a, SNil{}) : String}` | The empty string is a right identity for append: a ++ "" = a, reversed to rewrite toward the simple side. | next |
| `nil_append_sym(a)` | `∀ -a: String. {a == String.append(SNil{}, a) : String}` | The empty string is a left identity for append: "" ++ a = a, reversed to rewrite toward the simple side. | next |
| `append_assoc_sym(a, b, c)` | `∀ a: String, -b: String, -c: String. {String.append(a, String.append(b, c)) == String.append(String.append(a, b), c) : String}` | Append is associative: (a ++ b) ++ c = a ++ (b ++ c), reversed to rewrite toward the simple side. | next |
| `length_append_sym(a, b)` | `∀ a: String, -b: String. {Nat.add(String.length(a), String.length(b)) == String.length(String.append(a, b)) : Nat}` | The length of an append is the sum of the lengths, reversed to rewrite toward the simple side. | next |
| `reverse_go_spec_sym(s, acc)` | `∀ s: String, acc: String. {String.append(String.reverse(s), acc) == String.reverse.go(s, acc) : String}` | The reverse accumulator loop appends the reversed string to the accumulator, reversed to rewrite toward the simple side. | next |
| `reverse_append_sym(a, b)` | `∀ a: String, b: String. {String.append(String.reverse(b), String.reverse(a)) == String.reverse(String.append(a, b)) : String}` | Reversing an append reverses and swaps the parts: reverse (a ++ b) = reverse b ++ reverse a, reversed to rewrite toward the simple side. | next |
| `reverse_reverse_sym(a)` | `∀ a: String. {a == String.reverse(String.reverse(a)) : String}` | Reversing twice gives the string back, reversed to rewrite toward the simple side. | next |
| `u32_cmp_refl_sym(x)` | `∀ x: U32. {EQ{} == U32.cmp(x, x) : Cmp}` | Comparing a U32 with itself gives EQ, reversed to rewrite toward the simple side. | next |
| `char_cmp_refl_sym(c)` | `∀ c: Char. {((c, c), EQ{}) == Char.cmp(c, c) : (Char & Char) & Cmp}` | Comparing a character with itself gives EQ and hands both back, reversed to rewrite toward the simple side. | next |
| `cmp_refl_sym(s)` | `∀ s: String. {((s, s), EQ{}) == String.cmp(s, s) : (String & String) & Cmp}` | Comparing a string with itself gives EQ and hands both back, reversed to rewrite toward the simple side. | next |
| `eq_refl_sym(s)` | `∀ s: String. {True{} == String.eq(s, s) : Bool}` | Every string is equal to itself under String.eq, reversed to rewrite toward the simple side. | next |

213 lemmas + 152 generated _sym twins, 6 predicates. Generated by `tools/mathlib/index.ts`.
