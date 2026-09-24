# bend-mathlib

Machine-checked lemmas for Bend 2, checked with `bend 2.0.27`.
Not related to the hub package `bend-math-lib`.

Rewriting: `%e : P` replaces the right side of `e` with its left side, so `name` expands the simple
side into the compound one and `name_sym` simplifies the compound side.

## bool

```python
import bend-mathlib@0.1.0.0/bool.bend as MBool
```

| lemma | statement | meaning |
|---|---|---|
| `not_not(b)` | `∀ b: Bool. {Bool.not(Bool.not(b)) == b : Bool}` | Negating a boolean twice gives it back. |
| `and_comm(a, b)` | `∀ a: Bool, b: Bool. {Bool.and(a, b) == Bool.and(b, a) : Bool}` | Boolean and is commutative. |
| `or_comm(a, b)` | `∀ a: Bool, b: Bool. {Bool.or(a, b) == Bool.or(b, a) : Bool}` | Boolean or is commutative. |
| `and_assoc(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}` | Boolean and is associative. |
| `or_assoc(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}` | Boolean or is associative. |
| `and_true(a)` | `∀ a: Bool. {Bool.and(a, True{}) == a : Bool}` | True is a right identity for and: a and true is a. |
| `true_and(a)` | `∀ -a: Bool. {Bool.and(True{}, a) == a : Bool}` | True is a left identity for and: true and a is a. |
| `and_false(a)` | `∀ a: Bool. {Bool.and(a, False{}) == False{} : Bool}` | False absorbs and on the right: a and false is false. |
| `false_and(a)` | `∀ -a: Bool. {Bool.and(False{}, a) == False{} : Bool}` | False absorbs and on the left: false and a is false. |
| `or_false(a)` | `∀ a: Bool. {Bool.or(a, False{}) == a : Bool}` | False is a right identity for or: a or false is a. |
| `false_or(a)` | `∀ -a: Bool. {Bool.or(False{}, a) == a : Bool}` | False is a left identity for or: false or a is a. |
| `or_true(a)` | `∀ a: Bool. {Bool.or(a, True{}) == True{} : Bool}` | True absorbs or on the right: a or true is true. |
| `true_or(a)` | `∀ -a: Bool. {Bool.or(True{}, a) == True{} : Bool}` | True absorbs or on the left: true or a is true. |
| `de_morgan_and(a, b)` | `∀ a: Bool, -b: Bool. {Bool.not(Bool.and(a, b)) == Bool.or(Bool.not(a), Bool.not(b)) : Bool}` | De Morgan: not (a and b) is (not a) or (not b). |
| `de_morgan_or(a, b)` | `∀ a: Bool, -b: Bool. {Bool.not(Bool.or(a, b)) == Bool.and(Bool.not(a), Bool.not(b)) : Bool}` | De Morgan: not (a or b) is (not a) and (not b). |
| `true_ne_false()` | `{True{} != False{} : Bool}` | True and False are different booleans. |
| `not_not_sym(b)` | `∀ b: Bool. {b == Bool.not(Bool.not(b)) : Bool}` | Negating a boolean twice gives it back, reversed to rewrite toward the simple side. |
| `and_comm_sym(a, b)` | `∀ a: Bool, b: Bool. {Bool.and(b, a) == Bool.and(a, b) : Bool}` | Boolean and is commutative, reversed to rewrite toward the simple side. |
| `or_comm_sym(a, b)` | `∀ a: Bool, b: Bool. {Bool.or(b, a) == Bool.or(a, b) : Bool}` | Boolean or is commutative, reversed to rewrite toward the simple side. |
| `and_assoc_sym(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}` | Boolean and is associative, reversed to rewrite toward the simple side. |
| `or_assoc_sym(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}` | Boolean or is associative, reversed to rewrite toward the simple side. |
| `and_true_sym(a)` | `∀ a: Bool. {a == Bool.and(a, True{}) : Bool}` | True is a right identity for and: a and true is a, reversed to rewrite toward the simple side. |
| `true_and_sym(a)` | `∀ -a: Bool. {a == Bool.and(True{}, a) : Bool}` | True is a left identity for and: true and a is a, reversed to rewrite toward the simple side. |
| `and_false_sym(a)` | `∀ a: Bool. {False{} == Bool.and(a, False{}) : Bool}` | False absorbs and on the right: a and false is false, reversed to rewrite toward the simple side. |
| `false_and_sym(a)` | `∀ -a: Bool. {False{} == Bool.and(False{}, a) : Bool}` | False absorbs and on the left: false and a is false, reversed to rewrite toward the simple side. |
| `or_false_sym(a)` | `∀ a: Bool. {a == Bool.or(a, False{}) : Bool}` | False is a right identity for or: a or false is a, reversed to rewrite toward the simple side. |
| `false_or_sym(a)` | `∀ -a: Bool. {a == Bool.or(False{}, a) : Bool}` | False is a left identity for or: false or a is a, reversed to rewrite toward the simple side. |
| `or_true_sym(a)` | `∀ a: Bool. {True{} == Bool.or(a, True{}) : Bool}` | True absorbs or on the right: a or true is true, reversed to rewrite toward the simple side. |
| `true_or_sym(a)` | `∀ -a: Bool. {True{} == Bool.or(True{}, a) : Bool}` | True absorbs or on the left: true or a is true, reversed to rewrite toward the simple side. |
| `de_morgan_and_sym(a, b)` | `∀ a: Bool, -b: Bool. {Bool.or(Bool.not(a), Bool.not(b)) == Bool.not(Bool.and(a, b)) : Bool}` | De Morgan: not (a and b) is (not a) or (not b), reversed to rewrite toward the simple side. |
| `de_morgan_or_sym(a, b)` | `∀ a: Bool, -b: Bool. {Bool.and(Bool.not(a), Bool.not(b)) == Bool.not(Bool.or(a, b)) : Bool}` | De Morgan: not (a or b) is (not a) and (not b), reversed to rewrite toward the simple side. |

## equal

```python
import bend-mathlib@0.1.0.0/equal.bend as MEqual
```

| lemma | statement | meaning |
|---|---|---|
| `cong2(A, B, C, f, a1, a2, b1, b2, ea, eb)` | `∀ -A: Type, -B: Type, -C: Type, -f: A -> B -> C, -a1: A, -a2: A, -b1: B, -b2: B, ea: {a1 == a2 : A}, eb: {b1 == b2 : B}. {f(a1, b1) == f(a2, b2) : C}` | Applying a two-argument function to equal arguments gives equal results. |
| `subst(A, P, a, b, e, p)` | `∀ -A: Type, -P: A -> Type, -a: A, -b: A, e: {a == b : A}, p: P(a). P(b)` | If a equals b, any property of a is also a property of b. |
| `trans3(A, a, b, c, d, ab, bc, cd)` | `∀ -A: Type, -a: A, -b: A, -c: A, -d: A, ab: {a == b : A}, bc: {b == c : A}, cd: {c == d : A}. {a == d : A}` | Equality chains through three steps: a = b, b = c and c = d give a = d. |
| `cong_succ(a, b, e)` | `∀ -a: Nat, -b: Nat, e: {a == b : Nat}. {1n+a == 1n+b : Nat}` | Equal naturals have equal successors. |

## list

```python
import bend-mathlib@0.1.0.0/list.bend as MList
```

| lemma | statement | meaning |
|---|---|---|
| `append_nil(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {List.append(a, A, xs, Nil{}) == xs : List<a, A>}` | The empty list is a right identity for append: xs ++ [] = xs. |
| `nil_append(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), -xs: List<a, A>. {List.append(a, A, Nil{}, xs) == xs : List<a, A>}` | The empty list is a left identity for append: [] ++ xs = xs. |
| `append_assoc(a, A, xs, ys, zs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>, -zs: List<a, A>. {List.append(a, A, List.append(a, A, xs, ys), zs) == List.append(a, A, xs, List.append(a, A, ys, zs)) : List<a, A>}` | Append is associative: (xs ++ ys) ++ zs = xs ++ (ys ++ zs). |
| `length_append(a, A, xs, ys)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>. {List.length(a, A, List.append(a, A, xs, ys)) == Nat.add(List.length(a, A, xs), List.length(a, A, ys)) : Nat}` | The length of an append is the sum of the lengths. |
| `reverse_go_spec(a, A, xs, acc)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>. {List.reverse.go(a, A, xs, acc) == List.append(a, A, List.reverse(a, A, xs), acc) : List<a, A>}` | The reverse accumulator loop appends the reversed list to the accumulator. |
| `reverse_append(a, A, xs, ys)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, ys: List<a, A>. {List.reverse(a, A, List.append(a, A, xs, ys)) == List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)) : List<a, A>}` | Reversing an append reverses and swaps the parts: reverse (xs ++ ys) = reverse ys ++ reverse xs. |
| `reverse_reverse(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {List.reverse(a, A, List.reverse(a, A, xs)) == xs : List<a, A>}` | Reversing twice gives the list back. |
| `length_reverse(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {List.length(a, A, List.reverse(a, A, xs)) == List.length(a, A, xs) : Nat}` | Reversing preserves the length. |
| `foldr_append(~a, ~A, ~B, ~f, xs, ys, z)` | `∀ ~a: Quant, ~A: Kind(a), ~B: Type, ~f: A -> B -> B, xs: List<a, A>, -ys: List<a, A>, -z: B. {List.foldr(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) == List.foldr(~a, ~A, ~B, ~f, xs, List.foldr(~a, ~A, ~B, ~f, ys, z)) : B}` | A right fold over an append folds the first part onto the fold of the second. |
| `take_append_drop(a, A, xs, n)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat. {List.append(a, A, List.take(a, A, xs, n), List.drop(a, A, xs, n)) == xs : List<a, A>}` | Taking n elements and appending the rest after dropping n gives the list back. |
| `length_map(~A, ~B, ~f, xs)` | `∀ ~A: Type, ~B: Type, ~f: A -> B, xs: List<A>. {List.length(&1, B, List.map(~A, ~B, ~f, xs)) == List.length(&1, A, xs) : Nat}` | Mapping preserves the length. |
| `map_append(~A, ~B, ~f, xs, ys)` | `∀ ~A: Type, ~B: Type, ~f: A -> B, xs: List<A>, -ys: List<A>. {List.map(~A, ~B, ~f, List.append(&1, A, xs, ys)) == List.append(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, ys)) : List<B>}` | Mapping over an append maps each part: map f (xs ++ ys) = map f xs ++ map f ys. |
| `map_map(~A, ~B, ~C, ~f, ~g, xs)` | `∀ ~A: Type, ~B: Type, ~C: Type, ~f: A -> B, ~g: B -> C, xs: List<A>. {List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, xs)) == List.map(~A, ~C, ~(x => g(f(x))), xs) : List<C>}` | Mapping twice is mapping the composition: map g (map f xs) = map (g . f) xs. |
| `append_nil_sym(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {xs == List.append(a, A, xs, Nil{}) : List<a, A>}` | The empty list is a right identity for append: xs ++ [] = xs, reversed to rewrite toward the simple side. |
| `nil_append_sym(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), -xs: List<a, A>. {xs == List.append(a, A, Nil{}, xs) : List<a, A>}` | The empty list is a left identity for append: [] ++ xs = xs, reversed to rewrite toward the simple side. |
| `append_assoc_sym(a, A, xs, ys, zs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>, -zs: List<a, A>. {List.append(a, A, xs, List.append(a, A, ys, zs)) == List.append(a, A, List.append(a, A, xs, ys), zs) : List<a, A>}` | Append is associative: (xs ++ ys) ++ zs = xs ++ (ys ++ zs), reversed to rewrite toward the simple side. |
| `length_append_sym(a, A, xs, ys)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>. {Nat.add(List.length(a, A, xs), List.length(a, A, ys)) == List.length(a, A, List.append(a, A, xs, ys)) : Nat}` | The length of an append is the sum of the lengths, reversed to rewrite toward the simple side. |
| `reverse_go_spec_sym(a, A, xs, acc)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>. {List.append(a, A, List.reverse(a, A, xs), acc) == List.reverse.go(a, A, xs, acc) : List<a, A>}` | The reverse accumulator loop appends the reversed list to the accumulator, reversed to rewrite toward the simple side. |
| `reverse_append_sym(a, A, xs, ys)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, ys: List<a, A>. {List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)) == List.reverse(a, A, List.append(a, A, xs, ys)) : List<a, A>}` | Reversing an append reverses and swaps the parts: reverse (xs ++ ys) = reverse ys ++ reverse xs, reversed to rewrite toward the simple side. |
| `reverse_reverse_sym(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {xs == List.reverse(a, A, List.reverse(a, A, xs)) : List<a, A>}` | Reversing twice gives the list back, reversed to rewrite toward the simple side. |
| `length_reverse_sym(a, A, xs)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>. {List.length(a, A, xs) == List.length(a, A, List.reverse(a, A, xs)) : Nat}` | Reversing preserves the length, reversed to rewrite toward the simple side. |
| `foldr_append_sym(~a, ~A, ~B, ~f, xs, ys, z)` | `∀ ~a: Quant, ~A: Kind(a), ~B: Type, ~f: A -> B -> B, xs: List<a, A>, -ys: List<a, A>, -z: B. {List.foldr(~a, ~A, ~B, ~f, xs, List.foldr(~a, ~A, ~B, ~f, ys, z)) == List.foldr(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) : B}` | A right fold over an append folds the first part onto the fold of the second, reversed to rewrite toward the simple side. |
| `take_append_drop_sym(a, A, xs, n)` | `∀ -a: Quant, -A: Kind(a), xs: List<a, A>, n: Nat. {xs == List.append(a, A, List.take(a, A, xs, n), List.drop(a, A, xs, n)) : List<a, A>}` | Taking n elements and appending the rest after dropping n gives the list back, reversed to rewrite toward the simple side. |
| `length_map_sym(~A, ~B, ~f, xs)` | `∀ ~A: Type, ~B: Type, ~f: A -> B, xs: List<A>. {List.length(&1, A, xs) == List.length(&1, B, List.map(~A, ~B, ~f, xs)) : Nat}` | Mapping preserves the length, reversed to rewrite toward the simple side. |
| `map_append_sym(~A, ~B, ~f, xs, ys)` | `∀ ~A: Type, ~B: Type, ~f: A -> B, xs: List<A>, -ys: List<A>. {List.append(&1, B, List.map(~A, ~B, ~f, xs), List.map(~A, ~B, ~f, ys)) == List.map(~A, ~B, ~f, List.append(&1, A, xs, ys)) : List<B>}` | Mapping over an append maps each part: map f (xs ++ ys) = map f xs ++ map f ys, reversed to rewrite toward the simple side. |
| `map_map_sym(~A, ~B, ~C, ~f, ~g, xs)` | `∀ ~A: Type, ~B: Type, ~C: Type, ~f: A -> B, ~g: B -> C, xs: List<A>. {List.map(~A, ~C, ~(x => g(f(x))), xs) == List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, xs)) : List<C>}` | Mapping twice is mapping the composition: map g (map f xs) = map (g . f) xs, reversed to rewrite toward the simple side. |

## nat

```python
import bend-mathlib@0.1.0.0/nat.bend as MNat
```

| predicate | definition |
|---|---|
| `le(a: Nat, b: Nat) -> Data` | `{Nat.is_le(a, b) == True{} : Bool}` |
| `lt(a: Nat, b: Nat) -> Data` | `{Nat.is_lt(a, b) == True{} : Bool}` |
| `ge(a: Nat, b: Nat) -> Data` | `{Nat.is_ge(a, b) == True{} : Bool}` |
| `gt(a: Nat, b: Nat) -> Data` | `{Nat.is_gt(a, b) == True{} : Bool}` |

| lemma | statement | meaning |
|---|---|---|
| `add_zero(x)` | `∀ x: Nat. {Nat.add(x, 0n) == x : Nat}` | Zero is a right identity for addition: x + 0 = x. |
| `zero_add(x)` | `∀ -x: Nat. {Nat.add(0n, x) == x : Nat}` | Zero is a left identity for addition: 0 + x = x. |
| `add_succ(n, m)` | `∀ n: Nat, -m: Nat. {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}` | Adding a successor on the right: n + (m + 1) = (n + m) + 1. |
| `succ_add(n, m)` | `∀ -n: Nat, -m: Nat. {Nat.add(1n+n, m) == 1n+Nat.add(n, m) : Nat}` | Adding a successor on the left: (n + 1) + m = (n + m) + 1. |
| `add_comm(n, m)` | `∀ n: Nat, m: Nat. {Nat.add(n, m) == Nat.add(m, n) : Nat}` | Addition is commutative: n + m = m + n. |
| `add_assoc(a, b, c)` | `∀ a: Nat, -b: Nat, -c: Nat. {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}` | Addition is associative: (a + b) + c = a + (b + c). |
| `add_left_comm(a, b, c)` | `∀ a: Nat, b: Nat, -c: Nat. {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}` | Left commutativity of addition: a + (b + c) = b + (a + c). |
| `add_right_comm(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}` | Right commutativity of addition: (a + b) + c = (a + c) + b. |
| `add_add_add_comm(a, b, c, d)` | `∀ a: Nat, b: Nat, c: Nat, -d: Nat. {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}` | Four-way regrouping of a sum: (a + b) + (c + d) = (a + c) + (b + d). |
| `succ_inj(a, b, e)` | `∀ -a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}. {a == b : Nat}` | The successor function is injective: a + 1 = b + 1 implies a = b. |
| `zero_ne_succ(n)` | `∀ -n: Nat. {0n != 1n+n : Nat}` | Zero is not a successor. |
| `succ_ne_zero(n)` | `∀ -n: Nat. {1n+n != 0n : Nat}` | A successor is not zero. |
| `add_left_cancel(a, b, c, e)` | `∀ a: Nat, -b: Nat, -c: Nat, e: {Nat.add(a, b) == Nat.add(a, c) : Nat}. {b == c : Nat}` | Addition cancels on the left: a + b = a + c implies b = c. |
| `add_right_cancel(a, b, c, e)` | `∀ a: Nat, b: Nat, c: Nat, e: {Nat.add(a, b) == Nat.add(c, b) : Nat}. {a == c : Nat}` | Addition cancels on the right: a + b = c + b implies a = c. |
| `mul_zero(x)` | `∀ x: Nat. {Nat.mul(x, 0n) == 0n : Nat}` | Zero absorbs multiplication on the right: x * 0 = 0. |
| `zero_mul(x)` | `∀ -x: Nat. {Nat.mul(0n, x) == 0n : Nat}` | Zero absorbs multiplication on the left: 0 * x = 0. |
| `mul_one(x)` | `∀ x: Nat. {Nat.mul(x, 1n) == x : Nat}` | One is a right identity for multiplication: x * 1 = x. |
| `one_mul(x)` | `∀ x: Nat. {Nat.mul(1n, x) == x : Nat}` | One is a left identity for multiplication: 1 * x = x. |
| `mul_succ(n, m)` | `∀ n: Nat, m: Nat. {Nat.mul(n, 1n+m) == Nat.add(Nat.mul(n, m), n) : Nat}` | Multiplying by a successor on the right: n * (m + 1) = n * m + n. |
| `succ_mul(n, m)` | `∀ n: Nat, m: Nat. {Nat.mul(1n+n, m) == Nat.add(Nat.mul(n, m), m) : Nat}` | Multiplying by a successor on the left: (n + 1) * m = n * m + m. |
| `mul_comm(n, m)` | `∀ n: Nat, m: Nat. {Nat.mul(n, m) == Nat.mul(m, n) : Nat}` | Multiplication is commutative: n * m = m * n. |
| `add_mul(a, b, c)` | `∀ a: Nat, -b: Nat, c: Nat. {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}` | Multiplication distributes over addition on the right: (a + b) * c = a * c + b * c. |
| `mul_add(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}` | Multiplication distributes over addition on the left: a * (b + c) = a * b + a * c. |
| `mul_assoc(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}` | Multiplication is associative: (a * b) * c = a * (b * c). |
| `le_refl(a)` | `∀ a: Nat. le(a, a)` | Every natural is at most itself: a <= a. |
| `zero_le(b)` | `∀ b: Nat. le(0n, b)` | Zero is at most every natural: 0 <= b. |
| `le_succ(n)` | `∀ n: Nat. le(n, 1n+n)` | Every natural is at most its successor: n <= n + 1. |
| `le_add_right(n, k)` | `∀ n: Nat, k: Nat. le(n, Nat.add(n, k))` | Adding on the right never decreases a natural: n <= n + k. |
| `le_trans(a, b, c, ab, bc)` | `∀ a: Nat, b: Nat, c: Nat, ab: le(a, b), bc: le(b, c). le(a, c)` | The order is transitive: a <= b and b <= c imply a <= c. |
| `le_antisymm(a, b, ab, ba)` | `∀ a: Nat, b: Nat, ab: le(a, b), ba: le(b, a). {a == b : Nat}` | The order is antisymmetric: a <= b and b <= a imply a = b. |
| `le_total(a, b)` | `∀ a: Nat, b: Nat. Or(le(a, b), le(b, a))` | The order is total: a <= b or b <= a. |
| `le_total_d(a, b)` | `∀ a: Nat, b: Nat. Either<&2, &2, le(a, b), le(b, a)>` | The order is total, as a reusable sum: a <= b or b <= a. |
| `lt_irrefl(a)` | `∀ a: Nat. lt(a, a) -> Empty` | No natural is less than itself. |
| `lt_trans(a, b, c, ab, bc)` | `∀ a: Nat, b: Nat, c: Nat, ab: lt(a, b), bc: lt(b, c). lt(a, c)` | The strict order is transitive: a < b and b < c imply a < c. |
| `le_of_lt(a, b, h)` | `∀ a: Nat, b: Nat, h: lt(a, b). le(a, b)` | A strict inequality implies the weak one: a < b implies a <= b. |
| `le_of_ge(a, b, h)` | `∀ a: Nat, b: Nat, h: ge(a, b). le(b, a)` | Flipping a >= b gives b <= a. |
| `ge_of_le(a, b, h)` | `∀ a: Nat, b: Nat, h: le(b, a). ge(a, b)` | Flipping b <= a gives a >= b. |
| `lt_of_gt(a, b, h)` | `∀ a: Nat, b: Nat, h: gt(a, b). lt(b, a)` | Flipping a > b gives b < a. |
| `gt_of_lt(a, b, h)` | `∀ a: Nat, b: Nat, h: lt(b, a). gt(a, b)` | Flipping b < a gives a > b. |
| `add_zero_sym(x)` | `∀ x: Nat. {x == Nat.add(x, 0n) : Nat}` | Zero is a right identity for addition: x + 0 = x, reversed to rewrite toward the simple side. |
| `zero_add_sym(x)` | `∀ -x: Nat. {x == Nat.add(0n, x) : Nat}` | Zero is a left identity for addition: 0 + x = x, reversed to rewrite toward the simple side. |
| `add_succ_sym(n, m)` | `∀ n: Nat, -m: Nat. {1n+Nat.add(n, m) == Nat.add(n, 1n+m) : Nat}` | Adding a successor on the right: n + (m + 1) = (n + m) + 1, reversed to rewrite toward the simple side. |
| `succ_add_sym(n, m)` | `∀ -n: Nat, -m: Nat. {1n+Nat.add(n, m) == Nat.add(1n+n, m) : Nat}` | Adding a successor on the left: (n + 1) + m = (n + m) + 1, reversed to rewrite toward the simple side. |
| `add_comm_sym(n, m)` | `∀ n: Nat, m: Nat. {Nat.add(m, n) == Nat.add(n, m) : Nat}` | Addition is commutative: n + m = m + n, reversed to rewrite toward the simple side. |
| `add_assoc_sym(a, b, c)` | `∀ a: Nat, -b: Nat, -c: Nat. {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}` | Addition is associative: (a + b) + c = a + (b + c), reversed to rewrite toward the simple side. |
| `add_left_comm_sym(a, b, c)` | `∀ a: Nat, b: Nat, -c: Nat. {Nat.add(b, Nat.add(a, c)) == Nat.add(a, Nat.add(b, c)) : Nat}` | Left commutativity of addition: a + (b + c) = b + (a + c), reversed to rewrite toward the simple side. |
| `add_right_comm_sym(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.add(Nat.add(a, c), b) == Nat.add(Nat.add(a, b), c) : Nat}` | Right commutativity of addition: (a + b) + c = (a + c) + b, reversed to rewrite toward the simple side. |
| `add_add_add_comm_sym(a, b, c, d)` | `∀ a: Nat, b: Nat, c: Nat, -d: Nat. {Nat.add(Nat.add(a, c), Nat.add(b, d)) == Nat.add(Nat.add(a, b), Nat.add(c, d)) : Nat}` | Four-way regrouping of a sum: (a + b) + (c + d) = (a + c) + (b + d), reversed to rewrite toward the simple side. |
| `mul_zero_sym(x)` | `∀ x: Nat. {0n == Nat.mul(x, 0n) : Nat}` | Zero absorbs multiplication on the right: x * 0 = 0, reversed to rewrite toward the simple side. |
| `zero_mul_sym(x)` | `∀ -x: Nat. {0n == Nat.mul(0n, x) : Nat}` | Zero absorbs multiplication on the left: 0 * x = 0, reversed to rewrite toward the simple side. |
| `mul_one_sym(x)` | `∀ x: Nat. {x == Nat.mul(x, 1n) : Nat}` | One is a right identity for multiplication: x * 1 = x, reversed to rewrite toward the simple side. |
| `one_mul_sym(x)` | `∀ x: Nat. {x == Nat.mul(1n, x) : Nat}` | One is a left identity for multiplication: 1 * x = x, reversed to rewrite toward the simple side. |
| `mul_succ_sym(n, m)` | `∀ n: Nat, m: Nat. {Nat.add(Nat.mul(n, m), n) == Nat.mul(n, 1n+m) : Nat}` | Multiplying by a successor on the right: n * (m + 1) = n * m + n, reversed to rewrite toward the simple side. |
| `succ_mul_sym(n, m)` | `∀ n: Nat, m: Nat. {Nat.add(Nat.mul(n, m), m) == Nat.mul(1n+n, m) : Nat}` | Multiplying by a successor on the left: (n + 1) * m = n * m + m, reversed to rewrite toward the simple side. |
| `mul_comm_sym(n, m)` | `∀ n: Nat, m: Nat. {Nat.mul(m, n) == Nat.mul(n, m) : Nat}` | Multiplication is commutative: n * m = m * n, reversed to rewrite toward the simple side. |
| `add_mul_sym(a, b, c)` | `∀ a: Nat, -b: Nat, c: Nat. {Nat.add(Nat.mul(a, c), Nat.mul(b, c)) == Nat.mul(Nat.add(a, b), c) : Nat}` | Multiplication distributes over addition on the right: (a + b) * c = a * c + b * c, reversed to rewrite toward the simple side. |
| `mul_add_sym(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == Nat.mul(a, Nat.add(b, c)) : Nat}` | Multiplication distributes over addition on the left: a * (b + c) = a * b + a * c, reversed to rewrite toward the simple side. |
| `mul_assoc_sym(a, b, c)` | `∀ a: Nat, b: Nat, c: Nat. {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(Nat.mul(a, b), c) : Nat}` | Multiplication is associative: (a * b) * c = a * (b * c), reversed to rewrite toward the simple side. |

119 lemmas. Generated by `tools/mathlib/index.ts`.
