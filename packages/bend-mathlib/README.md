# bend-mathlib

Machine-checked lemmas for Bend 2, checked with `bend 2.0.27`.

Rewriting: `%e : P` replaces the right side of `e` with its left side, so `name` expands the simple
side into the compound one and `name_sym` simplifies the compound side.

Rows marked `next` are proved in this repository but not yet published: the import lines above do not contain them yet.

## bool

```python
import bend-mathlib@0.1.0.1/bool.bend as MBool
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
| `and_self(a)` | `∀ a: Bool. {Bool.and(a, a) == a : Bool}` | And with itself: a and a is a. | next |
| `or_self(a)` | `∀ a: Bool. {Bool.or(a, a) == a : Bool}` | Or with itself: a or a is a. | next |
| `and_not_self(a)` | `∀ a: Bool. {Bool.and(a, Bool.not(a)) == False{} : Bool}` | A boolean and its negation are never both true: a and (not a) is false. | next |
| `or_not_self(a)` | `∀ a: Bool. {Bool.or(a, Bool.not(a)) == True{} : Bool}` | A boolean or its negation is always true: a or (not a) is true. | next |
| `and_or_distrib_left(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.and(a, Bool.or(b, c)) == Bool.or(Bool.and(a, b), Bool.and(a, c)) : Bool}` | And distributes over or: a and (b or c) is (a and b) or (a and c). | next |
| `or_and_distrib_left(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.or(a, Bool.and(b, c)) == Bool.and(Bool.or(a, b), Bool.or(a, c)) : Bool}` | Or distributes over and: a or (b and c) is (a or b) and (a or c). | next |
| `and_or_absorb(a, b)` | `∀ a: Bool, -b: Bool. {Bool.and(a, Bool.or(a, b)) == a : Bool}` | Absorption: a and (a or b) is a. | next |
| `or_and_absorb(a, b)` | `∀ a: Bool, -b: Bool. {Bool.or(a, Bool.and(a, b)) == a : Bool}` | Absorption: a or (a and b) is a. | next |
| `xor_comm(a, b)` | `∀ a: Bool, b: Bool. {Bool.xor(a, b) == Bool.xor(b, a) : Bool}` | Exclusive or is commutative. | next |
| `xor_assoc(a, b, c)` | `∀ a: Bool, b: Bool, c: Bool. {Bool.xor(Bool.xor(a, b), c) == Bool.xor(a, Bool.xor(b, c)) : Bool}` | Exclusive or is associative. | next |
| `xor_self(a)` | `∀ a: Bool. {Bool.xor(a, a) == False{} : Bool}` | A boolean xor itself is false. | next |
| `xor_false(a)` | `∀ a: Bool. {Bool.xor(a, False{}) == a : Bool}` | False is an identity for xor: a xor false is a. | next |
| `xor_true(a)` | `∀ a: Bool. {Bool.xor(a, True{}) == Bool.not(a) : Bool}` | Xor with true negates: a xor true is not a. | next |
| `not_inj(a, b, h)` | `∀ a: Bool, b: Bool, h: {Bool.not(a) == Bool.not(b) : Bool}. {a == b : Bool}` | Negation is injective: not a = not b implies a = b. | next |
| `eq_true_of_ne_false(a, h)` | `∀ a: Bool, h: {a == False{} : Bool} -> Empty. {a == True{} : Bool}` | A boolean that is not false is true. | next |
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
| `and_self_sym(a)` | `∀ a: Bool. {a == Bool.and(a, a) : Bool}` | And with itself: a and a is a, reversed to rewrite toward the simple side. | next |
| `or_self_sym(a)` | `∀ a: Bool. {a == Bool.or(a, a) : Bool}` | Or with itself: a or a is a, reversed to rewrite toward the simple side. | next |
| `and_not_self_sym(a)` | `∀ a: Bool. {False{} == Bool.and(a, Bool.not(a)) : Bool}` | A boolean and its negation are never both true: a and (not a) is false, reversed to rewrite toward the simple side. | next |
| `or_not_self_sym(a)` | `∀ a: Bool. {True{} == Bool.or(a, Bool.not(a)) : Bool}` | A boolean or its negation is always true: a or (not a) is true, reversed to rewrite toward the simple side. | next |
| `and_or_distrib_left_sym(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.or(Bool.and(a, b), Bool.and(a, c)) == Bool.and(a, Bool.or(b, c)) : Bool}` | And distributes over or: a and (b or c) is (a and b) or (a and c), reversed to rewrite toward the simple side. | next |
| `or_and_distrib_left_sym(a, b, c)` | `∀ a: Bool, -b: Bool, -c: Bool. {Bool.and(Bool.or(a, b), Bool.or(a, c)) == Bool.or(a, Bool.and(b, c)) : Bool}` | Or distributes over and: a or (b and c) is (a or b) and (a or c), reversed to rewrite toward the simple side. | next |
| `and_or_absorb_sym(a, b)` | `∀ a: Bool, -b: Bool. {a == Bool.and(a, Bool.or(a, b)) : Bool}` | Absorption: a and (a or b) is a, reversed to rewrite toward the simple side. | next |
| `or_and_absorb_sym(a, b)` | `∀ a: Bool, -b: Bool. {a == Bool.or(a, Bool.and(a, b)) : Bool}` | Absorption: a or (a and b) is a, reversed to rewrite toward the simple side. | next |
| `xor_comm_sym(a, b)` | `∀ a: Bool, b: Bool. {Bool.xor(b, a) == Bool.xor(a, b) : Bool}` | Exclusive or is commutative, reversed to rewrite toward the simple side. | next |
| `xor_assoc_sym(a, b, c)` | `∀ a: Bool, b: Bool, c: Bool. {Bool.xor(a, Bool.xor(b, c)) == Bool.xor(Bool.xor(a, b), c) : Bool}` | Exclusive or is associative, reversed to rewrite toward the simple side. | next |
| `xor_self_sym(a)` | `∀ a: Bool. {False{} == Bool.xor(a, a) : Bool}` | A boolean xor itself is false, reversed to rewrite toward the simple side. | next |
| `xor_false_sym(a)` | `∀ a: Bool. {a == Bool.xor(a, False{}) : Bool}` | False is an identity for xor: a xor false is a, reversed to rewrite toward the simple side. | next |
| `xor_true_sym(a)` | `∀ a: Bool. {Bool.not(a) == Bool.xor(a, True{}) : Bool}` | Xor with true negates: a xor true is not a, reversed to rewrite toward the simple side. | next |

## equal

```python
import bend-mathlib@0.1.0.1/equal.bend as MEqual
```

| lemma | statement | meaning | since |
|---|---|---|---|
| `cong2(A, B, C, f, a1, a2, b1, b2, ea, eb)` | `∀ -A: Type, -B: Type, -C: Type, -f: A -> B -> C, -a1: A, -a2: A, -b1: B, -b2: B, ea: {a1 == a2 : A}, eb: {b1 == b2 : B}. {f(a1, b1) == f(a2, b2) : C}` | Applying a two-argument function to equal arguments gives equal results. | 0.1.0.0 |
| `subst(A, P, a, b, e, p)` | `∀ -A: Type, -P: A -> Type, -a: A, -b: A, e: {a == b : A}, p: P(a). P(b)` | If a equals b, any property of a is also a property of b. | 0.1.0.0 |
| `trans3(A, a, b, c, d, ab, bc, cd)` | `∀ -A: Type, -a: A, -b: A, -c: A, -d: A, ab: {a == b : A}, bc: {b == c : A}, cd: {c == d : A}. {a == d : A}` | Equality chains through three steps: a = b, b = c and c = d give a = d. | 0.1.0.0 |
| `cong_succ(a, b, e)` | `∀ -a: Nat, -b: Nat, e: {a == b : Nat}. {1n+a == 1n+b : Nat}` | Equal naturals have equal successors. | 0.1.0.0 |

## list

```python
import bend-mathlib@0.1.0.1/list.bend as MList
```

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

## nat

```python
import bend-mathlib@0.1.0.1/nat.bend as MNat
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
| `sub_zero(n)` | `∀ n: Nat. {Nat.sub(n, 0n) == n : Nat}` | Subtracting zero changes nothing: n - 0 = n. | next |
| `zero_sub(n)` | `∀ n: Nat. {Nat.sub(0n, n) == 0n : Nat}` | Truncated subtraction from zero is zero: 0 - n = 0. | next |
| `sub_self(n)` | `∀ n: Nat. {Nat.sub(n, n) == 0n : Nat}` | A natural minus itself is zero: n - n = 0. | next |
| `succ_sub_succ(n, m)` | `∀ -n: Nat, -m: Nat. {Nat.sub(1n+n, 1n+m) == Nat.sub(n, m) : Nat}` | Subtracting successors: (n + 1) - (m + 1) = n - m. | next |
| `add_sub_cancel(n, m)` | `∀ n: Nat, m: Nat. {Nat.sub(Nat.add(n, m), m) == n : Nat}` | Adding then subtracting m cancels: (n + m) - m = n. | next |
| `add_sub_cancel_left(n, m)` | `∀ n: Nat, m: Nat. {Nat.sub(Nat.add(n, m), n) == m : Nat}` | Adding then subtracting n cancels: (n + m) - n = m. | next |
| `sub_add_cancel(n, m, h)` | `∀ n: Nat, m: Nat, h: le(m, n). {Nat.add(Nat.sub(n, m), m) == n : Nat}` | If m <= n, subtracting and adding m back gives n: (n - m) + m = n. | next |
| `sub_sub(n, m, k)` | `∀ n: Nat, m: Nat, k: Nat. {Nat.sub(Nat.sub(n, m), k) == Nat.sub(n, Nat.add(m, k)) : Nat}` | Subtracting twice is subtracting the sum: (n - m) - k = n - (m + k). | next |
| `sub_le(n, m)` | `∀ n: Nat, m: Nat. le(Nat.sub(n, m), n)` | Truncated subtraction never increases: n - m <= n. | next |
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
| `sub_zero_sym(n)` | `∀ n: Nat. {n == Nat.sub(n, 0n) : Nat}` | Subtracting zero changes nothing: n - 0 = n, reversed to rewrite toward the simple side. | next |
| `zero_sub_sym(n)` | `∀ n: Nat. {0n == Nat.sub(0n, n) : Nat}` | Truncated subtraction from zero is zero: 0 - n = 0, reversed to rewrite toward the simple side. | next |
| `sub_self_sym(n)` | `∀ n: Nat. {0n == Nat.sub(n, n) : Nat}` | A natural minus itself is zero: n - n = 0, reversed to rewrite toward the simple side. | next |
| `succ_sub_succ_sym(n, m)` | `∀ -n: Nat, -m: Nat. {Nat.sub(n, m) == Nat.sub(1n+n, 1n+m) : Nat}` | Subtracting successors: (n + 1) - (m + 1) = n - m, reversed to rewrite toward the simple side. | next |
| `add_sub_cancel_sym(n, m)` | `∀ n: Nat, m: Nat. {n == Nat.sub(Nat.add(n, m), m) : Nat}` | Adding then subtracting m cancels: (n + m) - m = n, reversed to rewrite toward the simple side. | next |
| `add_sub_cancel_left_sym(n, m)` | `∀ n: Nat, m: Nat. {m == Nat.sub(Nat.add(n, m), n) : Nat}` | Adding then subtracting n cancels: (n + m) - n = m, reversed to rewrite toward the simple side. | next |
| `sub_sub_sym(n, m, k)` | `∀ n: Nat, m: Nat, k: Nat. {Nat.sub(n, Nat.add(m, k)) == Nat.sub(Nat.sub(n, m), k) : Nat}` | Subtracting twice is subtracting the sum: (n - m) - k = n - (m + k), reversed to rewrite toward the simple side. | next |

163 lemmas. Generated by `tools/mathlib/index.ts`.
