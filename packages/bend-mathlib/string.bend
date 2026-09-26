# bend-mathlib/string.bend: String append, reverse and length, and comparison.
# Comparison descends String.eq -> String.cmp -> Char.cmp -> U32.cmp -> Word.cmp.
import Base
import ./bool.bend as MBool

def internal_false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def internal_append_nil(a: String) -> {a == String.append(a, SNil{}) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %internal_append_nil(t) : {SCon{h, t} == SCon{h, _} : String}
      {==}

# The empty string is a right identity for append: a ++ "" = a.
law append_nil:
  for a: String
  {String.append(a, SNil{}) == a : String}

def append_nil(a):
  Equal.sym(String, a, String.append(a, SNil{}), internal_append_nil(a))

# The empty string is a left identity for append: "" ++ a = a.
law nil_append:
  for -a: String
  {String.append(SNil{}, a) == a : String}

def nil_append(a):
  {==}

def internal_append_assoc(a: String, -b: String, -c: String) -> {String.append(a, String.append(b, c)) == String.append(String.append(a, b), c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %internal_append_assoc(t, b, c) : {SCon{h, String.append(t, String.append(b, c))} == SCon{h, _} : String}
      {==}

# Append is associative: (a ++ b) ++ c = a ++ (b ++ c).
law append_assoc:
  for a: String
  for -b: String
  for -c: String
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}

def append_assoc(a, b, c):
  Equal.sym(String, String.append(a, String.append(b, c)), String.append(String.append(a, b), c), internal_append_assoc(a, b, c))

def internal_length_append(a: String, -b: String) -> {Nat.add(String.length(a), String.length(b)) == String.length(String.append(a, b)) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %internal_length_append(t, b) : {1n+Nat.add(String.length(t), String.length(b)) == 1n+_ : Nat}
      {==}

# The length of an append is the sum of the lengths.
law length_append:
  for a: String
  for -b: String
  {String.length(String.append(a, b)) == Nat.add(String.length(a), String.length(b)) : Nat}

def length_append(a, b):
  Equal.sym(Nat, Nat.add(String.length(a), String.length(b)), String.length(String.append(a, b)), internal_length_append(a, b))

def internal_reverse_go_spec(s: String, +acc: String) -> {String.append(String.reverse(s), acc) == String.reverse.go(s, acc) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %internal_reverse_go_spec(t, SCon{h, SNil{}}) : {String.append(_, acc) == String.reverse.go(t, SCon{h, acc}) : String}
      %internal_append_assoc(String.reverse(t), SCon{h, SNil{}}, acc) : {_ == String.reverse.go(t, SCon{h, acc}) : String}
      %internal_reverse_go_spec(t, SCon{h, acc}) : {String.append(String.reverse(t), SCon{h, acc}) == _ : String}
      {==}

# The reverse accumulator loop appends the reversed string to the accumulator.
law reverse_go_spec:
  for s: String
  for acc: String
  {String.reverse.go(s, acc) == String.append(String.reverse(s), acc) : String}

def reverse_go_spec(s, acc):
  Equal.sym(String, String.append(String.reverse(s), acc), String.reverse.go(s, acc), internal_reverse_go_spec(s, acc))

def internal_reverse_append(a: String, +b: String) -> {String.append(String.reverse(b), String.reverse(a)) == String.reverse(String.append(a, b)) : String}:
  match a:
    case SNil{}:
      %internal_append_nil(String.reverse(b)) : {_ == String.reverse(b) : String}
      {==}
    case SCon{+h, +t}:
      %internal_reverse_go_spec(t, SCon{h, SNil{}}) : {String.append(String.reverse(b), _) == String.reverse.go(String.append(t, b), SCon{h, SNil{}}) : String}
      %internal_reverse_go_spec(String.append(t, b), SCon{h, SNil{}}) : {String.append(String.reverse(b), String.append(String.reverse(t), SCon{h, SNil{}})) == _ : String}
      %internal_reverse_append(t, b) : {String.append(String.reverse(b), String.append(String.reverse(t), SCon{h, SNil{}})) == String.append(_, SCon{h, SNil{}}) : String}
      %internal_append_assoc(String.reverse(b), String.reverse(t), SCon{h, SNil{}}) : {String.append(String.reverse(b), String.append(String.reverse(t), SCon{h, SNil{}})) == _ : String}
      {==}

# Reversing an append reverses and swaps the parts: reverse (a ++ b) = reverse b ++ reverse a.
law reverse_append:
  for a: String
  for b: String
  {String.reverse(String.append(a, b)) == String.append(String.reverse(b), String.reverse(a)) : String}

def reverse_append(a, b):
  Equal.sym(String, String.append(String.reverse(b), String.reverse(a)), String.reverse(String.append(a, b)), internal_reverse_append(a, b))

def internal_reverse_reverse(a: String) -> {a == String.reverse(String.reverse(a)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %internal_reverse_go_spec(t, SCon{h, SNil{}}) : {SCon{h, t} == String.reverse.go(_, SNil{}) : String}
      %internal_reverse_append(String.reverse(t), SCon{h, SNil{}}) : {SCon{h, t} == _ : String}
      %internal_reverse_reverse(t) : {SCon{h, t} == String.append(String.reverse(SCon{h, SNil{}}), _) : String}
      {==}

# Reversing twice gives the string back.
law reverse_reverse:
  for a: String
  {String.reverse(String.reverse(a)) == a : String}

def reverse_reverse(a):
  Equal.sym(String, a, String.reverse(String.reverse(a)), internal_reverse_reverse(a))

def internal_word_cmp_refl(n: Nat, w: Word(n)) -> {EQ{} == Word.cmp(n, w, w) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{ab, at}:
          %internal_word_cmp_refl(p, at) : {EQ{} == Word.cmp.fin(ab, ab, _) : Cmp}
          %Equal.sym(Cmp, Bool.cmp(ab, ab), EQ{}, MBool.cmp_refl(ab)) : {EQ{} == _ : Cmp}
          {==}

def internal_u32_cmp_refl(x: U32) -> {EQ{} == U32.cmp(x, x) : Cmp}:
  match x:
    case U32{w}:
      %internal_word_cmp_refl(32n, w) : {EQ{} == _ : Cmp}
      {==}

# Comparing a U32 with itself gives EQ.
law u32_cmp_refl:
  for x: U32
  {U32.cmp(x, x) == EQ{} : Cmp}

def u32_cmp_refl(x):
  Equal.sym(Cmp, EQ{}, U32.cmp(x, x), internal_u32_cmp_refl(x))

def internal_char_cmp_refl(c: Char) -> {((c, c), EQ{}) == Char.cmp(c, c) : (Char & Char) & Cmp}:
  match c:
    case Chr{x}:
      %internal_u32_cmp_refl(x) : {((Chr{x}, Chr{x}), EQ{}) == ((Chr{x}, Chr{x}), _) : (Char & Char) & Cmp}
      {==}

# Comparing a character with itself gives EQ and hands both back.
law char_cmp_refl:
  for c: Char
  {Char.cmp(c, c) == ((c, c), EQ{}) : (Char & Char) & Cmp}

def char_cmp_refl(c):
  Equal.sym((Char & Char) & Cmp, ((c, c), EQ{}), Char.cmp(c, c), internal_char_cmp_refl(c))

def internal_cmp_refl(s: String) -> {((s, s), EQ{}) == String.cmp(s, s) : (String & String) & Cmp}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          %internal_u32_cmp_refl(x) : {((SCon{Chr{x}, t}, SCon{Chr{x}, t}), EQ{}) == String.cmp.fin(t, t, ((Chr{x}, Chr{x}), _)) : (String & String) & Cmp}
          %internal_cmp_refl(t) : {((SCon{Chr{x}, t}, SCon{Chr{x}, t}), EQ{}) == String.cmp.rec(Chr{x}, Chr{x}, _) : (String & String) & Cmp}
          {==}

# Comparing a string with itself gives EQ and hands both back.
law cmp_refl:
  for s: String
  {String.cmp(s, s) == ((s, s), EQ{}) : (String & String) & Cmp}

def cmp_refl(s):
  Equal.sym((String & String) & Cmp, ((s, s), EQ{}), String.cmp(s, s), internal_cmp_refl(s))

# Every string is equal to itself under String.eq.
law eq_refl:
  for s: String
  {String.eq(s, s) == True{} : Bool}

def eq_refl(s):
  %internal_cmp_refl(s) : {String.eq.fin(_) == True{} : Bool}
  {==}

def internal_fin_head(ab: Bool, bb: Bool, c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}) -> {ab == bb : Bool}:
  match c:
    case LT{}:
      Empty.absurd({ab == bb : Bool}, internal_false_ne_true(h))
    case EQ{}:
      MBool.eq_of_cmp_eq(ab, bb, h)
    case GT{}:
      Empty.absurd({ab == bb : Bool}, internal_false_ne_true(h))

def internal_fin_tail(ab: Bool, bb: Bool, c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, internal_false_ne_true(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, internal_false_ne_true(h))

def internal_word_eq(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %internal_fin_head(ab, bb, Word.cmp(p, at, bt), h) : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %internal_word_eq(p, at, bt, internal_fin_tail(ab, bb, Word.cmp(p, at, bt), h)) : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

# Two U32s that U32.is_eq calls equal are equal.
law u32_eq_of_is_eq:
  for a: U32
  for b: U32
  for h: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

def u32_eq_of_is_eq(a, b, h):
  match a b:
    case U32{x} U32{y}:
      %internal_word_eq(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

# Two characters that Char.is_eq calls equal are equal.
law char_eq_of_is_eq:
  for a: Char
  for b: Char
  for h: {Char.is_eq(a, b) == True{} : Bool}
  {a == b : Char}

def char_eq_of_is_eq(a, b, h):
  match a b:
    case Chr{x} Chr{y}:
      %u32_eq_of_is_eq(x, y, h) : {Chr{x} == Chr{_} : Char}
      {==}

def internal_rec_is_eq(h1: Char, h2: Char, rr: (String & String) & Cmp) -> {String.eq.fin(String.cmp.rec(h1, h2, rr)) == String.eq.fin(rr) : Bool}:
  match rr:
    case ((a, b), c):
      {==}

def internal_is_eq_of(c: Cmp, +d: Cmp, e: {c == d : Cmp}, h: {Cmp.is_eq(c) == True{} : Bool}) -> {Cmp.is_eq(d) == True{} : Bool}:
  %e : {Cmp.is_eq(_) == True{} : Bool}
  h

def internal_step(+x: U32, +y: U32, +t1: String, +t2: String, c: Cmp, ec: {c == U32.cmp(x, y) : Cmp}, h: {String.eq.fin(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c))) == True{} : Bool}, ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String}) -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}:
  match c:
    case LT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, internal_false_ne_true(h))
    case GT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, internal_false_ne_true(h))
    case EQ{}:
      %u32_eq_of_is_eq(x, y, internal_is_eq_of(EQ{}, U32.cmp(x, y), ec, {==})) : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %ih(Equal.trans(Bool, String.eq(t1, t2), String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))), True{}, Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))), String.eq(t1, t2), internal_rec_is_eq(Chr{x}, Chr{y}, String.cmp(t1, t2))), h)) : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}

# Two strings that String.eq calls equal are equal.
law eq_of_eq_true:
  for a: String
  for b: String
  for h: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

def eq_of_eq_true(a, b, h):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{x, t}:
      Empty.absurd({SNil{} == SCon{x, t} : String}, internal_false_ne_true(h))
    case SCon{x, t} SNil{}:
      Empty.absurd({SCon{x, t} == SNil{} : String}, internal_false_ne_true(h))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      internal_step(x, y, t1, t2, U32.cmp(x, y), {==}, h, hh => eq_of_eq_true(t1, t2, hh))

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# The empty string is a right identity for append: a ++ "" = a, reversed to rewrite toward the simple side.
law append_nil_sym:
  for a: String
  {a == String.append(a, SNil{}) : String}

def append_nil_sym(a):
  Equal.sym(String, String.append(a, SNil{}), a, append_nil(a))

# The empty string is a left identity for append: "" ++ a = a, reversed to rewrite toward the simple side.
law nil_append_sym:
  for -a: String
  {a == String.append(SNil{}, a) : String}

def nil_append_sym(a):
  Equal.sym(String, String.append(SNil{}, a), a, nil_append(a))

# Append is associative: (a ++ b) ++ c = a ++ (b ++ c), reversed to rewrite toward the simple side.
law append_assoc_sym:
  for a: String
  for -b: String
  for -c: String
  {String.append(a, String.append(b, c)) == String.append(String.append(a, b), c) : String}

def append_assoc_sym(a, b, c):
  Equal.sym(String, String.append(String.append(a, b), c), String.append(a, String.append(b, c)), append_assoc(a, b, c))

# The length of an append is the sum of the lengths, reversed to rewrite toward the simple side.
law length_append_sym:
  for a: String
  for -b: String
  {Nat.add(String.length(a), String.length(b)) == String.length(String.append(a, b)) : Nat}

def length_append_sym(a, b):
  Equal.sym(Nat, String.length(String.append(a, b)), Nat.add(String.length(a), String.length(b)), length_append(a, b))

# The reverse accumulator loop appends the reversed string to the accumulator, reversed to rewrite toward the simple side.
law reverse_go_spec_sym:
  for s: String
  for acc: String
  {String.append(String.reverse(s), acc) == String.reverse.go(s, acc) : String}

def reverse_go_spec_sym(s, acc):
  Equal.sym(String, String.reverse.go(s, acc), String.append(String.reverse(s), acc), reverse_go_spec(s, acc))

# Reversing an append reverses and swaps the parts: reverse (a ++ b) = reverse b ++ reverse a, reversed to rewrite toward the simple side.
law reverse_append_sym:
  for a: String
  for b: String
  {String.append(String.reverse(b), String.reverse(a)) == String.reverse(String.append(a, b)) : String}

def reverse_append_sym(a, b):
  Equal.sym(String, String.reverse(String.append(a, b)), String.append(String.reverse(b), String.reverse(a)), reverse_append(a, b))

# Reversing twice gives the string back, reversed to rewrite toward the simple side.
law reverse_reverse_sym:
  for a: String
  {a == String.reverse(String.reverse(a)) : String}

def reverse_reverse_sym(a):
  Equal.sym(String, String.reverse(String.reverse(a)), a, reverse_reverse(a))

# Comparing a U32 with itself gives EQ, reversed to rewrite toward the simple side.
law u32_cmp_refl_sym:
  for x: U32
  {EQ{} == U32.cmp(x, x) : Cmp}

def u32_cmp_refl_sym(x):
  Equal.sym(Cmp, U32.cmp(x, x), EQ{}, u32_cmp_refl(x))

# Comparing a character with itself gives EQ and hands both back, reversed to rewrite toward the simple side.
law char_cmp_refl_sym:
  for c: Char
  {((c, c), EQ{}) == Char.cmp(c, c) : (Char & Char) & Cmp}

def char_cmp_refl_sym(c):
  Equal.sym((Char & Char) & Cmp, Char.cmp(c, c), ((c, c), EQ{}), char_cmp_refl(c))

# Comparing a string with itself gives EQ and hands both back, reversed to rewrite toward the simple side.
law cmp_refl_sym:
  for s: String
  {((s, s), EQ{}) == String.cmp(s, s) : (String & String) & Cmp}

def cmp_refl_sym(s):
  Equal.sym((String & String) & Cmp, String.cmp(s, s), ((s, s), EQ{}), cmp_refl(s))

# Every string is equal to itself under String.eq, reversed to rewrite toward the simple side.
law eq_refl_sym:
  for s: String
  {True{} == String.eq(s, s) : Bool}

def eq_refl_sym(s):
  Equal.sym(Bool, String.eq(s, s), True{}, eq_refl(s))
