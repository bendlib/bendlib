import Base

law and_self:
  for a: Bool
  {Bool.and(a, a) == a : Bool}

law or_self:
  for a: Bool
  {Bool.or(a, a) == a : Bool}

law and_not_self:
  for a: Bool
  {Bool.and(a, Bool.not(a)) == False{} : Bool}

law or_not_self:
  for a: Bool
  {Bool.or(a, Bool.not(a)) == True{} : Bool}

law and_or_distrib_left:
  for a: Bool
  for b: Bool
  for c: Bool
  {Bool.and(a, Bool.or(b, c)) == Bool.or(Bool.and(a, b), Bool.and(a, c)) : Bool}

law or_and_distrib_left:
  for a: Bool
  for b: Bool
  for c: Bool
  {Bool.or(a, Bool.and(b, c)) == Bool.and(Bool.or(a, b), Bool.or(a, c)) : Bool}

law and_or_absorb:
  for a: Bool
  for b: Bool
  {Bool.and(a, Bool.or(a, b)) == a : Bool}

law or_and_absorb:
  for a: Bool
  for b: Bool
  {Bool.or(a, Bool.and(a, b)) == a : Bool}

law xor_comm:
  for a: Bool
  for b: Bool
  {Bool.xor(a, b) == Bool.xor(b, a) : Bool}

law xor_assoc:
  for a: Bool
  for b: Bool
  for c: Bool
  {Bool.xor(Bool.xor(a, b), c) == Bool.xor(a, Bool.xor(b, c)) : Bool}

law xor_self:
  for a: Bool
  {Bool.xor(a, a) == False{} : Bool}

law xor_false:
  for a: Bool
  {Bool.xor(a, False{}) == a : Bool}

law xor_true:
  for a: Bool
  {Bool.xor(a, True{}) == Bool.not(a) : Bool}

law not_inj:
  for a: Bool
  for b: Bool
  for h: {Bool.not(a) == Bool.not(b) : Bool}
  {a == b : Bool}

law eq_true_of_ne_false:
  for a: Bool
  for h: {a == False{} : Bool} -> Empty
  {a == True{} : Bool}
