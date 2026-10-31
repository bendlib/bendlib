import Base

# U32.add hides the value from lawcheck's size prediction, so a huge instance really runs.
law to_nat_le_self:
  for a: U32
  {Nat.is_le(U32.to_nat(a), U32.to_nat(U32.add(a, 0))) == True{} : Bool}
