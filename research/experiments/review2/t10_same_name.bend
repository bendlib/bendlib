import Base
import ./ma/m.bend as MList
import ./mb/m.bend as MString

def a(xs: List<&2, Nat>) -> {List.append(&2, Nat, xs, Nil{}) == xs : List<&2, Nat>}:
  MList.append_assoc(xs)

def b(s: String) -> {String.append(s, "") == s : String}:
  MString.append_assoc(s)
