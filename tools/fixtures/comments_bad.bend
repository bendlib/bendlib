# One.
# Two.
# Three.
# Four.
import Base

# lowercase and no period
law append_nil:
  for xs: List<&2, Nat>
  {List.append(&2, Nat, xs, Nil{}) == xs : List<&2, Nat>}

def append_nil(xs):
  # TODO make this generic
  # def old_append_nil(xs):
  {==}
