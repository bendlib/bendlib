import Base

law append_assoc:
  for s: String
  {String.append(s, "") == s : String}

def append_assoc(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %append_assoc(t) : {SCon{h, String.append(t, "")} == SCon{h, _} : String}
      {==}
