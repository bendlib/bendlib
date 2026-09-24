import Base

law s1:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def s1(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %s1(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

law s2:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def s2(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %s2(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

law s3:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def s3(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %s3(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

law s4:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def s4(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %s4(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

law s5:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def s5(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %s5(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

law s6:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def s6(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %s6(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

law s7:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def s7(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %s7(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

law s8:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def s8(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %s8(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

law s9:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def s9(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %s9(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

law s10:
  for x: Nat
  for y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def s10(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %s10(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}
