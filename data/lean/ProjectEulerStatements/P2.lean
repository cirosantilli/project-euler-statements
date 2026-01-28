namespace ProjectEulerStatements.P2

def fib : Nat -> Nat
  | 0       => 1
  | 1       => 2
  | n + 2   => fib (n) + fib (n + 1)

partial def naive (n : Nat) : Nat :=
  let rec go (i total : Nat) : Nat :=
    let f := fib i
    if f <= n then
      go (i + 1) (if f % 2 = 0 then total + f else total)
    else
      total
  go 0 0

end ProjectEulerStatements.P2
