import ProjectEulerStatements.Lib.TruncatablePrimesTree

/-! Small independent certificates for the bounded right-prime tree and its
proper truncations. No declaration enumerates the full million-value interval. -/
namespace ProjectEulerStatements.TruncatablePrimes

set_option Elab.async false
set_option maxRecDepth 10000

private theorem children_2 : children 2 = [23, 29] := by
  norm_num [children, P37.isPrime]

private theorem children_3 : children 3 = [31, 37] := by
  norm_num [children, P37.isPrime]

private theorem children_5 : children 5 = [53, 59] := by
  norm_num [children, P37.isPrime]

private theorem children_7 : children 7 = [71, 73, 79] := by
  norm_num [children, P37.isPrime]

private theorem children_23 : children 23 = [233, 239] := by
  norm_num [children, P37.isPrime]

private theorem children_29 : children 29 = [293] := by
  norm_num [children, P37.isPrime]

private theorem children_31 : children 31 = [311, 313, 317] := by
  norm_num [children, P37.isPrime]

private theorem children_37 : children 37 = [373, 379] := by
  norm_num [children, P37.isPrime]

private theorem children_53 : children 53 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_59 : children 59 = [593, 599] := by
  norm_num [children, P37.isPrime]

private theorem children_71 : children 71 = [719] := by
  norm_num [children, P37.isPrime]

private theorem children_73 : children 73 = [733, 739] := by
  norm_num [children, P37.isPrime]

private theorem children_79 : children 79 = [797] := by
  norm_num [children, P37.isPrime]

private theorem children_233 : children 233 = [2333, 2339] := by
  norm_num [children, P37.isPrime]

private theorem children_239 : children 239 = [2393, 2399] := by
  norm_num [children, P37.isPrime]

private theorem children_293 : children 293 = [2939] := by
  norm_num [children, P37.isPrime]

private theorem children_311 : children 311 = [3119] := by
  norm_num [children, P37.isPrime]

private theorem children_313 : children 313 = [3137] := by
  norm_num [children, P37.isPrime]

private theorem children_317 : children 317 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_373 : children 373 = [3733, 3739] := by
  norm_num [children, P37.isPrime]

private theorem children_379 : children 379 = [3793, 3797] := by
  norm_num [children, P37.isPrime]

private theorem children_593 : children 593 = [5939] := by
  norm_num [children, P37.isPrime]

private theorem children_599 : children 599 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_719 : children 719 = [7193] := by
  norm_num [children, P37.isPrime]

private theorem children_733 : children 733 = [7331, 7333] := by
  norm_num [children, P37.isPrime]

private theorem children_739 : children 739 = [7393] := by
  norm_num [children, P37.isPrime]

private theorem children_797 : children 797 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_2333 : children 2333 = [23333, 23339] := by
  norm_num [children, P37.isPrime]

private theorem children_2339 : children 2339 = [23399] := by
  norm_num [children, P37.isPrime]

private theorem children_2393 : children 2393 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_2399 : children 2399 = [23993] := by
  norm_num [children, P37.isPrime]

private theorem children_2939 : children 2939 = [29399] := by
  norm_num [children, P37.isPrime]

private theorem children_3119 : children 3119 = [31193] := by
  norm_num [children, P37.isPrime]

private theorem children_3137 : children 3137 = [31379] := by
  norm_num [children, P37.isPrime]

private theorem children_3733 : children 3733 = [37337, 37339] := by
  norm_num [children, P37.isPrime]

private theorem children_3739 : children 3739 = [37397] := by
  norm_num [children, P37.isPrime]

private theorem children_3793 : children 3793 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_3797 : children 3797 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_5939 : children 5939 = [59393, 59399] := by
  norm_num [children, P37.isPrime]

private theorem children_7193 : children 7193 = [71933] := by
  norm_num [children, P37.isPrime]

private theorem children_7331 : children 7331 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_7333 : children 7333 = [73331] := by
  norm_num [children, P37.isPrime]

private theorem children_7393 : children 7393 = [73939] := by
  norm_num [children, P37.isPrime]

private theorem children_23333 : children 23333 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_23339 : children 23339 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_23399 : children 23399 = [233993] := by
  norm_num [children, P37.isPrime]

private theorem children_23993 : children 23993 = [239933] := by
  norm_num [children, P37.isPrime]

private theorem children_29399 : children 29399 = [293999] := by
  norm_num [children, P37.isPrime]

private theorem children_31193 : children 31193 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_31379 : children 31379 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_37337 : children 37337 = [373379] := by
  norm_num [children, P37.isPrime]

private theorem children_37339 : children 37339 = [373393] := by
  norm_num [children, P37.isPrime]

private theorem children_37397 : children 37397 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_59393 : children 59393 = [593933] := by
  norm_num [children, P37.isPrime]

private theorem children_59399 : children 59399 = [593993] := by
  norm_num [children, P37.isPrime]

private theorem children_71933 : children 71933 = [719333] := by
  norm_num [children, P37.isPrime]

private theorem children_73331 : children 73331 = [] := by
  norm_num [children, P37.isPrime]

private theorem children_73939 : children 73939 = [739391, 739393, 739397, 739399] := by
  norm_num [children, P37.isPrime]

def rightValues : List Nat :=
  [2, 3, 5, 7] ++
  [23, 29, 31, 37, 53, 59, 71, 73, 79] ++
  [233, 239, 293, 311, 313, 317, 373, 379, 593, 599, 719, 733, 739, 797] ++
  [2333, 2339, 2393, 2399, 2939, 3119, 3137, 3733, 3739, 3793, 3797, 5939, 7193, 7331, 7333,
    7393] ++
  [23333, 23339, 23399, 23993, 29399, 31193, 31379, 37337, 37339, 37397, 59393, 59399, 71933,
    73331, 73939] ++
  [233993, 239933, 293999, 373379, 373393, 593933, 593993, 719333, 739391, 739393, 739397, 739399]

theorem tree_values : tree 5 = rightValues := by
  simp only [tree, roots, rightValues, List.flatMap_cons, List.flatMap_nil,
    children_2, children_3, children_5, children_7, children_23,
    children_29, children_31, children_37, children_53, children_59,
    children_71, children_73, children_79, children_233, children_239,
    children_293, children_311, children_313, children_317, children_373,
    children_379, children_593, children_599, children_719, children_733,
    children_739, children_797, children_2333, children_2339, children_2393,
    children_2399, children_2939, children_3119, children_3137, children_3733,
    children_3739, children_3793, children_3797, children_5939, children_7193,
    children_7331, children_7333, children_7393, children_23333, children_23339,
    children_23399, children_23993, children_29399, children_31193, children_31379,
    children_37337, children_37339, children_37397, children_59393, children_59399,
    children_71933, children_73331, children_73939,
    List.cons_append, List.nil_append]

private theorem accepted_2 : P37.isTruncatablePrime 2 = false := by
  decide +kernel

private theorem accepted_3 : P37.isTruncatablePrime 3 = false := by
  decide +kernel

private theorem accepted_5 : P37.isTruncatablePrime 5 = false := by
  decide +kernel

private theorem accepted_7 : P37.isTruncatablePrime 7 = false := by
  decide +kernel

private theorem accepted_23 : P37.isTruncatablePrime 23 = true := by
  have truncations : P37.truncations 23 = [3, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_29 : P37.isTruncatablePrime 29 = false := by
  have truncations : P37.truncations 29 = [9, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_31 : P37.isTruncatablePrime 31 = false := by
  have truncations : P37.truncations 31 = [1, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_37 : P37.isTruncatablePrime 37 = true := by
  have truncations : P37.truncations 37 = [7, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_53 : P37.isTruncatablePrime 53 = true := by
  have truncations : P37.truncations 53 = [3, 5] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_59 : P37.isTruncatablePrime 59 = false := by
  have truncations : P37.truncations 59 = [9, 5] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_71 : P37.isTruncatablePrime 71 = false := by
  have truncations : P37.truncations 71 = [1, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_73 : P37.isTruncatablePrime 73 = true := by
  have truncations : P37.truncations 73 = [3, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_79 : P37.isTruncatablePrime 79 = false := by
  have truncations : P37.truncations 79 = [9, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_233 : P37.isTruncatablePrime 233 = false := by
  have truncations : P37.truncations 233 = [33, 3, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_239 : P37.isTruncatablePrime 239 = false := by
  have truncations : P37.truncations 239 = [39, 9, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_293 : P37.isTruncatablePrime 293 = false := by
  have truncations : P37.truncations 293 = [93, 3, 29, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_311 : P37.isTruncatablePrime 311 = false := by
  have truncations : P37.truncations 311 = [11, 1, 31, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_313 : P37.isTruncatablePrime 313 = true := by
  have truncations : P37.truncations 313 = [13, 3, 31, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_317 : P37.isTruncatablePrime 317 = true := by
  have truncations : P37.truncations 317 = [17, 7, 31, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_373 : P37.isTruncatablePrime 373 = true := by
  have truncations : P37.truncations 373 = [73, 3, 37, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_379 : P37.isTruncatablePrime 379 = false := by
  have truncations : P37.truncations 379 = [79, 9, 37, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_593 : P37.isTruncatablePrime 593 = false := by
  have truncations : P37.truncations 593 = [93, 3, 59, 5] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_599 : P37.isTruncatablePrime 599 = false := by
  have truncations : P37.truncations 599 = [99, 9, 59, 5] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_719 : P37.isTruncatablePrime 719 = false := by
  have truncations : P37.truncations 719 = [19, 9, 71, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_733 : P37.isTruncatablePrime 733 = false := by
  have truncations : P37.truncations 733 = [33, 3, 73, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_739 : P37.isTruncatablePrime 739 = false := by
  have truncations : P37.truncations 739 = [39, 9, 73, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_797 : P37.isTruncatablePrime 797 = true := by
  have truncations : P37.truncations 797 = [97, 7, 79, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_2333 : P37.isTruncatablePrime 2333 = false := by
  have truncations : P37.truncations 2333 = [333, 33, 3, 233, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_2339 : P37.isTruncatablePrime 2339 = false := by
  have truncations : P37.truncations 2339 = [339, 39, 9, 233, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_2393 : P37.isTruncatablePrime 2393 = false := by
  have truncations : P37.truncations 2393 = [393, 93, 3, 239, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_2399 : P37.isTruncatablePrime 2399 = false := by
  have truncations : P37.truncations 2399 = [399, 99, 9, 239, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_2939 : P37.isTruncatablePrime 2939 = false := by
  have truncations : P37.truncations 2939 = [939, 39, 9, 293, 29, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_3119 : P37.isTruncatablePrime 3119 = false := by
  have truncations : P37.truncations 3119 = [119, 19, 9, 311, 31, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_3137 : P37.isTruncatablePrime 3137 = true := by
  have truncations : P37.truncations 3137 = [137, 37, 7, 313, 31, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_3733 : P37.isTruncatablePrime 3733 = false := by
  have truncations : P37.truncations 3733 = [733, 33, 3, 373, 37, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_3739 : P37.isTruncatablePrime 3739 = false := by
  have truncations : P37.truncations 3739 = [739, 39, 9, 373, 37, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_3793 : P37.isTruncatablePrime 3793 = false := by
  have truncations : P37.truncations 3793 = [793, 93, 3, 379, 37, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_3797 : P37.isTruncatablePrime 3797 = true := by
  have truncations : P37.truncations 3797 = [797, 97, 7, 379, 37, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_5939 : P37.isTruncatablePrime 5939 = false := by
  have truncations : P37.truncations 5939 = [939, 39, 9, 593, 59, 5] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_7193 : P37.isTruncatablePrime 7193 = false := by
  have truncations : P37.truncations 7193 = [193, 93, 3, 719, 71, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_7331 : P37.isTruncatablePrime 7331 = false := by
  have truncations : P37.truncations 7331 = [331, 31, 1, 733, 73, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_7333 : P37.isTruncatablePrime 7333 = false := by
  have truncations : P37.truncations 7333 = [333, 33, 3, 733, 73, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_7393 : P37.isTruncatablePrime 7393 = false := by
  have truncations : P37.truncations 7393 = [393, 93, 3, 739, 73, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_23333 : P37.isTruncatablePrime 23333 = false := by
  have truncations : P37.truncations 23333 = [3333, 333, 33, 3, 2333, 233, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_23339 : P37.isTruncatablePrime 23339 = false := by
  have truncations : P37.truncations 23339 = [3339, 339, 39, 9, 2333, 233, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_23399 : P37.isTruncatablePrime 23399 = false := by
  have truncations : P37.truncations 23399 = [3399, 399, 99, 9, 2339, 233, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_23993 : P37.isTruncatablePrime 23993 = false := by
  have truncations : P37.truncations 23993 = [3993, 993, 93, 3, 2399, 239, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_29399 : P37.isTruncatablePrime 29399 = false := by
  have truncations : P37.truncations 29399 = [9399, 399, 99, 9, 2939, 293, 29, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_31193 : P37.isTruncatablePrime 31193 = false := by
  have truncations : P37.truncations 31193 = [1193, 193, 93, 3, 3119, 311, 31, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_31379 : P37.isTruncatablePrime 31379 = false := by
  have truncations : P37.truncations 31379 = [1379, 379, 79, 9, 3137, 313, 31, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_37337 : P37.isTruncatablePrime 37337 = false := by
  have truncations : P37.truncations 37337 = [7337, 337, 37, 7, 3733, 373, 37, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_37339 : P37.isTruncatablePrime 37339 = false := by
  have truncations : P37.truncations 37339 = [7339, 339, 39, 9, 3733, 373, 37, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_37397 : P37.isTruncatablePrime 37397 = false := by
  have truncations : P37.truncations 37397 = [7397, 397, 97, 7, 3739, 373, 37, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_59393 : P37.isTruncatablePrime 59393 = false := by
  have truncations : P37.truncations 59393 = [9393, 393, 93, 3, 5939, 593, 59, 5] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_59399 : P37.isTruncatablePrime 59399 = false := by
  have truncations : P37.truncations 59399 = [9399, 399, 99, 9, 5939, 593, 59, 5] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_71933 : P37.isTruncatablePrime 71933 = false := by
  have truncations : P37.truncations 71933 = [1933, 933, 33, 3, 7193, 719, 71, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_73331 : P37.isTruncatablePrime 73331 = false := by
  have truncations : P37.truncations 73331 = [3331, 331, 31, 1, 7333, 733, 73, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_73939 : P37.isTruncatablePrime 73939 = false := by
  have truncations : P37.truncations 73939 = [3939, 939, 39, 9, 7393, 739, 73, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_233993 : P37.isTruncatablePrime 233993 = false := by
  have truncations : P37.truncations 233993 =
      [33993, 3993, 993, 93, 3, 23399, 2339, 233, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_239933 : P37.isTruncatablePrime 239933 = false := by
  have truncations : P37.truncations 239933 =
      [39933, 9933, 933, 33, 3, 23993, 2399, 239, 23, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_293999 : P37.isTruncatablePrime 293999 = false := by
  have truncations : P37.truncations 293999 =
      [93999, 3999, 999, 99, 9, 29399, 2939, 293, 29, 2] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_373379 : P37.isTruncatablePrime 373379 = false := by
  have truncations : P37.truncations 373379 =
      [73379, 3379, 379, 79, 9, 37337, 3733, 373, 37, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_373393 : P37.isTruncatablePrime 373393 = false := by
  have truncations : P37.truncations 373393 =
      [73393, 3393, 393, 93, 3, 37339, 3733, 373, 37, 3] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_593933 : P37.isTruncatablePrime 593933 = false := by
  have truncations : P37.truncations 593933 =
      [93933, 3933, 933, 33, 3, 59393, 5939, 593, 59, 5] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_593993 : P37.isTruncatablePrime 593993 = false := by
  have truncations : P37.truncations 593993 =
      [93993, 3993, 993, 93, 3, 59399, 5939, 593, 59, 5] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_719333 : P37.isTruncatablePrime 719333 = false := by
  have truncations : P37.truncations 719333 =
      [19333, 9333, 333, 33, 3, 71933, 7193, 719, 71, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_739391 : P37.isTruncatablePrime 739391 = false := by
  have truncations : P37.truncations 739391 =
      [39391, 9391, 391, 91, 1, 73939, 7393, 739, 73, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_739393 : P37.isTruncatablePrime 739393 = false := by
  have truncations : P37.truncations 739393 =
      [39393, 9393, 393, 93, 3, 73939, 7393, 739, 73, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_739397 : P37.isTruncatablePrime 739397 = true := by
  have truncations : P37.truncations 739397 =
      [39397, 9397, 397, 97, 7, 73939, 7393, 739, 73, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

private theorem accepted_739399 : P37.isTruncatablePrime 739399 = false := by
  have truncations : P37.truncations 739399 =
      [39399, 9399, 399, 99, 9, 73939, 7393, 739, 73, 7] := by
    decide +kernel
  norm_num [P37.isTruncatablePrime, P37.isPrime, truncations, P37.listAll]

def values : List Nat :=
  [23, 37, 53, 73, 313, 317, 373, 797, 3137, 3797, 739397]

theorem tree_accepted : (tree 5).filter P37.isTruncatablePrime = values := by
  rw [tree_values]
  simp only [rightValues, values, List.filter_cons, List.filter_nil,
    accepted_2, accepted_3, accepted_5, accepted_7, accepted_23,
    accepted_29, accepted_31, accepted_37, accepted_53, accepted_59,
    accepted_71, accepted_73, accepted_79, accepted_233, accepted_239,
    accepted_293, accepted_311, accepted_313, accepted_317, accepted_373,
    accepted_379, accepted_593, accepted_599, accepted_719, accepted_733,
    accepted_739, accepted_797, accepted_2333, accepted_2339, accepted_2393,
    accepted_2399, accepted_2939, accepted_3119, accepted_3137, accepted_3733,
    accepted_3739, accepted_3793, accepted_3797, accepted_5939, accepted_7193,
    accepted_7331, accepted_7333, accepted_7393, accepted_23333, accepted_23339,
    accepted_23399, accepted_23993, accepted_29399, accepted_31193, accepted_31379,
    accepted_37337, accepted_37339, accepted_37397, accepted_59393, accepted_59399,
    accepted_71933, accepted_73331, accepted_73939, accepted_233993, accepted_239933,
    accepted_293999, accepted_373379, accepted_373393, accepted_593933, accepted_593993,
    accepted_719333, accepted_739391, accepted_739393, accepted_739397, accepted_739399,
    Bool.false_eq_true, if_true, if_false, List.nil_append,
    List.cons_append]

theorem values_length : values.length = 11 := by decide +kernel
theorem values_sum : values.sum = 748317 := by decide +kernel
theorem values_nodup : values.Nodup := by decide +kernel
theorem values_bounds : values.all (fun n => decide (11 ≤ n ∧ n < 1000000)) = true := by
  decide +kernel

end ProjectEulerStatements.TruncatablePrimes
