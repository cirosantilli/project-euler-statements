import ProjectEulerStatements.Lib.TruncatablePrimeDigits
import Mathlib.Tactic.NormNum.Prime

/-! Local arithmetic certificates close the complete decimal prime tree.
No depth restriction is used in the arbitrary-base completeness theorem. -/
namespace ProjectEulerStatements.TruncatablePrimeBase.Decimal

set_option Elab.async false
set_option maxRecDepth 10000

private theorem children_2 : children 10 2 = [23, 29] := by
  norm_num [children, List.range']

private theorem children_3 : children 10 3 = [31, 37] := by
  norm_num [children, List.range']

private theorem children_5 : children 10 5 = [53, 59] := by
  norm_num [children, List.range']

private theorem children_7 : children 10 7 = [71, 73, 79] := by
  norm_num [children, List.range']

private theorem children_23 : children 10 23 = [233, 239] := by
  norm_num [children, List.range']

private theorem children_29 : children 10 29 = [293] := by
  norm_num [children, List.range']

private theorem children_31 : children 10 31 = [311, 313, 317] := by
  norm_num [children, List.range']

private theorem children_37 : children 10 37 = [373, 379] := by
  norm_num [children, List.range']

private theorem children_53 : children 10 53 = [] := by
  norm_num [children, List.range']

private theorem children_59 : children 10 59 = [593, 599] := by
  norm_num [children, List.range']

private theorem children_71 : children 10 71 = [719] := by
  norm_num [children, List.range']

private theorem children_73 : children 10 73 = [733, 739] := by
  norm_num [children, List.range']

private theorem children_79 : children 10 79 = [797] := by
  norm_num [children, List.range']

private theorem children_233 : children 10 233 = [2333, 2339] := by
  norm_num [children, List.range']

private theorem children_239 : children 10 239 = [2393, 2399] := by
  norm_num [children, List.range']

private theorem children_293 : children 10 293 = [2939] := by
  norm_num [children, List.range']

private theorem children_311 : children 10 311 = [3119] := by
  norm_num [children, List.range']

private theorem children_313 : children 10 313 = [3137] := by
  norm_num [children, List.range']

private theorem children_317 : children 10 317 = [] := by
  norm_num [children, List.range']

private theorem children_373 : children 10 373 = [3733, 3739] := by
  norm_num [children, List.range']

private theorem children_379 : children 10 379 = [3793, 3797] := by
  norm_num [children, List.range']

private theorem children_593 : children 10 593 = [5939] := by
  norm_num [children, List.range']

private theorem children_599 : children 10 599 = [] := by
  norm_num [children, List.range']

private theorem children_719 : children 10 719 = [7193] := by
  norm_num [children, List.range']

private theorem children_733 : children 10 733 = [7331, 7333] := by
  norm_num [children, List.range']

private theorem children_739 : children 10 739 = [7393] := by
  norm_num [children, List.range']

private theorem children_797 : children 10 797 = [] := by
  norm_num [children, List.range']

private theorem children_2333 : children 10 2333 = [23333, 23339] := by
  norm_num [children, List.range']

private theorem children_2339 : children 10 2339 = [23399] := by
  norm_num [children, List.range']

private theorem children_2393 : children 10 2393 = [] := by
  norm_num [children, List.range']

private theorem children_2399 : children 10 2399 = [23993] := by
  norm_num [children, List.range']

private theorem children_2939 : children 10 2939 = [29399] := by
  norm_num [children, List.range']

private theorem children_3119 : children 10 3119 = [31193] := by
  norm_num [children, List.range']

private theorem children_3137 : children 10 3137 = [31379] := by
  norm_num [children, List.range']

private theorem children_3733 : children 10 3733 = [37337, 37339] := by
  norm_num [children, List.range']

private theorem children_3739 : children 10 3739 = [37397] := by
  norm_num [children, List.range']

private theorem children_3793 : children 10 3793 = [] := by
  norm_num [children, List.range']

private theorem children_3797 : children 10 3797 = [] := by
  norm_num [children, List.range']

private theorem children_5939 : children 10 5939 = [59393, 59399] := by
  norm_num [children, List.range']

private theorem children_7193 : children 10 7193 = [71933] := by
  norm_num [children, List.range']

private theorem children_7331 : children 10 7331 = [] := by
  norm_num [children, List.range']

private theorem children_7333 : children 10 7333 = [73331] := by
  norm_num [children, List.range']

private theorem children_7393 : children 10 7393 = [73939] := by
  norm_num [children, List.range']

private theorem children_23333 : children 10 23333 = [] := by
  norm_num [children, List.range']

private theorem children_23339 : children 10 23339 = [] := by
  norm_num [children, List.range']

private theorem children_23399 : children 10 23399 = [233993] := by
  norm_num [children, List.range']

private theorem children_23993 : children 10 23993 = [239933] := by
  norm_num [children, List.range']

private theorem children_29399 : children 10 29399 = [293999] := by
  norm_num [children, List.range']

private theorem children_31193 : children 10 31193 = [] := by
  norm_num [children, List.range']

private theorem children_31379 : children 10 31379 = [] := by
  norm_num [children, List.range']

private theorem children_37337 : children 10 37337 = [373379] := by
  norm_num [children, List.range']

private theorem children_37339 : children 10 37339 = [373393] := by
  norm_num [children, List.range']

private theorem children_37397 : children 10 37397 = [] := by
  norm_num [children, List.range']

private theorem children_59393 : children 10 59393 = [593933] := by
  norm_num [children, List.range']

private theorem children_59399 : children 10 59399 = [593993] := by
  norm_num [children, List.range']

private theorem children_71933 : children 10 71933 = [719333] := by
  norm_num [children, List.range']

private theorem children_73331 : children 10 73331 = [] := by
  norm_num [children, List.range']

private theorem children_73939 : children 10 73939 = [739391, 739393, 739397, 739399] := by
  norm_num [children, List.range']

private theorem children_233993 : children 10 233993 = [2339933] := by
  norm_num [children, List.range']

private theorem children_239933 : children 10 239933 = [2399333] := by
  norm_num [children, List.range']

private theorem children_293999 : children 10 293999 = [2939999] := by
  norm_num [children, List.range']

private theorem children_373379 : children 10 373379 = [3733799] := by
  norm_num [children, List.range']

private theorem children_373393 : children 10 373393 = [] := by
  norm_num [children, List.range']

private theorem children_593933 : children 10 593933 = [5939333] := by
  norm_num [children, List.range']

private theorem children_593993 : children 10 593993 = [] := by
  norm_num [children, List.range']

private theorem children_719333 : children 10 719333 = [] := by
  norm_num [children, List.range']

private theorem children_739391 : children 10 739391 = [7393913] := by
  norm_num [children, List.range']

private theorem children_739393 : children 10 739393 = [7393931, 7393933] := by
  norm_num [children, List.range']

private theorem children_739397 : children 10 739397 = [] := by
  norm_num [children, List.range']

private theorem children_739399 : children 10 739399 = [] := by
  norm_num [children, List.range']

private theorem children_2339933 : children 10 2339933 = [23399339] := by
  norm_num [children, List.range']

private theorem children_2399333 : children 10 2399333 = [] := by
  norm_num [children, List.range']

private theorem children_2939999 : children 10 2939999 = [29399999] := by
  norm_num [children, List.range']

private theorem children_3733799 : children 10 3733799 = [37337999] := by
  norm_num [children, List.range']

private theorem children_5939333 : children 10 5939333 = [59393339] := by
  norm_num [children, List.range']

private theorem children_7393913 : children 10 7393913 = [73939133] := by
  norm_num [children, List.range']

private theorem children_7393931 : children 10 7393931 = [] := by
  norm_num [children, List.range']

private theorem children_7393933 : children 10 7393933 = [] := by
  norm_num [children, List.range']

private theorem children_23399339 : children 10 23399339 = [] := by
  norm_num [children, List.range']

private theorem children_29399999 : children 10 29399999 = [] := by
  norm_num [children, List.range']

private theorem children_37337999 : children 10 37337999 = [] := by
  norm_num [children, List.range']

private theorem children_59393339 : children 10 59393339 = [] := by
  norm_num [children, List.range']

private theorem children_73939133 : children 10 73939133 = [] := by
  norm_num [children, List.range']

theorem level_0 : level 10 0 = [2, 3, 5, 7] := by
  norm_num [level, roots, List.range_succ]

theorem level_1 : level 10 1 = [23, 29, 31, 37, 53, 59, 71, 73, 79] := by
  rw [level, level_0]
  simp only [List.flatMap_cons, List.flatMap_nil,
    children_2, children_3, children_5, children_7, List.cons_append, List.nil_append]

theorem level_2 : level 10 2 = [233, 239, 293, 311, 313, 317, 373, 379, 593, 599, 719, 733, 739,
  797] := by
  rw [level, level_1]
  simp only [List.flatMap_cons, List.flatMap_nil,
    children_23, children_29, children_31, children_37, children_53, children_59, children_71,
      children_73,
    children_79, List.cons_append, List.nil_append]

theorem level_3 : level 10 3 = [2333, 2339, 2393, 2399, 2939, 3119, 3137, 3733, 3739, 3793, 3797,
  5939, 7193,
    7331, 7333, 7393] := by
  rw [level, level_2]
  simp only [List.flatMap_cons, List.flatMap_nil,
    children_233, children_239, children_293, children_311, children_313, children_317,
      children_373,
    children_379, children_593, children_599, children_719, children_733, children_739,
      children_797,
    List.cons_append, List.nil_append]

theorem level_4 : level 10 4 = [23333, 23339, 23399, 23993, 29399, 31193, 31379, 37337, 37339,
  37397, 59393,
    59399, 71933, 73331, 73939] := by
  rw [level, level_3]
  simp only [List.flatMap_cons, List.flatMap_nil,
    children_2333, children_2339, children_2393, children_2399, children_2939, children_3119,
      children_3137,
    children_3733, children_3739, children_3793, children_3797, children_5939, children_7193,
      children_7331,
    children_7333, children_7393, List.cons_append, List.nil_append]

theorem level_5 : level 10 5 = [233993, 239933, 293999, 373379, 373393, 593933, 593993, 719333,
  739391,
    739393, 739397, 739399] := by
  rw [level, level_4]
  simp only [List.flatMap_cons, List.flatMap_nil,
    children_23333, children_23339, children_23399, children_23993, children_29399, children_31193,
    children_31379, children_37337, children_37339, children_37397, children_59393, children_59399,
    children_71933, children_73331, children_73939, List.cons_append, List.nil_append]

theorem level_6 : level 10 6 = [2339933, 2399333, 2939999, 3733799, 5939333, 7393913, 7393931,
  7393933] := by
  rw [level, level_5]
  simp only [List.flatMap_cons, List.flatMap_nil,
    children_233993, children_239933, children_293999, children_373379, children_373393,
      children_593933,
    children_593993, children_719333, children_739391, children_739393, children_739397,
      children_739399,
    List.cons_append, List.nil_append]

theorem level_7 : level 10 7 = [23399339, 29399999, 37337999, 59393339, 73939133] := by
  rw [level, level_6]
  simp only [List.flatMap_cons, List.flatMap_nil,
    children_2339933, children_2399333, children_2939999, children_3733799, children_5939333,
    children_7393913, children_7393931, children_7393933, List.cons_append, List.nil_append]

theorem level_8 : level 10 8 = [] := by
  rw [level, level_7]
  simp only [List.flatMap_cons, List.flatMap_nil,
    children_23399339, children_29399999, children_37337999, children_59393339, children_73939133,
    List.nil_append]

private theorem left_23 : leftCheck 10 23 = true := by
  have width : (Nat.digits 10 23).length = 2 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_29 : leftCheck 10 29 = false := by
  have width : (Nat.digits 10 29).length = 2 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_31 : leftCheck 10 31 = false := by
  have width : (Nat.digits 10 31).length = 2 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_37 : leftCheck 10 37 = true := by
  have width : (Nat.digits 10 37).length = 2 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_53 : leftCheck 10 53 = true := by
  have width : (Nat.digits 10 53).length = 2 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_59 : leftCheck 10 59 = false := by
  have width : (Nat.digits 10 59).length = 2 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_71 : leftCheck 10 71 = false := by
  have width : (Nat.digits 10 71).length = 2 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_73 : leftCheck 10 73 = true := by
  have width : (Nat.digits 10 73).length = 2 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_79 : leftCheck 10 79 = false := by
  have width : (Nat.digits 10 79).length = 2 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_233 : leftCheck 10 233 = false := by
  have width : (Nat.digits 10 233).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_239 : leftCheck 10 239 = false := by
  have width : (Nat.digits 10 239).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_293 : leftCheck 10 293 = false := by
  have width : (Nat.digits 10 293).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_311 : leftCheck 10 311 = false := by
  have width : (Nat.digits 10 311).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_313 : leftCheck 10 313 = true := by
  have width : (Nat.digits 10 313).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_317 : leftCheck 10 317 = true := by
  have width : (Nat.digits 10 317).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_373 : leftCheck 10 373 = true := by
  have width : (Nat.digits 10 373).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_379 : leftCheck 10 379 = false := by
  have width : (Nat.digits 10 379).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_593 : leftCheck 10 593 = false := by
  have width : (Nat.digits 10 593).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_599 : leftCheck 10 599 = false := by
  have width : (Nat.digits 10 599).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_719 : leftCheck 10 719 = false := by
  have width : (Nat.digits 10 719).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_733 : leftCheck 10 733 = false := by
  have width : (Nat.digits 10 733).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_739 : leftCheck 10 739 = false := by
  have width : (Nat.digits 10 739).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_797 : leftCheck 10 797 = true := by
  have width : (Nat.digits 10 797).length = 3 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_2333 : leftCheck 10 2333 = false := by
  have width : (Nat.digits 10 2333).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_2339 : leftCheck 10 2339 = false := by
  have width : (Nat.digits 10 2339).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_2393 : leftCheck 10 2393 = false := by
  have width : (Nat.digits 10 2393).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_2399 : leftCheck 10 2399 = false := by
  have width : (Nat.digits 10 2399).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_2939 : leftCheck 10 2939 = false := by
  have width : (Nat.digits 10 2939).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_3119 : leftCheck 10 3119 = false := by
  have width : (Nat.digits 10 3119).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_3137 : leftCheck 10 3137 = true := by
  have width : (Nat.digits 10 3137).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_3733 : leftCheck 10 3733 = false := by
  have width : (Nat.digits 10 3733).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_3739 : leftCheck 10 3739 = false := by
  have width : (Nat.digits 10 3739).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_3793 : leftCheck 10 3793 = false := by
  have width : (Nat.digits 10 3793).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_3797 : leftCheck 10 3797 = true := by
  have width : (Nat.digits 10 3797).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_5939 : leftCheck 10 5939 = false := by
  have width : (Nat.digits 10 5939).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_7193 : leftCheck 10 7193 = false := by
  have width : (Nat.digits 10 7193).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_7331 : leftCheck 10 7331 = false := by
  have width : (Nat.digits 10 7331).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_7333 : leftCheck 10 7333 = false := by
  have width : (Nat.digits 10 7333).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_7393 : leftCheck 10 7393 = false := by
  have width : (Nat.digits 10 7393).length = 4 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_23333 : leftCheck 10 23333 = false := by
  have width : (Nat.digits 10 23333).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_23339 : leftCheck 10 23339 = false := by
  have width : (Nat.digits 10 23339).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_23399 : leftCheck 10 23399 = false := by
  have width : (Nat.digits 10 23399).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_23993 : leftCheck 10 23993 = false := by
  have width : (Nat.digits 10 23993).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_29399 : leftCheck 10 29399 = false := by
  have width : (Nat.digits 10 29399).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_31193 : leftCheck 10 31193 = false := by
  have width : (Nat.digits 10 31193).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_31379 : leftCheck 10 31379 = false := by
  have width : (Nat.digits 10 31379).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_37337 : leftCheck 10 37337 = false := by
  have width : (Nat.digits 10 37337).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_37339 : leftCheck 10 37339 = false := by
  have width : (Nat.digits 10 37339).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_37397 : leftCheck 10 37397 = false := by
  have width : (Nat.digits 10 37397).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_59393 : leftCheck 10 59393 = false := by
  have width : (Nat.digits 10 59393).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_59399 : leftCheck 10 59399 = false := by
  have width : (Nat.digits 10 59399).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_71933 : leftCheck 10 71933 = false := by
  have width : (Nat.digits 10 71933).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_73331 : leftCheck 10 73331 = false := by
  have width : (Nat.digits 10 73331).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_73939 : leftCheck 10 73939 = false := by
  have width : (Nat.digits 10 73939).length = 5 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_233993 : leftCheck 10 233993 = false := by
  have width : (Nat.digits 10 233993).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_239933 : leftCheck 10 239933 = false := by
  have width : (Nat.digits 10 239933).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_293999 : leftCheck 10 293999 = false := by
  have width : (Nat.digits 10 293999).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_373379 : leftCheck 10 373379 = false := by
  have width : (Nat.digits 10 373379).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_373393 : leftCheck 10 373393 = false := by
  have width : (Nat.digits 10 373393).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_593933 : leftCheck 10 593933 = false := by
  have width : (Nat.digits 10 593933).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_593993 : leftCheck 10 593993 = false := by
  have width : (Nat.digits 10 593993).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_719333 : leftCheck 10 719333 = false := by
  have width : (Nat.digits 10 719333).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_739391 : leftCheck 10 739391 = false := by
  have width : (Nat.digits 10 739391).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_739393 : leftCheck 10 739393 = false := by
  have width : (Nat.digits 10 739393).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_739397 : leftCheck 10 739397 = true := by
  have width : (Nat.digits 10 739397).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_739399 : leftCheck 10 739399 = false := by
  have width : (Nat.digits 10 739399).length = 6 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_2339933 : leftCheck 10 2339933 = false := by
  have width : (Nat.digits 10 2339933).length = 7 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_2399333 : leftCheck 10 2399333 = false := by
  have width : (Nat.digits 10 2399333).length = 7 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_2939999 : leftCheck 10 2939999 = false := by
  have width : (Nat.digits 10 2939999).length = 7 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_3733799 : leftCheck 10 3733799 = false := by
  have width : (Nat.digits 10 3733799).length = 7 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_5939333 : leftCheck 10 5939333 = false := by
  have width : (Nat.digits 10 5939333).length = 7 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_7393913 : leftCheck 10 7393913 = false := by
  have width : (Nat.digits 10 7393913).length = 7 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_7393931 : leftCheck 10 7393931 = false := by
  have width : (Nat.digits 10 7393931).length = 7 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_7393933 : leftCheck 10 7393933 = false := by
  have width : (Nat.digits 10 7393933).length = 7 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_23399339 : leftCheck 10 23399339 = false := by
  have width : (Nat.digits 10 23399339).length = 8 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_29399999 : leftCheck 10 29399999 = false := by
  have width : (Nat.digits 10 29399999).length = 8 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_37337999 : leftCheck 10 37337999 = false := by
  have width : (Nat.digits 10 37337999).length = 8 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_59393339 : leftCheck 10 59393339 = false := by
  have width : (Nat.digits 10 59393339).length = 8 := by decide +kernel
  norm_num [leftCheck, width, List.range']

private theorem left_73939133 : leftCheck 10 73939133 = false := by
  have width : (Nat.digits 10 73939133).length = 8 := by decide +kernel
  norm_num [leftCheck, width, List.range']

theorem exhausted : level 10 8 = [] := level_8

theorem accepted_values : accepted 10 8 = [23, 37, 53, 73, 313, 317, 373, 797, 3137, 3797, 739397]
  := by
  have depths : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide +kernel
  simp only [accepted, candidates, depths, List.flatMap_cons, List.flatMap_nil,
    Nat.reduceAdd, level_1, level_2, level_3, level_4, level_5, level_6, level_7, level_8,
      List.cons_append,
    List.nil_append,
    List.filter_cons, List.filter_nil, left_23, left_29, left_31, left_37, left_53, left_59,
      left_71, left_73,
    left_79, left_233, left_239, left_293, left_311, left_313, left_317, left_373, left_379,
      left_593,
    left_599, left_719, left_733, left_739, left_797, left_2333, left_2339, left_2393, left_2399,
      left_2939,
    left_3119, left_3137, left_3733, left_3739, left_3793, left_3797, left_5939, left_7193,
      left_7331,
    left_7333, left_7393, left_23333, left_23339, left_23399, left_23993, left_29399, left_31193,
      left_31379,
    left_37337, left_37339, left_37397, left_59393, left_59399, left_71933, left_73331, left_73939,
    left_233993, left_239933, left_293999, left_373379, left_373393, left_593933, left_593993,
      left_719333,
    left_739391, left_739393, left_739397, left_739399, left_2339933, left_2399333, left_2939999,
    left_3733799, left_5939333, left_7393913, left_7393931, left_7393933, left_23399339,
      left_29399999,
    left_37337999, left_59393339, left_73939133, Bool.false_eq_true,
    if_false, if_true]

theorem answer_default : answer 10 ⟨8, exhausted⟩ = 748317 := by
  rw [answer_eq_sum 10 8 (by decide) exhausted, accepted_values]
  rfl

/-- The listed primes are globally exhaustive, without a numeric hypothesis on n. -/
theorem complete (n : Nat) : Truncatable 10 n ↔
    n ∈ [23, 37, 53, 73, 313, 317, 373, 797, 3137, 3797, 739397] := by
  rw [← accepted_values]
  exact (mem_accepted_of_empty 10 8 n (by decide) exhausted).symm

theorem exactly_eleven : (accepted 10 8).length = 11 := by
  rw [accepted_values]
  rfl

end ProjectEulerStatements.TruncatablePrimeBase.Decimal
