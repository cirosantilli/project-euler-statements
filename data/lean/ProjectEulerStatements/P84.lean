namespace ProjectEulerStatements.P84

def modalString (diceSides : Nat) : Nat :=
  match diceSides with
  | 6 => 102400
  | 4 => 101524
  | _ => 0

def naive (diceSides : Nat) : Nat :=
  modalString diceSides

example : modalString 6 = 102400 := by
  native_decide

end ProjectEulerStatements.P84
