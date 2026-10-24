import ProjectEulerSolutions.Lib.HeapRows
import ProjectEulerSolutions.Lib.HeapCollection
import lang.py.FormalSW.ComprehensionCalls
import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p59.py.ast»
import lang.py.FormalSW.Calls
import lang.py.FormalSW.HeapCalls
import ProjectEulerSolutions.Lib.XorDecryption

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace data.«project-euler-statements».data.py.project_euler_statements.p59
open FormalSW.PyAst
private abbrev program := P59Ast.module

theorem xor.value_eq (a b : Int) : integerBitXor a b = Int.xor a b := by
  cases a <;> cases b <;> rfl

/-- The source XOR helper terminates for both positive and negative integers. -/
theorem xor.result (a b : Int) :
    Calls.ReturnsValue program "xor" [.int a, .int b] (.int (integerBitXor a b)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.binary (Calls.Evaluates.lookup rfl) (Calls.Evaluates.lookup rfl) rfl

theorem xor.«Returns» (a b : Int) :
    (Calls.function program "xor" [.int a, .int b]).Returns :=
  (xor.result a b).returns

/-- Calls from the decryption comprehension preserve every caller heap and global. -/
theorem xor.heap_result (a b : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    HeapCalls.ReturnsValue program "xor" [.scalar (.int a), .scalar (.int b)] heap
      (.scalar (.int (integerBitXor a b))) heap globals := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.binary (av := .scalar (.int a)) (bv := .scalar (.int b))
    (HeapCalls.Evaluates.lookup (by cases globals <;> rfl))
    (HeapCalls.Evaluates.lookup (by cases globals <;> rfl)) rfl

namespace char_weight
open FormalSW.PyAst.HeapCalls
private abbrev characterProgram := P59Ast.module
private abbrev characterInt (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev characterBool (value : Bool) : Mutable.Value := .scalar (.bool value)

private inductive WeightGuard where
  | equal (value : Int)
  | member (bytes : List UInt8)

private def WeightGuard.expression : WeightGuard → Expr
  | .equal value => .compare (.name "value") [(.eq, .constant (.int value))]
  | .member bytes => .membership (.name "value") (.constant (.bytes bytes)) false

private def WeightGuard.flag : WeightGuard → Int → Bool
  | .equal target, value => decide (value = target)
  | .member bytes, value => FormalSW.Py.Builtin.Bytes.containsByte bytes (UInt8.ofNat value.toNat)

private def weightGuards : List (WeightGuard × Int) :=
  [(.equal 32, 10), (.equal 101, 6),
   (.member [116, 97, 111], 5),
   (.member [105, 110, 115, 104, 114], 4),
   (.member [100, 108], 3),
   (.member [117, 99, 109, 119, 102, 103, 121, 112], 2),
   (.member [98, 118, 107, 46, 44, 59, 58, 39, 34, 33, 63, 40, 41, 45], 1),
   (.member [123, 125, 91, 93, 124, 94, 126, 96], -3)]

/-- Keep Python's real unary-minus syntax for negative return literals. -/
private def scoreExpression (score : Int) : Expr :=
  if score < 0 then .unaryOp .uSub (.constant (.int (-score))) else .constant (.int score)

private def guardBody : List (WeightGuard × Int) → List Stmt
  | [] => [.return (.constant (.int 0))]
  | (guard, score) :: rest =>
      .ifThen guard.expression [.return (scoreExpression score)] [] :: guardBody rest

private def guardScore : List (WeightGuard × Int) → Int → Int
  | [], _ => 0
  | (guard, score) :: rest, value => if guard.flag value then score else guardScore rest value

/-- The classifier performs only finite pure byte membership, never source execution. -/
private def classifier (value : Int) : Int :=
  guardScore weightGuards (ProjectEulerSolutions.XorDecryption.lowercaseCode value)

private def upperExpression : Expr :=
  .compare (.constant (.int 65)) [(.ltE, .name "value"), (.ltE, .constant (.int 90))]
private def upperFlag (value : Int) : Bool := decide (65 ≤ value ∧ value ≤ 90)
private def normalizationBody : List Stmt :=
  [.ifThen upperExpression [.augAssign (.name "value") .add (.constant (.int 32))] []]
private def characterBody : List Stmt := normalizationBody ++ guardBody weightGuards

/-- Live source anchor for every statement of the actual function, without a hash
or a replacement function. A source edit must recheck this equality. -/
private theorem character_body_source :
    executableBody ((findFunctionIn characterProgram.body "char_weight").getD ([], [])).2 = characterBody := rfl

private theorem compare_integer (op : CmpOp) (left right : Int) (heap : Mutable.Heap) :
    HeapCalls.compare op (characterInt left) (characterInt right) heap =
      some (.ok (characterBool (evalCmpOp op left right)), heap) := rfl

private theorem guard_evaluates (module : Module) (env : HeapCalls.Env) (guard : WeightGuard)
    (value : Int) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (getValue : env "value" = some (characterInt value)) (lower : 0 ≤ value) (upper : value ≤ 255) :
    Evaluates module env guard.expression heap (characterBool (guard.flag value)) heap globals := by
  cases guard with
  | equal target =>
      apply Evaluates.compare (Evaluates.lookup getValue) Evaluates.constant
      exact compare_integer .eq value target heap
  | member bytes =>
      apply Evaluates.membership (.cons (Evaluates.lookup getValue) (.cons Evaluates.constant .nil))
      exact HeapCalls.membership_bytes_integer heap bytes value false lower upper

private theorem score_evaluates (module : Module) (env : HeapCalls.Env) (score : Int)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    Evaluates module env (scoreExpression score) heap (characterInt score) heap globals := by
  unfold scoreExpression
  split
  · apply Evaluates.unary (Evaluates.constant (value := .int (-score)))
    simp [HeapCalls.unary, scalarResult, scalarExpr, characterInt]
  · exact Evaluates.constant

/-- One generic induction follows exactly the source's first-true return order. -/
private theorem guardBody_result (module : Module) (env : HeapCalls.Env)
    (guards : List (WeightGuard × Int)) (value : Int) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (getValue : env "value" = some (characterInt value)) (lower : 0 ≤ value) (upper : value ≤ 255) :
    BlockReturns module env (guardBody guards) heap (characterInt (guardScore guards value)) heap globals := by
  induction guards with
  | nil => exact BlockReturns.return_value Evaluates.constant
  | cons entry rest ih =>
      rcases entry with ⟨guard, score⟩
      have evaluated := guard_evaluates module env guard value heap globals getValue lower upper
      cases tested : guard.flag value with
      | false =>
          simp only [tested] at evaluated
          simp only [guardBody, guardScore, tested, Bool.false_eq_true, if_false]
          apply BlockReturns.branch (flag := false) evaluated rfl
          exact ih
      | true =>
          simp only [tested] at evaluated
          simp only [guardBody, guardScore, tested, ↓reduceIte]
          apply BlockReturns.branch (flag := true) evaluated rfl
          exact BlockReturns.return_value (score_evaluates module env score heap globals)

/-- The middle operand of the real chained comparison is evaluated once. -/
private theorem upper_evaluates (module : Module) (env : HeapCalls.Env) (value : Int)
    (heap : Mutable.Heap) (globals : Mutable.Globals)
    (getValue : env "value" = some (characterInt value)) :
    Evaluates module env upperExpression heap (characterBool (upperFlag value)) heap globals := by
  by_cases lower : 65 ≤ value
  · have first : HeapCalls.compare .ltE (characterInt 65) (characterInt value) heap =
        some (.ok (characterBool true), heap) := by
      simpa only [evalCmpOp, decide_eq_true lower] using compare_integer .ltE 65 value heap
    have evaluated : Evaluates module env upperExpression heap (characterBool (decide (value ≤ 90))) heap globals := by
      apply Evaluates.chain Evaluates.constant
      apply Evaluates.Compares.next (Evaluates.lookup getValue) first rfl
      exact Evaluates.Compares.last Evaluates.constant (compare_integer .ltE value 90 heap)
    simpa [upperFlag, lower] using evaluated
  · have first : HeapCalls.compare .ltE (characterInt 65) (characterInt value) heap =
        some (.ok (characterBool false), heap) := by
      simpa only [evalCmpOp, decide_eq_false lower] using compare_integer .ltE 65 value heap
    have evaluated : Evaluates module env upperExpression heap (characterBool false) heap globals := by
      apply Evaluates.chain Evaluates.constant
      exact Evaluates.Compares.stop (Evaluates.lookup getValue) first rfl
    simpa [upperFlag, lower] using evaluated

/-- Execute the actual optional local +=32, preserving the complete caller heap. -/
private theorem normalization_result (module : Module) (env : HeapCalls.Env) (value : Int)
    (heap : Mutable.Heap) (globals : Mutable.Globals)
    (getValue : env "value" = some (characterInt value)) :
    ∃ afterEnv,
      BlockContinues module env normalizationBody heap afterEnv heap globals ∧
      afterEnv "value" = some (characterInt (ProjectEulerSolutions.XorDecryption.lowercaseCode value)) := by
  have evaluated := upper_evaluates module env value heap globals getValue
  by_cases isUpper : 65 ≤ value ∧ value ≤ 90
  · have trueFlag : upperFlag value = true := by simp only [upperFlag, decide_eq_true isUpper]
    simp only [trueFlag] at evaluated
    refine ⟨HeapCalls.setLocal env "value" (characterInt (value + 32)), ?_, ?_⟩
    · apply BlockContinues.branch (flag := true) evaluated rfl
      exact BlockContinues.augAssign getValue Evaluates.constant rfl
    · simp only [HeapCalls.setLocal, ↓reduceIte, ProjectEulerSolutions.XorDecryption.lowercaseCode, if_pos isUpper]
  · have falseFlag : upperFlag value = false := by simp only [upperFlag, decide_eq_false isUpper]
    simp only [falseFlag] at evaluated
    refine ⟨env, ?_, ?_⟩
    · exact BlockContinues.branch (flag := false) evaluated rfl BlockContinues.nil
    · simpa only [ProjectEulerSolutions.XorDecryption.lowercaseCode, if_neg isUpper] using getValue

private theorem characterBody_result (module : Module) (env : HeapCalls.Env) (value : Int)
    (heap : Mutable.Heap) (globals : Mutable.Globals)
    (getValue : env "value" = some (characterInt value)) (lower : 0 ≤ value) (upper : value ≤ 255) :
    BlockReturns module env characterBody heap (characterInt (classifier value)) heap globals := by
  obtain ⟨afterEnv, normalized, afterValue⟩ := normalization_result module env value heap globals getValue
  have normalizedLower : 0 ≤ ProjectEulerSolutions.XorDecryption.lowercaseCode value := by
    unfold ProjectEulerSolutions.XorDecryption.lowercaseCode
    split <;> omega
  have normalizedUpper : ProjectEulerSolutions.XorDecryption.lowercaseCode value ≤ 255 := by
    unfold ProjectEulerSolutions.XorDecryption.lowercaseCode
    split <;> omega
  exact normalized.returns (guardBody_result module afterEnv weightGuards _ heap globals afterValue normalizedLower normalizedUpper)

/-- Cheap pure classification certificate; no HeapCalls/Reaches occurs here. -/
private theorem classifier_bytes : ∀ value : Fin 256,
    classifier value.val = ProjectEulerSolutions.XorDecryption.charWeight value.val := by decide

/-- Actual full-source function proof; source lookup/binding is composed once. -/
theorem heap_result (value : Nat) (bounded : value < 256) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  have certified := classifier_bytes ⟨value, bounded⟩
  rw [← certified]
  let params := ((findFunctionIn characterProgram.body "char_weight").getD ([], [])).1
  let body := ((findFunctionIn characterProgram.body "char_weight").getD ([], [])).2
  let entry := functionEnv params body [.scalar (.int value)] globals
  apply BlockReturns.function rfl rfl
  change BlockReturns characterProgram entry (executableBody body) heap (characterInt (classifier value)) heap globals
  rw [show executableBody body = characterBody from character_body_source]
  apply characterBody_result
  · cases globals <;> rfl
  · omega
  · omega

end char_weight


namespace char_weight

theorem «Returns» (value : Int)
    (nonnegative : Calls.Condition P59Ast.module
      (fun name => if name = "value" then some (.int value) else none) P59Ast.requires_char_weight_0)
    (bounded : Calls.Condition P59Ast.module
      (fun name => if name = "value" then some (.int value) else none) P59Ast.requires_char_weight_1) :
    (HeapCalls.scalarFunction P59Ast.module "char_weight" [.int value]).Returns := by
  have lower : 0 ≤ value := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare nonnegative rfl
  have upper : value < 256 := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare bounded rfl
  have returned :
      (HeapCalls.scalarFunction P59Ast.module "char_weight" [.int (value.toNat : Int)]).Returns :=
    HeapCalls.ReturnsValue.scalar_returns (heap_result value.toNat (by omega) [] [])
  simpa only [Int.toNat_of_nonneg lower] using returned

theorem «Supported» (value : Int)
    (nonnegative : Calls.Condition P59Ast.module
      (fun name => if name = "value" then some (.int value) else none) P59Ast.requires_char_weight_0)
    (bounded : Calls.Condition P59Ast.module
      (fun name => if name = "value" then some (.int value) else none) P59Ast.requires_char_weight_1) :
    (HeapCalls.scalarFunction P59Ast.module "char_weight" [.int value]).Supported :=
  («Returns» value nonnegative bounded).supported

end char_weight

end data.«project-euler-statements».data.py.project_euler_statements.p59

namespace data.«project-euler-statements».data.py.project_euler_statements.p59.decrypt
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

private abbrev source := P59Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private def encode (items : List Int) : List Mutable.Value := items.map number

private abbrev indexExpression : Expr :=
  .binOp (.name "i") .mod (.builtinCall .len [.name "key"])
private abbrev selectedKey : Expr :=
  .ifExp (.name "key") (.subscript (.name "key") indexExpression) (.constant (.int 0))
private abbrev element : Expr := .call (.name "xor") [.name "c", selectedKey]
private abbrev target : Expr := .tuple [.name "i", .name "c"]
private abbrev generators : List (Expr × Expr × List Expr) :=
  [(target, .call (.name "enumerate") [.name "cipher", .constant (.int 0)], [])]
private abbrev row (address : Nat) : List Stmt := [.comprehensionAppend address element]

private theorem sequence_bytes (cipher : List UInt8) (heap : Mutable.Heap) :
    Mutable.sequence (.scalar (.bytes cipher)) heap =
      some (.ok (encode (XorDecryption.encodeBytes cipher)), heap) := by
  simp [Mutable.sequence, encode, XorDecryption.encodeBytes, List.map_map, Function.comp_def]

/-- The source's nonempty-key branch reads the cyclic element of the actual list. -/
private theorem selected_key (key : XorDecryption.Key) (position : Nat)
    (heap : Mutable.Heap) (keyAddress : Nat) (env : Mutable.Env)
    (found : heap[keyAddress]? = some (.list (encode (XorDecryption.keyValues key))))
    (getKey : env "key" = some (.ref keyAddress))
    (getIndex : env "i" = some (number position)) (globals : Mutable.Globals) :
    Evaluates source env selectedKey heap (number (XorDecryption.keyByte key position)) heap globals := by
  apply Evaluates.conditional (flag := true) (Evaluates.lookup getKey)
  · simp [Mutable.truth, found, encode, XorDecryption.keyValues]
  · apply Evaluates.subscript (index := indexExpression)
      (ordinary := by intro a b c equal; cases equal) (Evaluates.lookup getKey)
    · apply Evaluates.binary (value := number (position % 3)) (bv := number 3) (finalHeap := heap) (Evaluates.lookup getIndex)
        (Evaluates.builtin (.cons (Evaluates.lookup getKey) .nil) ?_) rfl
      simp [primitive, Mutable.length, found, encode, XorDecryption.keyValues]
    · have bound : position % 3 < (encode (XorDecryption.keyValues key)).length := by
        simpa [encode] using Nat.mod_lt position (by decide : 0 < 3)
      have selected : (encode (XorDecryption.keyValues key))[position % 3]? =
          some (number (XorDecryption.keyByte key position)) := by
        simpa only [encode, List.getElem?_map, Option.map_some] using
          congrArg (Option.map number) (XorDecryption.keyValues_getElem?_mod key position)
      have selectedValue : (encode (XorDecryption.keyValues key))[position % 3] =
          number (XorDecryption.keyByte key position) := by
        apply Option.some.inj
        simpa only [List.getElem?_eq_getElem bound] using selected
      simpa only [selectedValue] using
        Mutable.getItem_list heap keyAddress (position % 3) (encode (XorDecryption.keyValues key)) found bound

private theorem element_evaluates (key : XorDecryption.Key) (position : Nat) (byte : UInt8)
    (heap : Mutable.Heap) (keyAddress : Nat) (env : Mutable.Env)
    (found : heap[keyAddress]? = some (.list (encode (XorDecryption.keyValues key))))
    (getKey : env "key" = some (.ref keyAddress))
    (getIndex : env "i" = some (number position))
    (getByte : env "c" = some (number byte.toNat)) (globals : Mutable.Globals) :
    Evaluates source env element heap
      (number (Int.xor byte.toNat (XorDecryption.keyByte key position))) heap globals := by
  apply Evaluates.call (.cons (Evaluates.lookup getByte) (.cons
    (selected_key key position heap keyAddress env found getKey getIndex globals) .nil))
  simpa only [xor.value_eq] using xor.heap_result byte.toNat (XorDecryption.keyByte key position) heap globals

/-- The collector is the only mutable object touched by the comprehension. -/
private theorem collect (key : XorDecryption.Key) (remaining before : List UInt8)
    (plain : List Int) (base : Mutable.Heap) (keyAddress : Nat) (env : Mutable.Env)
    (foundKey : base[keyAddress]? = some (.list (encode (XorDecryption.keyValues key))))
    (getKey : env "key" = some (.ref keyAddress)) (globals : Mutable.Globals) :
    ∃ finalEnv, BlockContinues source env
      [.enumerateStepLoop "i" "c" (.scalar (.bytes (before ++ remaining))) before.length before.length (row base.length) []]
      (HeapCollection.working base (encode plain) []) finalEnv
      (HeapCollection.working base
        (encode (plain ++ XorDecryption.decryptFrom key before.length (XorDecryption.encodeBytes remaining))) []) globals := by
  induction remaining generalizing before plain env with
  | nil =>
      refine ⟨env, ?_⟩
      simp only [XorDecryption.encodeBytes, List.map_nil, XorDecryption.decryptFrom, List.append_nil]
      apply BlockContinues.enumerate_done (items := encode (XorDecryption.encodeBytes before))
      · simpa only [sequenceValue] using sequence_bytes before (HeapCollection.working base (encode plain) [])
      · simp [encode, XorDecryption.encodeBytes]
      · exact BlockContinues.nil
  | cons byte rest ih =>
      let bound := setLocal (setLocal env "i" (number before.length)) "c" (number byte.toNat)
      let decoded : Int := Int.xor byte.toNat (XorDecryption.keyByte key before.length)
      have keyNow : (HeapCollection.working base (encode plain) [])[keyAddress]? =
          some (.list (encode (XorDecryption.keyValues key))) := by
        exact HeapCollection.prefix_found base [.list (encode plain)] keyAddress _ foundKey
      have evaluated : Evaluates source bound element (HeapCollection.working base (encode plain) [])
          (number decoded) (HeapCollection.working base (encode plain) []) globals :=
        element_evaluates key before.length byte _ keyAddress bound keyNow
          (by simpa [bound, setLocal] using getKey) (by simp [bound, setLocal]) (by simp [bound, setLocal]) globals
      have emitted := HeapCollection.emit base (encode plain) [] [] (number decoded)
        (by simpa only [List.append_nil] using evaluated)
      obtain ⟨finalEnv, continued⟩ := ih (before ++ [byte]) (plain ++ [decoded]) bound
        (by simpa [bound, setLocal] using getKey)
      have continued' : BlockContinues source bound
          [.enumerateStepLoop "i" "c" (.scalar (.bytes (before ++ byte :: rest)))
            (before.length + 1) ((before.length : Int) + 1) (row base.length) []]
          (HeapCollection.working base (encode plain ++ [number decoded]) []) finalEnv
          (HeapCollection.working base
            (encode ((plain ++ [decoded]) ++ XorDecryption.decryptFrom key (before.length + 1)
              (XorDecryption.encodeBytes rest))) []) globals := by
        simpa [encode, List.map_append, List.append_assoc] using continued
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.enumerate_step
        (items := encode (XorDecryption.encodeBytes (before ++ byte :: rest))) (value := number byte.toNat)
        (by simpa only [sequenceValue] using sequence_bytes (before ++ byte :: rest) (HeapCollection.working base (encode plain) []))
        (by simp [encode, XorDecryption.encodeBytes, List.map_append])
      simpa [row, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        XorDecryption.encodeBytes, XorDecryption.decryptFrom, decoded,
        encode, List.map_append, List.append_assoc] using emitted.append continued'

/-- The actual source returns one freshly allocated plaintext list. Its caller
heap, key list and globals are retained, for every byte string and integer key. -/
theorem result (cipher : List UInt8) (key : XorDecryption.Key) (heap : Mutable.Heap) (keyAddress : Nat)
    (foundKey : heap[keyAddress]? = some (.list (encode (XorDecryption.keyValues key))))
    (globals : Mutable.Globals := []) :
    ReturnsValue source "decrypt" [.scalar (.bytes cipher), .ref keyAddress] heap (.ref heap.length)
      (heap ++ [.list (encode (XorDecryption.decryptFrom key 0 (XorDecryption.encodeBytes cipher)))]) globals := by
  let params := ((findFunctionIn source.body "decrypt").getD ([], [])).1
  let body := ((findFunctionIn source.body "decrypt").getD ([], [])).2
  let initial := functionEnv params body [.scalar (.bytes cipher), .ref keyAddress] globals
  let masked := comprehensionTargetsEnv initial generators
  have unmasked : generators.any (fun generator => (targetLocals generator.1).contains "key") = false := by
    simp [generators, target, targetLocals]
  have getKey : masked "key" = some (.ref keyAddress) := by
    simp only [masked, comprehensionTargetsEnv, unmasked, Bool.false_eq_true, if_false]
    cases globals <;> rfl
  obtain ⟨finalEnv, executed⟩ := collect key cipher [] [] heap keyAddress masked foundKey getKey globals
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.list_comp_targets_enumerate (finalEnv := finalEnv)
    (.cons (Evaluates.lookup (by cases globals <;> rfl)) (.cons (Evaluates.constant (value := .int 0)) .nil))
    (by rfl) (sequence_bytes cipher heap) (by rfl)
  simpa only [generators, target, row, comprehensionFilters, List.foldr_nil, comprehensionTargetsBody,
    sequenceSource, List.nil_append, List.length_nil, Nat.cast_zero,
    encode, List.map_nil, HeapCollection.working, masked, initial, params, body, element, selectedKey,
    indexExpression] using executed

/-- The fresh output address cannot alias the original key object. -/
theorem fresh (heap : Mutable.Heap) (key : XorDecryption.Key) (keyAddress : Nat)
    (foundKey : heap[keyAddress]? = some (.list (encode (XorDecryption.keyValues key)))) :
    keyAddress < heap.length :=
  (List.getElem?_eq_some_iff.mp foundKey).1

end data.«project-euler-statements».data.py.project_euler_statements.p59.decrypt

namespace data.«project-euler-statements».data.py.project_euler_statements.p59.text_score
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

private abbrev source := P59Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private def encode (items : List Int) : List Mutable.Value := items.map number

/-- Python's None return is distinct from a valid score, including zero or a negative score. -/
def valueOfScore : Option Int → Mutable.Value
  | none => .scalar .none
  | some score => number score

private abbrev rangeTest : Expr :=
  .compare (.constant (.int 32)) [(.ltE, .name "value"), (.ltE, .constant (.int 126))]
private abbrev tenTest : Expr := .compare (.name "value") [(.eq, .constant (.int 10))]
private abbrev thirteenTest : Expr := .compare (.name "value") [(.eq, .constant (.int 13))]
private abbrev allowed : Expr := .boolOp .or [rangeTest, tenTest, thirteenTest]
private abbrev rejected : Expr := .unaryOp .not allowed
private abbrev row : List Stmt :=
  [.ifThen rejected [.return (.constant .none)] [],
   .augAssign (.name "score") .add (.call (.name "char_weight") [.name "value"])]
private abbrev tail (address position : Nat) : List Stmt :=
  [.sequenceStepLoop "value" (.ref address) position row [], .return (.name "score")]

private theorem range_evaluates (value : Int) (env : Mutable.Env) (heap : Mutable.Heap)
    (getValue : env "value" = some (number value)) (globals : Mutable.Globals) :
    Evaluates source env rangeTest heap (flag (decide (32 ≤ value ∧ value ≤ 126))) heap globals := by
  by_cases lower : 32 ≤ value
  · simp only [lower, true_and]
    apply Evaluates.chain (Evaluates.constant (value := .int 32))
    apply Evaluates.Compares.next (compared := flag true) (afterComparison := heap) (Evaluates.lookup getValue)
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag, lower]
    · rfl
    · apply Evaluates.Compares.last (Evaluates.constant (value := .int 126))
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]
  · simp only [lower, false_and, decide_false]
    apply Evaluates.chain (Evaluates.constant (value := .int 32))
    apply Evaluates.Compares.stop (answer := flag false) (Evaluates.lookup getValue)
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag, lower]
    · rfl

/-- The actual comparison chain and short-circuiting or have the model's predicate. -/
private theorem allowed_evaluates (value : Int) (env : Mutable.Env) (heap : Mutable.Heap)
    (getValue : env "value" = some (number value)) (globals : Mutable.Globals) :
    Evaluates source env allowed heap (flag (XorDecryption.printable value)) heap globals := by
  have range := range_evaluates value env heap getValue globals
  have ten : Evaluates source env tenTest heap (flag (decide (value = 10))) heap globals := by
    apply Evaluates.compare (Evaluates.lookup getValue) (Evaluates.constant (value := .int 10))
    simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]
  have thirteen : Evaluates source env thirteenTest heap (flag (decide (value = 13))) heap globals := by
    apply Evaluates.compare (Evaluates.lookup getValue) (Evaluates.constant (value := .int 13))
    simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]
  by_cases within : 32 ≤ value ∧ value ≤ 126
  · have tested : Evaluates source env allowed heap (flag true) heap globals :=
      Evaluates.boolean_stop (op := .or) (rest := [tenTest, thirteenTest]) (flag := true)
        (by simpa only [within, decide_true] using range) rfl rfl
    simpa [XorDecryption.printable, within] using tested
  · by_cases equalTen : value = 10
    · have following : Evaluates source env (.boolOp .or [tenTest, thirteenTest]) heap (flag true) heap globals :=
        Evaluates.boolean_stop (op := .or) (rest := [thirteenTest]) (flag := true)
          (by simpa only [equalTen, decide_true] using ten) rfl rfl
      have tested : Evaluates source env allowed heap (flag true) heap globals :=
        Evaluates.boolean_next (op := .or) (flag := false)
          (by simpa only [within, decide_false] using range) rfl rfl following
      simpa [XorDecryption.printable, equalTen] using tested
    · have last : Evaluates source env (.boolOp .or [thirteenTest]) heap (flag (decide (value = 13))) heap globals :=
        Evaluates.boolean_last (op := .or) (flag := decide (value = 13)) thirteen rfl
      have following : Evaluates source env (.boolOp .or [tenTest, thirteenTest]) heap (flag (decide (value = 13))) heap globals :=
        Evaluates.boolean_next (op := .or) (flag := false)
          (by simpa only [equalTen, decide_false] using ten) rfl rfl last
      have tested : Evaluates source env allowed heap (flag (decide (value = 13))) heap globals :=
        Evaluates.boolean_next (op := .or) (flag := false)
          (by simpa only [within, decide_false] using range) rfl rfl following
      simpa [XorDecryption.printable, within, equalTen] using tested

private theorem rejected_evaluates (value : Int) (env : Mutable.Env) (heap : Mutable.Heap)
    (getValue : env "value" = some (number value)) (globals : Mutable.Globals) :
    Evaluates source env rejected heap (flag (!XorDecryption.printable value)) heap globals := by
  apply Evaluates.unary (allowed_evaluates value env heap getValue globals)
  simp [HeapCalls.unary, Mutable.truth, scalarTruth, flag]

private theorem weight_call (value : Int) (printable : XorDecryption.printable value = true)
    (env : Mutable.Env) (heap : Mutable.Heap) (getValue : env "value" = some (number value))
    (globals : Mutable.Globals) :
    Evaluates source env (.call (.name "char_weight") [.name "value"]) heap
      (number (XorDecryption.charWeight value)) heap globals := by
  have alternatives : value = 10 ∨ value = 13 ∨ (32 ≤ value ∧ value ≤ 126) :=
    of_decide_eq_true printable
  have lower : 0 ≤ value := by omega
  have upper : value < 256 := by omega
  apply Evaluates.call (.cons (Evaluates.lookup getValue) .nil)
  simpa only [Int.toNat_of_nonneg lower] using
    char_weight.heap_result value.toNat (by omega) heap globals

/-- A structural source loop proof, with arbitrary prefix and score accumulator. -/
private theorem loop (remaining before : List Int) (running : Int) (env : Mutable.Env)
    (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (encode (before ++ remaining))))
    (getScore : env "score" = some (number running)) (globals : Mutable.Globals) :
    BlockReturns source env (tail address before.length) heap
      (valueOfScore ((XorDecryption.scoreOnly remaining).map (fun score => running + score))) heap globals := by
  induction remaining generalizing before running env with
  | nil =>
      apply BlockReturns.sequence_done (items := encode (before ++ []))
        (by simp [sequenceValue, Mutable.sequence, found]) (by simp [encode])
      apply BlockReturns.return_value
      simpa [valueOfScore] using
        (Evaluates.lookup (module := source) (heap := heap) (globals := globals) getScore)
  | cons value rest ih =>
      apply BlockReturns.sequence_step (items := encode (before ++ value :: rest)) (value := number value)
        (by simp [sequenceValue, Mutable.sequence, found]) (by simp [encode, List.map_append])
      let bound := setLocal env "value" (number value)
      have getValue : bound "value" = some (number value) := by simp [bound, setLocal]
      cases valid : XorDecryption.printable value with
      | false =>
          have tested : Evaluates source bound rejected heap (flag true) heap globals := by
            simpa only [valid, Bool.not_false] using rejected_evaluates value bound heap getValue globals
          apply BlockReturns.branch tested rfl
          apply BlockReturns.return_value
          simpa [XorDecryption.scoreOnly_cons, valid, valueOfScore] using
            (Evaluates.constant (module := source) (env := bound) (heap := heap)
              (globals := globals) (value := Constant.none))
      | true =>
          have tested : Evaluates source bound rejected heap (flag false) heap globals := by
            simpa only [valid, Bool.not_true] using rejected_evaluates value bound heap getValue globals
          apply BlockReturns.branch tested rfl
          apply BlockReturns.augAssign
            (lookup := by simpa [bound, setLocal] using getScore)
            (weight_call value valid bound heap getValue globals) rfl
          have nextFound : heap[address]? = some (.list (encode ((before ++ [value]) ++ rest))) := by
            simpa only [List.append_assoc, List.singleton_append] using found
          have continued := ih (before ++ [value]) (running + XorDecryption.charWeight value)
            (setLocal bound "score" (number (running + XorDecryption.charWeight value))) nextFound
            (by simp [setLocal])
          simpa [tail, row, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            XorDecryption.scoreOnly_cons, valid, Option.map_map, Function.comp_def, Int.add_assoc] using continued

/-- Every finite integer list is scored by the actual reference, including early
None for invalid text. The original input, heap objects and globals are unchanged. -/
theorem result (text : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (encode text))) (globals : Mutable.Globals := []) :
    ReturnsValue source "text_score" [.ref address] heap (valueOfScore (XorDecryption.scoreOnly text)) heap globals := by
  let params := ((findFunctionIn source.body "text_score").getD ([], [])).1
  let body := ((findFunctionIn source.body "text_score").getD ([], [])).2
  let initial := functionEnv params body [.ref address] globals
  let initialized := setLocal initial "score" (number 0)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.constant (value := .int 0))
  apply BlockReturns.for_sequence (items := encode text) (ordinary := by intro expressions equal; cases equal)
    (Evaluates.lookup (by cases globals <;> rfl)) (by simp [Mutable.sequence, found])
  simpa [List.nil_append, Int.zero_add, Option.map_id, tail, row, rejected, allowed,
    rangeTest, tenTest, thirteenTest, initialized, initial, params, body] using
    loop text [] 0 initialized heap address found (by simp [initialized, setLocal]) globals

end data.«project-euler-statements».data.py.project_euler_statements.p59.text_score


namespace data.«project-euler-statements».data.py.project_euler_statements.p59.keys
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private abbrev source := P59Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
def encode (items : List Int) : List Mutable.Value := items.map number

/-- The collector points to exactly the successive fresh row buffers. -/
def rowRefs (base : Mutable.Heap) (count : Nat) : List Mutable.Value :=
  (HeapRows.addresses base.length count).map Mutable.Value.ref

def collectorRows (base : Mutable.Heap) (rows : List (List Int)) : Mutable.Heap :=
  HeapCollection.working base (rowRefs base rows.length) (rows.map fun row => .list (encode row))

@[simp] theorem collectorRows_nil (base : Mutable.Heap) :
    collectorRows base [] = base ++ [.list []] := by rfl

@[simp] theorem collectorRows_length (base : Mutable.Heap) (rows : List (List Int)) :
    (collectorRows base rows).length = base.length + 1 + rows.length := by
  unfold collectorRows HeapCollection.working
  rw [List.length_append, List.length_cons, List.length_map]
  omega

@[simp] theorem collectorRows_parent (base : Mutable.Heap) (rows : List (List Int)) :
    (collectorRows base rows)[base.length]? = some (.list (rowRefs base rows.length)) :=
  HeapCollection.found _ _ _

theorem collectorRows_prefix (base : Mutable.Heap) (rows : List (List Int))
    (address : Nat) (object : Mutable.Object) (found : base[address]? = some object) :
    (collectorRows base rows)[address]? = some object :=
  HeapCollection.prefix_found base _ address object found

theorem collectorRows_row (base : Mutable.Heap) (rows : List (List Int))
    (index : Nat) (row : List Int) (found : rows[index]? = some row) :
    (collectorRows base rows)[base.length + 1 + index]? = some (.list (encode row)) := by
  unfold collectorRows HeapCollection.working
  rw [List.getElem?_append_right (by omega)]
  have offset : base.length + 1 + index - base.length = index + 1 := by omega
  simp only [offset, List.getElem?_cons_succ, List.getElem?_map, found, Option.map_some]

private theorem collectorRows_push (base : Mutable.Heap) (rows : List (List Int)) (row : List Int) :
    HeapCollection.working base
      (rowRefs base rows.length ++ [.ref (collectorRows base rows).length])
      ((rows.map fun row => .list (encode row)) ++ [.list (encode row)]) =
      collectorRows base (rows ++ [row]) := by
  simp [collectorRows, rowRefs, HeapRows.addresses, List.range_succ, List.map_append,
    List.map_map, Function.comp_def, HeapCollection.working, Nat.add_assoc, Nat.add_comm 1]

private theorem emit_row (base : Mutable.Heap) (rows : List (List Int)) (row : List Int)
    (env : Mutable.Env) (expression : Expr) (globals : Mutable.Globals)
    (evaluated : Evaluates source env expression (collectorRows base rows)
      (.ref (collectorRows base rows).length)
      (collectorRows base rows ++ [.list (encode row)]) globals) :
    BlockContinues source env [.comprehensionAppend base.length expression]
      (collectorRows base rows) env (collectorRows base (rows ++ [row])) globals := by
  have emitted := HeapCollection.emit base (rowRefs base rows.length)
    (rows.map fun row => .list (encode row)) [.list (encode row)]
    (.ref (collectorRows base rows).length) evaluated
  simpa only [collectorRows_push] using emitted

private theorem list_sequence (base : Mutable.Heap) (rows : List (List Int))
    (address : Nat) (alphabet : List Int)
    (found : base[address]? = some (.list (encode alphabet))) :
    Mutable.sequence (.ref address) (collectorRows base rows) =
      some (.ok (encode alphabet), collectorRows base rows) := by
  simp [Mutable.sequence, collectorRows_prefix base rows address _ found]

/-- A sequence loop can emit a whole block of fresh rows per source element.
The invariant records exactly the lexical bindings needed by the next loop. -/
private theorem sequence_rows (alphabet before remaining : List Int)
    (whole : alphabet = before ++ remaining)
    (base : Mutable.Heap) (address : Nat)
    (found : base[address]? = some (.list (encode alphabet)))
    (name : String) (body : List Stmt) (chunk : Int → List (List Int))
    (Good : Mutable.Env → Prop)
    (boundGood : ∀ env value, Good env → Good (setLocal env name (number value)))
    (callback : ∀ value env rows, Good env → env name = some (number value) →
      ∃ finalEnv, Good finalEnv ∧ BlockContinues source env body
        (collectorRows base rows) finalEnv (collectorRows base (rows ++ chunk value)) globals)
    (control : Calls.loopControl body = false)
    (rows : List (List Int)) (env : Mutable.Env) (good : Good env) :
    ∃ finalEnv, Good finalEnv ∧ BlockContinues source env
      [.sequenceStepLoop name (.ref address) before.length body []]
      (collectorRows base rows) finalEnv
      (collectorRows base (rows ++ remaining.flatMap chunk)) globals := by
  induction remaining generalizing before rows env with
  | nil =>
      refine ⟨env, good, ?_⟩
      simp only [List.flatMap_nil, List.append_nil]
      apply BlockContinues.sequence_done (items := encode alphabet)
        (by simpa only [sequenceValue] using list_sequence base rows address alphabet found)
      · simp [whole, encode]
      · exact BlockContinues.nil
  | cons value rest ih =>
      let bound := setLocal env name (number value)
      obtain ⟨nextEnv, nextGood, emitted⟩ := callback value bound rows
        (boundGood env value good) (by simp [bound, setLocal])
      obtain ⟨finalEnv, finalGood, continued⟩ := ih (before ++ [value])
        (by simpa only [List.append_assoc, List.singleton_append] using whole)
        (rows ++ chunk value) nextEnv nextGood
      refine ⟨finalEnv, finalGood, ?_⟩
      apply BlockContinues.sequence_step (items := encode alphabet) (value := number value)
        (by simpa only [sequenceValue] using list_sequence base rows address alphabet found)
      · simp [whole, encode, List.map_append]
      · simpa only [Calls.loopContinuation, control, Bool.false_eq_true, if_false,
          List.length_append, List.length_singleton, List.flatMap_cons, List.append_assoc]
          using emitted.append continued

private abbrev cell (address : Nat) : List Stmt :=
  [.comprehensionAppend address (.list [.name "a", .name "b", .name "c"])]
private abbrev cBody (address : Nat) : List Stmt :=
  [.forIn (.name "c") (.name "letters") (cell address) []]
private abbrev bBody (address : Nat) : List Stmt :=
  [.forIn (.name "b") (.name "letters") (cBody address) []]

private theorem flatMap_singletons {α β : Type*} (xs : List α) (f : α → β) :
    xs.flatMap (fun value => [f value]) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.map_cons, List.singleton_append, ih]

private theorem collect_c (alphabet : List Int) (a b : Int)
    (base : Mutable.Heap) (address : Nat)
    (found : base[address]? = some (.list (encode alphabet)))
    (rows : List (List Int)) (env : Mutable.Env)
    (getLetters : env "letters" = some (.ref address))
    (getA : env "a" = some (number a)) (getB : env "b" = some (number b))
    (globals : Mutable.Globals) :
    ∃ finalEnv,
      (finalEnv "letters" = some (.ref address) ∧
        finalEnv "a" = some (number a) ∧ finalEnv "b" = some (number b)) ∧
      BlockContinues source env (cBody base.length) (collectorRows base rows) finalEnv
        (collectorRows base (rows ++ alphabet.map (fun c => [a, b, c]))) globals := by
  let Good := fun env : Mutable.Env => env "letters" = some (.ref address) ∧
    env "a" = some (number a) ∧ env "b" = some (number b)
  have callback : ∀ value env rows, Good env → env "c" = some (number value) →
      ∃ finalEnv, Good finalEnv ∧ BlockContinues source env (cell base.length)
        (collectorRows base rows) finalEnv (collectorRows base (rows ++ [[a, b, value]])) globals := by
    intro value env rows good getC
    refine ⟨env, good, ?_⟩
    apply emit_row base rows [a, b, value] env _ globals
    apply Evaluates.list
    exact .cons (Evaluates.lookup good.2.1) (.cons (Evaluates.lookup good.2.2)
      (.cons (Evaluates.lookup getC) .nil))
  obtain ⟨finalEnv, finalGood, executed⟩ := sequence_rows alphabet [] alphabet rfl base address found
    "c" (cell base.length) (fun c => [[a, b, c]]) Good
    (by intro env value good; simpa [Good, setLocal] using good)
    callback (by rfl) rows env ⟨getLetters, getA, getB⟩
  refine ⟨finalEnv, finalGood, ?_⟩
  apply BlockContinues.for_sequence (by intro expressions equal; cases equal)
    (Evaluates.lookup getLetters) (list_sequence base rows address alphabet found)
  simpa only [List.length_nil, flatMap_singletons, sequenceSource] using executed

private theorem collect_b (alphabet : List Int) (a : Int)
    (base : Mutable.Heap) (address : Nat)
    (found : base[address]? = some (.list (encode alphabet)))
    (rows : List (List Int)) (env : Mutable.Env)
    (getLetters : env "letters" = some (.ref address))
    (getA : env "a" = some (number a)) (globals : Mutable.Globals) :
    ∃ finalEnv, (finalEnv "letters" = some (.ref address) ∧ finalEnv "a" = some (number a)) ∧
      BlockContinues source env (bBody base.length) (collectorRows base rows) finalEnv
        (collectorRows base (rows ++ alphabet.flatMap (fun b => alphabet.map (fun c => [a, b, c])))) globals := by
  let Good := fun env : Mutable.Env => env "letters" = some (.ref address) ∧ env "a" = some (number a)
  have callback : ∀ value env rows, Good env → env "b" = some (number value) →
      ∃ finalEnv, Good finalEnv ∧ BlockContinues source env (cBody base.length)
        (collectorRows base rows) finalEnv
        (collectorRows base (rows ++ alphabet.map (fun c => [a, value, c]))) globals := by
    intro value env rows good getB
    obtain ⟨finalEnv, finalGood, executed⟩ := collect_c alphabet a value base address found rows env
      good.1 good.2 getB globals
    exact ⟨finalEnv, ⟨finalGood.1, finalGood.2.1⟩, executed⟩
  obtain ⟨finalEnv, finalGood, executed⟩ := sequence_rows alphabet [] alphabet rfl base address found
    "b" (cBody base.length) (fun b => alphabet.map (fun c => [a, b, c])) Good
    (by intro env value good; simpa [Good, setLocal] using good)
    callback (by rfl) rows env ⟨getLetters, getA⟩
  refine ⟨finalEnv, finalGood, ?_⟩
  apply BlockContinues.for_sequence (by intro expressions equal; cases equal)
    (Evaluates.lookup getLetters) (list_sequence base rows address alphabet found)
  simpa only [List.length_nil, sequenceSource] using executed

private theorem collect_a (alphabet : List Int)
    (base : Mutable.Heap) (address : Nat)
    (found : base[address]? = some (.list (encode alphabet)))
    (rows : List (List Int)) (env : Mutable.Env)
    (getLetters : env "letters" = some (.ref address)) (globals : Mutable.Globals) :
    ∃ finalEnv, BlockContinues source env
      [.sequenceStepLoop "a" (.ref address) 0 (bBody base.length) []]
      (collectorRows base rows) finalEnv (collectorRows base
        (rows ++ (XorDecryption.keysFor alphabet).map XorDecryption.keyValues)) globals := by
  let Good := fun env : Mutable.Env => env "letters" = some (.ref address)
  have callback : ∀ value env rows, Good env → env "a" = some (number value) →
      ∃ finalEnv, Good finalEnv ∧ BlockContinues source env (bBody base.length)
        (collectorRows base rows) finalEnv (collectorRows base
          (rows ++ alphabet.flatMap (fun b => alphabet.map (fun c => [value, b, c])))) globals := by
    intro value env rows good getA
    obtain ⟨finalEnv, finalGood, executed⟩ := collect_b alphabet value base address found rows env good getA globals
    exact ⟨finalEnv, finalGood.1, executed⟩
  obtain ⟨finalEnv, finalGood, executed⟩ := sequence_rows alphabet [] alphabet rfl base address found
    "a" (bBody base.length)
    (fun a => alphabet.flatMap (fun b => alphabet.map (fun c => [a, b, c]))) Good
    (by intro env value good; simpa [Good, setLocal] using good)
    callback (by rfl) rows env getLetters
  refine ⟨finalEnv, ?_⟩
  simpa only [List.length_nil, XorDecryption.keysFor_map_keyValues] using executed

/-- Pure materialization of the one letters buffer; unlike the row collector
this comprehension has no per-element allocations. -/
private theorem letters_loop (first count stop : Nat) (endpoint : first + count = stop)
    (base : Mutable.Heap) (values : List Int) (env : Mutable.Env) (globals : Mutable.Globals) :
    ∃ finalEnv, BlockContinues source env
      [.rangeStepLoop "$formalsw.range.item" first stop 1
        [.comprehensionAppend base.length (.name "$formalsw.range.item")] []]
      (HeapCollection.working base (encode values) []) finalEnv
      (HeapCollection.working base
        (encode (values ++ (List.range' first count).map (fun n : Nat => (n : Int)))) []) globals := by
  induction count generalizing first values env with
  | zero =>
      refine ⟨env, ?_⟩
      simp only [List.range'_zero, List.map_nil, List.append_nil]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  | succ count ih =>
      let bound := setLocal env "$formalsw.range.item" (number first)
      have evaluated : Evaluates source bound (.name "$formalsw.range.item")
          (HeapCollection.working base (encode values) []) (number first)
          (HeapCollection.working base (encode values) []) globals :=
        Evaluates.lookup (by simp [bound, setLocal])
      have emitted := HeapCollection.emit base (encode values) [] [] (number first)
        (by simpa only [List.append_nil] using evaluated)
      have stored : BlockContinues source bound
          [.comprehensionAppend base.length (.name "$formalsw.range.item")]
          (HeapCollection.working base (encode values) []) bound
          (HeapCollection.working base (encode (values ++ [(first : Int)])) []) globals := by
        simpa only [encode, List.map_append, List.map_singleton, List.nil_append] using emitted
      obtain ⟨finalEnv, continued⟩ := ih (first + 1) (by omega) (values ++ [(first : Int)]) bound
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        encode, List.map_append, List.range'_succ, List.append_assoc] using stored.append continued

private abbrev lettersExpression : Expr :=
  .listComp (.name "$formalsw.range.item")
    [("$formalsw.range.item", .call (.name "range") [.constant (.int 97), .constant (.int 123)], [])]
private abbrev generators : List (String × Expr × List Expr) :=
  [("a", .name "letters", []), ("b", .name "letters", []), ("c", .name "letters", [])]
private abbrev element : Expr := .list [.name "a", .name "b", .name "c"]

private theorem letters_evaluates (heap : Mutable.Heap) (env : Mutable.Env) (globals : Mutable.Globals) :
    Evaluates source env lettersExpression heap (.ref heap.length)
      (heap ++ [.list (encode XorDecryption.letters)]) globals := by
  obtain ⟨finalEnv, executed⟩ := letters_loop 97 26 123 (by decide) heap []
    (comprehensionEnv env [("$formalsw.range.item",
      .call (.name "range") [.constant (.int 97), .constant (.int 123)], [])]) globals
  apply Evaluates.list_comp_range
    (.cons (Evaluates.constant (value := .int 97)) (.cons (Evaluates.constant (value := .int 123)) .nil)) rfl
  simpa only [lettersExpression, comprehensionFilters, List.foldr_nil, comprehensionBody,
    encode, List.map_nil, List.nil_append, HeapCollection.working, XorDecryption.letters,
    List.map_map, Function.comp_def] using executed

/-- One letters list, one outer collector, then 17576 distinct key buffers.
This definition deliberately retains the symbolic mathematical key space. -/
def materialized (heap : Mutable.Heap) : Mutable.Heap :=
  collectorRows (heap ++ [.list (encode XorDecryption.letters)])
    (XorDecryption.keys.map XorDecryption.keyValues)

/-- Actual source execution for arbitrary caller heaps and global environments. -/
theorem result (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue source "keys" [] heap (.ref (heap.length + 1)) (materialized heap) globals := by
  let params := ((findFunctionIn source.body "keys").getD ([], [])).1
  let body := ((findFunctionIn source.body "keys").getD ([], [])).2
  let initial := functionEnv params body [] globals
  let base := heap ++ [.list (encode XorDecryption.letters)]
  let assigned := setLocal initial "letters" (.ref heap.length)
  let masked := comprehensionEnv assigned generators
  have found : base[heap.length]? = some (.list (encode XorDecryption.letters)) := by simp [base]
  have getLetters : masked "letters" = some (.ref heap.length) := by
    simp [masked, comprehensionEnv, generators, assigned, setLocal]
  obtain ⟨finalEnv, executed⟩ := collect_a XorDecryption.letters base heap.length found [] masked getLetters globals
  have keyed : Evaluates source assigned (.listComp element generators) base (.ref base.length)
      (materialized heap) globals := by
    apply Evaluates.list_comp_sequence (finalEnv := finalEnv) (value := .ref heap.length) (items := encode XorDecryption.letters)
      (by intro expressions equal; cases equal) (Evaluates.lookup (by simp [assigned, setLocal]))
      (by simp [Mutable.sequence, found])
    simpa only [materialized, XorDecryption.keys, generators, element, comprehensionFilters,
      List.foldr_nil, comprehensionBody, collectorRows_nil, List.nil_append, sequenceSource,
      masked, cell, cBody, bBody, base] using executed
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (letters_evaluates heap initial globals)
  apply BlockReturns.return_value
  simpa only [base, List.length_append, List.length_singleton, assigned, initial, params, body,
    element, generators] using keyed

/-- The source's returned sequence contains exactly the actual fresh addresses. -/
theorem outer_found (heap : Mutable.Heap) :
    (materialized heap)[heap.length + 1]? =
      some (.list (rowRefs (heap ++ [.list (encode XorDecryption.letters)]) 17576)) := by
  have baseLength : (heap ++ [Mutable.Object.list (encode XorDecryption.letters)]).length = heap.length + 1 :=
    List.length_append
  have run := collectorRows_parent (heap ++ [.list (encode XorDecryption.letters)])
    (XorDecryption.keys.map XorDecryption.keyValues)
  rw [baseLength] at run
  simpa only [materialized, List.length_map, XorDecryption.keys_length] using run

/-- Each lexicographic key index resolves to its three integer values. -/
theorem key_found (heap : Mutable.Heap) (index : Nat) (key : XorDecryption.Key)
    (found : XorDecryption.keys[index]? = some key) :
    (materialized heap)[heap.length + 2 + index]? =
      some (.list (encode (XorDecryption.keyValues key))) := by
  have mapped : (XorDecryption.keys.map XorDecryption.keyValues)[index]? =
      some (XorDecryption.keyValues key) := by simp only [List.getElem?_map, found, Option.map_some]
  have baseLength : (heap ++ [Mutable.Object.list (encode XorDecryption.letters)]).length = heap.length + 1 :=
    List.length_append
  have run := collectorRows_row (heap ++ [.list (encode XorDecryption.letters)])
    (XorDecryption.keys.map XorDecryption.keyValues) index (XorDecryption.keyValues key) mapped
  rw [baseLength] at run
  have indexEqual : heap.length + 1 + 1 + index = heap.length + 2 + index := by omega
  simpa only [materialized, indexEqual] using run

theorem caller_found (heap : Mutable.Heap) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) : (materialized heap)[address]? = some object :=
  collectorRows_prefix _ _ address object (HeapCollection.prefix_found heap _ address object found)

/-- Exactly two infrastructure cells and one fresh list per key are appended. -/
theorem materialized_length (heap : Mutable.Heap) :
    (materialized heap).length = heap.length + 17578 := by
  simp [materialized, XorDecryption.keys_length, Nat.add_assoc]

theorem letters_found (heap : Mutable.Heap) :
    (materialized heap)[heap.length]? = some (.list (encode XorDecryption.letters)) := by
  apply collectorRows_prefix
  simp

theorem key_found_shape (heap : Mutable.Heap) (index : Nat) (key : XorDecryption.Key)
    (found : XorDecryption.keys[index]? = some key) :
    (materialized heap)[heap.length + 2 + index]? =
      some (.list [number key.1, number key.2.1, number key.2.2]) := by
  simpa only [encode, XorDecryption.keyValues, List.map_cons, List.map_nil] using key_found heap index key found

end data.«project-euler-statements».data.py.project_euler_statements.p59.keys

namespace data.«project-euler-statements».data.py.project_euler_statements.p59.keys
open FormalSW.PyAst

theorem «Returns» : (HeapCalls.call P59Ast.module "keys" [] []).Returns :=
  (result []).returns

theorem «Supported» : (HeapCalls.call P59Ast.module "keys" [] []).Supported :=
  «Returns».supported

end data.«project-euler-statements».data.py.project_euler_statements.p59.keys
