import ProjectEulerSolutions.Lib.DigitDiceSelections
import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».RotationCore
import lang.py.FormalSW.CombinationCalls

/-! Each positional combination is copied into its own fresh list, retaining repeated labels. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p90.choose_faces
open FormalSW.PyAst HeapCalls ProjectEulerSolutions DigitDice
set_option Elab.async false

structure Row where
  labels : List Nat
  address : Nat

def Row.reference (row : Row) : Mutable.Value := .ref row.address
def Row.Valid (row : Row) (heap : Mutable.Heap) : Prop :=
  heap[row.address]? = some (.list (row.labels.map number))

def captured (rows : List (List Nat)) : List (List SequenceSource) :=
  rows.map (fun row => (row.map number).map sequenceSource)

def body (address : Nat) : List Stmt :=
  [.comprehensionAppend address (.builtinCall .list [.name "c"])]

/-- Copying an emitted tuple allocates a separate list before appending its reference. -/
theorem emit (base : Mutable.Heap) (values : List Mutable.Value) (garbage : Mutable.Heap)
    (digits : List Nat) (address : Nat) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (found : (HeapCollection.working base values garbage)[address]? = some (.tuple (digits.map number)))
    (getRow : env "c" = some (.ref address)) :
    BlockContinues program env (body base.length) (HeapCollection.working base values garbage) env
      (HeapCollection.working base (values ++ [.ref (HeapCollection.working base values garbage).length])
        (garbage ++ [.list (digits.map number)])) globals := by
  apply HeapCollection.emit (program := program) (globals := globals) base values garbage [.list (digits.map number)]
  exact Evaluates.builtin (.cons (Evaluates.lookup getRow) .nil)
    (primitive_list_tuple _ address (digits.map number) found)

/-- Every captured row produces one list; the collector preserves all existing noncollector objects. -/
theorem collect (rows : List (List Nat)) (base : Mutable.Heap) (values : List Mutable.Value)
    (garbage : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals) :
    ∃ (output : List Row) (extra : Mutable.Heap) (finalEnv : HeapCalls.Env),
      output.map Row.labels = rows ∧
      BlockContinues program env [.permutationStepLoop "c" (captured rows) (body base.length) []]
        (HeapCollection.working base values garbage) finalEnv
        (HeapCollection.working base (values ++ output.map Row.reference) (garbage ++ extra)) globals ∧
      ∀ row ∈ output, base.length < row.address ∧
        row.Valid (HeapCollection.working base (values ++ output.map Row.reference) (garbage ++ extra)) := by
  induction rows generalizing values garbage env with
  | nil =>
      refine ⟨[], [], env, rfl, ?_, by simp⟩
      simpa [captured] using (BlockContinues.permutation_done (module := program) (globals := globals)
        (env := env) (name := "c") (body := body base.length)
        (heap := HeapCollection.working base values garbage) BlockContinues.nil)
  | cons digits rest ih =>
      obtain ⟨address, tupleExtra, allocated, found⟩ :=
        HeapCollection.allocate_tuple (digits.map number) (HeapCollection.working base values garbage)
      let afterTuple := HeapCollection.working base values (garbage ++ tupleExtra)
      let row : Row := ⟨digits, afterTuple.length⟩
      let bound := setLocal env "c" (.ref address)
      have tupleFound : afterTuple[address]? = some (.tuple (digits.map number)) := by
        simpa only [afterTuple, HeapCollection.append] using found
      have emitted := emit base values (garbage ++ tupleExtra) digits address bound globals tupleFound rfl
      obtain ⟨output, extra, finalEnv, models, continued, valid⟩ :=
        ih (values ++ [row.reference]) ((garbage ++ tupleExtra) ++ [.list (digits.map number)]) bound
      refine ⟨row :: output, (tupleExtra ++ [.list (digits.map number)]) ++ extra, finalEnv, ?_, ?_, ?_⟩
      · simp only [List.map_cons, models, row]
      · apply BlockContinues.permutation_step (tuple := .ref address) (middle := afterTuple)
        · simpa [captured, List.map_map, Function.comp_def, sequenceValue, sequenceSource,
            afterTuple, HeapCollection.append] using allocated
        · simpa only [body, List.map_cons, List.append_assoc, List.singleton_append,
            Row.reference, row, afterTuple] using emitted.append continued
      · intro selected member
        have later : ∀ selected ∈ output, base.length < selected.address ∧
            selected.Valid (HeapCollection.working base (values ++ (row :: output).map Row.reference)
              (garbage ++ ((tupleExtra ++ [.list (digits.map number)]) ++ extra))) := by
          simpa only [List.map_cons, List.append_assoc, List.singleton_append] using valid
        rcases List.mem_cons.mp member with rfl | member
        · have fresh : base.length < row.address := by
            simp [row, afterTuple, HeapCollection.working]
          refine ⟨fresh, ?_⟩
          have allocatedList : (afterTuple ++ [.list (digits.map number)])[row.address]? =
              some (.list (digits.map number)) := by simp [row]
          have atCollector : (HeapCollection.working base values ((garbage ++ tupleExtra) ++ [.list (digits.map number)]))[row.address]? =
              some (.list (digits.map number)) := by simpa only [afterTuple, HeapCollection.append] using allocatedList
          have kept := HeapCollection.other_found base values (values ++ (row :: output).map Row.reference)
            ((garbage ++ tupleExtra) ++ [.list (digits.map number)]) extra row.address _ (Nat.ne_of_lt fresh) atCollector
          simpa only [Row.Valid, row, List.append_assoc] using kept
        · exact later selected member

end data.«project-euler-statements».data.py.project_euler_statements.p90.choose_faces
