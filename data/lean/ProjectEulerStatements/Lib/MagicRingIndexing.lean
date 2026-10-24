import ProjectEulerStatements.Lib.MagicRingRotation

/-! Indexed cyclic lines and the serialization order used by the Python helpers. -/
namespace ProjectEulerStatements.MagicRing
set_option Elab.async false

theorem cycle_getElem {n : Nat} (ring : Ring n) (index : Nat) (inside : index < n) :
    (cycle ring.outer ring.inner)[index]'(by rw [cycle_length]; exact inside) =
      (ring.outer[index]'(by rw [ring.outer_length]; exact inside),
       ring.inner[index]'(by rw [ring.inner_length]; exact inside),
       ring.inner[(index + 1) % n]'(by rw [ring.inner_length]; exact Nat.mod_lt _ (by omega))) := by
  simp only [cycle, triples, List.getElem_zipWith, List.getElem_zip, List.getElem_rotate,
    ring.inner_length]

def lineText (outer inner : List Nat) (index : Nat) : String :=
  toString ((outer[index]?).getD 0 : Int) ++ toString ((inner[index]?).getD 0 : Int) ++
    toString ((inner[(index + 1) % inner.length]?).getD 0 : Int)

def textFrom (outer inner : List Nat) (start : Nat) : String :=
  String.join ((List.range inner.length).map (fun offset =>
    lineText outer inner ((start + offset) % inner.length)))

def render (triple : Nat × Nat × Nat) : String :=
  toString (triple.1 : Int) ++ toString (triple.2.1 : Int) ++ toString (triple.2.2 : Int)

theorem lineText_cycle {n : Nat} (ring : Ring n) (index : Nat) (inside : index < n) :
    lineText ring.outer ring.inner index =
      render ((cycle ring.outer ring.inner)[index]'(by rw [cycle_length]; exact inside)) := by
  rw [cycle_getElem ring index inside]
  simp only [lineText, render, ring.inner_length,
    List.getElem?_eq_getElem (show index < ring.outer.length by
      rw [ring.outer_length]; exact inside),
    List.getElem?_eq_getElem (show index < ring.inner.length by
      rw [ring.inner_length]; exact inside),
    List.getElem?_eq_getElem (show (index + 1) % n < ring.inner.length by
      rw [ring.inner_length]; exact Nat.mod_lt _ (by omega)), Option.getD_some]

/-- Source offsets traverse exactly the rotated list of cyclic lines. -/
theorem textFrom_eq_rotated {n : Nat} (ring : Ring n) (start : Nat) :
    textFrom ring.outer ring.inner start =
      text (ring.rotate start).outer (ring.rotate start).inner := by
  have parts : (List.range n).map
      (fun offset => lineText ring.outer ring.inner ((start + offset) % n)) =
      (cycle (ring.rotate start).outer (ring.rotate start).inner).map render := by
    apply List.ext_getElem?
    intro index
    by_cases inside : index < n
    · have inRange : index < (List.range n).length := by simpa using inside
      have inCycle : index <
          (cycle (ring.rotate start).outer (ring.rotate start).inner).length := by
        rw [cycle_length]
        exact inside
      rw [List.getElem?_map, List.getElem?_eq_getElem inRange, List.getElem_range, Option.map_some,
        List.getElem?_map, List.getElem?_eq_getElem inCycle, Option.map_some]
      have rotated : (cycle (ring.rotate start).outer (ring.rotate start).inner)[index] =
          (cycle ring.outer ring.inner)[(index + start) % n]'(by
            rw [cycle_length]; exact Nat.mod_lt _ (by omega)) := by
        simp only [cycle_rotate, List.getElem_rotate, cycle_length]
      rw [rotated]
      congr 1
      simpa only [Nat.add_comm start index] using
        lineText_cycle ring ((index + start) % n) (Nat.mod_lt _ (by omega))
    · have first : (List.range n)[index]? = none :=
        List.getElem?_eq_none (by simpa using (by omega : n ≤ index))
      have second : (cycle (ring.rotate start).outer (ring.rotate start).inner)[index]? = none :=
        List.getElem?_eq_none (by rw [cycle_length]; omega)
      simp only [List.getElem?_map, first, second, Option.map_none]
  unfold textFrom text
  rw [ring.inner_length, parts]
  rfl

end ProjectEulerStatements.MagicRing
