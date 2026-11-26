import PEqualNP.Outside.L_meta_5148
import PEqualNP.Outside.L_meta_5150
import PEqualNP.Outside.L_meta_18284

namespace Petersen4940Pilot
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pet : (Fin 10 → Bool) → Bool := fun x : Fin 10 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def rawReaders (C : Circuit) (v : Fin 10) (S : Finset ℕ) : Prop :=
  ∀ j ∈ S, ∃ g : Gate, C.gates[j]? = some g ∧ (v : ℕ) ∈ g.inputs ∧
    (g.op = GateOp.not → g.inputs.head? = some (v : ℕ))

-- Every counterexample to the posted output-tap conclusion gives this
-- particular last-OR circuit. The two accounting bounds hold together.
theorem budget (C : Circuit) (fan : FanInTwo C) (size : C.size = 19)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = pet x) :
    PEqualNP.NotBracket.notCount C ≤ 2 ∧
    ∀ v : Fin 10, ∀ S : Finset ℕ, rawReaders C v S → S.card ≤ 3 := by
  constructor
  · have floor := PEqualNP.Outside.L_meta_18284 C fan computes
    omega
  · intro v S reads
    have key : ∀ i : Fin 10, pet (fun j => decide (j ≠ i)) = true := by decide
    rcases PEqualNP.Outside.L_meta_5148 10 C v S fan reads with ⟨c,hc⟩ | ⟨D,fanD,ds,agrees⟩
    · cases c with
      | false =>
        have h := computes (fun i => decide (i ≠ v))
        rw [hc _ (by simp), key v] at h
        exact (Bool.false_ne_true h).elim
      | true =>
        have h := computes (fun _ => false)
        rw [hc _ rfl] at h
        exact (Bool.false_ne_true h.symm).elim
    · by_contra h
      have ds' : D.size + (if false = true then 1 else 0) ≤ 15 := by
        simp only [Bool.false_eq_true, ite_false]
        omega
      obtain ⟨x,hv,hn⟩ := PEqualNP.Outside.L_meta_5150 v D false fanD ds'
      apply hn
      simpa only [Bool.false_eq_true, ite_false, agrees x hv] using computes x

def prefix (g : Gate) (tail : Circuit) : Circuit := ⟨g :: tail.gates, 0⟩

def tap (g : Gate) (tail : Circuit) (x : Fin 10 → Bool) (w : ℕ) : Bool :=
  ((prefix g tail).wires (List.ofFn x)).getD w false

theorem extract (g : Gate) (tail : Circuit) (a b : ℕ)
    (fanG : FanInTwo (⟨[g],0⟩ : Circuit)) (fanT : FanInTwo tail) (sizeT : tail.size = 17)
    (off : ∀ x, pet x = false → tap g tail x a = false ∧ tap g tail x b = false)
    (missed : ¬ ∃ x, pet x = true ∧ tap g tail x a = false ∧ tap g tail x b = false) :
    ∃ E : Circuit, E.gates = (g :: tail.gates) ++ [⟨.or,[a,b]⟩] ∧ FanInTwo E ∧
      E.size = 19 ∧ (∀ x, E.eval (List.ofFn x) = pet x) ∧
      PEqualNP.NotBracket.notCount E ≤ 2 ∧
      (∀ v S, rawReaders E v S → S.card ≤ 3) := by
  let F := pet
  let D : Circuit := ⟨g :: tail.gates, 0⟩
  let W := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x)).getD i false
  have fanD : FanInTwo D := by
    intro h mem
    rcases List.mem_cons.mp mem with rfl | ht
    · exact fanG _ List.mem_cons_self
    · exact fanT _ ht
  have sizeD : D.size = 18 := by
    change (g :: tail.gates).length = 18
    change tail.gates.length = 17 at sizeT
    simp only [List.length_cons, sizeT]
  have covered (x : Fin 10 → Bool) : (W x a || W x b) = F x := by
    cases hf : F x with
    | false =>
      obtain ⟨ha, hb⟩ := off x hf
      rw [ha, hb]
      rfl
    | true =>
      cases ha : W x a <;> cases hb : W x b
      · exact False.elim (missed ⟨x, hf, ha, hb⟩)
      all_goals rfl
  let last : Gate := ⟨GateOp.or, [a, b]⟩
  let E : Circuit := ⟨D.gates ++ [last], 10 + D.size⟩
  have fanE : FanInTwo E := by
    intro h mem
    rcases List.mem_append.mp mem with hd | hl
    · exact fanD _ hd
    · have eq : h = last := List.mem_singleton.mp hl
      subst h
      exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
  have sizeE : E.size = 19 := by
    change (D.gates ++ [last]).length = 19
    change D.gates.length = 18 at sizeD
    simp only [List.length_append, List.length_singleton, sizeD]
  have lenW (gs : List Gate) (w : List Bool) :
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons h gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have orEval (u v : Bool) : GateOp.or.eval [u, v] = (u || v) := by
    cases u <;> cases v <;> rfl
  have computes (x : Fin 10 → Bool) : E.eval (List.ofFn x) = F x := by
    have dl : (D.wires (List.ofFn x)).length = 10 + D.size := by
      change (D.gates.foldl _ (List.ofFn x)).length = _
      rw [lenW]
      simp only [List.length_ofFn]
      rfl
    change ((D.gates ++ [last]).foldl _ (List.ofFn x)).getD (10 + D.size) false = _
    rw [List.foldl_append]
    change ((D.wires (List.ofFn x)) ++ [GateOp.or.eval [W x a, W x b]]).getD (10 + D.size) false = _
    rw [orEval, ← dl]
    simpa using covered x

  obtain ⟨notBound,readerBound⟩ := budget E fanE sizeE computes
  exact ⟨E,rfl,fanE,sizeE,computes,notBound,readerBound⟩

end Petersen4940Pilot
