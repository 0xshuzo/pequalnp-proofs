import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4785_17
    (pack : let P : Finset (Fin 58) := Finset.univ.filter (fun i : Fin 58 => i.val < 21)
      let op := fun (M : Finset (Finset (Fin 58))) (z : Finset (Fin 58)) =>
        ∃ a ∈ M, ∃ b ∈ M, z = a ∪ b ∨ z = a ∩ b
      let low := fun z : Finset (Fin 58) => z ⊆ P ∧ z.card ≤ 1
      ∀ (cols : List (Finset (Fin 58))) (C : Circuit), Monotone2 C →
        (∀ k : Fin 58, C.eval (cols.map (fun z => decide (k ∈ z))) = true ↔ k ∈ P) →
        let I := insert ∅ (insert Finset.univ cols.toFinset)
        ∃ S : List (Finset (Fin 58)), S.length ≤ C.size ∧
        (∀ (u v : List (Finset (Fin 58))) (z : Finset (Fin 58)), S = u ++ z :: v →
          low z ∨ (2 ≤ (z ∩ P).card ∧ op (I ∪ u.toFinset) z)) ∧ P ∈ I ∪ S.toFinset)
    (hoist : let P : Finset (Fin 58) := Finset.univ.filter (fun i : Fin 58 => i.val < 21)
      let op := fun (M : Finset (Finset (Fin 58))) (z : Finset (Fin 58)) =>
        ∃ a ∈ M, ∃ b ∈ M, z = a ∪ b ∨ z = a ∩ b
      let low := fun z : Finset (Fin 58) => z ⊆ P ∧ z.card ≤ 1
      ∀ (I : Finset (Finset (Fin 58))) (S : List (Finset (Fin 58))), ∅ ∈ I →
        (∀ (u v : List (Finset (Fin 58))) (z : Finset (Fin 58)), S = u ++ z :: v →
          low z ∨ (2 ≤ (z ∩ P).card ∧ op (I ∪ u.toFinset) z)) → P ∈ I ∪ S.toFinset →
        ∃ (A : Finset (Fin 58)) (T : List (Finset (Fin 58))), A ⊆ P ∧
          A.card + T.length ≤ S.length ∧ (∀ (u v : List (Finset (Fin 58))) (z : Finset (Fin 58)), T = u ++ z :: v →
          2 ≤ (z ∩ P).card ∧ op (I ∪ A.image (fun q => {q}) ∪ u.toFinset) z) ∧ P ∈ I ∪ A.image (fun q => {q}) ∪ T.toFinset)
    (bound : let P : Finset (Fin 58) := Finset.univ.filter (fun i : Fin 58 => i.val < 21)
      let op := fun (M : Finset (Finset (Fin 58))) (z : Finset (Fin 58)) =>
        ∃ a ∈ M, ∃ b ∈ M, z = a ∪ b ∨ z = a ∩ b
      let col := fun (i : Fin 14) => Finset.univ.filter (fun k : Fin 58 =>
        (([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]: List ℕ).getD i.val 0).testBit k.val = true)
      ∀ r : Fin 14, r = 7 ∨ r = 9 →
        let I : Finset (Finset (Fin 58)) := insert ∅ (insert Finset.univ (List.ofFn col ++ [col 0 ∪ col r]).toFinset)
        ∀ (A : Finset (Fin 58)) (T : List (Finset (Fin 58))), A ⊆ P →
          (∀ (u v : List (Finset (Fin 58))) (z : Finset (Fin 58)), T = u ++ z :: v →
          2 ≤ (z ∩ P).card ∧ op (I ∪ A.image (fun q => {q}) ∪ u.toFinset) z) → P ∈ I ∪ A.image (fun q => {q}) ∪ T.toFinset → 26 ≤ A.card + T.length) :
    have x1 : ℕ → ℕ → Prop := fun (x1 x2 : ℕ) => ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD x1 (0 : ℕ)).testBit x2 = Bool.true; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), x1 ↑x3 ↑x4 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Fin (14 : ℕ) → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (14 : ℕ)) => PEqualNP.MetaComplexity.Monotone2 x4 ∧ ∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → (x4.eval (List.ofFn x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 (0 : Fin (14 : ℕ)), x6 x5]]) = Bool.true ↔ x2 x6); have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x6 ∈ x5.gates, x6.op = PEqualNP.CircuitLowerBounds.GateOp.and → ((14 : ℕ) ∈ x6.inputs → ∀ x10 ∈ x6.inputs, (14 : ℕ) ≤ x10) ∧ ∀ (x9 x10 : ℕ), x6.inputs = [x9, x10] → x9 < (14 : ℕ) → x10 < (14 : ℕ) → x9 ≠ x10 → x1 x9 x10 ∨ x1 x10 x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Fin (14 : ℕ)), x7 = (7 : Fin (14 : ℕ)) ∨ x7 = (9 : Fin (14 : ℕ)) → x4 x6 x7 → x5 x6 → (26 : ℕ) ≤ x6.size := by
  let E := fun u v : ℕ => (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u 0).testBit v = true
  let F := fun x : Fin 14 → Bool => ∃ u v : Fin 14, E u.val v.val ∧ x u=true ∧ x v=true
  let B := fun x : Fin 14 → Bool =>
    (F x ∧ ∀ i, x i=true → ¬ F (Function.update x i false)) ∨
    (¬ F x ∧ ∀ i, x i=false → F (Function.update x i true))
  let P : Finset (Fin 58) := Finset.univ.filter (fun i : Fin 58 => i.val < 21)
  let col := fun (i : Fin 14) => Finset.univ.filter (fun k : Fin 58 =>
        (([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]: List ℕ).getD i.val 0).testBit k.val = true)
  let row := fun (k : Fin 58) (i : Fin 14) => (([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752] : List ℕ).getD i.val 0).testBit k.val
  have cert : ∀ k : Fin 58, B (row k) ∧ (F (row k) ↔ k.val < 21) := by
    dsimp only [B,F,E,row]
    decide +kernel
  change ∀ (C : Circuit) (r : Fin 14), (r=7 ∨ r=9) →
    (Monotone2 C ∧ ∀ x, B x → (C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x r]]) = true ↔ F x)) →
    _ → 26 ≤ C.size
  intro C r hr hc _
  let cols := List.ofFn col ++ [col 0 ∪ col r]
  let I : Finset (Finset (Fin 58)) := insert ∅ (insert Finset.univ (List.ofFn col ++ [col 0 ∪ col r]).toFinset)
  have input (k : Fin 58) :
      cols.map (fun z => decide (k ∈ z)) = List.ofFn (row k) ++ [GateOp.or.eval [row k 0,row k r]] := by
    have getCol (i : Fin 14) : decide (k ∈ col i) = row k i := by
      apply Bool.eq_iff_iff.2
      rw [decide_eq_true_eq]
      exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
    have joinCol : decide (k ∈ col 0 ∪ col r) = (row k 0 || row k r) := by
      rw [← getCol 0,← getCol r]
      simp
    simp only [cols,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    have pre : (fun i : Fin 14 => decide (k ∈ col i)) = row k := funext getCol
    change List.ofFn (fun i : Fin 14 => decide (k ∈ col i)) ++ [decide (k ∈ col 0 ∪ col r)] =
      List.ofFn (row k) ++ [row k 0 || (row k r || false)]
    rw [pre,joinCol,Bool.or_false]
  have correct (k : Fin 58) : C.eval (cols.map fun z => decide (k ∈ z)) = true ↔ k ∈ P := by
    rw [input,hc.2 _ (cert k).1,(cert k).2]
    simp [P]
  obtain ⟨S,hs,hsteps,goalS⟩ := pack cols C hc.1 correct
  obtain ⟨A,T,ha,short,steps,out⟩ := hoist I S (Finset.mem_insert_self _ _) hsteps goalS
  have h := bound r hr A T ha steps out
  omega
