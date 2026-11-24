import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 2300000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_2223_417
  (crossing : ∀ (C : Circuit) (i : Fin 14) (T : ℕ → Prop), (∀ (j : ℕ) (g : Gate), C.gates[j]?=some g →
      (g.op=.and ∨ g.op=.or) ∧ ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j) →
    T C.output → (∀ j (g : Gate), C.gates[j]?=some g → T (14+j) → ∀ a∈g.inputs, T a) → 2≤C.lineDeg 14 {i.val} →
    ∃ (j : ℕ) (g : Gate), C.gates[j]?=some g ∧ T (14+j) ∧ g.op=.and ∧
      (∀ a∈g.inputs, (C.lineDegrees 14 {i.val}).getD a 0=1) ∧
      ∀ a<14+j, T a → (C.lineDegrees 14 {i.val}).getD a 0≤1)
  (exclude : let I := fun p l : Fin 7 => p=l ∨ p=l+1 ∨ p=l+3
    ¬∃ (C : Circuit) (p l : Fin 7), C.size≤27 ∧ (∀ (j : ℕ) (g : Gate), C.gates[j]?=some g →
      (g.op=.and ∨ g.op=.or) ∧ ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔
        ∃ u v : Fin 7, I u v ∧ x (Fin.castAdd 7 u)=true ∧ x (Fin.natAdd 7 v)=true) ∧ I p l ∧
      (¬((C.output::C.gates.flatMap Gate.inputs).filter (fun w => decide (14≤w))).Nodup) ∧
      let T (w : ℕ) := Relation.ReflTransGen (fun a b : ℕ => ∃ (j : ℕ) (g : Gate),
        b=14+j ∧ C.gates[j]?=some g ∧ a∈g.inputs) w C.output
      ∀ i∈[Fin.castAdd 7 p, Fin.natAdd 7 l], ∃ (j : ℕ) (g : Gate), C.gates[j]?=some g ∧ T (14+j) ∧ g.op=.and ∧
      (∀ a∈g.inputs, (C.lineDegrees 14 {i.val}).getD a 0=1) ∧
      ∀ a<14+j, T a → (C.lineDegrees 14 {i.val}).getD a 0≤1) :
  have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x1 x5 x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x2 x11 ∧ x3 x11 ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {↑x5} ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} := by
  intro inc valid tree C p l hv edge dp dl
  by_cases ht : tree C
  · exact ⟨C,hv,ht,dp,dl⟩
  apply False.elim
  apply exclude
  refine ⟨C,p,l,hv.1,hv.2.1,hv.2.2,edge,ht,?_⟩
  let T (w : ℕ) := Relation.ReflTransGen (fun a b : ℕ => ∃ (j : ℕ) (g : Gate),
        b=14+j ∧ C.gates[j]?=some g ∧ a∈g.inputs) w C.output
  dsimp only
  intro i hi
  have deg : 2≤C.lineDeg 14 {i.val} := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl
    · exact dp
    · exact dl
  apply crossing C i T hv.2.1 Relation.ReflTransGen.refl _ deg
  intro j g hg along a ha
  exact Relation.ReflTransGen.head ⟨j,g,rfl,hg,ha⟩ along
