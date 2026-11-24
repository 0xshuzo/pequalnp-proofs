import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5176_417
    (hpin : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (z : Fin n → Bool) (S : Set ℕ),
    PEqualNP.TopForm.IsAO2 n C →
    let w := fun k => (C.wires (List.ofFn z)).getD k false
    (∀ i : Fin n, ↑i ∈ S → z i = false) →
    (∀ j g, C.gates[j]? = some g → n+j ∈ S →
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i ∈ g.inputs, i ∈ S) ∧
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∃ i ∈ g.inputs, i ∈ S) ∨ ∀ i ∈ g.inputs, w i = false)) →
    ∀ k ∈ S, w k = false)
    (hfinite : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), 63 ≤ C.size → C.size ≤ 64 →
    PEqualNP.TopForm.IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
    let E := fun p l : Fin 13 => (p-l) ∈ ([0,1,3,9] : List (Fin 13))
    let row := fun (P L : Fin 13 → Bool) => List.ofFn (Fin.addCases P L)
    (∀ p l, E p l → C.eval (row (fun t => decide (t=p)) (fun t => decide (t=l))) = true) →
    (∀ T : Finset (Fin 13), T.card ≤ 3 →
      let pick := fun t => decide (t∈T)
      C.eval (row pick (fun l => decide (∀ p∈T, ¬E p l))) = false ∧
      C.eval (row (fun p => decide (∀ l∈T, ¬E p l)) pick) = false) →
    ∃ b ∈ ([0,13] : List ℕ),
      let w := (C.wires (List.ofFn fun t : Fin 26 => ((2:ℕ)^b).testBit t.val))
      Relation.ReflTransGen (fun a k => ∃ j g q, C.gates[j]? = some g ∧ k = 26+j ∧
        (g.inputs = [a,q] ∨ g.inputs = [q,a]) ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ w.getD q false = true)) (13-b) C.output) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             have x7 : ℕ → ℕ → Bool := fun (x7 x8 : ℕ) => (x1.wires (List.ofFn fun (x9 : Fin (26 : ℕ)) => x7.testBit ↑x9)).getD x8 Bool.false;             ∃ x8 ∈ [(0 : ℕ), (13 : ℕ)],               have x9 : ℕ := if x8 = (0 : ℕ) then (25034751 : ℕ) else (67108341 : ℕ);               have x10 : ℕ := if x8 = (0 : ℕ) then (8191 : ℕ) else (67100672 : ℕ);               have x11 : ℕ := if x8 = (0 : ℕ) then (25018369 : ℕ) else (15860 : ℕ);               ∀ (x12 : Set ℕ), x1.output ∈ x12 → (∀ (x14 : Fin (26 : ℕ)), ↑x14 ∈ x12 → x9.testBit ↑x14 = Bool.false) → ¬∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x15]? = Option.some x16 → (26 : ℕ) + x15 ∈ x12 → (x16.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ x20 ∈ x16.inputs, x20 ∈ x12) ∧ (x16.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ x20 ∈ x16.inputs, x20 ∈ x12) ∨ (∀ x20 ∈ x16.inputs, x7 ((2 : ℕ) ^ x8) x20 = Bool.false) ∧ x7 x10 ((26 : ℕ) + x15) = Bool.false ∧ x7 x11 ((26 : ℕ) + x15) = Bool.false) := by
  intro C lo hi model nd spec
  let E := fun p l : Fin 13 => (p-l) ∈ ([0,1,3,9] : List (Fin 13))
  have edge : ∀ p l : Fin 13, E p l ↔ p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9 := by decide
  let row := fun (P L : Fin 13 → Bool) => List.ofFn (Fin.addCases P L)
  have pos : ∀ p l, E p l → C.eval (row (fun t => decide (t=p)) (fun t => decide (t=l))) = true := by
    intro p l adj
    apply (spec _).2
    refine ⟨p,l,(edge p l).1 adj,?_,?_⟩ <;> simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq]
  have neg : ∀ T : Finset (Fin 13), T.card ≤ 3 →
      let pick := fun t => decide (t∈T)
      C.eval (row pick (fun l => decide (∀ p∈T, ¬E p l))) = false ∧
      C.eval (row (fun p => decide (∀ l∈T, ¬E p l)) pick) = false := by
    intro T _
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p,l,e,hp,hl⟩ := (spec _).1 h
      simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hp hl
      exact hl p hp ((edge p l).2 e)
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p,l,e,hp,hl⟩ := (spec _).1 h
      simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hp hl
      exact hp l hl ((edge p l).2 e)
  obtain ⟨b,bb,path⟩ := hfinite C lo hi model nd pos neg
  refine ⟨b,bb,?_⟩
  let u : ℕ := if b=0 then 25034751 else 67108341
  let w := fun (m k : ℕ) => (C.wires (List.ofFn fun t : Fin 26 => m.testBit t.val)).getD k false
  intro _ _ _ S out raw closed
  have sides : b=0 ∨ b=13 := by simpa using bb
  have seed : ∀ i : Fin 26, u.testBit i.val=false → ((2:ℕ)^b).testBit i.val=false := by
    rcases sides with rfl|rfl <;> decide
  have protectedBit : ∀ i ∈ S, w (2^b) i=false := by
    apply hpin 26 C (fun t : Fin 26 => ((2:ℕ)^b).testBit t.val) S model
    · intro i h; exact seed i (raw i h)
    · intro j g hit mem
      obtain ⟨ho,ha⟩ := closed j g hit mem
      exact ⟨ho,fun h => (ha h).imp id (fun e => e.1)⟩
  have root : 13-b ∉ S := by
    intro mem
    have e : ∃ i : Fin 26, i.val=13-b ∧ u.testBit i.val=true := by
      rcases sides with rfl|rfl <;> decide
    obtain ⟨i,ei,on⟩ := e
    exact Bool.noConfusion ((raw i (ei.symm ▸ mem)).symm.trans on)
  have walk : ∀ k, Relation.ReflTransGen (fun (a k : ℕ) => ∃ j g q, C.gates[j]? = some g ∧ k=26+j ∧
        (g.inputs=[a,q] ∨ g.inputs=[q,a]) ∧
        (g.op=PEqualNP.CircuitLowerBounds.GateOp.or ∨ w (2^b) q=true)) (13-b) k → k ∉ S := by
    intro k hk
    induction hk with
    | refl => exact root
    | @tail a k hp step ih =>
      obtain ⟨j,g,q,hit,rfl,ins,hg⟩ := step
      intro mem
      obtain ⟨hor,hand⟩ := closed j g hit mem
      rcases hg with ho|hq
      · exact ih (hor ho _ (by rcases ins with ha|ha <;> simp [ha]))
      have op := model.1 g (List.mem_of_getElem? hit)
      rcases op with ha|ho
      · rcases hand ha with ⟨i,im,si⟩|except
        · have alt : i=a ∨ i=q := by rcases ins with e|e <;> simpa [e,or_comm] using im
          rcases alt with e|e
          · exact ih (e ▸ si)
          · exact Bool.noConfusion ((protectedBit q (e ▸ si)).symm.trans hq)
        · exact Bool.noConfusion ((except.1 q (by rcases ins with e|e <;> simp [e])).symm.trans hq)
      · exact ih (hor ho _ (by rcases ins with e|e <;> simp [e]))
  exact walk C.output path out
