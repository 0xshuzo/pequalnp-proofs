import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4678_417
    (hsafe : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
    let L := PEqualNP.HeptadCover.singerLines3
    PEqualNP.GenericRejection.RightOnIncidentPairs L C →
    (∀ Q, PEqualNP.HeptadCover.IsQuadrangle L Q → C.eval (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines L Q))=false) →
    let edges := PEqualNP.HeptadCover.incidences L
    let single := fun (e : Fin 13 × Fin 13) => PEqualNP.GenericRejection.incidenceInput {e.1} {e.2}
    let w := fun (x : List Bool) (j : ℕ) => (C.wires x).getD (26+j) false
    (∀ (j : Fin C.gates.length), (C.gates.get j).op=PEqualNP.CircuitLowerBounds.GateOp.and →
      (∃ u v : Fin 26, let r := List.ofFn (fun i : Fin 26 => decide (i=u ∨ i=v))
        C.eval r=false ∧ w r j.val=true) →
      ∀ a∈edges, ∀ b∈edges, w (single a) j.val=true → w (single b) j.val=true → a=b) → 64≤C.size)
    (hbad : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
    let L := PEqualNP.HeptadCover.singerLines3
    PEqualNP.GenericRejection.RightOnIncidentPairs L C →
    (∀ Q, PEqualNP.HeptadCover.IsQuadrangle L Q → C.eval (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines L Q))=false) →
    let edges := PEqualNP.HeptadCover.incidences L
    let single := fun (e : Fin 13 × Fin 13) => PEqualNP.GenericRejection.incidenceInput {e.1} {e.2}
    let w := fun (x : List Bool) (j : ℕ) => (C.wires x).getD (26+j) false
    C.size≤63 → (∃ g, C.gates.head?=some g ∧ g.op=PEqualNP.CircuitLowerBounds.GateOp.or) →
    ∀ (j : Fin C.gates.length), (C.gates.get j).op=PEqualNP.CircuitLowerBounds.GateOp.and →
      (∃ u v : Fin 26, let r := List.ofFn (fun i : Fin 26 => decide (i=u ∨ i=v))
        C.eval r=false ∧ w r j.val=true) →
      ∀ a∈edges, ∀ b∈edges, w (single a) j.val=true → w (single b) j.val=true → a=b) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), ∀ x6 ∈ (x4.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5; have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]]; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ x5, PEqualNP.MetaComplexity.Monotone2 x6 → x4 x6 → x3 x6 x7 → (63 : ℕ) ≤ x6.size := by
  intro D checks fits back menus C s hs mc top good
  let g : PEqualNP.CircuitLowerBounds.Gate := ⟨.or,s⟩
  let B : PEqualNP.CircuitLowerBounds.Circuit := ⟨g::C.gates,C.output⟩
  have sl : s.length≤2 := by
    have allShort : ∀ t∈menus, t.length≤2 := by decide
    exact allShort s hs
  have mono : PEqualNP.MetaComplexity.Monotone2 B := by
    intro h hh
    change h∈g::C.gates at hh
    rcases List.mem_cons.mp hh with e|e
    · exact e.symm ▸ ⟨Or.inr rfl,sl⟩
    · exact mc h e
  have wire (x : List Bool) : B.eval x=C.eval (x++[s.any fun i => x.getD i false]) := by
    change C.eval (x++[(s.map fun i => x.getD i false).any id])=_
    simp only [List.any_map,Function.comp_def,id_eq]
  let L := PEqualNP.HeptadCover.singerLines3
  have mem : ∀ p l : Fin 13, p∈L l ↔ p-l∈D := by decide
  have unpack (P Q : Finset (Fin 13)) : PEqualNP.GenericRejection.incidenceInput P Q =
      List.ofFn (fun i : Fin 13 => decide (i∈P)) ++ List.ofFn (fun i : Fin 13 => decide (i∈Q)) := rfl
  have yes : PEqualNP.GenericRejection.RightOnIncidentPairs L B := by
    intro l p h
    rw [wire]
    simpa only [unpack,Finset.mem_singleton] using good.1 p l ((mem p l).1 h)
  have no : ∀ Q, PEqualNP.HeptadCover.IsQuadrangle L Q →
      B.eval (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines L Q))=false := by
    intro Q h
    have eqn (l : Fin 13) : Q.filter (fun p => p-l∈D) = Q ∩ L l := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter, mem]
    have eqb (l : Fin 13) : l∈PEqualNP.HeptadCover.missLines L Q ↔ ∀ p∈Q, p-l∉D := by
      change l ∈ Finset.univ.filter (fun k => Disjoint (L k) Q) ↔ _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left]
      constructor
      · intro hn p hp adj; exact hn ((mem p l).2 adj) hp
      · intro hn p hp hq; exact hn p hq ((mem p l).1 hp)
    rw [wire]
    simpa only [unpack,eqb] using
      good.2 Q h.1 (fun l => (eqn l).symm ▸ h.2 l)
  have sz : B.size=C.size+1 := rfl
  by_contra short
  have hb : B.size≤63 := by omega
  have result := hsafe B mono yes no (hbad B mono yes no hb ⟨g,rfl,rfl⟩)
  omega
