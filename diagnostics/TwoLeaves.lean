import PEqualNP.Defs
namespace PCX150
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev Cl := Clause V
inductive ResTree (F : Set Cl) : Cl → Nat → Prop where
  | ax {C : Cl} : C ∈ F → ResTree F C 0
  | res {C D R : Cl} {i j : Nat} : ResTree F C i → ResTree F D j →
      IsResolvent C D R → ResTree F R (i+j+1)
end PCX150

namespace PCX150
open PEqualNP.ProofComplexity

theorem satOfTree {F : Set Cl} {C : Cl} {n : Nat} (tree : ResTree F C n)
    (a : V → Bool) (model : ∀ D ∈ F, ClauseSat a D) : ClauseSat a C := by
  induction tree with
  | ax h => exact model _ h
  | res _ _ step left right =>
    obtain ⟨v,_,_,rfl⟩ := step
    cases h : a v with
    | false =>
      obtain ⟨l,mem,val⟩ := left
      have ne : l ≠ (v,true) := by rintro rfl; simp [h] at val
      exact ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,mem⟩),val⟩
    | true =>
      obtain ⟨l,mem,val⟩ := right
      have ne : l ≠ (v,false) := by rintro rfl; simp [h] at val
      exact ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,mem⟩),val⟩

private theorem uniqueSign {x y z : Bool} (hx : x ≠ z) (hy : y ≠ z) : x = y := by
  cases x <;> cases y <;> cases z <;> simp_all

/-- Two nonempty clauses can refute by themselves only if one resolution step suffices. -/
theorem refuteTwo {A B : Cl} {n : Nat} (tree : ResTree ({A,B} : Set Cl) ∅ n)
    (na : A.Nonempty) (nb : B.Nonempty) : IsResolvent A B ∅ ∨ IsResolvent B A ∅ := by
  classical
  have noBoth (a : V → Bool) (sa : ClauseSat a A) (sb : ClauseSat a B) : False := by
    have sat := satOfTree tree a (by
      intro D hd
      rcases Set.mem_insert_iff.mp hd with eq | mem
      · simpa [eq] using sa
      · have eq : D = B := Set.mem_singleton_iff.mp mem
        simpa [eq] using sb)
    simpa [ClauseSat] using sat
  have opposite (l) (hl : l ∈ A) (m) (hm : m ∈ B) : l.1 = m.1 ∧ l.2 ≠ m.2 := by
    by_cases eq : l.1 = m.1
    · refine ⟨eq,?_⟩
      intro same
      exact noBoth (fun _ => l.2) ⟨l,hl,rfl⟩ ⟨m,hm,same⟩
    · let a : V → Bool := fun v => if v = l.1 then l.2 else m.2
      exact (noBoth a ⟨l,hl,by simp [a]⟩ ⟨m,hm,by simp [a,Ne.symm eq]⟩).elim
  obtain ⟨u,hu⟩ := na
  obtain ⟨v,hv⟩ := nb
  have h := opposite u hu v hv
  have oneA : A = {u} := by
    ext l
    constructor
    · intro hl
      have p := opposite l hl v hv
      exact Finset.mem_singleton.mpr (Prod.ext (p.1.trans h.1.symm) (uniqueSign p.2 h.2))
    · intro hl
      exact (Finset.mem_singleton.mp hl).symm ▸ hu
  have oneB : B = {v} := by
    ext m
    constructor
    · intro hm
      have p := opposite u hu m hm
      exact Finset.mem_singleton.mpr (Prod.ext (p.1.symm.trans h.1) (uniqueSign (Ne.symm p.2) (Ne.symm h.2)))
    · intro hm
      exact (Finset.mem_singleton.mp hm).symm ▸ hv
  obtain ⟨u,us⟩ := u
  obtain ⟨v,vs⟩ := v
  change u = v ∧ us ≠ vs at h
  obtain ⟨rfl,neq⟩ := h
  rw [oneA,oneB]
  cases us <;> cases vs <;> simp_all [IsResolvent]

end PCX150
