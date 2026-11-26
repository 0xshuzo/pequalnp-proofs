import PEqualNP.Outside.L_meta_3289
import Mathlib

namespace PencilForest

variable {α : Type*} [DecidableEq α]

/-- Charge one binary split if a clean wire needs two earlier clean wires.
The frontier is a set so reconvergent paths charge each split only once. -/
theorem frontier (labels : ℕ → Finset α) (clean pay : ℕ → Prop) [DecidablePred pay]
    (step : ∀ k, clean k → 1 < (labels k).card → ∃ D ⊆ Finset.range k,
      (∀ d ∈ D, clean d) ∧ D.card ≤ (if pay k then 2 else 1) ∧ labels k ⊆ D.biUnion labels)
    (k : ℕ) (F : Finset ℕ) (old : F ⊆ Finset.range k) (good : ∀ w ∈ F, clean w) :
    (F.biUnion labels).card ≤ F.card + ((Finset.range k).filter pay).card := by
  classical
  induction k generalizing F with
  | zero =>
    have eq : F = ∅ := Finset.subset_empty.mp (by simpa using old)
    simp [eq]
  | succ k ih =>
    by_cases top : k ∈ F
    · let A := F.erase k
      have aOld : A ⊆ Finset.range k := by
        intro w hw
        obtain ⟨wk,wf⟩ := Finset.mem_erase.mp hw
        have hlt := Finset.mem_range.mp (old wf)
        exact Finset.mem_range.mpr (by omega)
      have aGood : ∀ w ∈ A, clean w := fun w hw => good w (Finset.mem_of_mem_erase hw)
      have erase : A.card + 1 = F.card := Finset.card_erase_add_one top
      have more : ((Finset.range k).filter pay).card ≤ ((Finset.range (k+1)).filter pay).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
      by_cases small : (labels k).card ≤ 1
      · have sub : F.biUnion labels ⊆ A.biUnion labels ∪ labels k := by
          intro x hx
          obtain ⟨w,wf,xw⟩ := Finset.mem_biUnion.mp hx
          by_cases wk : w=k
          · exact Finset.mem_union_right _ (wk ▸ xw)
          · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨w,Finset.mem_erase.mpr ⟨wk,wf⟩,xw⟩)
        have u := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
        have h := ih A aOld aGood
        omega
      obtain ⟨D,dOld,dGood,cap,covers⟩ := step k (good k top) (by omega)
      have adOld : A ∪ D ⊆ Finset.range k := Finset.union_subset aOld dOld
      have adGood : ∀ w ∈ A ∪ D, clean w :=
        fun w hw => (Finset.mem_union.mp hw).elim (aGood w) (dGood w)
      have sub : F.biUnion labels ⊆ (A ∪ D).biUnion labels := by
        intro x hx
        obtain ⟨w,wf,xw⟩ := Finset.mem_biUnion.mp hx
        by_cases wk : w=k
        · obtain ⟨d,hd,xd⟩ := Finset.mem_biUnion.mp (covers (wk ▸ xw))
          exact Finset.mem_biUnion.mpr ⟨d,Finset.mem_union_right _ hd,xd⟩
        · exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨wk,wf⟩),xw⟩
      have h := (Finset.card_le_card sub).trans (ih (A ∪ D) adOld adGood)
      have sz := Finset.card_union_le A D
      by_cases charged : pay k
      · have inc : ((Finset.range (k+1)).filter pay).card = ((Finset.range k).filter pay).card+1 := by
          rw [Finset.range_succ,Finset.filter_insert,if_pos charged,Finset.card_insert_of_notMem]
          simp
        simp only [charged,if_true] at cap
        omega
      · simp only [charged,if_false] at cap
        omega
    · have prior : F ⊆ Finset.range k := by
        intro w hw
        have h := Finset.mem_range.mp (old hw)
        have wk : w ≠ k := by rintro rfl; exact top hw
        exact Finset.mem_range.mpr (by omega)
      have h := ih F prior good
      exact h.trans (Nat.add_le_add_left (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))) _)

end PencilForest

namespace PencilForest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3289

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

def labels (C : Circuit) (pos : α → Fin n → Bool) (w : ℕ) : Finset α :=
  Finset.univ.filter fun a => rn C (pos a) w=true

noncomputable def pool (C : Circuit) (pos : α → Fin n → Bool) (off : Fin n → Bool) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter fun w =>
    n ≤ w ∧ (at_ C.gates (w-n)).op=.or ∧ rn C off w=false ∧ 1 < (labels C pos w).card

theorem local_or_count (C : Circuit) (ao : IsAO2 n C)
    (pos : α → Fin n → Bool) (off : Fin n → Bool)
    (raw : ∀ i, off i=false → (Finset.univ.filter fun a => pos a i=true).card ≤ 1)
    (w : ℕ) (quiet : rn C off w=false) : (labels C pos w).card ≤ (pool C pos off).card+1 := by
  classical
  let clean := fun w => rn C off w=false
  let pay := fun w => n ≤ w ∧ (at_ C.gates (w-n)).op=.or ∧ clean w ∧ 1<(labels C pos w).card
  have contains (a : α) (k : ℕ) : a ∈ labels C pos k ↔ rn C (pos a) k=true := by simp [labels]
  have step (k) (ck : clean k) (big : 1 < (labels C pos k).card) :
      ∃ D ⊆ Finset.range k, (∀ d ∈ D, clean d) ∧
        D.card ≤ (if pay k then 2 else 1) ∧ labels C pos k ⊆ D.biUnion (labels C pos) := by
    by_cases input : k<n
    · let i : Fin n := ⟨k,input⟩
      have quietI : off i=false := by rw [← rn_in C off i]; exact ck
      have eq : labels C pos k = Finset.univ.filter fun a => pos a i=true := by
        ext a
        rw [contains]
        change rn C (pos a) i.val = true ↔ _
        rw [rn_in]
        simp
      rw [eq] at big
      exact (Nat.not_lt_of_ge (raw i quietI) big).elim
    by_cases out : n+C.gates.length ≤ k
    · have empty : labels C pos k = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have h := (contains a k).mp ha
        rw [rn_big C (pos a) k out] at h
        contradiction
      simp [empty] at big
    obtain ⟨j,rfl⟩ : ∃ j, k = n+j := ⟨k-n,by omega⟩
    have hj : j<C.gates.length := by omega
    let g := at_ C.gates j
    have hg : g ∈ C.gates := at_mem _ _ hj
    obtain ⟨u,v,ins⟩ := List.length_eq_two.mp (ao.2.2 g hg)
    have uSmall : u < n+j := ao.2.1 j hj u (by change u ∈ g.inputs; simp [ins])
    have vSmall : v < n+j := ao.2.1 j hj v (by change v ∈ g.inputs; simp [ins])
    have ev (x : Fin n → Bool) : rn C x (n+j)=g.op.eval [rn C x u,rn C x v] := by
      rw [rn_gate C x j hj]
      change g.op.eval (g.inputs.map _) = _
      simp [ins,uSmall,vSmall]
    rcases ao.1 g hg with andOp|orOp
    · have andVal (x : Fin n → Bool) : rn C x (n+j) = (rn C x u && rn C x v) := by
        rw [ev x,andOp]; simp [GateOp.eval]
      have choose : clean u ∨ clean v := by
        change rn C off (n+j)=false at ck
        rw [andVal] at ck
        cases xu : rn C off u <;> cases xv : rn C off v <;> simp_all [clean]
      rcases choose with hu|hv
      · refine ⟨{u},Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr uSmall),?_,?_,?_⟩
        · simpa using hu
        · simp only [Finset.card_singleton]; split <;> omega
        · intro a ha
          have h := (contains a _).mp ha
          rw [andVal,Bool.and_eq_true] at h
          exact Finset.mem_biUnion.mpr ⟨u,by simp,(contains a u).mpr h.1⟩
      · refine ⟨{v},Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr vSmall),?_,?_,?_⟩
        · simpa using hv
        · simp only [Finset.card_singleton]; split <;> omega
        · intro a ha
          have h := (contains a _).mp ha
          rw [andVal,Bool.and_eq_true] at h
          exact Finset.mem_biUnion.mpr ⟨v,by simp,(contains a v).mpr h.2⟩
    · have orVal (x : Fin n → Bool) : rn C x (n+j) = (rn C x u || rn C x v) := by
        rw [ev x,orOp]; simp [GateOp.eval]
      have both : clean u ∧ clean v := by
        change rn C off (n+j)=false at ck
        rw [orVal] at ck
        cases xu : rn C off u <;> cases xv : rn C off v <;> simp_all [clean]
      have paid : pay (n+j) := ⟨by omega,by simpa only [Nat.add_sub_cancel_left] using orOp,ck,big⟩
      refine ⟨{u,v},Finset.insert_subset (Finset.mem_range.mpr uSmall)
        (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr vSmall)),?_,?_,?_⟩
      · intro d hd
        rcases Finset.mem_insert.mp hd with rfl|hd
        · exact both.1
        · exact Finset.mem_singleton.mp hd ▸ both.2
      · rw [if_pos paid]
        exact Finset.card_le_two
      · intro a ha
        have h := (contains a _).mp ha
        rw [orVal,Bool.or_eq_true] at h
        rcases h with h|h
        · exact Finset.mem_biUnion.mpr ⟨u,by simp,(contains a u).mpr h⟩
        · exact Finset.mem_biUnion.mpr ⟨v,by simp,(contains a v).mpr h⟩
  by_cases old : w < n + C.gates.length
  · have h := frontier (labels C pos) clean pay step (n+C.gates.length) {w}
      (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr old)) (by simpa using quiet)
    simpa [pool,clean,pay,Nat.add_comm] using h
  · have empty : labels C pos w = ∅ := by
      ext a
      simp [labels,rn_big C (pos a) w (by omega)]
    simp [empty]

end PencilForest
