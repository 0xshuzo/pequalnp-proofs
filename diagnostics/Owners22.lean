import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_166.Owners
abbrev K := Fin 45
abbrev S := Fin 24
def early (assign : K → Nat) (i : Nat) : Finset K := Finset.univ.filter (fun k => assign k < i)
def split (miss : K → S → Prop) (k : K) : Prop :=
  (∃s,miss k s) ∧ (∃s,¬miss k s)
theorem splitEarly (assign : K→Nat) (miss : Nat→K→S→Prop)
    (owned : ∀k s,miss (assign k) k s)
    (before : ∀i k s,miss i k s → assign k ≤ i)
    {i : Nat} {k : K} (h : split (miss i) k) : k ∈ early assign i := by
  obtain ⟨⟨s,hs⟩,t,ht⟩:=h
  have le:=before i k s hs
  have neq : assign k ≠ i := by
    intro eq
    exact ht (eq ▸ owned k t)
  simpa [early] using Nat.lt_of_le_of_ne le neq

theorem floor22 (assign : K→Nat) (q : Nat)
    (multi : ∀i<q, ∀a b : K, a ≠ b → assign a=i → assign b=i → 22 ≤ (early assign i).card)
    (terminal : 22 ≤ (early assign q).card) : 22 ≤ q := by
  by_contra h
  have hq : q<22 := by omega
  have count : ∀i, i≤q → (early assign i).card≤i := by
    intro i
    induction i with
    | zero => intro _; simp [early]
    | succ i ih =>
      intro hle
      have hi := ih (by omega)
      by_cases ex : ∃k,assign k=i
      · obtain ⟨k,hk⟩ := ex
        have only : ∀j,assign j=i → j=k := by
          intro j hj
          by_contra ne
          have z:=multi i (by omega) j k ne hj hk
          omega
        have sub : early assign (i+1) ⊆ insert k (early assign i) := by
          intro j hj
          have hh : assign j<i+1 := (Finset.mem_filter.mp hj).2
          by_cases eq : assign j=i
          · exact Finset.mem_insert.mpr (Or.inl (only j eq))
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨by simp,by omega⟩))
        have hk' : k∉early assign i := by simp [early,hk]
        have c:=Finset.card_le_card sub
        rw [Finset.card_insert_of_notMem hk'] at c
        omega
      · have sub : early assign (i+1) ⊆ early assign i := by
          intro j hj
          have hh := (Finset.mem_filter.mp hj).2
          have neq : assign j ≠ i := fun eq => ex ⟨j,eq⟩
          exact Finset.mem_filter.mpr ⟨by simp,by omega⟩
        exact (Finset.card_le_card sub).trans (by omega)
  have := count q le_rfl
  omega

theorem ledger111 (len surplus sites : Nat) (assign : K→Nat)
    (area : 89+surplus≤len) (count : sites≤surplus)
    (multi : ∀i<sites, ∀a b : K, a ≠ b → assign a=i → assign b=i → 22 ≤ (early assign i).card)
    (terminal : 22 ≤ (early assign sites).card) : 111≤len := by
  have := floor22 assign sites multi terminal
  omega
end PEqualNP.Outside.L_pcx_166.Owners
