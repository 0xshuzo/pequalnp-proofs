import PEqualNP.Defs
namespace Reset8811
inductive Source {n s : ℕ} (a b op : Fin s → ℕ) : ℕ → ℕ → Prop where
  | input (u : ℕ) (hu : u<n) : Source a b op u u
  | first (j : Fin s) (u : ℕ) (h : op j=0 ∨ op j=1) (earlier : Source a b op (a j) u) :
    Source a b op (n+j.val) u
  | second (j : Fin s) (u : ℕ) (h : op j=0) (earlier : Source a b op (b j) u) :
    Source a b op (n+j.val) u
theorem raw_src {n s : ℕ} {a b op : Fin s → ℕ} {w u : ℕ} (hw : w<n) :
    Source (n:=n) a b op w u ↔ w=u := by
  constructor
  · intro h
    cases h with
    | input => rfl
    | first => omega
    | second => omega
  · rintro rfl; exact Source.input _ hw
theorem step_src {n s : ℕ} {a b op : Fin s → ℕ} (j : Fin s) (u : ℕ) :
    Source (n:=n) a b op (n+j.val) u ↔
      ((op j=0 ∨ op j=1) ∧ Source (n:=n) a b op (a j) u) ∨
      (op j=0 ∧ Source (n:=n) a b op (b j) u) := by
  constructor
  · intro h
    generalize eq : n+j.val = w at h
    cases h with
    | input v hv => omega
    | first k v ho hprev =>
      have id : j=k := Fin.ext (by omega)
      subst k
      exact Or.inl ⟨ho,hprev⟩
    | second k v ho hprev =>
      have id : j=k := Fin.ext (by omega)
      subst k
      exact Or.inr ⟨ho,hprev⟩
  · rintro (⟨k,p⟩|⟨k,p⟩)
    exact .first j u k p
    exact .second j u k p

theorem maskBank {n s : ℕ} (a b op : Fin s → ℕ) (prior : ∀ j, a j<n+j.val ∧ b j<n+j.val)
    (tags : ∀ j, op j≤3) (U : ℕ → Finset ℕ) (inRaw : ∀ i<n, U i={i}) (M : Finset ℕ)
    (steps : ∀ j, (op j=0 → U (n+j.val)=U (a j)∪U (b j)) ∧
      (op j=1 → U (n+j.val)=U (a j)) ∧ (op j=2 → U (n+j.val)=∅) ∧
      (op j=3 → j.val∉M → U (n+j.val)=∅)) :
    ∃ H : ℕ → Finset ℕ, (∀ i<n, H i={i}) ∧ (∀ j,
      (op j=0 → H (n+j.val)=H (a j) ∪ H (b j)) ∧ (op j=1 → H (n+j.val)=H (a j)) ∧
      (2≤op j → H (n+j.val)=∅)) ∧
      (∀ w<n+s, H w⊆U w) ∧ (∀ w<n+s, ∀ u∈U w, u∉H w →
        ∃ j : Fin s, j.val∈M ∧ op j=3 ∧ u∈U (n+j.val) ∧ U (n+j.val)⊆U w) := by
  classical
  let H (w : ℕ) := (Finset.range n).filter (fun u => Source (n:=n) a b op w u)
  have mem (w u : ℕ) : u∈H w ↔ u<n ∧ Source (n:=n) a b op w u := by simp [H]
  have raw (i : ℕ) (hi : i<n) : H i={i} := by
    ext u; rw [mem,raw_src hi,Finset.mem_singleton]; omega
  have updates (j : Fin s) : (op j=0 → H (n+j.val)=H (a j) ∪ H (b j)) ∧
      (op j=1 → H (n+j.val)=H (a j)) ∧ (2≤op j → H (n+j.val)=∅) := by
    refine ⟨?_,?_,?_⟩
    · intro k; ext u; simp only [Finset.mem_union,mem,step_src,k]; tauto
    · intro k; ext u; simp [mem,step_src,k]
    · intro k; have no : op j≠0 := by omega
      have no' : op j≠1 := by omega
      ext u; simp [mem,step_src,no,no']
  have both (w : ℕ) (hw : w<n+s) : H w⊆U w ∧ (∀ u∈U w, u∉H w →
        ∃ j : Fin s, j.val∈M ∧ op j=3 ∧ u∈U (n+j.val) ∧ U (n+j.val)⊆U w) := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases wr : w<n
      · rw [raw w wr,inRaw w wr]
        exact ⟨fun _ h => h,fun u hu no => (no hu).elim⟩
      let j : Fin s := ⟨w-n,by omega⟩
      have eq : n+j.val=w := by dsimp [j]; omega
      have left := (prior j).1; have right := (prior j).2
      rw [eq] at left right
      have A := ih (a j) left (left.trans hw)
      have B := ih (b j) right (right.trans hw)
      rw [←eq]
      by_cases k : op j=0
      · rw [(updates j).1 k,(steps j).1 k]
        refine ⟨Finset.union_subset_union A.1 B.1,?_⟩
        intro u hu nm
        rcases Finset.mem_union.mp hu with hu|hu
        · obtain ⟨t,mt,ot,ht,st⟩ := A.2 u hu (fun h => nm (Finset.mem_union_left _ h))
          exact ⟨t,mt,ot,ht,st.trans Finset.subset_union_left⟩
        · obtain ⟨t,mt,ot,ht,st⟩ := B.2 u hu (fun h => nm (Finset.mem_union_right _ h))
          exact ⟨t,mt,ot,ht,st.trans Finset.subset_union_right⟩
      by_cases k1 : op j=1
      · rw [(updates j).2.1 k1,(steps j).2.1 k1]
        exact A
      rw [(updates j).2.2 (by omega)]
      constructor
      · exact Finset.empty_subset _
      intro u hu _
      have k3 : op j=3 := by
        have bound := tags j
        by_contra h
        rw [(steps j).2.2.1 (by omega)] at hu
        exact Finset.notMem_empty _ hu
      by_cases marked : j.val∈M
      · exact ⟨j,marked,k3,hu,Finset.Subset.rfl⟩
      · rw [(steps j).2.2.2 k3 marked] at hu
        exact (Finset.notMem_empty _ hu).elim
  exact ⟨H,raw,updates,fun w hw => (both w hw).1,fun w hw => (both w hw).2⟩
end Reset8811
