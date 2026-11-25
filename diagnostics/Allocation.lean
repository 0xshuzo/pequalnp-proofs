import Mathlib

namespace Cut3321
variable {V E J : Type*} [DecidableEq V] [DecidableEq J]

def Target (edges : Finset E) (support : E → Finset V) (X : Finset V) :=
  ∃ e∈edges, support e ⊆ X

noncomputable def marks [DecidableEq E] (edges : Finset E) (support : E → Finset V)
    (alloc : E → Finset J) (X : Finset V) : Finset J := by
  classical
  exact (edges.filter (fun e => support e ⊆ X)).biUnion alloc

theorem mark_iff [DecidableEq E] (edges : Finset E) (support : E → Finset V)
    (alloc : E → Finset J) (X : Finset V) (j : J) :
    j∈marks edges support alloc X ↔ ∃ e∈edges, support e ⊆ X ∧ j∈alloc e := by
  classical
  simp only [marks,Finset.mem_biUnion,Finset.mem_filter]
  aesop

variable [DecidableEq E] {edges : Finset E} {support : E → Finset V}
    {K : Finset V → Finset J → Prop}

theorem negative {alloc : E → Finset J} {X : Finset V} (h : ¬Target edges support X) :
    marks edges support alloc X = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨e,he,sub,_⟩ := (mark_iff _ _ _ _ _).mp hj
  exact h ⟨e,he,sub⟩

theorem canonical (old : Finset V → Finset J)
    (correct : ∀ X, K X (old X) ↔ Target edges support X)
    (mono : ∀ {X Y a b}, X ⊆ Y → a ⊆ b → K X a → K Y b)
    (alloc : E → Finset J) (covers : ∀ e∈edges, K (support e) (alloc e)) :
    ∀ X, K X (marks edges support alloc X) ↔ Target edges support X := by
  classical
  intro X
  constructor
  · intro up
    by_contra no
    rw [negative no] at up
    exact no ((correct X).mp (mono (Finset.Subset.refl _) (Finset.empty_subset _) up))
  · rintro ⟨e,he,sub⟩
    apply mono sub _ (covers e he)
    intro j hj
    exact (mark_iff _ _ _ _ _).mpr ⟨e,he,sub,hj⟩

theorem supported {alloc : E → Finset J} {j : J} {X : Finset V}
    (on : j∈marks edges support alloc X) : Target edges support X := by
  obtain ⟨e,he,sub,_⟩ := (mark_iff _ _ _ _ _).mp on
  exact ⟨e,he,sub⟩

theorem marks_at_edge (incomparable : ∀ e∈edges, ∀ f∈edges, support e ⊆ support f → e=f)
    (alloc : E → Finset J) {e} (he : e∈edges) :
    marks edges support alloc (support e)=alloc e := by
  ext j
  rw [mark_iff]
  constructor
  · rintro ⟨f,hf,le,hj⟩
    exact incomparable f hf e he le ▸ hj
  · exact fun h => ⟨e,he,Finset.Subset.refl _,h⟩

theorem criterion (old : Finset V → Finset J)
    (correct : ∀ X, K X (old X) ↔ Target edges support X)
    (mono : ∀ {X Y a b}, X ⊆ Y → a ⊆ b → K X a → K Y b)
    (incomparable : ∀ e∈edges, ∀ f∈edges, support e ⊆ support f → e=f)
    (alloc : E → Finset J) :
    (∀ X, K X (marks edges support alloc X) ↔ Target edges support X) ↔
      ∀ e∈edges, K (support e) (alloc e) := by
  constructor
  · intro h e he
    rw [← marks_at_edge incomparable alloc he]
    exact (h _).mpr ⟨e,he,Finset.Subset.refl _⟩
  · exact canonical old correct mono alloc

theorem one_owner (old : Finset V → Finset J)
    (correct : ∀ X, K X (old X) ↔ Target edges support X)
    (mono : ∀ {X Y a b}, X ⊆ Y → a ⊆ b → K X a → K Y b)
    (additive : ∀ X A, K X A → K X ∅ ∨ ∃ i∈A, K X {i}) :
    ∃ alloc : E → Finset J, (∀ e, (alloc e).card ≤ 1) ∧
      (∀ e∈edges, alloc e ⊆ old (support e)) ∧
      ∀ X, K X (marks edges support alloc X) ↔ Target edges support X := by
  classical
  have choices (e : E) : ∃ S : Finset J, S.card ≤ 1 ∧ S ⊆ old (support e) ∧
      (e∈edges → K (support e) S) := by
    by_cases he : e∈edges
    · have ok := (correct (support e)).mpr ⟨e,he,Finset.Subset.refl _⟩
      rcases additive _ _ ok with empty | ⟨i,hi,one⟩
      · exact ⟨∅,by simp,Finset.empty_subset _,fun _ => empty⟩
      · exact ⟨{i},by simp,Finset.singleton_subset_iff.mpr hi,fun _ => one⟩
    · exact ⟨∅,by simp,Finset.empty_subset _,fun h => (he h).elim⟩
  choose alloc cost used feasible using choices
  exact ⟨alloc,cost,fun e _ => used e,canonical old correct mono alloc feasible⟩

end Cut3321
