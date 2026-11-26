import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9743_Separated
variable {V : Type}

def boxFree (g : V → V → Prop) : Prop := ∀ a a' b b', a≠a' → b≠b' →
  g a b → g a b' → g a' b → g a' b' → False
def small (s : Set V) := ∀ i∈s, ∀ j∈s, i=j

theorem thin {g : V → V → Prop} (c4 : boxFree g) {a b : Set V}
    (all : ∀ i∈a, ∀ j∈b, g i j) : small a ∨ small b := by
  classical
  by_cases h : small a
  · exact Or.inl h
  · right
    unfold small at h
    push_neg at h
    obtain ⟨i,hi,i',hi',ne⟩ := h
    intro j hj j' hj'
    by_contra nj
    exact c4 i i' j j' ne nj (all i hi j hj) (all i hi j' hj')
      (all i' hi' j hj) (all i' hi' j' hj')

def depends (p : Set V → Prop) (a : Set V) := ∀ s t : Set V,
  (∀ v∈a, v∈s ↔ v∈t) → (p s ↔ p t)
def increasing (p : Set V → Prop) := ∀ s t : Set V, s⊆t → p s → p t

theorem project_one {p : Set V → Prop} {a : Set V} (h : depends p a) {i j : V}
    (out : j∉a) : p {i,j} ↔ p {i} := by
  apply h
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro (rfl|rfl)
    · rfl
    · exact False.elim (out hx)
  · exact Or.inl

theorem project_two {p : Set V → Prop} {a : Set V} (h : depends p a) {i j : V}
    (out : i∉a) : p {i,j} ↔ p {j} := by
  rw [Set.pair_comm i j]
  exact project_one h out

theorem empty_pair {p : Set V → Prop} {a : Set V} (h : depends p a) {i j : V}
    (iout : i∉a) (jout : j∉a) : p {i,j} ↔ p ∅ := by
  apply h
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
  rintro (rfl|rfl)
  · exact iout hx
  · exact jout hx

-- Each input of a disjoint-support AND has access only to its own side.
-- The required pairs touch every input and the ambient allowed graph contains no C4.
theorem separated (a b : Set V) (p q : Set V → Prop) (d g : V → V → Prop)
    (sep : ∀ v, v∈a → v∉b) (pa : depends p a) (qb : depends q b)
    (up : increasing p) (uq : increasing q) (zp : ¬p ∅) (zq : ¬q ∅)
    (spanA : ∀ i∈a, ∃ j∈a ∪ b, d i j) (spanB : ∀ j∈b, ∃ i∈a ∪ b, d i j)
    (yes : ∀ i j, d i j → p {i,j} ∧ q {i,j})
    (safe : ∀ i∈a, ∀ j∈b, p {i,j} → q {i,j} → g i j) (c4 : boxFree g) :
    (small a ∨ small b) ∧
    (∀ i∈a, ∀ j∈b, d i j) ∧
    ∀ s, (p s ∧ q s) ↔ (∃ i∈a, i∈s) ∧ (∃ j∈b, j∈s) := by
  classical
  have otherA : ∀ i∈a, ∃ j∈b, d i j := by
    intro i hi
    obtain ⟨j,hj,h⟩ := spanA i hi
    rcases hj with ja | jb
    · exact False.elim (zq ((empty_pair qb (sep i hi) (sep j ja)).1 (yes i j h).2))
    · exact ⟨j,jb,h⟩
  have otherB : ∀ j∈b, ∃ i∈a, d i j := by
    intro j hj
    obtain ⟨i,hi,h⟩ := spanB j hj
    rcases hi with ia | ib
    · exact ⟨i,ia,h⟩
    · exact False.elim (zp ((empty_pair pa (fun h => sep i h ib) (fun h => sep j h hj)).1 (yes i j h).1))
  have p1 : ∀ i∈a, p {i} := by
    intro i hi
    obtain ⟨j,hj,h⟩ := otherA i hi
    exact (project_one pa (fun h => sep j h hj)).1 (yes i j h).1
  have q1 : ∀ j∈b, q {j} := by
    intro j hj
    obtain ⟨i,hi,h⟩ := otherB j hj
    exact (project_two qb (sep i hi)).1 (yes i j h).2
  have all : ∀ i∈a, ∀ j∈b, g i j := by
    intro i hi j hj
    exact safe i hi j hj ((project_one pa (fun h => sep j h hj)).2 (p1 i hi))
      ((project_two qb (sep i hi)).2 (q1 j hj))
  have half := thin c4 all
  refine ⟨half,?_,?_⟩
  · intro i hi j hj
    rcases half with ha | hb
    · obtain ⟨i',hi',h⟩ := otherB j hj
      exact (ha i' hi' i hi) ▸ h
    · obtain ⟨j',hj',h⟩ := otherA i hi
      exact (hb j' hj' j hj) ▸ h
  · intro s
    constructor
    · rintro ⟨ps,qs⟩
      constructor
      · by_contra miss
        push_neg at miss
        exact zp ((pa s ∅ (fun i hi => ⟨fun v => False.elim (miss i hi v),fun v => False.elim v⟩)).1 ps)
      · by_contra miss
        push_neg at miss
        exact zq ((qb s ∅ (fun j hj => ⟨fun v => False.elim (miss j hj v),fun v => False.elim v⟩)).1 qs)
    · rintro ⟨⟨i,hi,hs⟩,⟨j,hj,ht⟩⟩
      exact ⟨up _ _ (Set.singleton_subset_iff.mpr hs) (p1 i hi),
        uq _ _ (Set.singleton_subset_iff.mpr ht) (q1 j hj)⟩

end PEqualNP.Outside.L_meta_9743_Separated
