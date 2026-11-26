import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9762_SignedSplice

variable {V : Type}

def edge (g : V → V → Prop) (s : Set V) : Prop := ∃ i∈s, ∃ j∈s, g i j
def incident (n : V → Prop) (s : Set V) : Prop := ∃ i∈s, n i
def slice (g : V → V → Prop) (n : V → Prop) (b : Bool) (s : Set V) : Prop :=
  edge g s ∨ b=true ∧ incident n s
def fires (terms : Set (Set V)) (s : Set V) : Prop := ∃ t∈terms, t⊆s
def output (r : V → V → Prop) (p : V → Prop) (donor : Bool → Set (Set V))
    (b : Bool) (s : Set V) : Prop := slice r p b s ∨ fires (donor b) s

theorem slice_up {g : V → V → Prop} {n : V → Prop} {b : Bool} {s t : Set V}
    (inc : s⊆t) : slice g n b s → slice g n b t := by
  rintro (⟨i,hi,j,hj,h⟩ | ⟨hb,i,hi,h⟩)
  · exact Or.inl ⟨i,inc hi,j,inc hj,h⟩
  · exact Or.inr ⟨hb,i,inc hi,h⟩

theorem output_up {r : V → V → Prop} {p : V → Prop} {d : Bool → Set (Set V)}
    {b : Bool} {s t : Set V} (inc : s⊆t) : output r p d b s → output r p d b t := by
  rintro (h | ⟨q,hq,qs⟩)
  · exact Or.inl (slice_up inc h)
  · exact Or.inr ⟨q,hq,qs.trans inc⟩

theorem subset_pair {s : Set V} {i j : V} (hi : i∈s) (hj : j∈s) : ({i,j}:Set V)⊆s := by
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | h
  · exact hi
  · exact (Set.mem_singleton_iff.mp h) ▸ hj

theorem splice_iff (g r : V → V → Prop) (n p : V → Prop) (d : Bool → Set (Set V))
    (sub : ∀ i j, r i j → g i j) (pin : ∀ i, p i → n i) :
    (∀ b s, output r p d b s ↔ slice g n b s) ↔
    (∀ b t, t∈d b → slice g n b t) ∧
    (∀ b i j, g i j → output r p d b {i,j}) ∧
    (∀ i, n i → output r p d true {i}) := by
  constructor
  · intro hx
    refine ⟨?_,?_,?_⟩
    · intro b t ht
      exact (hx b t).1 (Or.inr ⟨t,ht,Set.Subset.rfl⟩)
    · intro b i j h
      exact (hx b {i,j}).2 (Or.inl ⟨i,by simp,j,by simp,h⟩)
    · intro i h
      exact (hx true {i}).2 (Or.inr ⟨rfl,i,by simp,h⟩)
  · rintro ⟨valid,pairs,stars⟩ b s
    constructor
    · rintro ((⟨i,hi,j,hj,h⟩ | ⟨hb,i,hi,h⟩) | ⟨t,ht,ts⟩)
      · exact Or.inl ⟨i,hi,j,hj,sub i j h⟩
      · exact Or.inr ⟨hb,i,hi,pin i h⟩
      · exact slice_up ts (valid b t ht)
    · rintro (⟨i,hi,j,hj,h⟩ | ⟨hb,i,hi,h⟩)
      · exact output_up (subset_pair hi hj) (pairs b i j h)
      · subst b
        exact output_up (Set.singleton_subset_iff.mpr hi) (stars i h)

-- At a fixed assignment of the other variables, the two literal inputs form a
-- monotone two-input square. The negative literal can be replaced by a constant
-- except when both extremal kinds of square occur at some remaining assignments.
variable {X : Type}

def diagonal (h : Bool → Bool → X → Prop) (b : Bool) (x : X) := h b (!b) x
def rise (h : Bool → Bool → X → Prop) : Prop :=
  ∀ x, (h false false x → h false true x) ∧ (h false false x → h true false x) ∧
       (h false true x → h true true x) ∧ (h true false x → h true true x)
def andFace (h : Bool → Bool → X → Prop) (x : X) :=
  h true true x ∧ ¬ h true false x ∧ ¬ h false true x
def orFace (h : Bool → Bool → X → Prop) (x : X) :=
  ¬ h false false x ∧ h true false x ∧ h false true x

theorem clamp_true (h : Bool → Bool → X → Prop) (up : rise h)
    (mon : ∀ x, diagonal h false x → diagonal h true x) :
    (∀ b x, diagonal h b x ↔ h b true x) ↔ ¬ ∃ x, andFace h x := by
  classical
  constructor
  · rintro eq ⟨x,yes,no,_⟩
    exact no ((eq true x).2 yes)
  · intro free b x
    cases b with
    | false => rfl
    | true =>
      constructor
      · exact (up x).2.2.2
      · intro yes
        by_contra no
        exact free ⟨x,yes,no,fun w => no (mon x w)⟩

theorem clamp_false (h : Bool → Bool → X → Prop) (up : rise h)
    (mon : ∀ x, diagonal h false x → diagonal h true x) :
    (∀ b x, diagonal h b x ↔ h b false x) ↔ ¬ ∃ x, orFace h x := by
  classical
  constructor
  · rintro eq ⟨x,no,_,yes⟩
    exact no ((eq false x).1 yes)
  · intro free b x
    cases b with
    | true => rfl
    | false =>
      constructor
      · intro yes
        by_contra no
        exact free ⟨x,no,mon x yes,yes⟩
      · exact (up x).1

end PEqualNP.Outside.L_meta_9762_SignedSplice
