import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9762_veto

variable {P L : Type}

def hit (G : P → L → Prop) (s : Set P) (t : Set L) : Prop :=
  ∃ p l, p ∈ s ∧ l ∈ t ∧ G p l

private theorem solo (G : P → L → Prop) (p : P) (l : L) :
    hit G {p} {l} ↔ G p l := by
  simp [hit]

private theorem row (G : P → L → Prop) (p : P) (l m : L) :
    hit G {p} {l, m} ↔ G p l ∨ G p m := by
  simp only [hit, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    subst x
    rcases hy with hy | hy
    · subst y; exact Or.inl h
    · subst y; exact Or.inr h
  · rintro (h | h)
    · exact ⟨p, l, rfl, Or.inl rfl, h⟩
    · exact ⟨p, m, rfl, Or.inr rfl, h⟩

private theorem col (G : P → L → Prop) (p q : P) (l : L) :
    hit G {p, q} {l} ↔ G p l ∨ G q l := by
  simp only [hit, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    subst y
    rcases hx with hx | hx
    · subst x; exact Or.inl h
    · subst x; exact Or.inr h
  · rintro (h | h)
    · exact ⟨p, l, Or.inl rfl, rfl, h⟩
    · exact ⟨q, l, Or.inr rfl, rfl, h⟩

variable (G R H : P → L → Prop) (B : Set P → Set L → Prop)

def corrected : Prop :=
  ∀ s t, hit G s t ↔ hit R s t ∨ (hit H s t ∧ ¬ B s t)

def increasing : Prop := ∀ s s' t t', s ⊆ s' → t ⊆ t' → B s t → B s' t'

private theorem dirty (ok : corrected G R H B) {p l} (hH : H p l) (hG : ¬ G p l) :
    ¬ R p l ∧ B {p} {l} := by
  classical
  have k := ok {p} {l}
  simp only [solo] at k
  exact ⟨fun h => hG (k.mpr (Or.inl h)), by
    by_contra h
    exact hG (k.mpr (Or.inr ⟨hH, h⟩))⟩

theorem exclusive_clean (ok : corrected G R H B) (up : increasing B)
    {p l} (g : G p l) (r : ¬ R p l) :
    H p l ∧ (∀ m, H p m → G p m) ∧ (∀ q, H q l → G q l) := by
  classical
  have k := ok {p} {l}
  simp only [solo] at k
  refine ⟨((k.mp g).resolve_left r).1, ?_, ?_⟩
  · intro m hm
    by_contra bad
    have ds := dirty G R H B ok hm bad
    have big : B {p} {l,m} := up {p} {p} {m} {l,m} (by intro x h; exact h)
      (by intro x h; simp only [Set.mem_singleton_iff] at h; subst x; simp) ds.2
    have t := ok {p} {l,m}
    simp only [row] at t
    rcases t.mp (Or.inl g) with (h|h) | h
    · exact r h
    · exact ds.1 h
    · exact h.2 big
  · intro q hq
    by_contra bad
    have ds := dirty G R H B ok hq bad
    have big : B {p,q} {l} := up {q} {p,q} {l} {l}
      (by intro x h; simp only [Set.mem_singleton_iff] at h; subst x; simp)
      (by intro x h; exact h) ds.2
    have t := ok {p,q} {l}
    simp only [col] at t
    rcases t.mp (Or.inl g) with (h|h) | h
    · exact r h
    · exact ds.1 h
    · exact h.2 big

/-- Deleting all vertices incident with dirty edges in the positive donor removes
the veto entirely. Both the residual and the positive donor are edge functions. -/
theorem delete_dirty_vertices (ok : corrected G R H B) (up : increasing B) (s : Set P) (t : Set L) :
    hit G s t ↔ hit R s t ∨ hit H
      {p | p ∈ s ∧ ∀ l, H p l → G p l} {l | l ∈ t ∧ ∀ p, H p l → G p l} := by
  classical
  constructor
  · rintro ⟨p,l,sp,tl,g⟩
    by_cases r : R p l
    · exact Or.inl ⟨p,l,sp,tl,r⟩
    · obtain ⟨h,cr,cl⟩ := exclusive_clean G R H B ok up g r
      exact Or.inr ⟨p,l,⟨sp,cr⟩,⟨tl,cl⟩,h⟩
  · rintro (r | h)
    · exact (ok s t).mpr (Or.inl r)
    · rcases h with ⟨p,l,sp,tl,e⟩
      exact ⟨p,l,sp.1,tl.1,sp.2 l e⟩

end PEqualNP.Outside.L_meta_9762_veto
