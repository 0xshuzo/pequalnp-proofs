import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9792.Pencil

variable {P L : Type}
def hits {A : Type} (bank : Set (Set A)) (x : A → Prop) : Prop :=
  ∀r∈bank,∃a∈r,x a
def common {A : Type} (bank : Set (Set A)) (a : A) := ∀r∈bank,a∈r
def incident (ed : P → L → Prop) (x : P → Prop) (y : L → Prop) :=
  ∃p l, ed p l ∧ x p ∧ y l
def Sufficient (ed : P → L → Prop) (ps : Set (Set P)) (ls : Set (Set L)) :=
  ∀x y, hits ps x → hits ls y → incident ed x y

theorem flag {ed : P → L → Prop} {ps : Set (Set P)} {ls : Set (Set L)}
    (safe : Sufficient ed ps ls) {p : P} {l : L} (hp : common ps p) (hl : common ls l) :
    ed p l := by
  obtain ⟨a,b,h,rfl,rfl⟩ := safe (fun a => p=a) (fun b => l=b)
    (fun r hr => ⟨p,hp r hr,rfl⟩) (fun r hr => ⟨l,hl r hr,rfl⟩)
  exact h

theorem rowPartner {ed : P → L → Prop} {ps : Set (Set P)} {ls : Set (Set L)}
    (safe : Sufficient ed ps ls) {p : P} (hp : common ps p) :
    ∃r∈ls,∀l∈r,ed p l := by
  classical
  by_contra no
  push_neg at no
  obtain ⟨a,b,yes,eq,bad⟩ := safe (fun a => a=p) (fun l => ¬ed p l)
    (fun r hr => ⟨p,hp r hr,rfl⟩) (fun r hr => no r hr)
  exact bad (eq ▸ yes)

theorem colPartner {ed : P → L → Prop} {ps : Set (Set P)} {ls : Set (Set L)}
    (safe : Sufficient ed ps ls) {l : L} (hl : common ls l) :
    ∃r∈ps,∀p∈r,ed p l := by
  classical
  by_contra no
  push_neg at no
  obtain ⟨a,b,yes,bad,eq⟩ := safe (fun p => ¬ed p l) (fun b => b=l)
    (fun r hr => no r hr) (fun r hr => ⟨l,hl r hr,rfl⟩)
  exact bad (eq ▸ yes)

/-- A sufficient product of arbitrarily many one-shore disjunctions can be
replaced on all accepted flags by one raw center and one existing disjunction. -/
theorem normalize {ed : P → L → Prop} {ps : Set (Set P)} {ls : Set (Set L)}
    (square : ∀p q l k, ed p l → ed p k → ed q l → ed q k → p=q ∨ l=k)
    (safe : Sufficient ed ps ls) {p₀ : P} {l₀ : L}
    (h₀ : common ps p₀) (k₀ : common ls l₀) :
    (∃r∈ls, (∀l∈r,ed p₀ l) ∧ ∀p l,common ps p → common ls l → p=p₀ ∧ l∈r) ∨
    (∃r∈ps, (∀p∈r,ed p l₀) ∧ ∀p l,common ps p → common ls l → p∈r ∧ l=l₀) := by
  classical
  by_cases only : ∀p,common ps p → p=p₀
  · obtain ⟨r,h,valid⟩ := rowPartner safe h₀
    exact Or.inl ⟨r,h,valid,fun p l hp hl => ⟨only p hp,hl r h⟩⟩
  · push_neg at only
    obtain ⟨q,hq,diff⟩ := only
    obtain ⟨r,h,valid⟩ := colPartner safe k₀
    refine Or.inr ⟨r,h,valid,fun p l hp hl => ⟨hp r h,?_⟩⟩
    exact (square q p₀ l l₀ (flag safe hq hl) (flag safe hq k₀)
      (flag safe h₀ hl) (flag safe h₀ k₀)).resolve_left diff

end PEqualNP.Outside.L_meta_9792.Pencil
