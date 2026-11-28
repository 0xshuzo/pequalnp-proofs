import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.Veto
variable {P L : Type}
def hit (G : P → L → Prop) (s : Set P) (t : Set L) := ∃ p∈s,∃ l∈t,G p l
def inc (F : Set P → Set L → Prop) :=
  ∀ (s s' : Set P) (t t' : Set L),s⊆s' → t⊆t' → F s t → F s' t'
def rowPrime (F : Set P → Set L → Prop) (p : P) (l m : L) :=
  F {p} {l,m} ∧ ¬F ∅ {l,m} ∧ ¬F {p} {l} ∧ ¬F {p} {m}
def colPrime (F : Set P → Set L → Prop) (p q : P) (l : L) :=
  F {p,q} {l} ∧ ¬F {p,q} ∅ ∧ ¬F {p} {l} ∧ ¬F {q} {l}
def fourFree (G : P → L → Prop) :=
  ∀p q l m,p≠q → l≠m → G p l → G p m → G q l → G q m → False
variable (G : P → L → Prop) (F H B : Set P → Set L → Prop)
def equation := ∀s t,hit G s t ↔ F s t ∨ (H s t ∧ ¬B s t)
private theorem edge {p l} : hit G {p} {l} ↔ G p l := by simp [hit]
theorem dirtyBudget (ok : equation G F H B) {p l} (h : H {p} {l}) (no : ¬G p l) :
    ¬F {p} {l} ∧ B {p} {l} := by
  classical
  have e := ok {p} {l}
  rw [edge] at e
  refine ⟨fun f => no (e.mpr (.inl f)),?_⟩
  by_contra b
  exact no (e.mpr (.inr ⟨h,b⟩))

theorem forcedRow (ok : equation G F H B) (up : inc B)
    {p l m} (real : G p l) (absent : ¬F {p} {l}) (sp : H {p} {m}) (bad : ¬G p m) :
    rowPrime F p l m := by
  obtain ⟨nm,b⟩ := dirtyBudget G F H B ok sp bad
  have big : B {p} {l,m} := up _ _ _ _ (by intro x h;exact h)
    (by intro x h; simp only [Set.mem_singleton_iff] at h; subst x; simp) b
  have target : hit G {p} {l,m} := ⟨p,by simp,l,by simp,real⟩
  refine ⟨((ok _ _).mp target).resolve_right (fun q => q.2 big),?_,absent,nm⟩
  intro f
  have bad0 := (ok ∅ {l,m}).mpr (Or.inl f)
  simpa [hit] using bad0

theorem forcedCol (ok : equation G F H B) (up : inc B)
    {p q l} (real : G p l) (absent : ¬F {p} {l}) (sp : H {q} {l}) (bad : ¬G q l) :
    colPrime F p q l := by
  obtain ⟨nm,b⟩ := dirtyBudget G F H B ok sp bad
  have big : B {p,q} {l} := up _ _ _ _
    (by intro x h; simp only [Set.mem_singleton_iff] at h; subst x; simp)
    (by intro x h;exact h) b
  have target : hit G {p,q} {l} := ⟨p,by simp,l,by simp,real⟩
  refine ⟨((ok _ _).mp target).resolve_right (fun z => z.2 big),?_,absent,nm⟩
  intro f
  have bad0 := (ok {p,q} ∅).mpr (Or.inl f)
  simpa [hit] using bad0

-- A genuine two-by-two-or-larger rectangle cannot own two distinct target
-- edges unless the exterior has a three-variable prime on an exposed row or column.
theorem uniqueResidual (ok : equation G F H B) (up : inc B) (no4 : fourFree G)
    (S : Set P) (T : Set L) (full : ∀p∈S,∀l∈T,H {p} {l})
    (nr : ∀p∈S,∀l∈T,∀m∈T,¬rowPrime F p l m)
    (nc : ∀p∈S,∀q∈S,∀l∈T,¬colPrime F p q l)
    {p1 p2 : P} {l1 l2 : L} (s1 : p1∈S) (s2 : p2∈S) (p12 : p1≠p2)
    (t1 : l1∈T) (t2 : l2∈T) (l12 : l1≠l2)
    {p q : P} {l m : L} (ps : p∈S) (qs : q∈S) (lt : l∈T) (mt : m∈T)
    (e : G p l) (e' : G q m) (f : ¬F {p} {l}) (f' : ¬F {q} {m}) :
    p=q ∧ l=m := by
  classical
  have allRows : ∀ u∈S,∀v∈T,G u v → ¬F {u} {v} → ∀w∈T,G u w := by
    intro u hu v hv uv hf w hw
    by_contra missing
    exact nr u hu v hv w hw (forcedRow G F H B ok up uv hf (full u hu w hw) missing)
  have allCols : ∀ u∈S,∀v∈T,G u v → ¬F {u} {v} → ∀w∈S,G w v := by
    intro u hu v hv uv hf w hw
    by_contra missing
    exact nc u hu w hw v hv (forcedCol G F H B ok up uv hf (full w hw v hv) missing)
  constructor
  · by_contra diff
    exact no4 p q l1 l2 diff l12 (allRows p ps l lt e f l1 t1) (allRows p ps l lt e f l2 t2)
      (allRows q qs m mt e' f' l1 t1) (allRows q qs m mt e' f' l2 t2)
  · by_contra diff
    exact no4 p1 p2 l m p12 diff (allCols p ps l lt e f p1 s1) (allCols q qs m mt e' f' p1 s1)
      (allCols p ps l lt e f p2 s2) (allCols q qs m mt e' f' p2 s2)

theorem bypass (ok : equation G F H B) (fm : inc F) {p l} (edge0 : G p l)
    (only : ∀u v,G u v → ¬F {u} {v} → u=p ∧ v=l) (s : Set P) (t : Set L) :
    hit G s t ↔ F s t ∨ (p∈s ∧ l∈t) := by
  classical
  constructor
  · rintro ⟨u,hu,v,hv,g⟩
    by_cases got : F {u} {v}
    · exact .inl (fm _ _ _ _ (by simpa using hu) (by simpa using hv) got)
    · obtain ⟨rfl,rfl⟩ := only u v g got
      exact .inr ⟨hu,hv⟩
  · rintro (f | ⟨hp,hl⟩)
    · exact (ok _ _).mpr (.inl f)
    · exact ⟨p,hp,l,hl,edge0⟩
end PEqualNP.Outside.L_meta_9809.Veto
