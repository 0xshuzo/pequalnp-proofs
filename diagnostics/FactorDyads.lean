import PEqualNP.Defs

namespace PEqualNP.Outside.Pcx9792Factor

abbrev P := Fin 13
abbrev L := Fin 11
abbrev Family := Finset P → Finset L → Prop
def flags : Finset (P × L) := {(0,2),(0,8),(0,10),(1,3),(1,9),(2,0),(2,4),(2,10),(3,0),(3,1),(3,5),(4,1),(4,2),(4,6),(5,0),(5,2),(5,3),(5,7),(6,1),(6,3),(6,4),(6,8),(7,2),(7,4),(7,5),(7,9),(8,3),(8,5),(8,6),(8,10),(9,4),(9,6),(9,7),(10,5),(10,7),(10,8),(11,0),(11,6),(11,8),(11,9),(12,1),(12,7),(12,9),(12,10)}
def edge (p : P) (l : L) : Prop := (p,l)∈flags
instance (p : P) (l : L) : Decidable (edge p l) := inferInstanceAs (Decidable (_ ∈ flags))
def target (s : Finset P) (t : Finset L) : Prop := ∃ p ∈ s, ∃ l ∈ t, edge p l
def increasing (A : Family) : Prop := ∀ ⦃s s' : Finset P⦄ ⦃t t' : Finset L⦄,
  s⊆s' → t⊆t' → A s t → A s' t'

theorem alternatives {A B : Family} (a : increasing A) (b : increasing B)
    (implements : ∀ s t, target s t ↔ A s t ∧ B s t) (t : Finset L) :
    (∀ s, target s t ↔ A s t) ∨ (∀ s, target s t ↔ B s t) := by
  classical
  let bad := Finset.univ.filter (fun p : P => ¬ ∃ l ∈ t, edge p l)
  have no : ¬target bad t := by
    rintro ⟨p,hp,l,hl,e⟩
    exact (Finset.mem_filter.mp hp).2 ⟨l,hl,e⟩
  have sub {s : Finset P} (n : ¬target s t) : s⊆bad := by
    intro p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rintro ⟨l,hl,e⟩
    exact n ⟨p,hp,l,hl,e⟩
  by_cases ab : A bad t
  · right
    intro s
    refine ⟨fun y=>((implements s t).mp y).2,?_⟩
    intro y
    by_contra n
    exact no ((implements bad t).mpr ⟨ab,b (sub n) (by rfl) y⟩)
  · left
    intro s
    refine ⟨fun y=>((implements s t).mp y).1,?_⟩
    intro y
    by_contra n
    exact ab (a (sub n) (by rfl) y)

theorem cross {A B : Family} (a : increasing A) (b : increasing B)
    (implements : ∀ s t, target s t ↔ A s t ∧ B s t) {p q : P} {l m : L}
    (ex : ¬edge p l) (ey : ¬edge q m) (x : A {p} {l}) (y : B {q} {m}) :
    edge p m ∨ edge q l := by
  have aa : A {p,q} {l,m} := a (by simp) (by simp) x
  have bb : B {p,q} {l,m} := b (by simp) (by simp) y
  obtain ⟨r,hr,s,hs,v⟩ := (implements _ _).mpr ⟨aa,bb⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr hs
  rcases hr with h1|h2 <;> rcases hs with h3|h4
  · exact False.elim (ex (h1 ▸ h3 ▸ v))
  · exact Or.inl (h1 ▸ h4 ▸ v)
  · exact Or.inr (h2 ▸ h3 ▸ v)
  · exact False.elim (ey (h2 ▸ h4 ▸ v))

def merge (A : Family) (l r : L) : Prop := ∀ p, edge p r → A {p} {l}

set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem outsidePair : ∀ r l m : L, r≠l → r≠m →
    ∃ p : P, edge p r ∧ ¬edge p l ∧ ¬edge p m := by decide +kernel

theorem mergedGuard {A B : Family} (a : increasing A) (b : increasing B)
    (impl : ∀ s t, target s t ↔ A s t ∧ B s t)
    {l r : L} (ne : l≠r) (fwd : merge A l r) (rev : merge A r l)
    {q : P} {m : L} (ey : ¬edge q m) (y : B {q} {m}) : edge q l ∧ edge q r := by
  have dir {l r : L} (ne : l≠r) (f : merge A l r) (g : merge A r l) : edge q l := by
    by_contra nl
    by_cases rm : r=m
    · subst m
      obtain ⟨p,pr,pl,_⟩ := outsidePair r l l ne.symm ne.symm
      -- Both factors are exact or stronger at flags. If m=r, the reverse
      -- merger accepts points of l on that same selector.
      obtain ⟨s,sl,sr,_⟩ := outsidePair l r r ne ne
      exact (cross a b impl sr ey (g s sl) y).elim sr ey
    · obtain ⟨p,pr,pl,pm⟩ := outsidePair r l m ne.symm rm
      exact (cross a b impl pl ey (f p pr) y).elim pm nl
  exact ⟨dir ne fwd rev,dir ne.symm rev fwd⟩

end PEqualNP.Outside.Pcx9792Factor
