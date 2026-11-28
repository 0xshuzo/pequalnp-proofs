import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9792.Crossed
abbrev V := Fin 24
def graph : List (V×V) := [(0,15),(0,21),(0,23),(1,16),(1,22),(2,13),(2,17),(2,23),(3,13),(3,14),(3,18),(4,14),(4,15),(4,19),(5,13),(5,15),(5,16),(5,20),(6,14),(6,16),(6,17),(6,21),(7,15),(7,17),(7,18),(7,22),(8,16),(8,18),(8,19),(8,23),(9,17),(9,19),(9,20),(10,18),(10,20),(10,21),(11,13),(11,19),(11,21),(11,22),(12,14),(12,20),(12,22),(12,23)]

def hasEdge (x : V → Bool) := ∃p l,(p,l)∈graph ∧ x p=true ∧ x l=true
def a : List V := [0,4,5,7]
def b : List V := [2,3,5,11]
def sufficientProduct (x : V → Bool) :=
  ((x 13 || ((x 13 || x 15) && a.any x)) && b.any x)
theorem listedA : ∀i : V,i∈a → (i,15)∈graph := by decide +kernel
theorem listedB : ∀i : V,i∈b → (i,13)∈graph := by decide +kernel
theorem safe (x : V → Bool) (hit : sufficientProduct x=true) : hasEdge x := by
  unfold sufficientProduct at hit
  obtain ⟨alternative,bOn⟩ := Bool.and_eq_true_iff.mp hit
  obtain ⟨p,hm,hp⟩ := List.any_eq_true.mp bOn
  rw [Bool.or_eq_true] at alternative
  rcases alternative with yes|alt
  · exact ⟨p,13,listedB _ hm,hp,yes⟩
  · obtain ⟨lineOn,aOn⟩ := Bool.and_eq_true_iff.mp alt
    rw [Bool.or_eq_true] at lineOn
    rcases lineOn with yes|yes
    · exact ⟨p,13,listedB _ hm,hp,yes⟩
    · obtain ⟨q,hm',hq⟩ := List.any_eq_true.mp aOn
      exact ⟨q,15,listedA _ hm',hq,yes⟩

def dyad (p l : V) (i : V) := decide (i=p ∨ i=l)
def five : List (V×V) := [(2,13),(3,13),(5,13),(5,15),(11,13)]
theorem exactDyads : ∀p l : V,p.val<13 → 13≤l.val →
    (sufficientProduct (dyad p l)=true ↔ (p,l)∈five) := by decide +kernel
theorem nonstar : ¬∃v : V,∀p : V,∀l : V,(p,l)∈five → v=p ∨ v=l := by decide +kernel
end PEqualNP.Outside.L_meta_9792.Crossed
