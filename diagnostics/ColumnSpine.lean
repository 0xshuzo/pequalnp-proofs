import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166_Column
open PEqualNP.ProofComplexity
abbrev H := Fin 4
abbrev V := H × H
abbrev C := Clause V
def masks : Array Nat := #[33825, 18465, 33345, 10305, 17025, 9345, 33810, 18450, 33090, 6210, 16770, 5250, 33300, 10260, 33060, 6180, 8580, 4740, 16920, 9240, 16680, 5160, 8520, 4680]
def atCell (k : Fin 24) (v : V) : Bool := (masks[k.val]?.getD 0).testBit (4*v.1.val+v.2.val)
def target (h : H) : C := Finset.univ.image (fun r : H=>((r,h),true))
def good (c : C) : Prop := ∀k, ClauseSat (atCell k) c
def one (h : H) (u : V) : C := insert (u,true) (target h)
def two (h : H) (u v : V) : C := insert (v,true) (one h u)

set_option maxRecDepth 10000 in
theorem avoids : ∀r h : H, ∀u v : V, u≠(r,h) → v≠(r,h) →
    ∃k : Fin 24, atCell k u=false ∧ atCell k v=false ∧ ∀j : H, j≠r → atCell k (j,h)=false := by decide +kernel

theorem spine {c : C} {h : H} {u v : V} (g : good c) (sub : c⊆two h u v) :
    target h ⊆ c := by
  intro l m
  obtain ⟨r,_,rfl⟩:=Finset.mem_image.mp m
  by_contra missing
  let s : V := (r,if h=0 then 1 else 0)
  have ns : s≠(r,h) := by
    intro eq
    have e:=congrArg Prod.snd eq
    by_cases z : h=0 <;> simp_all [s]
  let a := if u=(r,h) then s else u
  let b := if v=(r,h) then s else v
  have sa : a≠(r,h) := by by_cases eq : u=(r,h) <;> simp_all [a]
  have sb : b≠(r,h) := by by_cases eq : v=(r,h) <;> simp_all [b]
  obtain ⟨k,ua,vb,off⟩:=avoids r h a b sa sb
  obtain ⟨x,hx,on⟩:=g k
  have atx:=sub hx
  rcases Finset.mem_insert.mp atx with ev|rest
  · subst x
    by_cases eq : v=(r,h)
    · exact missing (eq ▸ hx)
    · change atCell k v=true at on
      simp [b,eq,on] at vb
  rcases Finset.mem_insert.mp rest with eu|rest
  · subst x
    by_cases eq : u=(r,h)
    · exact missing (eq ▸ hx)
    · change atCell k u=true at on
      simp [a,eq,on] at ua
  obtain ⟨j,_,ej⟩:=Finset.mem_image.mp rest
  subst x
  by_cases eq : j=r
  · subst j; exact missing hx
  · change atCell k (j,h)=true at on
    simp [off j eq] at on

theorem firstParent {p n c : C} {w : V} (cut : c=p.erase (w,true) ∪ n.erase (w,false)) :
    p⊆insert (w,true) c := by
  intro x m
  by_cases eq : x=(w,true)
  · exact Finset.mem_insert.mpr (Or.inl eq)
  · apply Finset.mem_insert.mpr
    right
    rw [cut]
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,m⟩)

theorem oneStep {p n : C} {w : V} {h : H} (g : good p)
    (step : target h=p.erase (w,true) ∪ n.erase (w,false)) (fresh : p≠target h) :
    p=one h w ∧ (w,true)∉target h := by
  have sub:=firstParent step
  have ext : p⊆two h w w := fun x m=>Finset.mem_insert_of_mem (sub m)
  have all:=spine g ext
  have tr : (w,true)∈p := by
    by_contra no
    apply fresh
    apply Finset.Subset.antisymm _ all
    intro x hx
    rcases Finset.mem_insert.mp (sub hx) with eq|yes
    · exact False.elim (no (eq ▸ hx))
    · exact yes
  constructor
  · apply Finset.Subset.antisymm sub
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|yes
    · exact tr
    · exact all yes
  · intro m
    apply fresh
    apply Finset.Subset.antisymm _ all
    intro x hx
    rcases Finset.mem_insert.mp (sub hx) with rfl|q
    · exact m
    · exact q

end PEqualNP.Outside.L_pcx_166_Column
