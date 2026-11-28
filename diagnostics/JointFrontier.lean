import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_166_JointFrontier
open PEqualNP.ProofComplexity
abbrev Row := Fin 5
abbrev Hole := Fin 4
abbrev V := Row × Hole
abbrev Board := Hole → Row
abbrev C := Clause V

def one (g : Board) (v : V) : Bool := decide (g v.2 = v.1)
def fails (X : Set Board) (c : C) : Prop := ∀ g∈X,¬ClauseSat (one g) c
def hull {ι : Type} (X : ι → Set Board) : Set Board :=
  {g | ∀ h : Hole,∃ i : ι,∃ b∈X i,b h=g h}

theorem hull_fails {ι : Type} (X : ι → Set Board) {c : C} (killed : ∀ i,fails (X i) c) :
    fails (hull X) c := by
 intro g hg sat
 obtain ⟨l,lm,ls⟩ := sat
 obtain ⟨i,b,bmem,eq⟩ := hg l.1.2
 apply killed i b bmem
 refine ⟨l,lm,?_⟩
 change decide (b l.1.2=l.1.1)=l.2
 change decide (g l.1.2=l.1.1)=l.2 at ls
 rwa [eq]

def cut (X : Set Board) (v : V) (side : Bool) : Set Board := {g | g∈X ∧ one g v=side}
def join (p n : C) (v : V) : C := p.erase (v,true) ∪ n.erase (v,false)

-- All demands served by the same physical line are assigned together, with its same pivot.
theorem shared_step {ι : Type} (X : ι → Set Board) {p n : C} {v : V}
    (served : ∀ i,fails (X i) (join p n v)) :
    fails (cut (hull X) v false) p ∧ fails (cut (hull X) v true) n := by
 have dead := hull_fails X served
 constructor
 · intro g h ⟨l,lm,ls⟩
   obtain ⟨hg,bit⟩ := h
   have ne : l≠(v,true) := by
     intro eq
     subst l
     change one g v=true at ls
     rw [bit] at ls
     contradiction
   exact dead g hg ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,lm⟩),ls⟩
 · intro g h ⟨l,lm,ls⟩
   obtain ⟨hg,bit⟩ := h
   have ne : l≠(v,false) := by
     intro eq
     subst l
     change one g v=false at ls
     rw [bit] at ls
     contradiction
   exact dead g hg ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,lm⟩),ls⟩

theorem collision_sat (i j : Row) (h : Hole) (ne : i≠j) (g : Board) :
    ClauseSat (one g) ({((i,h),false),((j,h),false)} : C) := by
 by_cases a : g h=i
 · refine ⟨((j,h),false),by simp,?_⟩
   change decide (g h=j)=false
   simp [a,ne]
 · refine ⟨((i,h),false),by simp,?_⟩
   change decide (g h=i)=false
   simp [a]

theorem shared_collision {ι : Type} (X : ι → Set Board) (i j : Row) (h : Hole)
    (ne : i≠j) (p : C) (v : V)
    (served : ∀ t,fails (X t) (join p {((i,h),false),((j,h),false)} v)) :
    fails (hull X) p := by
 obtain ⟨left,right⟩ := shared_step X served
 intro g hg
 cases b : one g v with
 | false => exact left g ⟨hg,b⟩
 | true => exact False.elim (right g ⟨hg,b⟩ (collision_sat i j h ne g))
end PEqualNP.Outside.L_pcx_166_JointFrontier
