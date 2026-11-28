import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166_Lift
open PEqualNP.ProofComplexity
abbrev V := Fin 5 × Fin 4
abbrev C := Clause V
abbrev E := C × Option (C × C × V)

def ax (c : C) : Bool :=
  decide (∃ i : Fin 5, c=Finset.univ.image (fun j : Fin 4=>((i,j),true))) ||
  decide (∃ i j : Fin 5, ∃h : Fin 4, i≠j ∧ c={((i,h),false),((j,h),false)})

theorem ax_true {c : C} (h : ax c=true) : c∈PHP 5 4 := by
  simp only [ax,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨r,hr⟩|⟨r,s,j,ne,eq⟩
  · exact Or.inl ⟨r,hr⟩
  · exact Or.inr ⟨r,s,j,ne,eq⟩

def check (seed : List C) : List E → Bool
  | [] => true
  | (c,none)::tail => ax c && check seed tail
  | (c,some (p,n,v))::tail =>
      decide (p∈tail.map Prod.fst ++ seed ∧ n∈tail.map Prod.fst ++ seed ∧
        (v,true)∈p ∧ (v,false)∈n ∧ c=p.erase (v,true) ∪ n.erase (v,false)) && check seed tail

theorem liftMem {seed pre : List C} (h : ∀c∈seed, c∈pre)
    {add : List C} {c : C} (hc : c∈add++seed) : c∈add++pre := by
  rcases List.mem_append.mp hc with a|b
  · exact List.mem_append.mpr (Or.inl a)
  · exact List.mem_append.mpr (Or.inr (h c b))

theorem check_sound {seed pre : List C} (base : IsDerivation (PHP 5 4) pre)
    (h : ∀c∈seed,c∈pre) : ∀t : List E, check seed t=true →
      IsDerivation (PHP 5 4) (t.map Prod.fst ++ pre)
  | [], _ => base
  | (c,none)::tail, ok => by
    simp only [check,Bool.and_eq_true] at ok
    exact IsDerivation.ax (check_sound base h tail ok.2) (ax_true ok.1)
  | (c,some (p,n,v))::tail,ok => by
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨⟨mp,mn,pp,nn,eq⟩,old⟩:=ok
    exact IsDerivation.res (check_sound base h tail old) (liftMem h mp) (liftMem h mn) ⟨v,pp,nn,eq⟩

def targets : List C := [{((0,0),true),((1,0),true),((2,0),true),((3,0),true)},{((0,1),true),((1,1),true),((2,1),true),((3,1),true)},{((0,2),true),((1,2),true),((2,2),true),((3,2),true)},{((0,3),true),((1,3),true),((2,3),true),((3,3),true)}]
def suffix : List E := [
  ((∅ : C), some ({((4,3),true)},{((4,3),false)},(4,3))),
  ({((4,3),true)}, some ({((4,2),true),((4,3),true)},{((4,2),false)},(4,2))),
  ({((4,2),true),((4,3),true)}, some ({((4,1),true),((4,2),true),((4,3),true)},{((4,1),false)},(4,1))),
  ({((4,1),true),((4,2),true),((4,3),true)}, some ({((4,0),true),((4,1),true),((4,2),true),((4,3),true)},{((4,0),false)},(4,0))),
  ({((4,3),false)}, some ({((3,3),true),((4,3),false)},{((3,3),false),((4,3),false)},(3,3))),
  ({((3,3),true),((4,3),false)}, some ({((2,3),true),((3,3),true),((4,3),false)},{((2,3),false),((4,3),false)},(2,3))),
  ({((2,3),true),((3,3),true),((4,3),false)}, some ({((1,3),true),((2,3),true),((3,3),true),((4,3),false)},{((1,3),false),((4,3),false)},(1,3))),
  ({((1,3),true),((2,3),true),((3,3),true),((4,3),false)}, some ({((0,3),true),((1,3),true),((2,3),true),((3,3),true)},{((0,3),false),((4,3),false)},(0,3))),
  ({((4,2),false)}, some ({((3,2),true),((4,2),false)},{((3,2),false),((4,2),false)},(3,2))),
  ({((3,2),true),((4,2),false)}, some ({((2,2),true),((3,2),true),((4,2),false)},{((2,2),false),((4,2),false)},(2,2))),
  ({((2,2),true),((3,2),true),((4,2),false)}, some ({((1,2),true),((2,2),true),((3,2),true),((4,2),false)},{((1,2),false),((4,2),false)},(1,2))),
  ({((1,2),true),((2,2),true),((3,2),true),((4,2),false)}, some ({((0,2),true),((1,2),true),((2,2),true),((3,2),true)},{((0,2),false),((4,2),false)},(0,2))),
  ({((4,1),false)}, some ({((3,1),true),((4,1),false)},{((3,1),false),((4,1),false)},(3,1))),
  ({((3,1),true),((4,1),false)}, some ({((2,1),true),((3,1),true),((4,1),false)},{((2,1),false),((4,1),false)},(2,1))),
  ({((2,1),true),((3,1),true),((4,1),false)}, some ({((1,1),true),((2,1),true),((3,1),true),((4,1),false)},{((1,1),false),((4,1),false)},(1,1))),
  ({((1,1),true),((2,1),true),((3,1),true),((4,1),false)}, some ({((0,1),true),((1,1),true),((2,1),true),((3,1),true)},{((0,1),false),((4,1),false)},(0,1))),
  ({((4,0),false)}, some ({((3,0),true),((4,0),false)},{((3,0),false),((4,0),false)},(3,0))),
  ({((3,0),true),((4,0),false)}, some ({((2,0),true),((3,0),true),((4,0),false)},{((2,0),false),((4,0),false)},(2,0))),
  ({((2,0),true),((3,0),true),((4,0),false)}, some ({((1,0),true),((2,0),true),((3,0),true),((4,0),false)},{((1,0),false),((4,0),false)},(1,0))),
  ({((1,0),true),((2,0),true),((3,0),true),((4,0),false)}, some ({((0,0),true),((1,0),true),((2,0),true),((3,0),true)},{((0,0),false),((4,0),false)},(0,0))),
  ({((3,3),false),((4,3),false)}, none),
  ({((2,3),false),((4,3),false)}, none),
  ({((1,3),false),((4,3),false)}, none),
  ({((0,3),false),((4,3),false)}, none),
  ({((3,2),false),((4,2),false)}, none),
  ({((2,2),false),((4,2),false)}, none),
  ({((1,2),false),((4,2),false)}, none),
  ({((0,2),false),((4,2),false)}, none),
  ({((3,1),false),((4,1),false)}, none),
  ({((2,1),false),((4,1),false)}, none),
  ({((1,1),false),((4,1),false)}, none),
  ({((0,1),false),((4,1),false)}, none),
  ({((3,0),false),((4,0),false)}, none),
  ({((2,0),false),((4,0),false)}, none),
  ({((1,0),false),((4,0),false)}, none),
  ({((0,0),false),((4,0),false)}, none),
  ({((4,0),true),((4,1),true),((4,2),true),((4,3),true)}, none)]

set_option maxRecDepth 8000 in
theorem replay : check targets suffix=true := by decide +kernel

theorem lift37 {π : List C} (proof : IsDerivation (PHP 5 4) π)
    (surj : ∀c∈targets,c∈π) : ∃τ : List C, IsRefutation (PHP 5 4) τ ∧ τ.length=π.length+37 := by
  refine ⟨suffix.map Prod.fst ++ π,⟨check_sound proof surj suffix replay,?_⟩,?_⟩
  · exact List.mem_append.mpr (Or.inl (show (∅ : C)∈suffix.map Prod.fst by decide))
  · have h : suffix.length=37 := by decide
    simp [h,Nat.add_comm]

theorem threshold {π : List C} (proof : IsDerivation (PHP 5 4) π)
    (surj : ∀c∈targets,c∈π) (short : π.length≤92) :
    ∃τ : List C, IsRefutation (PHP 5 4) τ ∧ τ.length≤129 := by
  obtain ⟨τ,ref,le⟩:=lift37 proof surj
  exact ⟨τ,ref,by omega⟩

end PEqualNP.Outside.L_pcx_166_Lift
