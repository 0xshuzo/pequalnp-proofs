import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9471.SwitchInventory
open PEqualNP.ProofComplexity Finset
abbrev Big := Fin 6 × Fin 5
abbrev Small := Fin 5 × Fin 4
def pigeon (m n : Nat) (i : Fin m) : Clause (Fin m × Fin n) := univ.image (fun j => ((i,j),true))
def collision (m n : Nat) (i k : Fin m) (j : Fin n) : Clause (Fin m × Fin n) :=
  {((i,j),false),((k,j),false)}
def raw (m n : Nat) : Finset (Clause (Fin m × Fin n)) :=
  (univ.image (pigeon m n)) ∪
    ((univ.filter (fun v : Fin m × Fin m × Fin n => v.1≠v.2.1)).image
       (fun v => collision m n v.1 v.2.1 v.2.2))
theorem raw_spec {m n : Nat} {C : Clause (Fin m×Fin n)} : C∈raw m n ↔ C∈PHP m n := by
  simp only [raw,mem_union,mem_image,mem_univ,mem_filter,true_and]
  constructor
  · rintro (⟨i,rfl⟩|⟨⟨i,k,j⟩,ne,rfl⟩)
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨i,k,j,ne,rfl⟩
  · rintro (⟨i,rfl⟩|⟨i,k,j,ne,rfl⟩)
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨⟨i,k,j⟩,ne,rfl⟩

def emb (p : Fin 6) (h : Fin 5) (u : Small) : Big := (p.succAbove u.1,h.succAbove u.2)
def lower (p : Fin 6) (h : Fin 5) (z : Big) : Small :=
  (⟨(z.1.val - (if p<z.1 then 1 else 0))%5, Nat.mod_lt _ (by decide)⟩,
   ⟨(z.2.val - (if h<z.2 then 1 else 0))%4, Nat.mod_lt _ (by decide)⟩)
def switch (p : Fin 6) (h : Fin 5) (u : Small) (z : Big) : Option (Small × Bool) :=
  if z=(p,h) then some (u,false)
  else if z=(p,(emb p h u).2) ∨ z=((emb p h u).1,h) then some (u,true)
  else if z=emb p h u ∨ z.1=p ∨ z.2=h then none
  else some (lower p h z,true)

def translate {A B : Type} [DecidableEq B] (f : A→Option (B×Bool)) (z : A×Bool) :
    Finset (B×Bool) :=
  match f z.1 with
  | none => ∅
  | some (w,s) => {(w,if z.2 then s else !s)}
def body {A B : Type} [DecidableEq B] (f : A→Option (B×Bool)) (c : Clause A) :=
  c.biUnion (translate f)
def paid {A B : Type} [DecidableEq A] [DecidableEq B] (f : A→Option (B×Bool)) (c : Clause A) : Bool :=
  decide (∀ z∈c, f z.1=none → z.2=true) &&
    decide (∀ z∈body f c, (z.1,!z.2)∉body f c)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem oneSwitch : let f := switch 5 4 (0,0)
    (((raw 6 5).filter (fun c=> paid f c)).image (body f))=raw 5 4 := by decide +kernel

end PEqualNP.Outside.L_meta_9471.SwitchInventory
namespace PEqualNP.Outside.L_meta_9471.SwitchInventory
open PEqualNP.ProofComplexity Finset
def clauseImage (p : Fin 6) (h : Fin 5) (u : Small) :=
  let f := switch p h u
  ((raw 6 5).filter (fun c=>paid f c)).image (body f)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem firstRaw : ∀ u, clauseImage 0 0 u = raw 5 4 := by decide +kernel

end PEqualNP.Outside.L_meta_9471.SwitchInventory
