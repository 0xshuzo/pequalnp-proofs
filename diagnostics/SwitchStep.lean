import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166.Switch
open PEqualNP.ProofComplexity Finset
abbrev Big := Fin 5 × Fin 4
abbrev Small := Fin 4 × Fin 3
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

def emb (p : Fin 5) (h : Fin 4) (u : Small) : Big := (p.succAbove u.1,h.succAbove u.2)
def lower (p : Fin 5) (h : Fin 4) (z : Big) : Small :=
  (⟨(z.1.val - (if p<z.1 then 1 else 0))%4, Nat.mod_lt _ (by decide)⟩,
   ⟨(z.2.val - (if h<z.2 then 1 else 0))%3, Nat.mod_lt _ (by decide)⟩)
def switch (p : Fin 5) (h : Fin 4) (u : Small) (z : Big) : Option (Small × Bool) :=
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
theorem oneSwitch : let f := switch 4 3 (0,0)
    (((raw 5 4).filter (fun c=> paid f c)).image (body f))=raw 4 3 ∧
    ((raw 5 4).filter (fun c=> paid f c)).card=22 := by decide +kernel

end PEqualNP.Outside.L_pcx_166.Switch
namespace PEqualNP.Outside.L_pcx_166.Switch
open PEqualNP.ProofComplexity Finset
variable {A B : Type} [DecidableEq A] [DecidableEq B]
def flip (y : B×Bool) : B×Bool := (y.1,!y.2)
theorem twice (y : B×Bool) : flip (flip y)=y := by rcases y with ⟨a,b⟩; cases b <;> rfl
def Good (f : A→Option (B×Bool)) (c : Clause A) : Prop :=
  (∀ z∈c, f z.1=none → z.2=true) ∧ (∀ z∈body f c, flip z∉body f c)
def Join {T : Type} [DecidableEq T] (p n : Clause T) (w : T) :=
  p.erase (w,true) ∪ n.erase (w,false)
theorem monoBody (f : A→Option (B×Bool)) {a b : Clause A} (inc : a⊆b) :
    body f a⊆body f b := by
  intro z h
  obtain ⟨v,hv,mem⟩:=mem_biUnion.mp h
  exact mem_biUnion.mpr ⟨v,inc hv,mem⟩
theorem peeled {f : A→Option (B×Bool)} {c r : Clause A} {w : A×Bool}
    (inc : c.erase w⊆r) (z : B×Bool) (hz : z∈body f c) : z∈body f r ∨ z∈translate f w := by
  obtain ⟨v,hv,mem⟩:=mem_biUnion.mp hz
  by_cases eq : v=w
  · exact Or.inr (eq ▸ mem)
  · exact Or.inl (mem_biUnion.mpr ⟨v,inc (mem_erase.mpr ⟨eq,hv⟩),mem⟩)
theorem fixedClean {f : A→Option (B×Bool)} {c r : Clause A} {w : A×Bool}
    (inc : c.erase w⊆r) (hr : Good f r) (pin : f w.1=none → w.2=true) :
    ∀ z∈c, f z.1=none → z.2=true := by
  intro z mem off
  by_cases eq : z=w
  · subst z; exact pin off
  · exact hr.1 z (inc (mem_erase.mpr ⟨eq,mem⟩)) off
theorem boundedClean {f : A→Option (B×Bool)} {c r : Clause A}
    (ok : ∀ z∈c, f z.1=none → z.2=true) (hr : Good f r) (inc : body f c⊆body f r) :
    Good f c := ⟨ok,fun z hz opp=> hr.2 z (inc hz) (inc opp)⟩
theorem extraClean {f : A→Option (B×Bool)} {c r : Clause A} {v : B×Bool}
    (ok : ∀ z∈c, f z.1=none → z.2=true) (hr : Good f r)
    (inc : ∀ z∈body f c, z∈body f r ∨ z=v) (opp : flip v∉body f r) : Good f c := by
  refine ⟨ok,?_⟩
  intro z hz hy
  rcases inc z hz with h|e
  · rcases inc (flip z) hy with hh|eq
    · exact hr.2 _ h hh
    · have zz : flip v=z := by rw [←eq,twice]
      exact opp (zz.symm ▸ h)
  · subst z
    rcases inc (flip v) hy with hh|eq
    · exact opp hh
    · rcases v with ⟨i,b⟩; cases b <;> simp [flip] at eq

theorem localstep {f : A→Option (B×Bool)} {p n : Clause A} {w : A}
    (hr : Good f (Join p n w)) :
    (Good f p ∧ body f p⊆body f (Join p n w)) ∨
    (Good f n ∧ body f n⊆body f (Join p n w)) ∨
    (∃v : B×Bool, f w=some v ∧ Good f p ∧ Good f n ∧
      (∀z∈body f p, z∈body f (Join p n w) ∨ z=v) ∧
      (∀z∈body f n, z∈body f (Join p n w) ∨ z=flip v)) := by
  have lp : p.erase (w,true)⊆Join p n w := fun _ h=>mem_union_left _ h
  have ln : n.erase (w,false)⊆Join p n w := fun _ h=>mem_union_right _ h
  cases hw : f w with
  | none =>
    have inc : body f p⊆body f (Join p n w) := by
      intro z hz
      rcases peeled lp z hz with h|h
      · exact h
      · simp [translate,hw] at h
    exact Or.inl ⟨boundedClean (fixedClean lp hr (fun _=>rfl)) hr inc,inc⟩
  | some v =>
    have op := fixedClean lp hr (fun _=>rfl)
    have on := fixedClean ln hr (by intro off; change f w=none at off; rw [hw] at off; contradiction)
    have bp : ∀z∈body f p, z∈body f (Join p n w) ∨ z=v := by
      intro z hz
      rcases peeled lp z hz with a|b
      · exact Or.inl a
      · right; rcases v with ⟨i,bv⟩; simpa [translate,hw] using b
    have bn : ∀z∈body f n, z∈body f (Join p n w) ∨ z=flip v := by
      intro z hz
      rcases peeled ln z hz with a|b
      · exact Or.inl a
      · right; rcases v with ⟨i,bv⟩; simpa [translate,hw,flip] using b
    by_cases a : v∈body f (Join p n w)
    · have inc : body f p⊆body f (Join p n w) := by
        intro z hz; rcases bp z hz with ok|rfl; exact ok; exact a
      exact Or.inl ⟨boundedClean op hr inc,inc⟩
    by_cases b : flip v∈body f (Join p n w)
    · have inc : body f n⊆body f (Join p n w) := by
        intro z hz; rcases bn z hz with ok|rfl; exact ok; exact b
      exact Or.inr (Or.inl ⟨boundedClean on hr inc,inc⟩)
    exact Or.inr (Or.inr ⟨v,rfl,extraClean op hr bp b,extraClean on hr bn (by simpa [twice] using a),bp,bn⟩)
end PEqualNP.Outside.L_pcx_166.Switch
