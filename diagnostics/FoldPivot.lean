import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166_Fold
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]
abbrev C := Clause V
def Reach (F : Set (C (V:=V))) (pre : List C) (k : Nat) (z : C) : Prop :=
  ∃ s : List C, IsDerivation F (s ++ pre) ∧ s.length ≤ k ∧ ∃ c ∈ s ++ pre, c ⊆ z

theorem one {F : Set (C (V:=V))} {pre : List C} (d : IsDerivation F pre)
    {p n z : C} {v : V} (hp : p∈pre) (hn : n∈pre)
    (ps : p⊆insert (v,true) z) (ns : n⊆insert (v,false) z) : Reach F pre 1 z := by
 classical
 by_cases pos : (v,true)∈p
 · by_cases neg : (v,false)∈n
   · let r := p.erase (v,true) ∪ n.erase (v,false)
     refine ⟨[r],IsDerivation.res d hp hn ⟨v,pos,neg,rfl⟩,by decide,r,by simp,?_⟩
     intro l hl
     rcases Finset.mem_union.mp hl with a|b
     · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp a
       exact (Finset.mem_insert.mp (ps mem)).resolve_left ne
     · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp b
       exact (Finset.mem_insert.mp (ns mem)).resolve_left ne
   · refine ⟨[],d,by decide,n,hn,?_⟩
     intro l hl
     rcases Finset.mem_insert.mp (ns hl) with e|h
     · exact False.elim (neg (e ▸ hl))
     · exact h
 · refine ⟨[],d,by decide,p,hp,?_⟩
   intro l hl
   rcases Finset.mem_insert.mp (ps hl) with e|h
   · exact False.elim (pos (e ▸ hl))
   · exact h

theorem chain {F : Set (C (V:=V))} {pre : List C} {z g : C} {a b : Nat}
    (s : Reach F pre a z)
    (f : ∀ (t : List C),IsDerivation F (t++pre) → ∀ c∈t++pre,c⊆z → Reach F (t++pre) b g) :
    Reach F pre (a+b) g := by
 obtain ⟨t,d,tc,c,cm,cs⟩ := s
 obtain ⟨u,du,uc,k,km,ks⟩ := f t d c cm cs
 exact ⟨u++t,by simpa only [List.append_assoc] using du,by simp only [List.length_append]; omega,
   k,by simpa only [List.append_assoc] using km,ks⟩

-- One folded pivot represents x ∨ (a ∧ b). Residual literals may survive in z.
theorem three {F : Set (C (V:=V))} {pre : List C} (d : IsDerivation F pre)
    (x a b : V) (z p₁ p₂ n₁ n₂ : C) (p₁m : p₁∈pre) (p₂m : p₂∈pre)
    (n₁m : n₁∈pre) (n₂m : n₂∈pre)
    (h₁ : p₁ ⊆ insert (a,true) (insert (x,true) z))
    (h₂ : p₂ ⊆ insert (b,true) (insert (x,true) z))
    (h₃ : n₁ ⊆ insert (x,false) z)
    (h₄ : n₂ ⊆ insert (a,false) (insert (b,false) z)) : Reach F pre 3 z := by
 have first : Reach F pre 1 (insert (b,false) (insert (x,true) z)) := by
   apply one d p₁m n₂m (v:=a)
   · intro l hl
     have h := h₁ hl
     simp only [Finset.mem_insert] at h ⊢
     tauto
   · intro l hl
     have h := h₄ hl
     simp only [Finset.mem_insert] at h ⊢
     tauto
 apply chain (a:=1) (b:=2) first
 intro t dt c cm cs
 have second := one dt (List.mem_append.mpr (Or.inr p₂m)) cm h₂ cs
 apply chain (a:=1) (b:=1) second
 intro u du w wm ws
 exact one du wm (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr n₁m)))) ws h₃
end PEqualNP.Outside.L_pcx_166_Fold
