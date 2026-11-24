import Mathlib
import PEqualNP.Outside.L_meta_5242
import PEqualNP.Outside.L_meta_4115

namespace Entry1768

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_5242
open PEqualNP.MetaComplexity.NestedCover

/-- The two test assignments differ positively at just v. Follow that difference
through OR gates and retain the first AND port exposing v. -/
theorem separate {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : PEqualNP.TopForm.TopForm G C)
    (x y : Fin n → Bool) (v : Fin n)
    (unique : ∀ w, x w = true → y w ≠ true → w = v) :
    ∀ g ∈ junk G C, gateVal n C g x = true → gateVal n C g y ≠ true →
    ∃ h ∈ junk G C, (h = g ∨ InCone n C h g) ∧ gateVal n C h x = true ∧
      ∃ d : Fin 2, v ∈ side C h d ∧ ∀ w ∈ side C h d, y w ≠ true := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hj vx vy
    obtain ⟨hg, hand, _⟩ := Structural.junk_spec hj
    have off : ∃ d : Fin 2, Base.val C (List.ofFn y) (opnd C g d) ≠ true := by
      by_contra hn
      apply vy
      apply (Structural.and_true_iff hAO hg hand y).mpr
      intro d
      by_contra hd
      exact hn ⟨d,hd⟩
    obtain ⟨d, hd⟩ := off
    have on := (Structural.and_true_iff hAO hg hand x).mp vx d
    have rawOff (w : Fin n) (hw : w ∈ side C g d) : y w ≠ true :=
      fun hy => hd (Final.raw_up y w hw hy)
    rcases (Structural.and_operand_iff hAO hT hg hand (Structural.opnd_mem hAO hg d) x).mp on with
      ⟨w, hw, hx⟩ | ⟨k, hk, kc, kr, kv⟩
    · have ew := unique w hx (rawOff w hw)
      exact ⟨g,hj,Or.inl rfl,vx,d,ew ▸ hw,rawOff⟩
    · have ky : gateVal n C k y ≠ true := fun hy => hd (Final.reach_up y kr hy)
      obtain ⟨h,hh,below,hx,hport⟩ := ih k (Structural.inCone_lt kc) hk kv ky
      have hc : InCone n C h g := by
        rcases below with eq | hc
        · simpa only [eq] using kc
        · exact Structural.inCone_trans hc kc
      exact ⟨h,hh,Or.inr hc,hx,hport⟩

theorem entry :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (w : Fin n) (p : G.Walk w w), p.IsCycle → 5 ≤ p.length) →
      IsAO2 n C → PEqualNP.TopForm.TopForm G C → ∀ (u v : Fin n), G.Adj u v →
      ∀ a ∈ tops G C, ∀ (b : Fin 2) (g : ℕ), g ∈ junk G C →
      u ∈ side C a b → OrReaches n C (opnd C a (1-b)) g →
      gateVal n C g (pairInput u v) = true →
      ∃ h ∈ junk G C, (h = g ∨ InCone n C h g) ∧
        gateVal n C h (pairInput u v) = true ∧
        ∃ d : Fin 2, v ∈ side C h d ∧ ∀ w ∈ side C h d, ¬ G.Adj v w := by
  intro n G inst C hG hAO hT u v huv a ha b g hj hu hr hv
  let S := Finset.univ.filter (fun w => G.Adj v w)
  let y := GraphSupport.input S
  have hy (w : Fin n) : y w = true ↔ G.Adj v w := by
    simp only [y, GraphSupport.input, decide_eq_true_eq, S, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have independent : graphFun G ∅ y ≠ true := by
    intro he
    obtain ⟨p,q,hpq,hp,hq⟩ := (GraphSupport.graph_true G S).mp he
    have vp : G.Adj v p := (Finset.mem_filter.mp hp).2
    have vq : G.Adj v q := (Finset.mem_filter.mp hq).2
    exact PEqualNP.Outside.L_meta_4115.Sole.triangle hG vp hpq vq.symm
  have reject : gateVal n C g y ≠ true := by
    intro gv
    apply independent
    apply Final.top_force hAO ha y
    intro i
    rcases Final.two_cases b i with h | h
    · subst i
      exact Final.raw_up y u hu ((hy u).mpr huv.symm)
    · subst i
      exact Final.reach_up y hr gv
  have unique : ∀ w, pairInput u v w = true → y w ≠ true → w = v := by
    intro w hw hn
    rcases (Base.pairInput_true u v w).mp hw with wu | wv
    · exact (hn ((hy w).mpr (by simpa only [wu] using huv.symm))).elim
    · exact wv
  obtain ⟨h,hh,hc,hon,d,hd,hoff⟩ := separate hAO hT (pairInput u v) y v unique g hj hv reject
  exact ⟨h,hh,hc,hon,d,hd,fun w hw hadj => hoff w hw ((hy w).mpr hadj)⟩

end Entry1768
