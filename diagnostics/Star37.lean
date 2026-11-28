import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_178.Star

open PEqualNP.ProofComplexity

abbrev VV : Type := Fin 5 × Fin 4

def par (a : VV → Bool) (f : Finset VV) : Prop := Odd (f.filter (fun v => a v = true)).card

theorem card_sd (s t : Finset VV) : (symmDiff s t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : s ∪ t = (symmDiff s t) ∪ (s ∩ t) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff s t) (s ∩ t) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1; omega

theorem par_sd (a : VV → Bool) (s t : Finset VV) : par a (symmDiff s t) ↔ ¬ (par a s ↔ par a t) := by
  unfold par
  have hf : (symmDiff s t).filter (fun v => a v = true) =
      symmDiff (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  rw [hf]
  have := card_sd (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true))
  simp only [Nat.odd_iff]; omega

def sdl : List (LinEq VV) → Finset VV
  | [] => ∅
  | e :: l => symmDiff e.1 (sdl l)

def xbl : List (LinEq VV) → Bool
  | [] => false
  | e :: l => xor (!e.2) (xbl l)

theorem par_sdl (a : VV → Bool) (L : List (LinEq VV)) (h : ∀ e ∈ L, ¬ LinEqSat a e) :
    (par a (sdl L) ↔ xbl L = true) := by
  induction L with
  | nil => simp [par, sdl, xbl]
  | cons e l ih =>
    obtain ⟨f, b⟩ := e
    have he := h (f, b) (List.mem_cons_self ..)
    have hl := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he2 : par a f ↔ ¬ (b = true) := by
      unfold LinEqSat at he; unfold par; simp only at he; tauto
    simp only [sdl, xbl]
    rw [par_sd, hl, he2]
    cases b <;> cases xbl l <;> simp

def okB (q : LinEq VV) (D : LinClause VV) (L : List (LinEq VV)) : Bool :=
  L.all (fun e => decide (e ∈ D)) && decide (q.1 = sdl L) && (q.2 == !(xbl L))

theorem weak_cert (C D : LinClause VV) (certs : List (List (LinEq VV)))
    (h : ∀ q ∈ C, ∃ L ∈ certs, okB q D L = true) :
    ∀ a : VV → Bool, LinClauseSat a C → LinClauseSat a D := by
  intro a ⟨q, hq, hs⟩
  obtain ⟨L, _, hok⟩ := h q hq
  simp only [okB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hD, h1⟩, h2⟩ := hok
  by_contra hn
  have hn' : ∀ e ∈ L, ¬ LinEqSat a e := fun e he hse => hn ⟨e, hD e he, hse⟩
  have hp := par_sdl a L hn'
  unfold LinEqSat at hs
  rw [h1] at hs
  change par a (sdl L) ↔ q.2 = true at hs
  rw [hp, h2] at hs
  cases xbl L <;> simp at hs




set_option maxRecDepth 10000
abbrev F := (linOfClause '' PHP 5 4 : Set (LinClause VV))
def l0 := ({(({(0,0)} : Finset VV),true), (({(0,1)} : Finset VV),true), (({(0,2)} : Finset VV),true), (({(0,3)} : Finset VV),true)} : LinClause VV)
def p0 : List (LinClause VV) := l0 :: []
theorem d0 : IsLinDerivation F p0 := by
  apply IsLinDerivation.ax IsLinDerivation.nil
  exact ⟨Finset.univ.image (fun h : Fin 4 => (((0 : Fin 5),h),true)), Or.inl ⟨0,rfl⟩, by decide +kernel⟩
def l1 := ({(({(0,0)} : Finset VV),false), (({(1,0)} : Finset VV),false)} : LinClause VV)
def p1 : List (LinClause VV) := l1 :: p0
theorem d1 : IsLinDerivation F p1 := by
  apply IsLinDerivation.ax d0
  exact ⟨{(((0 : Fin 5),(0 : Fin 4)),false), (((1 : Fin 5),(0 : Fin 4)),false)}, Or.inr ⟨0,1,0,by decide,rfl⟩, by decide +kernel⟩
def l2 := ({(({(0,0)} : Finset VV),false), (({(2,0)} : Finset VV),false)} : LinClause VV)
def p2 : List (LinClause VV) := l2 :: p1
theorem d2 : IsLinDerivation F p2 := by
  apply IsLinDerivation.ax d1
  exact ⟨{(((0 : Fin 5),(0 : Fin 4)),false), (((2 : Fin 5),(0 : Fin 4)),false)}, Or.inr ⟨0,2,0,by decide,rfl⟩, by decide +kernel⟩
def l3 := ({(({(0,0)} : Finset VV),false), (({(3,0)} : Finset VV),false)} : LinClause VV)
def p3 : List (LinClause VV) := l3 :: p2
theorem d3 : IsLinDerivation F p3 := by
  apply IsLinDerivation.ax d2
  exact ⟨{(((0 : Fin 5),(0 : Fin 4)),false), (((3 : Fin 5),(0 : Fin 4)),false)}, Or.inr ⟨0,3,0,by decide,rfl⟩, by decide +kernel⟩
def l4 := ({(({(0,0)} : Finset VV),false), (({(4,0)} : Finset VV),false)} : LinClause VV)
def p4 : List (LinClause VV) := l4 :: p3
theorem d4 : IsLinDerivation F p4 := by
  apply IsLinDerivation.ax d3
  exact ⟨{(((0 : Fin 5),(0 : Fin 4)),false), (((4 : Fin 5),(0 : Fin 4)),false)}, Or.inr ⟨0,4,0,by decide,rfl⟩, by decide +kernel⟩
def l5 := ({(({(0,1)} : Finset VV),false), (({(1,1)} : Finset VV),false)} : LinClause VV)
def p5 : List (LinClause VV) := l5 :: p4
theorem d5 : IsLinDerivation F p5 := by
  apply IsLinDerivation.ax d4
  exact ⟨{(((0 : Fin 5),(1 : Fin 4)),false), (((1 : Fin 5),(1 : Fin 4)),false)}, Or.inr ⟨0,1,1,by decide,rfl⟩, by decide +kernel⟩
def l6 := ({(({(0,1)} : Finset VV),false), (({(2,1)} : Finset VV),false)} : LinClause VV)
def p6 : List (LinClause VV) := l6 :: p5
theorem d6 : IsLinDerivation F p6 := by
  apply IsLinDerivation.ax d5
  exact ⟨{(((0 : Fin 5),(1 : Fin 4)),false), (((2 : Fin 5),(1 : Fin 4)),false)}, Or.inr ⟨0,2,1,by decide,rfl⟩, by decide +kernel⟩
def l7 := ({(({(0,1)} : Finset VV),false), (({(3,1)} : Finset VV),false)} : LinClause VV)
def p7 : List (LinClause VV) := l7 :: p6
theorem d7 : IsLinDerivation F p7 := by
  apply IsLinDerivation.ax d6
  exact ⟨{(((0 : Fin 5),(1 : Fin 4)),false), (((3 : Fin 5),(1 : Fin 4)),false)}, Or.inr ⟨0,3,1,by decide,rfl⟩, by decide +kernel⟩
def l8 := ({(({(0,1)} : Finset VV),false), (({(4,1)} : Finset VV),false)} : LinClause VV)
def p8 : List (LinClause VV) := l8 :: p7
theorem d8 : IsLinDerivation F p8 := by
  apply IsLinDerivation.ax d7
  exact ⟨{(((0 : Fin 5),(1 : Fin 4)),false), (((4 : Fin 5),(1 : Fin 4)),false)}, Or.inr ⟨0,4,1,by decide,rfl⟩, by decide +kernel⟩
def l9 := ({(({(0,2)} : Finset VV),false), (({(1,2)} : Finset VV),false)} : LinClause VV)
def p9 : List (LinClause VV) := l9 :: p8
theorem d9 : IsLinDerivation F p9 := by
  apply IsLinDerivation.ax d8
  exact ⟨{(((0 : Fin 5),(2 : Fin 4)),false), (((1 : Fin 5),(2 : Fin 4)),false)}, Or.inr ⟨0,1,2,by decide,rfl⟩, by decide +kernel⟩
def l10 := ({(({(0,2)} : Finset VV),false), (({(2,2)} : Finset VV),false)} : LinClause VV)
def p10 : List (LinClause VV) := l10 :: p9
theorem d10 : IsLinDerivation F p10 := by
  apply IsLinDerivation.ax d9
  exact ⟨{(((0 : Fin 5),(2 : Fin 4)),false), (((2 : Fin 5),(2 : Fin 4)),false)}, Or.inr ⟨0,2,2,by decide,rfl⟩, by decide +kernel⟩
def l11 := ({(({(0,2)} : Finset VV),false), (({(3,2)} : Finset VV),false)} : LinClause VV)
def p11 : List (LinClause VV) := l11 :: p10
theorem d11 : IsLinDerivation F p11 := by
  apply IsLinDerivation.ax d10
  exact ⟨{(((0 : Fin 5),(2 : Fin 4)),false), (((3 : Fin 5),(2 : Fin 4)),false)}, Or.inr ⟨0,3,2,by decide,rfl⟩, by decide +kernel⟩
def l12 := ({(({(0,2)} : Finset VV),false), (({(4,2)} : Finset VV),false)} : LinClause VV)
def p12 : List (LinClause VV) := l12 :: p11
theorem d12 : IsLinDerivation F p12 := by
  apply IsLinDerivation.ax d11
  exact ⟨{(((0 : Fin 5),(2 : Fin 4)),false), (((4 : Fin 5),(2 : Fin 4)),false)}, Or.inr ⟨0,4,2,by decide,rfl⟩, by decide +kernel⟩
def l13 := ({(({(0,3)} : Finset VV),false), (({(1,3)} : Finset VV),false)} : LinClause VV)
def p13 : List (LinClause VV) := l13 :: p12
theorem d13 : IsLinDerivation F p13 := by
  apply IsLinDerivation.ax d12
  exact ⟨{(((0 : Fin 5),(3 : Fin 4)),false), (((1 : Fin 5),(3 : Fin 4)),false)}, Or.inr ⟨0,1,3,by decide,rfl⟩, by decide +kernel⟩
def l14 := ({(({(0,3)} : Finset VV),false), (({(2,3)} : Finset VV),false)} : LinClause VV)
def p14 : List (LinClause VV) := l14 :: p13
theorem d14 : IsLinDerivation F p14 := by
  apply IsLinDerivation.ax d13
  exact ⟨{(((0 : Fin 5),(3 : Fin 4)),false), (((2 : Fin 5),(3 : Fin 4)),false)}, Or.inr ⟨0,2,3,by decide,rfl⟩, by decide +kernel⟩
def l15 := ({(({(0,3)} : Finset VV),false), (({(3,3)} : Finset VV),false)} : LinClause VV)
def p15 : List (LinClause VV) := l15 :: p14
theorem d15 : IsLinDerivation F p15 := by
  apply IsLinDerivation.ax d14
  exact ⟨{(((0 : Fin 5),(3 : Fin 4)),false), (((3 : Fin 5),(3 : Fin 4)),false)}, Or.inr ⟨0,3,3,by decide,rfl⟩, by decide +kernel⟩
def l16 := ({(({(0,3)} : Finset VV),false), (({(4,3)} : Finset VV),false)} : LinClause VV)
def p16 : List (LinClause VV) := l16 :: p15
theorem d16 : IsLinDerivation F p16 := by
  apply IsLinDerivation.ax d15
  exact ⟨{(((0 : Fin 5),(3 : Fin 4)),false), (((4 : Fin 5),(3 : Fin 4)),false)}, Or.inr ⟨0,4,3,by decide,rfl⟩, by decide +kernel⟩
def l17 := ({(({(0,0)} : Finset VV),false), (({(2,0)} : Finset VV),true), (({(3,0)} : Finset VV),true), (({(4,0)} : Finset VV),true), (({(1,0), (2,0), (3,0), (4,0)} : Finset VV),false)} : LinClause VV)
def p17 : List (LinClause VV) := l17 :: p16
theorem d17 : IsLinDerivation F p17 := by
  apply IsLinDerivation.weak (C := l1) d16 (by decide +kernel)
  apply weak_cert l1 l17 [[(({(0,0)} : Finset VV),false)],[(({(2,0)} : Finset VV),true),(({(3,0)} : Finset VV),true),(({(4,0)} : Finset VV),true),(({(1,0), (2,0), (3,0), (4,0)} : Finset VV),false)]]
  intro q hq
  simp only [l1,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact ⟨[(({(0,0)} : Finset VV),false)],by decide +kernel,by decide +kernel⟩
  · exact ⟨[(({(2,0)} : Finset VV),true),(({(3,0)} : Finset VV),true),(({(4,0)} : Finset VV),true),(({(1,0), (2,0), (3,0), (4,0)} : Finset VV),false)],by decide +kernel,by decide +kernel⟩
def l18 := ({(({(0,0)} : Finset VV),false), (({(3,0)} : Finset VV),true), (({(4,0)} : Finset VV),true), (({(1,0), (2,0), (3,0), (4,0)} : Finset VV),false)} : LinClause VV)
def p18 : List (LinClause VV) := l18 :: p17
theorem d18 : IsLinDerivation F p18 := by
  exact IsLinDerivation.res (C := l2) (D := l17) d17 (by decide +kernel) (by decide +kernel) ⟨({(2,0)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l19 := ({(({(0,0)} : Finset VV),false), (({(4,0)} : Finset VV),true), (({(1,0), (2,0), (3,0), (4,0)} : Finset VV),false)} : LinClause VV)
def p19 : List (LinClause VV) := l19 :: p18
theorem d19 : IsLinDerivation F p19 := by
  exact IsLinDerivation.res (C := l3) (D := l18) d18 (by decide +kernel) (by decide +kernel) ⟨({(3,0)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l20 := ({(({(0,0)} : Finset VV),false), (({(1,0), (2,0), (3,0), (4,0)} : Finset VV),false)} : LinClause VV)
def p20 : List (LinClause VV) := l20 :: p19
theorem d20 : IsLinDerivation F p20 := by
  exact IsLinDerivation.res (C := l4) (D := l19) d19 (by decide +kernel) (by decide +kernel) ⟨({(4,0)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l21 := ({(({(0,1)} : Finset VV),true), (({(0,2)} : Finset VV),true), (({(0,3)} : Finset VV),true), (({(1,0), (2,0), (3,0), (4,0)} : Finset VV),false)} : LinClause VV)
def p21 : List (LinClause VV) := l21 :: p20
theorem d21 : IsLinDerivation F p21 := by
  exact IsLinDerivation.res (C := l20) (D := l0) d20 (by decide +kernel) (by decide +kernel) ⟨({(0,0)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l22 := ({(({(0,1)} : Finset VV),false), (({(2,1)} : Finset VV),true), (({(3,1)} : Finset VV),true), (({(4,1)} : Finset VV),true), (({(1,1), (2,1), (3,1), (4,1)} : Finset VV),false)} : LinClause VV)
def p22 : List (LinClause VV) := l22 :: p21
theorem d22 : IsLinDerivation F p22 := by
  apply IsLinDerivation.weak (C := l5) d21 (by decide +kernel)
  apply weak_cert l5 l22 [[(({(0,1)} : Finset VV),false)],[(({(2,1)} : Finset VV),true),(({(3,1)} : Finset VV),true),(({(4,1)} : Finset VV),true),(({(1,1), (2,1), (3,1), (4,1)} : Finset VV),false)]]
  intro q hq
  simp only [l5,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact ⟨[(({(0,1)} : Finset VV),false)],by decide +kernel,by decide +kernel⟩
  · exact ⟨[(({(2,1)} : Finset VV),true),(({(3,1)} : Finset VV),true),(({(4,1)} : Finset VV),true),(({(1,1), (2,1), (3,1), (4,1)} : Finset VV),false)],by decide +kernel,by decide +kernel⟩
def l23 := ({(({(0,1)} : Finset VV),false), (({(3,1)} : Finset VV),true), (({(4,1)} : Finset VV),true), (({(1,1), (2,1), (3,1), (4,1)} : Finset VV),false)} : LinClause VV)
def p23 : List (LinClause VV) := l23 :: p22
theorem d23 : IsLinDerivation F p23 := by
  exact IsLinDerivation.res (C := l6) (D := l22) d22 (by decide +kernel) (by decide +kernel) ⟨({(2,1)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l24 := ({(({(0,1)} : Finset VV),false), (({(4,1)} : Finset VV),true), (({(1,1), (2,1), (3,1), (4,1)} : Finset VV),false)} : LinClause VV)
def p24 : List (LinClause VV) := l24 :: p23
theorem d24 : IsLinDerivation F p24 := by
  exact IsLinDerivation.res (C := l7) (D := l23) d23 (by decide +kernel) (by decide +kernel) ⟨({(3,1)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l25 := ({(({(0,1)} : Finset VV),false), (({(1,1), (2,1), (3,1), (4,1)} : Finset VV),false)} : LinClause VV)
def p25 : List (LinClause VV) := l25 :: p24
theorem d25 : IsLinDerivation F p25 := by
  exact IsLinDerivation.res (C := l8) (D := l24) d24 (by decide +kernel) (by decide +kernel) ⟨({(4,1)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l26 := ({(({(0,2)} : Finset VV),true), (({(0,3)} : Finset VV),true), (({(1,0), (2,0), (3,0), (4,0)} : Finset VV),false), (({(1,1), (2,1), (3,1), (4,1)} : Finset VV),false)} : LinClause VV)
def p26 : List (LinClause VV) := l26 :: p25
theorem d26 : IsLinDerivation F p26 := by
  exact IsLinDerivation.res (C := l25) (D := l21) d25 (by decide +kernel) (by decide +kernel) ⟨({(0,1)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l27 := ({(({(0,2)} : Finset VV),false), (({(2,2)} : Finset VV),true), (({(3,2)} : Finset VV),true), (({(4,2)} : Finset VV),true), (({(1,2), (2,2), (3,2), (4,2)} : Finset VV),false)} : LinClause VV)
def p27 : List (LinClause VV) := l27 :: p26
theorem d27 : IsLinDerivation F p27 := by
  apply IsLinDerivation.weak (C := l9) d26 (by decide +kernel)
  apply weak_cert l9 l27 [[(({(0,2)} : Finset VV),false)],[(({(2,2)} : Finset VV),true),(({(3,2)} : Finset VV),true),(({(4,2)} : Finset VV),true),(({(1,2), (2,2), (3,2), (4,2)} : Finset VV),false)]]
  intro q hq
  simp only [l9,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact ⟨[(({(0,2)} : Finset VV),false)],by decide +kernel,by decide +kernel⟩
  · exact ⟨[(({(2,2)} : Finset VV),true),(({(3,2)} : Finset VV),true),(({(4,2)} : Finset VV),true),(({(1,2), (2,2), (3,2), (4,2)} : Finset VV),false)],by decide +kernel,by decide +kernel⟩
def l28 := ({(({(0,2)} : Finset VV),false), (({(3,2)} : Finset VV),true), (({(4,2)} : Finset VV),true), (({(1,2), (2,2), (3,2), (4,2)} : Finset VV),false)} : LinClause VV)
def p28 : List (LinClause VV) := l28 :: p27
theorem d28 : IsLinDerivation F p28 := by
  exact IsLinDerivation.res (C := l10) (D := l27) d27 (by decide +kernel) (by decide +kernel) ⟨({(2,2)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l29 := ({(({(0,2)} : Finset VV),false), (({(4,2)} : Finset VV),true), (({(1,2), (2,2), (3,2), (4,2)} : Finset VV),false)} : LinClause VV)
def p29 : List (LinClause VV) := l29 :: p28
theorem d29 : IsLinDerivation F p29 := by
  exact IsLinDerivation.res (C := l11) (D := l28) d28 (by decide +kernel) (by decide +kernel) ⟨({(3,2)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l30 := ({(({(0,2)} : Finset VV),false), (({(1,2), (2,2), (3,2), (4,2)} : Finset VV),false)} : LinClause VV)
def p30 : List (LinClause VV) := l30 :: p29
theorem d30 : IsLinDerivation F p30 := by
  exact IsLinDerivation.res (C := l12) (D := l29) d29 (by decide +kernel) (by decide +kernel) ⟨({(4,2)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l31 := ({(({(0,3)} : Finset VV),true), (({(1,0), (2,0), (3,0), (4,0)} : Finset VV),false), (({(1,1), (2,1), (3,1), (4,1)} : Finset VV),false), (({(1,2), (2,2), (3,2), (4,2)} : Finset VV),false)} : LinClause VV)
def p31 : List (LinClause VV) := l31 :: p30
theorem d31 : IsLinDerivation F p31 := by
  exact IsLinDerivation.res (C := l30) (D := l26) d30 (by decide +kernel) (by decide +kernel) ⟨({(0,2)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l32 := ({(({(0,3)} : Finset VV),false), (({(2,3)} : Finset VV),true), (({(3,3)} : Finset VV),true), (({(4,3)} : Finset VV),true), (({(1,3), (2,3), (3,3), (4,3)} : Finset VV),false)} : LinClause VV)
def p32 : List (LinClause VV) := l32 :: p31
theorem d32 : IsLinDerivation F p32 := by
  apply IsLinDerivation.weak (C := l13) d31 (by decide +kernel)
  apply weak_cert l13 l32 [[(({(0,3)} : Finset VV),false)],[(({(2,3)} : Finset VV),true),(({(3,3)} : Finset VV),true),(({(4,3)} : Finset VV),true),(({(1,3), (2,3), (3,3), (4,3)} : Finset VV),false)]]
  intro q hq
  simp only [l13,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact ⟨[(({(0,3)} : Finset VV),false)],by decide +kernel,by decide +kernel⟩
  · exact ⟨[(({(2,3)} : Finset VV),true),(({(3,3)} : Finset VV),true),(({(4,3)} : Finset VV),true),(({(1,3), (2,3), (3,3), (4,3)} : Finset VV),false)],by decide +kernel,by decide +kernel⟩
def l33 := ({(({(0,3)} : Finset VV),false), (({(3,3)} : Finset VV),true), (({(4,3)} : Finset VV),true), (({(1,3), (2,3), (3,3), (4,3)} : Finset VV),false)} : LinClause VV)
def p33 : List (LinClause VV) := l33 :: p32
theorem d33 : IsLinDerivation F p33 := by
  exact IsLinDerivation.res (C := l14) (D := l32) d32 (by decide +kernel) (by decide +kernel) ⟨({(2,3)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l34 := ({(({(0,3)} : Finset VV),false), (({(4,3)} : Finset VV),true), (({(1,3), (2,3), (3,3), (4,3)} : Finset VV),false)} : LinClause VV)
def p34 : List (LinClause VV) := l34 :: p33
theorem d34 : IsLinDerivation F p34 := by
  exact IsLinDerivation.res (C := l15) (D := l33) d33 (by decide +kernel) (by decide +kernel) ⟨({(3,3)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l35 := ({(({(0,3)} : Finset VV),false), (({(1,3), (2,3), (3,3), (4,3)} : Finset VV),false)} : LinClause VV)
def p35 : List (LinClause VV) := l35 :: p34
theorem d35 : IsLinDerivation F p35 := by
  exact IsLinDerivation.res (C := l16) (D := l34) d34 (by decide +kernel) (by decide +kernel) ⟨({(4,3)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def l36 := ({(({(1,0), (2,0), (3,0), (4,0)} : Finset VV),false), (({(1,1), (2,1), (3,1), (4,1)} : Finset VV),false), (({(1,2), (2,2), (3,2), (4,2)} : Finset VV),false), (({(1,3), (2,3), (3,3), (4,3)} : Finset VV),false)} : LinClause VV)
def p36 : List (LinClause VV) := l36 :: p35
theorem d36 : IsLinDerivation F p36 := by
  exact IsLinDerivation.res (C := l35) (D := l31) d35 (by decide +kernel) (by decide +kernel) ⟨({(0,3)} : Finset VV),by decide +kernel,by decide +kernel,by decide +kernel⟩
def others (h : Fin 4) : Finset VV := Finset.univ.filter fun q => q.1 ≠ 0 ∧ q.2 = h
theorem star37 : ∃ pi : List (LinClause VV), IsLinDerivation F pi ∧ pi.length = 37 ∧ (Finset.univ.image fun h : Fin 4 => (others h,false)) ∈ pi := by
  exact ⟨p36,d36,by decide +kernel,by decide +kernel⟩
end PEqualNP.Outside.L_pcx_178.Star
