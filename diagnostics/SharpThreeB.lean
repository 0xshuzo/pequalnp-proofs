import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_121_pair
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]
def Heard (a b : V → Bool) (C : LinClause V) := LinClauseSat a C ∨ LinClauseSat b C
def TwoHits (a b : V → Bool) (C : LinClause V) :=
  ∀ q : LinEq V, ∃ e∈C, e≠q ∧ (LinEqSat a e ∨ LinEqSat b e)

theorem fromHit {a b : V → Bool} {C : LinClause V} {e : LinEq V} (mem : e∈C)
    (h : LinEqSat a e ∨ LinEqSat b e) : Heard a b C := by
  rcases h with av|bv
  · exact Or.inl ⟨e,mem,av⟩
  · exact Or.inr ⟨e,mem,bv⟩

theorem twoHeard {a b : V → Bool} {C : LinClause V} (h : TwoHits a b C) : Heard a b C := by
  obtain ⟨e,m,_,v⟩ := h (∅,false)
  exact fromHit m v

theorem resHeard {a b : V → Bool} {C D R : LinClause V} (res : IsLinResolvent C D R)
    (h : TwoHits a b C ∨ TwoHits a b D) : Heard a b R := by
  obtain ⟨f,_,_,rfl⟩ := res
  rcases h with l|r
  · obtain ⟨e,m,ne,h⟩ := l (f,false)
    exact fromHit (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,m⟩)) h
  · obtain ⟨e,m,ne,h⟩ := r (f,true)
    exact fromHit (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,m⟩)) h

theorem weakHeard {a b : V → Bool} {C D : LinClause V}
    (h : ∀ x, LinClauseSat x C → LinClauseSat x D)
    (v : Heard a b C) : Heard a b D := v.imp (h a) (h b)

theorem selfHeard {a b : V → Bool} {C R : LinClause V} (res : IsLinResolvent C C R)
    (v : Heard a b C) : Heard a b R := by
  obtain ⟨f,_,_,rfl⟩ := res
  have eq : C.erase (f,false) ∪ C.erase (f,true) = C := by
    ext x
    simp only [Finset.mem_union,Finset.mem_erase]
    have ne : (f,false)≠(f,true) := by simp
    by_cases h : x=(f,false)
    · subst x; simp
    · tauto
  rwa [eq]

inductive Reason (F : Set (LinClause V)) (π : List (LinClause V)) (R : LinClause V) : Prop where
  | ax (mem : R∈F)
  | res (C D : LinClause V) (cm : C∈π) (dm : D∈π) (step : IsLinResolvent C D R)
  | weak (C : LinClause V) (cm : C∈π) (imp : ∀x, LinClauseSat x C → LinClauseSat x R)

theorem peel {F : Set (LinClause V)} {π : List (LinClause V)} {R : LinClause V}
    (d : IsLinDerivation F (R::π)) : IsLinDerivation F π ∧ Reason F π R := by
  cases d with
  | ax h m => exact ⟨h,.ax m⟩
  | res h c d j => exact ⟨h,.res _ _ c d j⟩
  | weak h c w => exact ⟨h,.weak _ c w⟩

theorem first {F : Set (LinClause V)} {π : List (LinClause V)} {R : LinClause V}
    {a b : V → Bool} (all : ∀c∈F, TwoHits a b c) (raw : ∀ c∈π, c∈F)
    (step : Reason F π R) : Heard a b R := by
  cases step with
  | ax h => exact twoHeard (all _ h)
  | res C D cm dm r => exact resHeard r (Or.inl (all _ (raw _ cm)))
  | weak C cm imp => exact weakHeard imp (twoHeard (all _ (raw _ cm)))

theorem second {F : Set (LinClause V)} {π : List (LinClause V)} {S R : LinClause V}
    {a b : V → Bool} (all : ∀c∈F, TwoHits a b c) (raw : ∀ c∈π, c∈F)
    (earlier : Heard a b S) (step : Reason F (S::π) R) : Heard a b R := by
  cases step with
  | ax h => exact twoHeard (all _ h)
  | weak C cm imp =>
    rcases List.mem_cons.mp cm with rfl|before
    · exact weakHeard imp earlier
    · exact weakHeard imp (twoHeard (all _ (raw _ before)))
  | res C D cm dm r =>
    rcases List.mem_cons.mp cm with rfl|before
    · rcases List.mem_cons.mp dm with rfl|before
      · exact selfHeard r earlier
      · exact resHeard r (Or.inr (all _ (raw _ before)))
    · exact resHeard r (Or.inl (all _ (raw _ before)))

theorem physicalThree {F : Set (LinClause V)} {π xs : List (LinClause V)} {R : LinClause V}
    {a b : V → Bool} (all : ∀c∈F, TwoHits a b c) (raw : ∀ c∈π, c∈F)
    (d : IsLinDerivation F (xs++π)) (mem : R∈xs++π) (quiet : ¬Heard a b R) :
    3≤xs.length := by
  cases xs with
  | nil => exact False.elim (quiet (twoHeard (all _ (raw _ mem))))
  | cons x tail =>
    obtain ⟨dt,s⟩ := peel d
    cases tail with
    | nil =>
      rcases List.mem_cons.mp mem with rfl|before
      · exact False.elim (quiet (first all raw s))
      · exact False.elim (quiet (twoHeard (all _ (raw _ before))))
    | cons y rest =>
      cases rest with
      | nil =>
        obtain ⟨_,prior⟩ := peel dt
        have yheard := first all raw prior
        rcases List.mem_cons.mp mem with rfl|other
        · exact False.elim (quiet (second all raw yheard s))
        rcases List.mem_cons.mp other with rfl|before
        · exact False.elim (quiet yheard)
        · exact False.elim (quiet (twoHeard (all _ (raw _ before))))
      | cons z zs => simp

abbrev VV : Type := Fin 4 × Fin 3

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




def singletonEq (v : VV) (b : Bool) : LinEq VV := ({v},b)
def invert (a : VV → Bool) (v : VV) := !(a v)

theorem singletonHeard (a : VV → Bool) (v : VV) (s : Bool) :
    LinEqSat a (singletonEq v s) ∨ LinEqSat (invert a) (singletonEq v s) := by
  cases ha : a v <;> cases s <;> simp [LinEqSat,singletonEq,invert,Finset.filter_singleton,ha]

theorem pairGives (C : LinClause VV) (a : VV → Bool) (u v : VV) (s : Bool)
    (hu : singletonEq u s∈C) (hv : singletonEq v s∈C) (ne : u≠v) :
    TwoHits a (invert a) C := by
  intro q
  by_cases unequal : singletonEq u s=q
  · have other : singletonEq v s≠q := by
      intro eq
      have pair : singletonEq u s=singletonEq v s := unequal.trans eq.symm
      have eqset := congrArg Prod.fst pair
      have same : u=v := by simpa [singletonEq] using eqset
      exact ne same
    exact ⟨_,hv,other,singletonHeard a v s⟩
  · exact ⟨_,hu,unequal,singletonHeard a u s⟩

abbrev Formula := linOfClause '' PHP 4 3

theorem boardTwo (a : VV → Bool) : ∀ c∈Formula, TwoHits a (invert a) c := by
  rintro c ⟨C,h,rfl⟩
  rcases h with ⟨i,rfl⟩|⟨i,k,j,ne,rfl⟩
  · apply pairGives _ _ (i,0) (i,1) true
    · exact Finset.mem_image.mpr ⟨((i,0),true),Finset.mem_image.mpr
        ⟨0,Finset.mem_univ _,rfl⟩,rfl⟩
    · exact Finset.mem_image.mpr ⟨((i,1),true),Finset.mem_image.mpr
        ⟨1,Finset.mem_univ _,rfl⟩,rfl⟩
    · simp
  · apply pairGives _ _ (i,j) (k,j) false
    · exact Finset.mem_image.mpr ⟨((i,j),false),by simp,rfl⟩
    · exact Finset.mem_image.mpr ⟨((k,j),false),by simp,rfl⟩
    · exact fun e=>ne (congrArg Prod.fst e)

theorem boardDepth {π xs : List (LinClause VV)} {R : LinClause VV} (a : VV → Bool)
    (raw : ∀ c∈π, c∈Formula) (d : IsLinDerivation Formula (xs++π)) (m : R∈xs++π)
    (quiet : ¬Heard a (invert a) R) : 3≤xs.length :=
  physicalThree (boardTwo a) raw d m quiet

def A : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(1, 0)} : Finset VV), false)} : LinClause VV)

def B : LinClause VV := ({(({(2, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false)} : LinClause VV)

def R : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), true), (({(2, 1), (3, 1)} : Finset VV), true), (({(0, 0), (2, 1)} : Finset VV), false)} : LinClause VV)

def leftSlice : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), true), (({(2, 1), (3, 1)} : Finset VV), true), (({(0, 0), (2, 1)} : Finset VV), false), (({(0, 0)} : Finset VV), false)} : LinClause VV)

def rightSlice : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), true), (({(2, 1), (3, 1)} : Finset VV), true), (({(0, 0), (2, 1)} : Finset VV), false), (({(0, 0)} : Finset VV), true)} : LinClause VV)

theorem leftImp (a : VV → Bool) : LinClauseSat a A → LinClauseSat a leftSlice := by
  apply weak_cert A leftSlice [[(({(0, 0)} : Finset VV), false)], [(({(0, 0), (1, 0)} : Finset VV), true), (({(0, 0)} : Finset VV), false)]]
  intro q hq
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact ⟨[(({(0, 0)} : Finset VV), false)],by decide +kernel,by decide +kernel⟩
  · exact ⟨[(({(0, 0), (1, 0)} : Finset VV), true), (({(0, 0)} : Finset VV), false)],by decide +kernel,by decide +kernel⟩

theorem rightImp (a : VV → Bool) : LinClauseSat a B → LinClauseSat a rightSlice := by
  apply weak_cert B rightSlice [[(({(0, 0), (2, 1)} : Finset VV), false), (({(0, 0)} : Finset VV), true)], [(({(2, 1), (3, 1)} : Finset VV), true), (({(0, 0), (2, 1)} : Finset VV), false), (({(0, 0)} : Finset VV), true)]]
  intro q hq
  simp only [B, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact ⟨[(({(0, 0), (2, 1)} : Finset VV), false), (({(0, 0)} : Finset VV), true)],by decide +kernel,by decide +kernel⟩
  · exact ⟨[(({(2, 1), (3, 1)} : Finset VV), true), (({(0, 0), (2, 1)} : Finset VV), false), (({(0, 0)} : Finset VV), true)],by decide +kernel,by decide +kernel⟩

def alpha (v : VV) := decide (v=(0,0) ∨ v=(1,0))
theorem asleep : ¬Heard alpha (invert alpha) R := by
  intro h
  rcases h with ⟨q,m,on⟩|⟨q,m,on⟩ <;>
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at m <;>
    rcases m with rfl|rfl|rfl <;> revert on <;> unfold LinEqSat <;> decide +kernel

theorem threeUpper {π : List (LinClause VV)} (d : IsLinDerivation Formula π)
    (a : A∈π) (b : B∈π) :
    IsLinDerivation Formula ([R,rightSlice,leftSlice]++π) := by
  have dl := IsLinDerivation.weak d a leftImp
  have dr := IsLinDerivation.weak dl (List.mem_cons_of_mem _ b) rightImp
  apply IsLinDerivation.res (C:=leftSlice) (D:=rightSlice) dr
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_self
  · exact ⟨{(0,0)},by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem sharp {π : List (LinClause VV)} (d : IsLinDerivation Formula π)
    (raw : ∀ c∈π, c∈Formula) (a : A∈π) (b : B∈π) :
    (∃ xs : List (LinClause VV), xs.length=3 ∧ IsLinDerivation Formula (xs++π) ∧ R∈xs++π) ∧
    ∀ xs : List (LinClause VV), IsLinDerivation Formula (xs++π) → R∈xs++π → 3≤xs.length := by
  refine ⟨⟨[R,rightSlice,leftSlice],rfl,threeUpper d a b,List.mem_cons_self⟩,?_⟩
  intro xs legal m
  exact boardDepth alpha raw legal m asleep

end PEqualNP.Outside.L_pcx_121_pair
