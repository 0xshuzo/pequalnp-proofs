import PEqualNP.Defs

open PEqualNP.ProofComplexity
open scoped BigOperators

namespace BlockQuota
variable {n m h : ℕ}

def fiber {a d : ℕ} (f : Fin a → Fin d) (i : Fin d) : Finset (Fin a) :=
  Finset.univ.filter (fun e => f e = i)

def lits {V : Type} [DecidableEq V] (T : Finset (Fin n)) (inj : Fin n → V) (s : Bool) :
    Clause V := T.image (fun e => (inj e,s))

def base {V : Type} [DecidableEq V] (inj : Fin n → V) (row : Fin n → Fin m)
    (col : Fin n → Fin h) (lo : Fin m → ℕ) (hi : Fin h → ℕ) : Set (Clause V) :=
  {D | (∃ i T, T ⊆ fiber row i ∧ T.card + lo i = (fiber row i).card + 1 ∧ D = lits T inj true) ∨
       (∃ j T, T ⊆ fiber col j ∧ T.card = hi j + 1 ∧ D = lits T inj false)}

theorem count_fibers {a d : ℕ} (f : Fin a → Fin d) (X : Finset (Fin a)) :
    ∑ i, ((fiber f i) ∩ X).card = X.card := by
  have eqf (i : Fin d) : fiber f i ∩ X = X.filter (fun e => f e = i) := by
    ext e
    simp [fiber, and_comm]
  simp only [eqf]
  exact (Finset.card_eq_sum_card_fiberwise (f := f) (s := X) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)).symm

theorem obstruct (row : Fin n → Fin m) (col : Fin n → Fin h)
    (lo : Fin m → ℕ) (hi : Fin h → ℕ) (bad : ∑ j, hi j < ∑ i, lo i)
    (X : Finset (Fin n)) :
    (∃ i, ((fiber row i) ∩ X).card < lo i) ∨ (∃ j, hi j < ((fiber col j) ∩ X).card) := by
  by_contra! hh
  have hr := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh.1 i)
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hh.2 j)
  rw [count_fibers] at hr hc
  omega

theorem unsat {V : Type} [DecidableEq V] (inj : Fin n → V) (row : Fin n → Fin m)
    (col : Fin n → Fin h) (lo : Fin m → ℕ) (hi : Fin h → ℕ)
    (hr : ∀ i, lo i ≤ (fiber row i).card) (bad : ∑ j, hi j < ∑ i, lo i) :
    ¬ Satisfiable (base inj row col lo hi) := by
  classical
  rintro ⟨a,ha⟩
  let X := Finset.univ.filter (fun e : Fin n => a (inj e) = true)
  rcases obstruct row col lo hi bad X with ⟨i,hi'⟩ | ⟨j,hj⟩
  · let R := fiber row i
    have hpart : (R \ X).card + (R ∩ X).card = R.card :=
      Finset.card_sdiff_add_card_inter _ _
    have hlo := hr i
    change (R ∩ X).card < lo i at hi'
    change lo i ≤ R.card at hlo
    have hk : R.card + 1 - lo i ≤ (R \ X).card := by omega
    obtain ⟨T,hT,ht⟩ := Finset.exists_subset_card_eq hk
    have hmem : lits T inj true ∈ base inj row col lo hi :=
      Or.inl ⟨i,T,(fun e he => (Finset.mem_sdiff.mp (hT he)).1),by change T.card + lo i = R.card + 1; omega,rfl⟩
    obtain ⟨l,hl,hal⟩ := ha _ hmem
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
    have hnot := (Finset.mem_sdiff.mp (hT he)).2
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hal⟩)
  · obtain ⟨T,hT,ht⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hj)
    have hmem : lits T inj false ∈ base inj row col lo hi :=
      Or.inr ⟨j,T,(fun e he => (Finset.mem_inter.mp (hT he)).1),ht,rfl⟩
    obtain ⟨l,hl,hal⟩ := ha _ hmem
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
    have hpos := (Finset.mem_filter.mp (Finset.mem_inter.mp (hT he)).2).2
    change a (inj e) = false at hal
    rw [hal] at hpos
    contradiction

end BlockQuota

namespace BlockQuota
open PEqualNP.ProofComplexity
variable {n m h : ℕ}
private def negs {V : Type} [DecidableEq V] (U : Finset V) : Clause V :=
  U.image (fun v => (v,false))

private theorem discharge {V : Type} [DecidableEq V] (F : Set (Clause V))
    (U : Finset V) (b : ℕ) (hU : U.card ≤ b) (units : ∀ u ∈ U, {(u,true)} ∈ F)
    (π : List (Clause V)) (d : IsDerivation F π) (mem : negs U ∈ π)
    (width : ∀ D ∈ π, D.card ≤ b+1) :
    ∃ τ : List (Clause V), IsRefutation F τ ∧ τ.length ≤ π.length+2*U.card ∧
      ∀ D ∈ τ, D.card ≤ b+1 := by
  classical
  induction U using Finset.induction_on generalizing π with
  | empty =>
    exact ⟨π,⟨d,by simpa [negs] using mem⟩,by simp,width⟩
  | insert x U hn ih =>
    let A : Clause V := {(x,true)}
    have ax : A ∈ F := units _ (Finset.mem_insert_self _ _)
    have hd : IsDerivation F (A::π) := .ax d ax
    have e : (negs (insert x U)).erase (x,false) = negs U := by
      ext l
      simp only [negs,Finset.image_insert,Finset.mem_erase,Finset.mem_insert]
      constructor
      · rintro ⟨hne,h|h⟩
        · exact (hne h).elim
        · exact h
      · intro hl
        refine ⟨?_,Or.inr hl⟩
        rintro rfl
        obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hl
        have hux : u = x := congrArg Prod.fst he
        exact hn (hux ▸ hu)
    have hr : IsResolvent A (negs (insert x U)) (negs U) := by
      refine ⟨x,by simp [A],by simp [negs],?_⟩
      simp [A,e]
    let p := negs U :: A :: π
    have deriv : IsDerivation F p := .res hd List.mem_cons_self (List.mem_cons_of_mem _ mem) hr
    have hu : U.card ≤ b := by rw [Finset.card_insert_of_notMem hn] at hU; omega
    have wp : ∀ D ∈ p, D.card ≤ b+1 := by
      intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact (Finset.card_image_le.trans hu).trans (by omega)
      rcases List.mem_cons.mp hD with rfl | hD
      · simp [A]
      exact width _ hD
    obtain ⟨τ,hh,hlen,hw⟩ := ih hu (fun u h => units _ (Finset.mem_insert_of_mem h))
      p deriv List.mem_cons_self wp
    refine ⟨τ,hh,?_,hw⟩
    rw [Finset.card_insert_of_notMem hn]
    simp only [p,List.length_cons] at hlen
    omega

theorem saturated {V : Type} [DecidableEq V] (inj : Fin n → V) (row : Fin n → Fin m)
    (col : Fin n → Fin h) (lo : Fin m → ℕ) (hi : Fin h → ℕ) (b : ℕ)
    (extreme : ∀ i, lo i = 0 ∨ lo i = (fiber row i).card)
    (hb : ∀ j, (fiber col j).card ≤ b) (bad : ∑ j, hi j < ∑ i, lo i) :
    ∃ π : List (Clause V), IsRefutation (base inj row col lo hi) π ∧
      π.length ≤ 2*b+1 ∧ ∀ D ∈ π, D.card ≤ b+1 := by
  classical
  let X := Finset.univ.filter (fun e : Fin n => lo (row e) = (fiber row (row e)).card)
  have hsat : ∀ i, lo i ≤ ((fiber row i) ∩ X).card := by
    intro i
    rcases extreme i with hz | he
    · omega
    · have hsub : fiber row i ⊆ X := by
        intro e h
        have er : row e = i := (Finset.mem_filter.mp h).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [er] using he⟩
      rw [Finset.inter_eq_left.mpr hsub,he]
  have over : ∃ j, hi j < ((fiber col j) ∩ X).card := by
    rcases obstruct row col lo hi bad X with ⟨i,hh⟩ | hh
    · exact (Nat.not_lt_of_ge (hsat i) hh).elim
    · exact hh
  obtain ⟨j,hj⟩ := over
  obtain ⟨T,hT,ht⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hj)
  let F := base inj row col lo hi
  let U := T.image inj
  have sT : T ⊆ fiber col j := fun _ he => (Finset.mem_inter.mp (hT he)).1
  have hneg : negs U ∈ F := by
    refine Or.inr ⟨j,T,sT,ht,?_⟩
    simp [negs,U,lits,Finset.image_image,Function.comp_def]
  have hU : U.card ≤ b := Finset.card_image_le.trans ((Finset.card_le_card sT).trans (hb j))
  have hunits : ∀ v ∈ U, {(v,true)} ∈ F := by
    intro v hv
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
    have eh := (Finset.mem_filter.mp (Finset.mem_inter.mp (hT he)).2).2
    refine Or.inl ⟨row e,{e},?_,?_,?_⟩
    · simpa [fiber] using (show e ∈ fiber row (row e) by simp [fiber])
    · change ({e} : Finset (Fin n)).card + lo (row e) = (fiber row (row e)).card + 1
      simp [eh,Nat.add_comm]
    · simp [lits]
  obtain ⟨τ,hh,hl,hw⟩ := discharge F U b hU hunits [negs U] (.ax .nil hneg)
    (by simp) (by intro D hd; obtain rfl := List.mem_singleton.mp hd
                  exact (Finset.card_image_le.trans hU).trans (by omega))
  exact ⟨τ,hh,by simp only [List.length_cons,List.length_nil] at hl; omega,hw⟩

end BlockQuota
