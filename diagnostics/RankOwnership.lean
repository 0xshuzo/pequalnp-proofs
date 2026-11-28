import PEqualNP.Defs

namespace PEqualNP.Outside.Pcx177RankOwner

open PEqualNP.ProofComplexity
abbrev R := Fin 5
abbrev H := Fin 4
abbrev V := R × H
abbrev C := LinClause V

def column (t : Finset R) (h : H) : Finset V := t.image (fun p => (p,h))
def guard (t : Finset R) : C := Finset.univ.image (fun h : H => (column t h,true))
def point (p : Finset R) (h : H) : V → Bool := fun v => decide (v.1 ∈ p ∧ v.2=h)
def slice (f : Finset V) (h : H) : Finset R := Finset.univ.filter (fun r => (r,h)∈f)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sample : ∀ s t : Finset R, s.Nonempty → s≠t →
    ∃ p : Finset R, Odd (s∩p).card ∧ Even (t∩p).card := by decide +kernel

theorem counts (f : Finset V) (p : Finset R) (h : H) :
    (f.filter (fun v => point p h v = true)).card = (slice f h ∩ p).card := by
  have e : f.filter (fun v => point p h v = true) = (slice f h ∩ p).image (fun r => (r,h)) := by
    ext v
    obtain ⟨r,j⟩ := v
    simp only [Finset.mem_filter,point,decide_eq_true_eq,Finset.mem_image,Finset.mem_inter,
      slice,Finset.mem_univ,true_and,Prod.mk.injEq]
    constructor
    · rintro ⟨a,b,rfl⟩
      exact ⟨r,⟨a,b⟩,rfl,rfl⟩
    · rintro ⟨p,⟨a,b⟩,rfl,rfl⟩
      exact ⟨a,b,rfl⟩
  have inj : Function.Injective (fun r : R => (r,h)) := fun _ _ eq => congrArg Prod.fst eq
  rw [e,Finset.card_image_of_injective _ inj]

theorem sliceCol (s : Finset R) (i j : H) :
    slice (column s i) j = if i=j then s else ∅ := by
  ext r
  by_cases e : i=j
  · subst j
    simp [slice,column]
  · simp [slice,column,e,Ne.symm e]

theorem off {t p : Finset R} {h : H} (zero : Even (t∩p).card) :
    ¬LinClauseSat (point p h) (guard t) := by
  rintro ⟨q,m,yes⟩
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp m
  change (Odd (((column t j).filter (fun v => point p h v=true)).card) ↔ true = true) at yes
  have odd := yes.mpr rfl
  rw [counts,sliceCol] at odd
  by_cases e : j=h
  · simp only [if_pos e] at odd
    rcases odd with ⟨a,ha⟩
    rcases zero with ⟨b,hb⟩
    omega
  · simp [e] at odd

def weak (K : C) (t : Finset R) := ∀ x, LinClauseSat x K → LinClauseSat x (guard t)

theorem sliceUnique {K : C} {t : Finset R} (w : weak K t) {f : Finset V}
    (m : (f,true)∈K) (j : H) (nonempty : (slice f j).Nonempty) : slice f j=t := by
  by_contra ne
  obtain ⟨p,a,b⟩ := sample _ _ nonempty ne
  apply off (h:=j) b (w _ ⟨(f,true),m,?_⟩)
  change Odd ((f.filter (fun v => point p j v=true)).card) ↔ true=true
  rw [counts]
  simp [a]

theorem zeroGuard (t : Finset R) : ¬ LinClauseSat (fun _ : V => false) (guard t) := by
  rintro ⟨q,m,yes⟩
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp m
  simpa [LinEqSat] using yes

theorem weakUnique {K : C} {s t : Finset R} (w : weak K s) (v : weak K t)
    (sat : ∃ x, LinClauseSat x K) : s=t := by
  obtain ⟨x,⟨⟨f,b⟩,m,yes⟩⟩ := sat
  cases b with
  | false =>
    apply False.elim (zeroGuard s (w _ ⟨(f,false),m,?_⟩))
    simp [LinEqSat]
  | true =>
    have ne : f.Nonempty := by
      by_contra no
      have empty := Finset.not_nonempty_iff_eq_empty.mp no
      simp [empty,LinEqSat] at yes
    obtain ⟨⟨r,h⟩,mem⟩ := ne
    have ss : (slice f h).Nonempty := ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem⟩⟩
    exact (sliceUnique w m h ss).symm.trans (sliceUnique v m h ss)

end PEqualNP.Outside.Pcx177RankOwner
