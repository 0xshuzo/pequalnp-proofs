import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9246.PrimeColumn

variable {V : Type} [DecidableEq V]
abbrev assumptions (c : Clause V) := negLit '' (↑c : Set (Literal V))
def clashes (G : Set (Clause V)) (B : Set (Literal V)) :=
  ∃ d∈G, ∀ l∈d, UPForces G B (negLit l)

theorem simulate {G H : Set (Clause V)} {A B : Set (Literal V)}
    (shrinks : ∀ d∈G, ∃ e∈H, e⊆d)
    (hypotheses : ∀ l∈A, UPForces H B l)
    (clean : ¬clashes H B) {l} (old : UPForces G A l) : UPForces H B l := by
  induction old with
  | hyp m => exact hypotheses _ m
  | @unit d k md hk other ih =>
    obtain ⟨e,he,sub⟩ := shrinks d md
    by_cases member : k∈e
    · exact .unit he member (fun z hz ne => ih z (sub hz) ne)
    · exact False.elim (clean ⟨e,he,fun z hz => ih z (sub hz) (fun eq => member (eq ▸ hz))⟩)

theorem shortenClause {G H : Set (Clause V)} {c e : Clause V}
    (shrinks : ∀ d∈G, ∃ f∈H, f⊆d)
    (reconstruct : ∀ l∈c, UPForces H (assumptions e) (negLit l))
    (old : IsRUP G c) : IsRUP H e := by
  change clashes H (assumptions e)
  by_contra clean
  obtain ⟨d,hd,dead⟩ := old
  obtain ⟨f,hf,sub⟩ := shrinks d hd
  apply clean
  refine ⟨f,hf,fun l hl => simulate shrinks ?_ clean (dead l (sub hl))⟩
  rintro _ ⟨z,hz,rfl⟩
  exact reconstruct z hz

theorem transform {G : Set (Clause V)} (f : Clause V → Clause V)
    (sub : ∀ c, f c⊆c)
    (reconstruct : ∀ H : Set (Clause V), G⊆H → ∀ c, ∀ l∈c,
      UPForces H (assumptions (f c)) (negLit l))
    {cs} (run : IsRUPRun G cs) : IsRUPRun G (cs.map f) := by
  induction run with
  | nil => exact IsRUPRun.nil
  | @learn cs c prev step ih =>
    apply IsRUPRun.learn ih (shortenClause ?_ (reconstruct _ (fun _ hg => Or.inl hg) c) step)
    rintro d (base|learned)
    · exact ⟨d,Or.inl base,fun _ m => m⟩
    · exact ⟨f d,Or.inr (List.mem_map.mpr ⟨d,learned,rfl⟩),sub d⟩

abbrev Cell := Fin 5 × Fin 4
abbrev C := Clause Cell
abbrev L := Literal Cell

def keep (c : C) (l : L) : Prop :=
  l.2=false ∨ ∀ q : Fin 5, q≠l.1.1 → ((q,l.1.2),false)∉c
noncomputable def reduced (c : C) : C := by
  classical
  exact c.filter (keep c)

theorem sub (c : C) : reduced c⊆c := Finset.filter_subset _ _
theorem remaining {c : C} {l : L} (m : l∈c) (k : keep c l) : l∈reduced c := by
  exact Finset.mem_filter.mpr ⟨m,k⟩

theorem recover (H : Set C) (incl : PHP 5 4⊆H) (c : C) (l : L) (m : l∈c) :
    UPForces H (assumptions (reduced c)) (negLit l) := by
  classical
  by_cases ok : keep c l
  · exact .hyp ⟨l,remaining m ok,rfl⟩
  rcases l with ⟨⟨p,h⟩,b⟩
  cases b with
  | false => exact False.elim (ok (Or.inl rfl))
  | true =>
    have bad : ∃ q : Fin 5, q≠p ∧ ((q,h),false)∈c := by
      by_contra no
      exact ok (Or.inr (fun q sep pos => no ⟨q,sep,pos⟩))
    obtain ⟨q,sep,old⟩ := bad
    let d : C := {((p,h),false),((q,h),false)}
    have hd : d∈H := incl (Or.inr ⟨p,q,h,Ne.symm sep,rfl⟩)
    change UPForces H (assumptions (reduced c)) ((p,h),false)
    apply UPForces.unit hd (by simp [d])
    intro z hz ne
    have side : z=((p,h),false) ∨ z=((q,h),false) := by simpa [d] using hz
    rcases side with eq|rfl
    · exact False.elim (ne eq)
    · exact .hyp ⟨((q,h),false),remaining old (Or.inl rfl),rfl⟩

theorem normalize {cs : List C} (run : IsRUPRun (PHP 5 4) cs) :
    IsRUPRun (PHP 5 4) (cs.map reduced) := transform reduced sub recover run

theorem exact_length_normal_form {cs : List C} (run : IsRUPRun (PHP 5 4) cs)
    (empty : (∅ : C)∈cs) :
    ∃ ds : List C, IsRUPRun (PHP 5 4) ds ∧ (∅ : C)∈ds ∧ ds.length=cs.length ∧
      ∀ d∈ds, ∀ (p q : Fin 5) (h : Fin 4), p≠q → ((p,h),true)∈d → ((q,h),false)∉d := by
  classical
  refine ⟨cs.map reduced,normalize run,?_,List.length_map ..,?_⟩
  · apply List.mem_map.mpr
    exact ⟨∅,empty,by simp [reduced]⟩
  · intro d mem p q h sep lit
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp mem
    have surv : keep c ((p,h),true) := (Finset.mem_filter.mp lit).2
    rcases surv with no|clean
    · cases no
    · intro neg
      exact clean q (Ne.symm sep) (sub c neg)

end PEqualNP.Outside.L_meta_9246.PrimeColumn
