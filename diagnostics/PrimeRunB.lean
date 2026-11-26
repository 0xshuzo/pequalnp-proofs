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

theorem sub (c : C) : reduced c⊆c := by
  classical
  exact Finset.filter_subset _ _
theorem remaining {c : C} {l : L} (m : l∈c) (k : keep c l) : l∈reduced c := by
  classical
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

namespace PEqualNP.Outside.L_meta_9246.PrimeColumn
open PEqualNP.ProofComplexity PEqualNP.Search
variable {V : Type} [DecidableEq V]
abbrev pool (G : Set (Clause V)) (cs : List (Clause V)) := G ∪ {d | d∈cs}
abbrev prime (G : Set (Clause V)) (c : Clause V) := ∀ d, d⊂c → ¬ IsRUP G d

theorem minSub (G : Set (Clause V)) (c : Clause V) (valid : IsRUP G c) :
    ∃ b, b⊆c ∧ IsRUP G b ∧ prime G b := by
  classical
  let P (n : Nat) : Prop := ∃ b : Clause V, b⊆c ∧ IsRUP G b ∧ b.card=n
  have nonempty : ∃ n, P n := ⟨c.card,c,Finset.Subset.rfl,valid,rfl⟩
  obtain ⟨b,sub,good,num⟩ := Nat.find_spec nonempty
  refine ⟨b,sub,good,?_⟩
  intro d proper small
  have atLeast : Nat.find nonempty ≤ d.card :=
    Nat.find_min' nonempty ⟨d,Finset.Subset.trans (Finset.ssubset_iff_subset_ne.mp proper).1 sub,small,rfl⟩
  have lt := Finset.card_lt_card proper
  omega

inductive PrimeRun (G : Set (Clause V)) : List (Clause V) → Prop
  | nil : PrimeRun G []
  | learn {cs c} (prior : PrimeRun G cs) (step : IsRUP (pool G cs) c)
      (tight : prime (pool G cs) c) (fresh : ∀ b ∈ pool G cs, ¬ b⊆c) : PrimeRun G (c::cs)

theorem PrimeRun.run {G : Set (Clause V)} {cs} (pr : PrimeRun G cs) : IsRUPRun G cs := by
  induction pr with
  | nil => exact .nil
  | learn _ s _ _ ih => exact .learn ih s

theorem primeRestore {G : Set (Clause V)} {cs} (old : IsRUPRun G cs) :
    ∃ ds, PrimeRun G ds ∧ ds.length ≤ cs.length ∧
      ∀ d ∈ pool G cs, ∃ b ∈ pool G ds, b⊆d := by
  classical
  induction old with
  | nil =>
    exact ⟨[],.nil,by simp,fun d m => ⟨d,m,Finset.Subset.rfl⟩⟩
  | @learn cs c prev step ih =>
    obtain ⟨ds,pr,len,shrink⟩ := ih
    by_cases seen : ∃ b∈pool G ds, b⊆c
    · refine ⟨ds,pr,by simp; omega,?_⟩
      rintro d (hg|hl)
      · exact shrink d (Or.inl hg)
      · rcases List.mem_cons.mp hl with rfl|hm
        · exact seen
        · exact shrink d (Or.inr hm)
    · have feasible : IsRUP (pool G ds) c :=
        shortenClause shrink (fun l m => UPForces.hyp ⟨l,m,rfl⟩) step
      obtain ⟨b,bc,valid,tight⟩ := minSub _ c feasible
      have fresh : ∀ q∈pool G ds, ¬q⊆b := by
        intro q hq qs
        exact seen ⟨q,hq,Finset.Subset.trans qs bc⟩
      refine ⟨b::ds,.learn pr valid tight fresh,by simpa using len,?_⟩
      rintro d (hg|hl)
      · exact ⟨d,Or.inl hg,Finset.Subset.rfl⟩
      · rcases List.mem_cons.mp hl with rfl|hm
        · exact ⟨b,Or.inr (by simp),bc⟩
        · obtain ⟨e,he,ed⟩ := shrink d (Or.inr hm)
          refine ⟨e,?_,ed⟩
          rcases he with h|h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem primeRefutation {G : Set (Clause V)} (nonempty : (∅ : Clause V)∉G) {cs}
    (old : IsRUPRun G cs) (dead : (∅ : Clause V)∈cs) :
    ∃ ds, PrimeRun G ds ∧ ds.length≤cs.length ∧ (∅ : Clause V)∈ds := by
  obtain ⟨ds,ready,len,sub⟩ := primeRestore old
  obtain ⟨e,whereFrom,below⟩ := sub ∅ (Or.inr dead)
  have eq : e=∅ := Finset.eq_empty_of_subset_empty below
  subst e
  exact ⟨ds,ready,len,whereFrom.resolve_left nonempty⟩

theorem primeColumn {G : Set C} (base : PHP 5 4⊆G) {c : C}
    (learn : IsRUP G c) (tight : prime G c) : reduced c=c := by
  by_contra wrong
  have ss : reduced c ⊂ c := Finset.ssubset_iff_subset_ne.mpr ⟨sub c,wrong⟩
  apply tight (reduced c) ss
  exact shortenClause (fun d hd => ⟨d,hd,Finset.Subset.rfl⟩) (recover G base c) learn

end PEqualNP.Outside.L_meta_9246.PrimeColumn
