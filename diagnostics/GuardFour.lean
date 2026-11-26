import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9246.GuardFour

open PEqualNP.ProofComplexity PEqualNP.Search

variable {V : Type} [DecidableEq V]

def replay (db : List (List (Literal V))) (fs : List (Literal V)) : List Nat → Bool
  | [] => false
  | i :: trail =>
    match db[i]? with
    | none => false
    | some d =>
      match d.filter (fun l => !fs.contains l) with
      | [] => true
      | [l] => replay db (negLit l :: fs) trail
      | _ => false

theorem replay_sound (db : List (List (Literal V))) (Γ : Set (Clause V))
    (A : Set (Literal V)) (hd : ∀ d ∈ db, d.toFinset ∈ Γ)
    (trail : List Nat) (fs : List (Literal V))
    (hf : ∀ l ∈ fs, UPForces Γ A (negLit l)) (h : replay db fs trail = true) :
    ∃ D ∈ Γ, ∀ l ∈ D, UPForces Γ A (negLit l) := by
  induction trail generalizing fs with
  | nil => simp [replay] at h
  | cons i trail ih =>
    simp only [replay] at h
    split at h
    · contradiction
    next d he =>
      have hm := hd d (List.mem_of_getElem? he)
      split at h
      next hnil =>
        refine ⟨d.toFinset, hm, ?_⟩
        intro l hl
        have hld : l ∈ d := List.mem_toFinset.mp hl
        apply hf
        by_contra hn
        have : l ∈ d.filter (fun l => !fs.contains l) := by simp [hld, hn]
        rw [hnil] at this
        exact List.not_mem_nil this
      next l hsingle =>
        have hld : l ∈ d.filter (fun v => !fs.contains v) := by
          rw [hsingle]
          exact List.mem_cons_self
        have hu : UPForces Γ A l := by
          apply UPForces.unit hm (List.mem_toFinset.mpr (List.mem_filter.mp hld).1)
          intro v hv hne
          apply hf
          by_contra hn
          have hvd : v ∈ d := List.mem_toFinset.mp hv
          have : v ∈ d.filter (fun x => !fs.contains x) := by simp [hvd, hn]
          rw [hsingle] at this
          exact hne (List.mem_singleton.mp this)
        apply ih (negLit l :: fs) _ h
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · simpa [negLit] using hu
        · exact hf v hv
      next => contradiction

def verify (db : List (List (Literal V))) :
    List (List (Literal V) × List Nat) → Bool
  | [] => true
  | (c, trail) :: steps => replay db c trail && verify (db ++ [c]) steps

def learned (s : List (List (Literal V) × List Nat)) (ρ : List (Clause V)) :=
  s.foldl (fun acc p => p.1.toFinset :: acc) ρ

theorem verify_sound (F : Set (Clause V)) (steps : List (List (Literal V) × List Nat))
    (db : List (List (Literal V))) (ρ : List (Clause V)) (hr : IsRUPRun F ρ)
    (hd : ∀ d ∈ db, d.toFinset ∈ F ∪ {D | D ∈ ρ}) (h : verify db steps = true) :
    IsRUPRun F (learned steps ρ) := by
  induction steps generalizing db ρ with
  | nil => exact hr
  | cons head steps ih =>
    obtain ⟨c, trail⟩ := head
    have ⟨ht, hs⟩ := Bool.and_eq_true_iff.mp h
    have hc : IsRUP (F ∪ {D | D ∈ ρ}) c.toFinset := by
      apply replay_sound db _ _ hd trail c _ ht
      intro l hl
      exact UPForces.hyp ⟨l, List.mem_toFinset.mpr hl, rfl⟩
    apply ih (db ++ [c]) (c.toFinset :: ρ) (IsRUPRun.learn hr hc) _ hs
    intro d hmem
    rcases List.mem_append.mp hmem with hm | hm
    · rcases hd d hm with hF | hρ
      · exact Or.inl hF
      · exact Or.inr (List.mem_cons_of_mem _ hρ)
    · have he : d = c := by simpa using hm
      exact Or.inr (he ▸ List.mem_cons_self)

abbrev Board := Fin 5 × Fin 4

def row (p : Fin 5) : List (Literal Board) :=
  (List.finRange 4).map (fun h => ((p, h), true))

def block (p q : Fin 5) (h : Fin 4) : List (Literal Board) :=
  [((p, h), false), ((q, h), false)]

def input : List (List (Literal Board)) :=
  (List.finRange 5).map row ++ (List.finRange 4).flatMap (fun h =>
    (List.finRange 5).flatMap (fun p =>
      ((List.finRange 5).filter (fun q => p < q)).map (fun q => block p q h)))

theorem input_sound (d : List (Literal Board)) (hd : d ∈ input) :
    d.toFinset ∈ PHP 5 4 := by
  rcases List.mem_append.mp hd with hr | hb
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
    left
    refine ⟨p, ?_⟩
    ext l
    simp [row]
  · obtain ⟨h, _, hh⟩ := List.mem_flatMap.mp hb
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hh
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    right
    exact ⟨p, q, h, ne_of_lt (of_decide_eq_true (List.mem_filter.mp hq).2), by simp [block]⟩

def readLiteral (k : Nat) : Literal Board :=
  ((Fin.ofNat 5 (k / 2 / 4), Fin.ofNat 4 (k / 2)), decide (k % 2 = 0))

def prefixSteps : List (List (Literal Board) × List Nat) :=
  ([([2, 4, 6, 12, 14, 30],[0, 5, 1, 6, 7, 8, 19, 20, 3, 21, 32, 2, 34, 4, 43]),
  ([14, 18, 20, 22, 28, 30],[2, 6, 9, 12, 3, 13, 17, 20, 1, 24, 25, 0, 31, 4, 38]),
  ([3, 12, 14, 30],[15, 1, 5, 9, 10, 11, 16, 17, 3, 18, 27, 32, 2, 34, 4, 36, 43]),
  ([13, 14, 22, 30],[25, 29, 30, 31, 46, 16, 19, 22, 3, 7, 0, 10, 12, 14, 23, 4, 38])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem checked_prefixSteps : verify input prefixSteps=true := by decide +kernel
theorem run_prefixSteps : IsRUPRun (PHP 5 4) (learned prefixSteps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (input_sound d hd)) checked_prefixSteps
def positiveSteps : List (List (Literal Board) × List Nat) :=
  ([([2, 4, 6, 12, 14, 30],[0, 5, 1, 6, 7, 8, 19, 20, 3, 21, 32, 2, 34, 4, 43]),
  ([14, 18, 20, 22, 28, 30],[2, 6, 9, 12, 3, 13, 17, 20, 1, 24, 25, 0, 31, 4, 38]),
  ([3, 12, 14, 30],[15, 1, 5, 9, 10, 11, 16, 17, 3, 18, 27, 32, 2, 34, 4, 36, 43]),
  ([13, 14, 22, 30],[25, 29, 30, 31, 46, 16, 19, 22, 3, 7, 0, 10, 12, 14, 23, 4, 38]),
  ([6, 14, 22, 30],[48, 47, 45, 26, 27, 28, 46, 19, 1, 5, 9, 10, 3, 11, 22])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem checked_positiveSteps : verify input positiveSteps=true := by decide +kernel
theorem run_positiveSteps : IsRUPRun (PHP 5 4) (learned positiveSteps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (input_sound d hd)) checked_positiveSteps
def negativeSteps : List (List (Literal Board) × List Nat) :=
  ([([2, 4, 6, 12, 14, 30],[0, 5, 1, 6, 7, 8, 19, 20, 3, 21, 32, 2, 34, 4, 43]),
  ([14, 18, 20, 22, 28, 30],[2, 6, 9, 12, 3, 13, 17, 20, 1, 24, 25, 0, 31, 4, 38]),
  ([3, 12, 14, 30],[15, 1, 5, 9, 10, 11, 16, 17, 3, 18, 27, 32, 2, 34, 4, 36, 43]),
  ([13, 14, 22, 30],[25, 29, 30, 31, 46, 16, 19, 22, 3, 7, 0, 10, 12, 14, 23, 4, 38]),
  ([39],[38, 41, 43, 44, 48, 47, 45, 26, 27, 28, 46, 19, 1, 5, 9, 10, 3, 11, 22])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem checked_negativeSteps : verify input negativeSteps=true := by decide +kernel
theorem run_negativeSteps : IsRUPRun (PHP 5 4) (learned negativeSteps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (input_sound d hd)) checked_negativeSteps

def hall : Clause Board := ([6,14,22,30].map readLiteral).toFinset
def negative : Clause Board := ([39].map readLiteral).toFinset
theorem hallMeaning : hall = {((0,3),true),((1,3),true),((2,3),true),((3,3),true)} := by decide +kernel
theorem negMeaning : negative = {((4,3),false)} := by decide +kernel
theorem learnFront {c : Clause Board} {ds : List (Clause Board)} (a : IsRUPRun (PHP 5 4) (c::ds)) :
    IsRUP (PHP 5 4 ∪ {d|d∈ds}) c := by
  cases a with
  | learn _ h => exact h
theorem sharedFour : ∃ ds : List (Clause Board), IsRUPRun (PHP 5 4) ds ∧ ds.length=4 ∧
    IsRUP (PHP 5 4 ∪ {d|d∈ds}) {((4,3),false)} ∧
    IsRUP (PHP 5 4 ∪ {d|d∈ds}) {((0,3),true),((1,3),true),((2,3),true),((3,3),true)} := by
  refine ⟨learned prefixSteps [],run_prefixSteps,by decide +kernel,?_,?_⟩
  · rw [←negMeaning]
    apply learnFront
    exact run_negativeSteps
  · rw [←hallMeaning]
    apply learnFront
    exact run_positiveSteps
end PEqualNP.Outside.L_meta_9246.GuardFour
