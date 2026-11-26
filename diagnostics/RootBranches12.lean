import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9246.RootBranches

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


def SharedSteps : List (List (Literal Board) × List Nat) :=
  ([([1, 22, 36, 38],[5, 6, 7, 8, 4, 18, 21, 23, 2, 24, 26, 29, 1, 32, 3, 35, 40]),([13, 24, 26],[25, 29, 30, 3, 31, 37, 40, 42, 44, 45, 0, 15, 16, 2, 9, 13, 4, 18]),([16, 18, 24, 26, 28],[3, 37, 40, 42, 2, 26, 29, 33, 44, 45, 0, 15, 1, 11, 4, 18]),([8, 10, 21],[26, 29, 1, 32, 33, 35, 39, 40, 41, 45, 0, 16, 17, 3, 12, 14, 4, 18]),([8, 10, 24, 26],[46, 1, 35, 39, 40, 3, 27, 32, 34, 41, 45, 0, 16, 2, 13, 4, 18]),([10, 18, 25],[7, 10, 12, 14, 48, 2, 36, 39, 1, 25, 0, 17, 18, 30, 31, 4, 42, 43]),([35],[18, 21, 23, 24, 50, 46, 49, 5, 9, 11, 47, 27, 0, 32, 2, 34, 35, 36]),([11, 20, 22, 30],[15, 19, 2, 6, 9, 12, 13, 20, 3, 21, 27, 0, 30, 34, 4, 35, 38]),([11, 16, 24],[15, 19, 20, 21, 46, 47, 27, 32, 2, 34, 36, 0, 5, 8, 4, 39, 42, 43]),([33],[8, 11, 13, 14, 51, 53, 48, 49, 17, 22, 2, 36, 0, 25, 1, 27, 28, 39]),([5],[25, 26, 27, 28, 51, 54, 4, 38, 41, 43, 44, 52, 1, 5, 9, 2, 10, 3, 16, 22]),([0, 2],[51, 54, 55, 0, 35, 36, 37, 38, 4, 31, 33, 34, 52, 1, 9, 2, 10, 3, 22])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem checkShared : verify input SharedSteps=true := by decide +kernel
theorem okShared : IsRUPRun (PHP 5 4) (learned SharedSteps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (input_sound d hd)) checkShared

def TrueSteps : List (List (Literal Board) × List Nat) :=
  ([([1, 22, 36, 38],[5, 6, 7, 8, 4, 18, 21, 23, 2, 24, 26, 29, 1, 32, 3, 35, 40]),([13, 24, 26],[25, 29, 30, 3, 31, 37, 40, 42, 44, 45, 0, 15, 16, 2, 9, 13, 4, 18]),([16, 18, 24, 26, 28],[3, 37, 40, 42, 2, 26, 29, 33, 44, 45, 0, 15, 1, 11, 4, 18]),([8, 10, 21],[26, 29, 1, 32, 33, 35, 39, 40, 41, 45, 0, 16, 17, 3, 12, 14, 4, 18]),([8, 10, 24, 26],[46, 1, 35, 39, 40, 3, 27, 32, 34, 41, 45, 0, 16, 2, 13, 4, 18]),([10, 18, 25],[7, 10, 12, 14, 48, 2, 36, 39, 1, 25, 0, 17, 18, 30, 31, 4, 42, 43]),([35],[18, 21, 23, 24, 50, 46, 49, 5, 9, 11, 47, 27, 0, 32, 2, 34, 35, 36]),([11, 20, 22, 30],[15, 19, 2, 6, 9, 12, 13, 20, 3, 21, 27, 0, 30, 34, 4, 35, 38]),([11, 16, 24],[15, 19, 20, 21, 46, 47, 27, 32, 2, 34, 36, 0, 5, 8, 4, 39, 42, 43]),([33],[8, 11, 13, 14, 51, 53, 48, 49, 17, 22, 2, 36, 0, 25, 1, 27, 28, 39]),([5],[25, 26, 27, 28, 51, 54, 4, 38, 41, 43, 44, 52, 1, 5, 9, 2, 10, 3, 16, 22]),([0, 2],[51, 54, 55, 0, 35, 36, 37, 38, 4, 31, 33, 34, 52, 1, 9, 2, 10, 3, 22]),([0],[51, 54, 55, 56, 15, 16, 17, 50, 46, 49, 9, 47, 32, 2, 34, 4, 36, 39, 42, 43])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem checkTrue : verify input TrueSteps=true := by decide +kernel
theorem okTrue : IsRUPRun (PHP 5 4) (learned TrueSteps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (input_sound d hd)) checkTrue

def FalseSteps : List (List (Literal Board) × List Nat) :=
  ([([1, 22, 36, 38],[5, 6, 7, 8, 4, 18, 21, 23, 2, 24, 26, 29, 1, 32, 3, 35, 40]),([13, 24, 26],[25, 29, 30, 3, 31, 37, 40, 42, 44, 45, 0, 15, 16, 2, 9, 13, 4, 18]),([16, 18, 24, 26, 28],[3, 37, 40, 42, 2, 26, 29, 33, 44, 45, 0, 15, 1, 11, 4, 18]),([8, 10, 21],[26, 29, 1, 32, 33, 35, 39, 40, 41, 45, 0, 16, 17, 3, 12, 14, 4, 18]),([8, 10, 24, 26],[46, 1, 35, 39, 40, 3, 27, 32, 34, 41, 45, 0, 16, 2, 13, 4, 18]),([10, 18, 25],[7, 10, 12, 14, 48, 2, 36, 39, 1, 25, 0, 17, 18, 30, 31, 4, 42, 43]),([35],[18, 21, 23, 24, 50, 46, 49, 5, 9, 11, 47, 27, 0, 32, 2, 34, 35, 36]),([11, 20, 22, 30],[15, 19, 2, 6, 9, 12, 13, 20, 3, 21, 27, 0, 30, 34, 4, 35, 38]),([11, 16, 24],[15, 19, 20, 21, 46, 47, 27, 32, 2, 34, 36, 0, 5, 8, 4, 39, 42, 43]),([33],[8, 11, 13, 14, 51, 53, 48, 49, 17, 22, 2, 36, 0, 25, 1, 27, 28, 39]),([5],[25, 26, 27, 28, 51, 54, 4, 38, 41, 43, 44, 52, 1, 5, 9, 2, 10, 3, 16, 22]),([0, 2],[51, 54, 55, 0, 35, 36, 37, 38, 4, 31, 33, 34, 52, 1, 9, 2, 10, 3, 22]),([1],[5, 6, 7, 8, 51, 53, 48, 49, 17, 22, 2, 36, 39, 1, 25, 30, 31, 4, 42, 43])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem checkFalse : verify input FalseSteps=true := by decide +kernel
theorem okFalse : IsRUPRun (PHP 5 4) (learned FalseSteps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (input_sound d hd)) checkFalse

def FinalSteps : List (List (Literal Board) × List Nat) :=
  ([([1, 22, 36, 38],[5, 6, 7, 8, 4, 18, 21, 23, 2, 24, 26, 29, 1, 32, 3, 35, 40]),([13, 24, 26],[25, 29, 30, 3, 31, 37, 40, 42, 44, 45, 0, 15, 16, 2, 9, 13, 4, 18]),([16, 18, 24, 26, 28],[3, 37, 40, 42, 2, 26, 29, 33, 44, 45, 0, 15, 1, 11, 4, 18]),([8, 10, 21],[26, 29, 1, 32, 33, 35, 39, 40, 41, 45, 0, 16, 17, 3, 12, 14, 4, 18]),([8, 10, 24, 26],[46, 1, 35, 39, 40, 3, 27, 32, 34, 41, 45, 0, 16, 2, 13, 4, 18]),([10, 18, 25],[7, 10, 12, 14, 48, 2, 36, 39, 1, 25, 0, 17, 18, 30, 31, 4, 42, 43]),([35],[18, 21, 23, 24, 50, 46, 49, 5, 9, 11, 47, 27, 0, 32, 2, 34, 35, 36]),([11, 20, 22, 30],[15, 19, 2, 6, 9, 12, 13, 20, 3, 21, 27, 0, 30, 34, 4, 35, 38]),([11, 16, 24],[15, 19, 20, 21, 46, 47, 27, 32, 2, 34, 36, 0, 5, 8, 4, 39, 42, 43]),([33],[8, 11, 13, 14, 51, 53, 48, 49, 17, 22, 2, 36, 0, 25, 1, 27, 28, 39]),([5],[25, 26, 27, 28, 51, 54, 4, 38, 41, 43, 44, 52, 1, 5, 9, 2, 10, 3, 16, 22]),([0, 2],[51, 54, 55, 0, 35, 36, 37, 38, 4, 31, 33, 34, 52, 1, 9, 2, 10, 3, 22]),([0],[51, 54, 55, 56, 15, 16, 17, 50, 46, 49, 9, 47, 32, 2, 34, 4, 36, 39, 42, 43]),([],[51, 54, 55, 57, 5, 6, 7, 53, 48, 49, 17, 22, 2, 36, 39, 1, 30, 31, 4, 42, 43])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem checkFinal : verify input FinalSteps=true := by decide +kernel
theorem okFinal : IsRUPRun (PHP 5 4) (learned FinalSteps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (input_sound d hd)) checkFinal

theorem last {c : Clause Board} {ds : List (Clause Board)} (ok : IsRUPRun (PHP 5 4) (c::ds)) :
    IsRUP (PHP 5 4 ∪ {d|d∈ds}) c := by cases ok with | learn _ h => exact h
theorem site12 : ∃ ps : List (Clause Board), IsRUPRun (PHP 5 4) ps ∧ ps.length=12 ∧
    ∀ b : Bool, IsRUP (PHP 5 4 ∪ {d | d ∈ ps}) {((0,0),b)} := by
  refine ⟨learned SharedSteps [], okShared,by decide +kernel,?_⟩
  intro b
  cases b with
  | false =>
    have e : learned FalseSteps [] = {((0,0),false)} :: learned SharedSteps [] := by decide +kernel
    exact last (e ▸ okFalse)
  | true =>
    have e : learned TrueSteps [] = {((0,0),true)} :: learned SharedSteps [] := by decide +kernel
    exact last (e ▸ okTrue)
end PEqualNP.Outside.L_meta_9246.RootBranches
