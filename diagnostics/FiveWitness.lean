import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9248.FreeFive

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

def initial : List (List (Literal Board) × List Nat) := ([([2, 10, 14, 37], [28, 31, 1, 5, 0, 9, 10, 11, 33, 34, 36, 2, 22, 3, 23, 37]),
([20, 22, 26, 28, 30, 38], [3, 7, 10, 12, 2, 14, 16, 19, 23, 4, 28, 0, 31, 1, 35]),
([6, 13, 26, 30], [25, 29, 30, 3, 7, 0, 10, 12, 14, 15, 16, 2, 18, 31, 4, 39, 43]),
([4, 6, 27, 38], [17, 0, 5, 6, 7, 8, 20, 22, 24, 4, 31, 1, 33, 2, 34, 39]),
([12, 14, 27, 38], [17, 20, 1, 5, 9, 10, 11, 22, 24, 4, 28, 0, 33, 2, 34, 36]),
([20, 22, 27, 38], [17, 20, 22, 2, 6, 9, 12, 13, 24, 4, 28, 0, 31, 1, 34, 35]),
([7, 8, 10, 18], [35, 1, 25, 29, 30, 31, 36, 2, 6, 12, 13, 37, 3, 17, 24, 4, 38]),
([8, 10, 18, 31], [37, 40, 1, 25, 29, 30, 31, 42, 2, 6, 0, 12, 13, 17, 18, 4, 44]),
([0, 2, 8, 23], [36, 0, 25, 26, 27, 28, 39, 1, 19, 20, 21, 42, 3, 12, 14, 4, 43]),
([0, 2, 8, 31], [37, 0, 25, 26, 27, 28, 40, 1, 19, 20, 21, 42, 2, 12, 13, 4, 44]),
([0, 2, 8, 39], [38, 0, 25, 26, 27, 28, 41, 1, 19, 20, 21, 43, 2, 12, 3, 13, 44]),
([0, 2, 8, 21], [26, 0, 29, 32, 33, 35, 1, 19, 20, 21, 36, 37, 3, 12, 14, 4, 38]),
([0, 15, 16, 18], [35, 39, 2, 26, 0, 15, 17, 18, 29, 32, 33, 40, 3, 10, 14, 4, 41]),
([0, 16, 18, 31], [37, 40, 42, 2, 26, 0, 15, 17, 18, 29, 1, 10, 11, 32, 33, 4, 44]),
([0, 16, 18, 39], [38, 41, 43, 2, 26, 0, 15, 17, 18, 29, 1, 10, 11, 32, 3, 33, 44]),
([0, 13, 16, 18], [25, 29, 2, 30, 31, 36, 0, 15, 17, 18, 39, 42, 3, 10, 14, 4, 43]),
([7, 8, 16, 18], [35, 36, 2, 26, 29, 1, 15, 20, 21, 32, 33, 37, 3, 7, 14, 4, 38]),
([8, 16, 18, 31], [37, 40, 42, 2, 26, 29, 1, 15, 0, 7, 8, 20, 21, 32, 33, 4, 44]),
([8, 16, 18, 39], [38, 41, 43, 2, 26, 29, 1, 15, 0, 7, 8, 20, 21, 32, 3, 33, 44]),
([5, 8, 16, 18], [25, 26, 2, 27, 28, 36, 39, 1, 15, 20, 21, 42, 3, 7, 14, 4, 43]),
([2, 15, 32, 34], [35, 39, 40, 41, 4, 28, 0, 5, 6, 7, 31, 33, 2, 19, 22, 3, 34])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def steps : List (List (Literal Board) × List Nat) := ([([0, 2, 8], [53, 54, 55, 56, 50, 46, 27, 0, 30, 34, 35, 1, 19, 2, 12, 13, 4, 21]),
([0, 8], [66, 15, 16, 17, 18, 51, 52, 47, 1, 39, 41, 57, 12, 3, 13, 4, 27, 32, 34]),
([19, 32], [16, 19, 22, 23, 65, 45, 4, 38, 43, 44, 47, 1, 5, 0, 9, 10, 3, 26, 27]),
([1], [5, 6, 7, 8, 68, 61, 62, 63, 64, 48, 3, 30, 32, 2, 34, 4, 18, 21, 1, 39]),
([], [69, 67, 9, 10, 11, 68, 57, 58, 59, 60, 49, 3, 27, 32, 2, 34, 4, 18, 0, 21, 36])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))

def Free : Set (Clause Board) := PHP 5 4 ∪ {c | IsRUP (PHP 5 4) c}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem localCert : initial.all (fun p => replay input p.1 p.2) = true := by decide +kernel

theorem freeInput (d : List (Literal Board)) (hd : d∈input ++ initial.map Prod.fst) : d.toFinset∈Free := by
  rcases List.mem_append.mp hd with old|new
  · exact Or.inl (input_sound _ old)
  · obtain ⟨p,hp,eq⟩ := List.mem_map.mp new
    subst d
    apply Or.inr
    apply replay_sound input (PHP 5 4) _ input_sound p.2 p.1 _ ((List.all_eq_true.mp localCert) _ hp)
    intro l hl
    exact UPForces.hyp ⟨l,List.mem_toFinset.mpr hl,rfl⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem checks : verify (input ++ initial.map Prod.fst) steps = true := by decide +kernel

theorem five : ∃ cs, IsRUPRun Free cs ∧ (∅ : Clause Board)∈cs ∧ cs.length=5 := by
  refine ⟨learned steps [],verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (freeInput d hd)) checks,?_,?_⟩ <;> decide +kernel

end PEqualNP.Outside.L_meta_9248.FreeFive
