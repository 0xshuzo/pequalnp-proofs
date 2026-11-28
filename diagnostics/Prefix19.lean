import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9471.SwitchPrefix

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

abbrev Board := Fin 6 × Fin 5

def row (p : Fin 6) : List (Literal Board) :=
  (List.finRange 5).map (fun h => ((p, h), true))

def block (p q : Fin 6) (h : Fin 5) : List (Literal Board) :=
  [((p, h), false), ((q, h), false)]

def input : List (List (Literal Board)) :=
  (List.finRange 6).map row ++ (List.finRange 5).flatMap (fun h =>
    (List.finRange 6).flatMap (fun p =>
      ((List.finRange 6).filter (fun q => p < q)).map (fun q => block p q h)))

theorem input_sound (d : List (Literal Board)) (hd : d ∈ input) :
    d.toFinset ∈ PHP 6 5 := by
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
  ((Fin.ofNat 6 (k / 2 / 5), Fin.ofNat 5 (k / 2)), decide (k % 2 = 0))

def steps : List (List (Literal Board) × List Nat) := ([([10, 18, 20, 30, 32, 34, 38, 40, 44, 48],[3, 53, 57, 60, 63, 4, 24, 28, 1, 31, 35, 36, 41, 2, 44, 64, 67, 0, 10, 5, 77]),([2, 8, 12, 14, 16, 18, 32, 36, 38, 48],[1, 6, 11, 12, 3, 13, 14, 38, 0, 45, 48, 49, 52, 54, 4, 31, 2, 35, 55, 5, 77]),([2, 4, 8, 14, 18, 24, 42, 44, 46, 48],[4, 9, 0, 13, 16, 18, 20, 51, 1, 26, 27, 29, 52, 2, 53, 55, 75, 3, 49, 5, 77]),([0, 2, 8, 10, 12, 16, 18, 42, 48, 58],[1, 36, 0, 41, 42, 43, 44, 52, 53, 54, 4, 16, 18, 20, 55, 5, 32, 2, 34, 3, 75]),([14, 16, 18, 24, 26, 28, 30, 34, 36, 38],[3, 23, 27, 1, 6, 11, 2, 13, 14, 30]),([26, 28, 36, 40, 44, 46, 48, 54, 56, 58],[4, 24, 28, 31, 33, 35, 5, 10, 14, 17, 2, 19, 37, 41, 45, 3, 68, 0, 51, 1, 72]),([0, 2, 4, 8, 14, 32, 34, 52, 54, 58],[0, 51, 52, 53, 54, 55, 5, 14, 17, 19, 3, 20, 72, 1, 26, 28, 75, 2, 46, 4, 78]),([4, 6, 8, 10, 14, 16, 18, 54, 56, 58],[1, 21, 0, 7, 8, 9, 10, 5, 26, 27, 28, 29]),([0, 4, 6, 8, 34, 40, 44, 46, 54, 56],[0, 21, 22, 23, 24, 4, 25, 73, 76, 78, 80, 5, 14, 17, 19, 3, 57, 1, 41, 2, 60]),([8, 24, 28, 40, 44, 48, 50, 52, 54, 58],[5, 55, 59, 62, 64, 65, 4, 24, 28, 31, 2, 7, 0, 11, 15, 33, 36, 1, 38, 3, 72]),([0, 2, 6, 8, 12, 18, 20, 22, 28, 42],[0, 36, 37, 2, 38, 39, 40, 56, 1, 12, 13, 14, 60, 61, 4, 62, 78, 3, 34, 5, 80]),([20, 22, 26, 28, 40, 46, 48, 50, 56, 58],[2, 37, 41, 45, 46, 4, 24, 28, 33, 35, 5, 47]),([10, 12, 14, 18, 30, 38, 40, 42, 48, 58],[1, 51, 56, 57, 58, 4, 39, 46, 48, 3, 23, 30, 34, 50, 59, 5, 10, 0, 17, 2, 67]),([10, 16, 18, 20, 26, 28, 30, 32, 36, 38],[3, 38, 42, 1, 21, 26, 2, 28, 29, 45]),([0, 4, 6, 8, 10, 20, 24, 28, 50, 58],[0, 21, 22, 2, 23, 24, 25, 56, 60, 61, 62, 5, 44, 1, 49, 50, 72, 3, 18, 4, 73]),([10, 14, 20, 22, 24, 28, 30, 34, 38, 50],[2, 52, 56, 60, 3, 23, 27, 1, 33, 34, 61, 62, 66, 73, 74, 5, 40, 0, 9, 4, 50]),([0, 2, 4, 6, 22, 24, 26, 32, 34, 36],[0, 66, 67, 2, 11, 15, 3, 16, 17, 68]),([2, 4, 6, 8, 32, 34, 36, 38],[0, 3, 6, 7, 8]),([42, 44, 46, 48, 52, 54, 56, 58],[4, 5, 9, 13, 16, 18, 20])] : List (List Nat × List Nat)).map (fun t => (t.1.map readLiteral,t.2))

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
theorem prefixRun : IsRUPRun (PHP 6 5) (learned steps []) :=
  verify_sound (PHP 6 5) steps input [] .nil (fun d hd => Or.inl (input_sound d hd)) (by decide +kernel)
theorem nineteen : (learned steps []).length=19 := by decide +kernel

end PEqualNP.Outside.L_meta_9471.SwitchPrefix
