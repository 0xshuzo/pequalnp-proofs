import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9246_aux

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

def steps : List (List (Literal Board) × List Nat) :=
  ([([1, 12, 14, 22],[5, 1, 6, 7, 8, 15, 19, 2, 20, 21, 26, 32, 3, 33, 4, 37, 44]),
([1, 28, 30, 38],[5, 6, 7, 3, 8, 17, 20, 22, 24, 4, 28, 31, 1, 33, 2, 35, 39]),
([1, 13, 22],[5, 6, 7, 8, 25, 29, 2, 16, 19, 22, 23, 30, 3, 31, 4, 37, 40, 44]),
([1, 23],[5, 6, 7, 8, 36, 39, 42, 43, 46, 27, 30, 1, 15, 19, 20, 21, 4, 32, 34]),
([1],[5, 6, 7, 8, 48, 47, 45, 35, 40, 41, 46, 27, 32, 2, 16, 19, 22, 23, 4, 34])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem checked : verify input steps = true := by decide +kernel

theorem run : IsRUPRun (PHP 5 4) (learned steps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (input_sound d hd)) checked

theorem firstExpiry : ∃ (ρ : List (Clause Board)), IsRUPRun (PHP 5 4) ρ ∧
    {((0,0), false)} ∈ ρ ∧ ρ.length=5 := by
  exact ⟨_,run,by decide +kernel,by decide +kernel⟩

end PEqualNP.Outside.L_meta_9246_aux
