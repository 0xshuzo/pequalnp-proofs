import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9246.RowProfile

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


def s1 : List (List (Literal Board) × List Nat) :=
  ([([2, 14, 21],[26, 29, 32, 33, 45, 0, 5, 1, 6, 7, 8, 19, 20, 3, 21, 4, 42, 44]),
([2, 30, 37],[28, 31, 33, 34, 45, 0, 5, 6, 7, 3, 8, 20, 1, 22, 2, 24, 39]),
([0, 24, 37],[28, 31, 33, 34, 45, 0, 15, 16, 17, 3, 18, 40, 1, 9, 2, 11, 42]),
([24, 28, 35],[18, 21, 23, 24, 3, 37, 40, 42, 44, 46, 2, 6, 0, 9, 1, 13, 25]),
([24, 28, 32, 36],[45, 49, 4, 41, 43, 44, 3, 17, 20, 22, 46, 2, 6, 0, 9, 1, 25]),
([4, 28, 33],[8, 11, 13, 14, 45, 0, 15, 16, 17, 3, 18, 40, 1, 29, 2, 31, 42]),
([21],[26, 29, 32, 33, 45, 51, 50, 7, 0, 10, 12, 15, 1, 16, 17, 18, 4, 39, 40, 41]),
([13],[25, 29, 30, 31, 45, 51, 50, 7, 0, 10, 12, 15, 16, 2, 17, 18, 4, 39, 42, 43]),
([17],[6, 9, 12, 13, 45, 48, 50, 27, 0, 15, 16, 17, 18, 4, 30, 1, 32, 39, 40, 41]),
([9],[5, 9, 10, 11, 45, 48, 50, 27, 0, 15, 16, 17, 18, 4, 30, 32, 2, 39, 42, 43]),
([23],[36, 39, 42, 43, 52, 53, 54, 55, 1, 15, 19, 20, 21, 47, 4, 8, 0, 14, 3, 27]),
([],[45, 52, 53, 54, 55, 56, 2, 16, 19, 1, 22, 23, 40, 41, 47, 4, 8, 0, 14, 3, 27])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def actual1 : List (List (Literal Board)) :=
  input ++ ([7] : List Nat).map (fun j => [readLiteral j])
def conditioned1 : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈([7] : List Nat), d = {readLiteral x}}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem pass1 : verify actual1 s1 = true := by decide +kernel
theorem profile1 : ∃ ρ : List (Clause Board), IsRUPRun conditioned1 ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length=12 := by
  refine ⟨learned s1 [], verify_sound _ _ _ _ IsRUPRun.nil ?_ pass1,by decide +kernel,by decide +kernel⟩
  intro d m
  apply Or.inl
  rcases List.mem_append.mp m with m|m
  · exact Or.inl (input_sound _ m)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m
    exact Or.inr ⟨j,hj,by simp⟩

def s2 : List (List (Literal Board) × List Nat) :=
  ([([12, 19],[16, 19, 22, 23, 45, 46, 0, 5, 1, 6, 7, 8, 39, 40, 3, 32, 34, 4, 41]),
([19],[16, 19, 22, 23, 45, 46, 0, 5, 6, 7, 8, 47, 29, 30, 3, 31, 4, 40, 42, 44]),
([24, 26, 37],[28, 31, 33, 34, 3, 37, 40, 42, 44, 47, 2, 6, 0, 9, 1, 13, 15]),
([30, 35],[18, 21, 23, 24, 45, 46, 0, 5, 6, 7, 3, 8, 30, 1, 32, 2, 34, 39]),
([20, 22],[45, 46, 48, 2, 6, 0, 9, 12, 13, 15, 17, 18, 49, 4, 41, 1, 30, 3, 44]),
([15],[35, 39, 40, 41, 45, 48, 50, 51, 29, 32, 33, 4, 8, 0, 11, 13, 14, 3, 15, 17]),
([13],[25, 29, 30, 31, 46, 48, 51, 39, 42, 43, 50, 4, 8, 0, 11, 13, 14, 3, 15, 17]),
([11],[15, 19, 20, 21, 45, 46, 0, 5, 6, 7, 8, 49, 4, 41, 43, 2, 29, 32, 3, 44]),
([],[45, 46, 48, 52, 53, 54, 1, 5, 0, 9, 10, 11, 17, 18, 49, 4, 43, 2, 32, 3, 44])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def actual2 : List (List (Literal Board)) :=
  input ++ ([5,7] : List Nat).map (fun j => [readLiteral j])
def conditioned2 : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈([5,7] : List Nat), d = {readLiteral x}}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem pass2 : verify actual2 s2 = true := by decide +kernel
theorem profile2 : ∃ ρ : List (Clause Board), IsRUPRun conditioned2 ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length=9 := by
  refine ⟨learned s2 [], verify_sound _ _ _ _ IsRUPRun.nil ?_ pass2,by decide +kernel,by decide +kernel⟩
  intro d m
  apply Or.inl
  rcases List.mem_append.mp m with m|m
  · exact Or.inl (input_sound _ m)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m
    exact Or.inr ⟨j,hj,by simp⟩

def s3 : List (List (Literal Board) × List Nat) :=
  ([([12, 14, 22],[45, 46, 47, 0, 5, 1, 6, 7, 8, 19, 2, 20, 21, 32, 3, 33, 4, 44]),
([28, 30, 38],[45, 46, 47, 0, 5, 6, 7, 3, 8, 20, 22, 24, 4, 31, 1, 33, 2, 39]),
([13, 22],[25, 29, 30, 31, 45, 47, 0, 5, 6, 2, 7, 8, 19, 22, 3, 23, 4, 40, 44]),
([23],[36, 39, 42, 43, 45, 46, 0, 5, 6, 7, 8, 49, 30, 1, 19, 20, 21, 4, 32, 34]),
([],[45, 46, 47, 0, 5, 6, 7, 8, 51, 50, 48, 40, 41, 49, 32, 2, 19, 22, 23, 4, 34])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def actual3 : List (List (Literal Board)) :=
  input ++ ([3,5,7] : List Nat).map (fun j => [readLiteral j])
def conditioned3 : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈([3,5,7] : List Nat), d = {readLiteral x}}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem pass3 : verify actual3 s3 = true := by decide +kernel
theorem profile3 : ∃ ρ : List (Clause Board), IsRUPRun conditioned3 ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length=5 := by
  refine ⟨learned s3 [], verify_sound _ _ _ _ IsRUPRun.nil ?_ pass3,by decide +kernel,by decide +kernel⟩
  intro d m
  apply Or.inl
  rcases List.mem_append.mp m with m|m
  · exact Or.inl (input_sound _ m)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m
    exact Or.inr ⟨j,hj,by simp⟩

end PEqualNP.Outside.L_meta_9246.RowProfile
