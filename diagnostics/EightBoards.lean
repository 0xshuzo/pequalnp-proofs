import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9248.EightBoards

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


def nums0 : List Nat := [3, 5, 7]
def data0 : List (List (Literal Board) × List Nat) :=
  ([([20, 22, 30], [45, 46, 47, 0, 5, 6, 2, 7, 8, 19, 22, 3, 23, 30, 1, 34, 4, 41]), ([15], [35, 39, 40, 41, 45, 46, 0, 5, 6, 7, 8, 48, 29, 32, 3, 20, 22, 24, 4, 33]), ([37], [28, 31, 33, 34, 45, 47, 0, 5, 6, 7, 8, 49, 1, 19, 2, 20, 3, 21, 42]), ([34], [45, 46, 47, 0, 5, 6, 7, 8, 49, 50, 4, 43, 44, 48, 29, 1, 19, 20, 3, 32]), ([], [45, 46, 47, 0, 5, 6, 7, 8, 49, 50, 51, 21, 1, 23, 24, 29, 2, 30, 3, 42])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def actual0 : List (List (Literal Board)) := input ++ nums0.map (fun j => [readLiteral j])
def conditioned0 : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈nums0, d = {readLiteral x}}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem pass0 : verify actual0 data0 = true := by decide +kernel
theorem profile0 : ∃ ρ : List (Clause Board), IsRUPRun conditioned0 ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length≤5 := by
  refine ⟨learned data0 [], verify_sound _ _ _ _ IsRUPRun.nil ?_ pass0,by decide +kernel,by decide +kernel⟩
  intro d m
  apply Or.inl
  rcases List.mem_append.mp m with m|m
  · exact Or.inl (input_sound _ m)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m
    exact Or.inr ⟨j,hj,by simp⟩
def nums1 : List Nat := [3, 5, 6]
def data1 : List (List (Literal Board) × List Nat) :=
  ([([18, 20, 28], [45, 46, 47, 35, 36, 2, 6, 9, 12, 13, 37, 3, 20, 1, 24, 31, 4, 38]), ([13], [25, 29, 30, 31, 45, 47, 35, 36, 37, 38, 48, 19, 22, 3, 7, 10, 12, 14, 4, 23]), ([35], [18, 21, 23, 24, 46, 47, 35, 36, 37, 38, 49, 1, 5, 9, 2, 10, 3, 11, 32]), ([32], [45, 46, 47, 35, 36, 37, 38, 49, 50, 4, 33, 34, 48, 19, 1, 5, 9, 10, 3, 22]), ([], [45, 46, 47, 35, 36, 37, 38, 49, 50, 51, 8, 11, 1, 13, 14, 19, 2, 20, 3, 32])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def actual1 : List (List (Literal Board)) := input ++ nums1.map (fun j => [readLiteral j])
def conditioned1 : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈nums1, d = {readLiteral x}}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem pass1 : verify actual1 data1 = true := by decide +kernel
theorem profile1 : ∃ ρ : List (Clause Board), IsRUPRun conditioned1 ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length≤5 := by
  refine ⟨learned data1 [], verify_sound _ _ _ _ IsRUPRun.nil ?_ pass1,by decide +kernel,by decide +kernel⟩
  intro d m
  apply Or.inl
  rcases List.mem_append.mp m with m|m
  · exact Or.inl (input_sound _ m)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m
    exact Or.inr ⟨j,hj,by simp⟩
def nums2 : List Nat := [3, 4, 7]
def data2 : List (List (Literal Board) × List Nat) :=
  ([([18, 22, 30], [45, 46, 25, 26, 2, 6, 9, 12, 13, 27, 3, 20, 1, 24, 28, 4, 35, 41]), ([15], [35, 39, 40, 41, 45, 46, 25, 26, 27, 28, 48, 19, 22, 3, 7, 10, 12, 14, 4, 23]), ([35], [18, 21, 23, 24, 46, 25, 26, 27, 28, 47, 49, 1, 5, 9, 2, 10, 3, 11, 42]), ([32], [45, 46, 25, 26, 27, 28, 47, 49, 50, 4, 43, 44, 48, 19, 1, 5, 9, 10, 3, 22]), ([], [45, 46, 25, 26, 27, 28, 47, 49, 50, 51, 8, 11, 1, 13, 14, 19, 2, 20, 3, 42])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def actual2 : List (List (Literal Board)) := input ++ nums2.map (fun j => [readLiteral j])
def conditioned2 : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈nums2, d = {readLiteral x}}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem pass2 : verify actual2 data2 = true := by decide +kernel
theorem profile2 : ∃ ρ : List (Clause Board), IsRUPRun conditioned2 ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length≤5 := by
  refine ⟨learned data2 [], verify_sound _ _ _ _ IsRUPRun.nil ?_ pass2,by decide +kernel,by decide +kernel⟩
  intro d m
  apply Or.inl
  rcases List.mem_append.mp m with m|m
  · exact Or.inl (input_sound _ m)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m
    exact Or.inr ⟨j,hj,by simp⟩
def nums3 : List Nat := [3, 4, 6]
def data3 : List (List (Literal Board) × List Nat) :=
  ([([18, 22, 30], [45, 46, 25, 26, 2, 6, 9, 12, 13, 27, 3, 20, 1, 24, 28, 4, 35, 41]), ([15], [35, 39, 40, 41, 45, 46, 25, 26, 27, 28, 47]), ([35], [18, 21, 23, 24, 46, 25, 26, 27, 28, 47, 35, 1, 5, 9, 2, 10, 3, 11, 36]), ([32], [45, 46, 25, 26, 27, 28, 47, 35, 36, 37, 38, 4, 21, 1, 5, 9, 2, 10, 3, 22]), ([], [45, 46, 25, 26, 27, 28, 47, 35, 36, 37, 38, 48, 19, 1, 5, 9, 10, 3, 11, 4, 22])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def actual3 : List (List (Literal Board)) := input ++ nums3.map (fun j => [readLiteral j])
def conditioned3 : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈nums3, d = {readLiteral x}}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem pass3 : verify actual3 data3 = true := by decide +kernel
theorem profile3 : ∃ ρ : List (Clause Board), IsRUPRun conditioned3 ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length≤5 := by
  refine ⟨learned data3 [], verify_sound _ _ _ _ IsRUPRun.nil ?_ pass3,by decide +kernel,by decide +kernel⟩
  intro d m
  apply Or.inl
  rcases List.mem_append.mp m with m|m
  · exact Or.inl (input_sound _ m)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m
    exact Or.inr ⟨j,hj,by simp⟩
def nums4 : List Nat := [2, 5, 7]
def data4 : List (List (Literal Board) × List Nat) :=
  ([([20, 22, 30], [45, 15, 16, 2, 6, 9, 12, 13, 17, 3, 18, 27, 30, 1, 34, 4, 35, 41]), ([15], [35, 39, 40, 41, 45, 15, 16, 17, 18, 46, 48, 29, 32, 3, 7, 10, 12, 14, 4, 33]), ([37], [28, 31, 33, 34, 45, 15, 16, 17, 18, 47, 49, 1, 5, 9, 2, 10, 3, 11, 42]), ([32], [45, 15, 16, 17, 18, 46, 47, 49, 50, 4, 43, 44, 48, 29, 1, 5, 9, 10, 3, 32]), ([], [45, 15, 16, 17, 18, 46, 47, 49, 50, 51, 8, 11, 1, 13, 14, 29, 2, 30, 3, 42])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def actual4 : List (List (Literal Board)) := input ++ nums4.map (fun j => [readLiteral j])
def conditioned4 : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈nums4, d = {readLiteral x}}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem pass4 : verify actual4 data4 = true := by decide +kernel
theorem profile4 : ∃ ρ : List (Clause Board), IsRUPRun conditioned4 ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length≤5 := by
  refine ⟨learned data4 [], verify_sound _ _ _ _ IsRUPRun.nil ?_ pass4,by decide +kernel,by decide +kernel⟩
  intro d m
  apply Or.inl
  rcases List.mem_append.mp m with m|m
  · exact Or.inl (input_sound _ m)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m
    exact Or.inr ⟨j,hj,by simp⟩
def nums5 : List Nat := [2, 5, 6]
def data5 : List (List (Literal Board) × List Nat) :=
  ([([20, 22, 30], [45, 15, 16, 2, 6, 9, 12, 13, 17, 3, 18, 27, 30, 1, 34, 4, 35, 41]), ([15], [35, 39, 40, 41, 45, 15, 16, 17, 18, 46, 47]), ([37], [28, 31, 33, 34, 45, 15, 16, 17, 18, 47, 35, 1, 5, 9, 2, 10, 3, 11, 36]), ([32], [45, 15, 16, 17, 18, 46, 47, 35, 36, 37, 38, 4, 31, 1, 5, 9, 2, 10, 3, 32]), ([], [45, 15, 16, 17, 18, 46, 47, 35, 36, 37, 38, 48, 29, 1, 5, 9, 10, 3, 11, 4, 32])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def actual5 : List (List (Literal Board)) := input ++ nums5.map (fun j => [readLiteral j])
def conditioned5 : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈nums5, d = {readLiteral x}}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem pass5 : verify actual5 data5 = true := by decide +kernel
theorem profile5 : ∃ ρ : List (Clause Board), IsRUPRun conditioned5 ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length≤5 := by
  refine ⟨learned data5 [], verify_sound _ _ _ _ IsRUPRun.nil ?_ pass5,by decide +kernel,by decide +kernel⟩
  intro d m
  apply Or.inl
  rcases List.mem_append.mp m with m|m
  · exact Or.inl (input_sound _ m)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m
    exact Or.inr ⟨j,hj,by simp⟩
def nums6 : List Nat := [2, 4, 7]
def data6 : List (List (Literal Board) × List Nat) :=
  ([([20, 22, 30], [45, 15, 16, 2, 6, 9, 12, 13, 17, 3, 18, 27, 30, 1, 34, 4, 35, 41]), ([15], [35, 39, 40, 41, 45, 15, 16, 17, 18, 46, 25, 26, 2, 6, 9, 12, 3, 13, 4, 27]), ([37], [28, 31, 33, 34, 45, 15, 16, 17, 18, 46]), ([32], [45, 15, 16, 17, 18, 46, 25, 26, 27, 28, 4, 38, 41, 1, 5, 9, 2, 10, 3, 42]), ([], [45, 15, 16, 17, 18, 46, 25, 26, 27, 28, 47, 49, 1, 5, 9, 2, 10, 3, 11, 4, 42])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def actual6 : List (List (Literal Board)) := input ++ nums6.map (fun j => [readLiteral j])
def conditioned6 : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈nums6, d = {readLiteral x}}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem pass6 : verify actual6 data6 = true := by decide +kernel
theorem profile6 : ∃ ρ : List (Clause Board), IsRUPRun conditioned6 ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length≤5 := by
  refine ⟨learned data6 [], verify_sound _ _ _ _ IsRUPRun.nil ?_ pass6,by decide +kernel,by decide +kernel⟩
  intro d m
  apply Or.inl
  rcases List.mem_append.mp m with m|m
  · exact Or.inl (input_sound _ m)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m
    exact Or.inr ⟨j,hj,by simp⟩
def nums7 : List Nat := [2, 4, 6]
def data7 : List (List (Literal Board) × List Nat) :=
  ([([20, 22, 30], [45, 15, 16, 2, 6, 9, 12, 13, 17, 3, 18, 27, 30, 1, 34, 4, 35, 41]), ([15], [35, 39, 40, 41, 45, 15, 16, 17, 18, 46, 25, 26, 2, 6, 9, 12, 3, 13, 4, 27]), ([37], [28, 31, 33, 34, 45, 15, 16, 17, 18, 46]), ([32], [45, 15, 16, 17, 18, 46, 25, 26, 27, 28, 4, 38, 41, 1, 5, 9, 2, 10, 3, 42]), ([], [45, 15, 16, 17, 18, 46, 25, 26, 27, 28, 47, 35, 1, 5, 9, 2, 10, 3, 11, 4, 36])] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral,p.2))
def actual7 : List (List (Literal Board)) := input ++ nums7.map (fun j => [readLiteral j])
def conditioned7 : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈nums7, d = {readLiteral x}}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem pass7 : verify actual7 data7 = true := by decide +kernel
theorem profile7 : ∃ ρ : List (Clause Board), IsRUPRun conditioned7 ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length≤5 := by
  refine ⟨learned data7 [], verify_sound _ _ _ _ IsRUPRun.nil ?_ pass7,by decide +kernel,by decide +kernel⟩
  intro d m
  apply Or.inl
  rcases List.mem_append.mp m with m|m
  · exact Or.inl (input_sound _ m)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m
    exact Or.inr ⟨j,hj,by simp⟩
def pins : List Board := [(0,1),(0,2),(0,3)]
def conditional (b : Board → Bool) : Set (Clause Board) := PHP 5 4 ∪ {d | ∃ x∈pins, d={(x,b x)}}
theorem uniform (b : Board → Bool) : ∃ ρ : List (Clause Board), IsRUPRun (conditional b) ρ ∧
    (∅ : Clause Board)∈ρ ∧ ρ.length≤5 := by
  cases h1 : b (0,1) <;> cases h2 : b (0,2) <;> cases h3 : b (0,3)
  · have eq : conditional b = conditioned0 := by
      ext d
      simp [conditional,conditioned0,nums0,pins,readLiteral,h1,h2,h3]
    rw [eq]
    exact profile0
  · have eq : conditional b = conditioned1 := by
      ext d
      simp [conditional,conditioned1,nums1,pins,readLiteral,h1,h2,h3]
    rw [eq]
    exact profile1
  · have eq : conditional b = conditioned2 := by
      ext d
      simp [conditional,conditioned2,nums2,pins,readLiteral,h1,h2,h3]
    rw [eq]
    exact profile2
  · have eq : conditional b = conditioned3 := by
      ext d
      simp [conditional,conditioned3,nums3,pins,readLiteral,h1,h2,h3]
    rw [eq]
    exact profile3
  · have eq : conditional b = conditioned4 := by
      ext d
      simp [conditional,conditioned4,nums4,pins,readLiteral,h1,h2,h3]
    rw [eq]
    exact profile4
  · have eq : conditional b = conditioned5 := by
      ext d
      simp [conditional,conditioned5,nums5,pins,readLiteral,h1,h2,h3]
    rw [eq]
    exact profile5
  · have eq : conditional b = conditioned6 := by
      ext d
      simp [conditional,conditioned6,nums6,pins,readLiteral,h1,h2,h3]
    rw [eq]
    exact profile6
  · have eq : conditional b = conditioned7 := by
      ext d
      simp [conditional,conditioned7,nums7,pins,readLiteral,h1,h2,h3]
    rw [eq]
    exact profile7
end PEqualNP.Outside.L_meta_9248.EightBoards
