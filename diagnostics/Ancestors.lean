import PEqualNP.Defs

namespace PCX150
open PEqualNP.ProofComplexity

abbrev IndexedClause := Clause (Fin 4 × Fin 3)

/-- Parents are physical lines, identified by their position in the newest-first list. -/
inductive LineReason (F : Set IndexedClause) (rows : List IndexedClause)
    (k : Nat) (R : IndexedClause) : Type where
  | ax (member : R ∈ F)
  | res (i j : Nat) (C D : IndexedClause)
      (earlierLeft : k < i) (earlierRight : k < j)
      (leftLine : rows[i]? = some C) (rightLine : rows[j]? = some D)
      (resolve : IsResolvent C D R)

private theorem address {rows : List IndexedClause} {C : IndexedClause}
    (h : C ∈ rows) : ∃ i : Nat, rows[i]? = some C := by
  induction rows with
  | nil => simp at h
  | cons r rows ih =>
    rcases List.mem_cons.mp h with eq | tail
    · subst r
      exact ⟨0, rfl⟩
    · obtain ⟨i, hi⟩ := ih tail
      exact ⟨i+1, by simpa using hi⟩

private def shiftReason {F rows k R} (x : LineReason F rows k R) (newest : IndexedClause) :
    LineReason F (newest :: rows) (k+1) R := by
  cases x with
  | ax h => exact .ax h
  | res i j C D hi hj hC hD step =>
    exact .res (i+1) (j+1) C D (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj)
      (by simpa using hC) (by simpa using hD) step

private theorem extendReasons {F rows R}
    (front : Nonempty (LineReason F (R :: rows) 0 R))
    (old : ∀ k C, rows[k]? = some C → Nonempty (LineReason F rows k C)) :
    ∀ k C, (R :: rows)[k]? = some C → Nonempty (LineReason F (R :: rows) k C) := by
  intro k C h
  cases k with
  | zero =>
    have eq : R = C := Option.some.inj h
    subst C
    exact front
  | succ k =>
    obtain ⟨reason⟩ := old k C (by simpa using h)
    exact ⟨shiftReason reason R⟩

theorem indexedDerivation {F : Set IndexedClause} {rows : List IndexedClause}
    (h : IsDerivation F rows) :
    ∀ k C, rows[k]? = some C → Nonempty (LineReason F rows k C) := by
  induction h with
  | nil => simp
  | ax _ mem ih => exact extendReasons ⟨.ax mem⟩ ih
  | res _ left right step ih =>
    obtain ⟨i, hi⟩ := address left
    obtain ⟨j, hj⟩ := address right
    exact extendReasons ⟨.res (i+1) (j+1) _ _ (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      (by simpa using hi) (by simpa using hj) step⟩ ih

theorem indexedRefutation {F : Set IndexedClause} {rows : List IndexedClause}
    (h : IsRefutation F rows) :
    ∃ root : Nat, rows[root]? = some ∅ ∧
      Nonempty ((i : Fin rows.length) → LineReason F rows i.val rows[i.val]) := by
  obtain ⟨root, hr⟩ := address h.2
  refine ⟨root, hr, ⟨fun i => Classical.choice (indexedDerivation h.1 i.val rows[i.val] ?_)⟩⟩
  simp [i.isLt]

end PCX150

namespace PCX150

def LineReason.parents {F rows k R} : LineReason F rows k R → List Nat
  | .ax _ => []
  | .res i j _ _ _ _ _ _ _ => [i,j]

theorem LineReason.parentIndex {F rows k R} (r : LineReason F rows k R)
    {i : Nat} (h : i ∈ r.parents) : k < i ∧ i < rows.length := by
  cases r with
  | ax _ => simp [LineReason.parents] at h
  | res a b C D ha hb hC hD _ =>
    simp only [LineReason.parents, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · subst i
      exact ⟨ha, by by_contra! hn; simp [List.getElem?_eq_none hn] at hC⟩
    · subst i
      exact ⟨hb, by by_contra! hn; simp [List.getElem?_eq_none hn] at hD⟩

section
variable (parent : Nat → List Nat) (root : Nat)

inductive LiveLine : Nat → Prop where
  | rootLine : LiveLine root
  | parentLine {k p} : LiveLine k → p ∈ parent k → LiveLine p

theorem liveReader {p} (h : LiveLine parent root p) (ne : p ≠ root) :
    ∃ k, LiveLine parent root k ∧ p ∈ parent k := by
  cases h with
  | rootLine => contradiction
  | parentLine hk hm => exact ⟨_,hk,hm⟩

variable {parent root}
theorem liveAfterRoot (forward : ∀ k p, p ∈ parent k → k < p)
    {k} (hk : LiveLine parent root k) : root ≤ k := by
  induction hk with
  | rootLine => exact Nat.le_refl _
  | parentLine _ hp ih => exact Nat.le_trans ih (Nat.le_of_lt (forward _ _ hp))

theorem rootUnread (forward : ∀ k p, p ∈ parent k → k < p)
    {k} (h : LiveLine parent root k) : root ∉ parent k := by
  intro hp
  exact Nat.not_lt_of_ge (liveAfterRoot forward h) (forward _ _ hp)

noncomputable def linesUsed (parent : Nat → List Nat) (root n : Nat) : Finset Nat := by
  classical
  exact (Finset.range n).filter (LiveLine parent root)

theorem linesUsed_spec {root k n : Nat} {parent : Nat → List Nat} :
    k ∈ linesUsed parent root n ↔ k < n ∧ LiveLine parent root k := by
  classical
  simp [linesUsed]

/-- Retaining exactly the ancestor lines preserves both inputs to every retained rule. -/
theorem parentsRetained {n : Nat} (bounded : ∀ k p, k < n → p ∈ parent k → p < n)
    {k p} (hk : k ∈ linesUsed parent root n) (hp : p ∈ parent k) :
    p ∈ linesUsed parent root n := by
  obtain ⟨hkn, hk'⟩ := linesUsed_spec.mp hk
  exact linesUsed_spec.mpr ⟨bounded _ _ hkn hp, .parentLine hk' hp⟩

end
end PCX150



namespace PCX150
open PEqualNP.ProofComplexity
abbrev SelectClause := Clause (Fin 4 × Fin 3)

def keepLines (keep : Nat → Bool) : List SelectClause → List SelectClause
  | [] => []
  | x :: xs =>
    let tail := keepLines (fun k => keep (k+1)) xs
    if keep 0 then x :: tail else tail

theorem keepLines_length (keep : Nat → Bool) (rows : List SelectClause) :
    (keepLines keep rows).length ≤ rows.length := by
  induction rows generalizing keep with
  | nil => simp [keepLines]
  | cons x xs ih =>
    have h := ih (fun k => keep (k+1))
    cases hb : keep 0 <;> simp [keepLines, hb] <;> omega

theorem keepLines_member {rows : List SelectClause} {keep : Nat → Bool} {k C}
    (atK : rows[k]? = some C) (on : keep k = true) : C ∈ keepLines keep rows := by
  induction rows generalizing keep k with
  | nil => simp at atK
  | cons x xs ih =>
    cases k with
    | zero =>
      have eq : x = C := Option.some.inj atK
      simp [keepLines, on, eq]
    | succ k =>
      have tail := ih (keep := fun j => keep (j+1)) (k := k) (by simpa using atK) on
      cases hb : keep 0 <;> simp [keepLines, hb, tail]

/-- Retained rows have retained witnesses in the original suffix. Offsets count
    from the first row strictly after the rule's conclusion. -/
def RetainedRules (F : Set SelectClause) (keep : Nat → Bool) (rows : List SelectClause) : Prop :=
  ∀ k R, rows[k]? = some R → keep k = true →
    R ∈ F ∨ ∃ a b C D, rows[k+1+a]? = some C ∧ rows[k+1+b]? = some D ∧
      keep (k+1+a) = true ∧ keep (k+1+b) = true ∧ IsResolvent C D R

theorem keepLines_derives {F : Set SelectClause} {keep rows}
    (rules : RetainedRules F keep rows) : IsDerivation F (keepLines keep rows) := by
  induction rows generalizing keep with
  | nil => exact .nil
  | cons x xs ih =>
    let later := fun k => keep (k+1)
    have tail : RetainedRules F later xs := by
      intro k R h hk
      rcases rules (k+1) R (by simpa using h) hk with raw | step
      · exact Or.inl raw
      · obtain ⟨a,b,C,D,ha,hb,ka,kb,hR⟩ := step
        have eqA : k + 1 + 1 + a = (k + 1 + a) + 1 := by omega
        have eqB : k + 1 + 1 + b = (k + 1 + b) + 1 := by omega
        rw [eqA] at ha
        rw [eqB] at hb
        exact Or.inr ⟨a,b,C,D,by simpa using ha,
          by simpa using hb,by simpa [later,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ka,
          by simpa [later,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using kb,hR⟩
    have d := ih tail
    cases hx : keep 0 with
    | false => simpa [keepLines,hx,later] using d
    | true =>
      simp only [keepLines,hx,if_true]
      rcases rules 0 x rfl hx with raw | step
      · exact .ax d raw
      · obtain ⟨a,b,C,D,ha,hb,ka,kb,hR⟩ := step
        have hC : xs[a]? = some C := by simpa [Nat.succ_add] using ha
        have hD : xs[b]? = some D := by simpa [Nat.succ_add] using hb
        have u : later a = true := by simpa [later,Nat.add_comm] using ka
        have v : later b = true := by simpa [later,Nat.add_comm] using kb
        exact .res d (keepLines_member hC u) (keepLines_member hD v) hR

end PCX150

namespace PCX150
open PEqualNP.ProofComplexity
abbrev Choices (F : Set IndexedClause) (rows : List IndexedClause) :=
  (i : Fin rows.length) → LineReason F rows i.val rows[i.val]

def parentsAt {F rows} (why : Choices F rows) (k : Nat) : List Nat :=
  if h : k < rows.length then (why ⟨k,h⟩).parents else []

theorem edgesForward {F rows} (why : Choices F rows) (k p : Nat)
    (h : p ∈ parentsAt why k) : k < p ∧ p < rows.length := by
  unfold parentsAt at h
  split at h
  next hk => exact (why ⟨k,hk⟩).parentIndex h
  next => simp at h

private theorem lookupIndex {rows : List IndexedClause} {k : Nat} {R}
    (h : rows[k]? = some R) : ∃ hk : k < rows.length, rows[k] = R := by
  by_cases hk : k < rows.length
  · exact ⟨hk,by simpa [hk] using h⟩
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt hk)] at h

theorem trimmedCertificate {F : Set IndexedClause} {rows root} (hr : rows[root]? = some ∅)
    (why : Choices F rows) :
    ∃ (keep : Nat → Bool), IsRefutation F (keepLines keep rows) ∧
      (keepLines keep rows).length ≤ rows.length ∧
      ∀ k, keep k = true ↔ k ∈ linesUsed (parentsAt why) root rows.length := by
  classical
  let alive := linesUsed (parentsAt why) root rows.length
  let keep := fun k : Nat => decide (k ∈ alive)
  have keep_iff (k : Nat) : keep k = true ↔ k ∈ alive := by simp [keep]
  obtain ⟨rootBound, _⟩ := lookupIndex hr
  have rootKept := (keep_iff root).mpr (linesUsed_spec.mpr ⟨rootBound,.rootLine⟩)
  refine ⟨keep, ⟨keepLines_derives ?_,keepLines_member hr rootKept⟩, keepLines_length _ _,keep_iff⟩
  intro k R lookup kept
  obtain ⟨hk,eq⟩ := lookupIndex lookup
  subst R
  have retained (p : Nat) (hp : p ∈ (why ⟨k,hk⟩).parents) : keep p = true := by
    apply (keep_iff p).mpr
    apply parentsRetained (parent := parentsAt why) (fun u v _ edge => (edgesForward why u v edge).2)
      ((keep_iff k).mp kept)
    simpa [parentsAt,hk] using hp
  generalize he : why ⟨k,hk⟩ = reason at retained ⊢
  cases reason with
  | ax mem => exact Or.inl mem
  | res i j C D hi hj hC hD hR =>
    have qi : k+1+(i-(k+1)) = i := by omega
    have qj : k+1+(j-(k+1)) = j := by omega
    refine Or.inr ⟨i-(k+1),j-(k+1),C,D,by simpa only [qi] using hC,by simpa only [qj] using hD,?_,?_,hR⟩
    · rw [qi]
      exact retained i (by simp [LineReason.parents])
    · rw [qj]
      exact retained j (by simp [LineReason.parents])

end PCX150
