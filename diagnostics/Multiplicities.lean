import PEqualNP.Defs

namespace PCX150

/-- A unique incoming slot is preserved when a list of line indices is replaced by
    its expanded occurrences, provided the unique reader has been expanded once. -/
theorem countParentsSingle (lines : List Nat) (ports : Nat → List Nat) (v u : Nat)
    (sole : ∀ x ∈ lines, (ports x).count v = if x = u then 1 else 0) :
    (lines.flatMap ports).count v = lines.count u := by
  induction lines with
  | nil => rfl
  | cons x xs ih =>
    have h := sole x (by simp)
    have tail := ih (fun y hy => sole y (by simp [hy]))
    by_cases eq : x = u
    · subst x
      simp_all [List.flatMap_cons,List.count_append,Nat.add_comm]
    · simp [List.flatMap_cons,List.count_append,h,tail,eq,Ne.symm eq]

theorem countParentsZero (lines : List Nat) (ports : Nat → List Nat) (v : Nat)
    (none : ∀ x ∈ lines, v ∉ ports x) : (lines.flatMap ports).count v = 0 := by
  induction lines with
  | nil => rfl
  | cons x xs ih =>
    have h := none x (by simp)
    have tail := ih (fun y hy => none y (by simp [hy]))
    simp [List.flatMap_cons,List.count_append,tail,List.count_eq_zero.mpr h]

/-- Conservation over the forest of fragments. The roots list has one copy of
    each cut line and the conclusion. A non-cut derived line ends no fragment. -/
theorem oneExpansionPerLine (nodes tips roots : List Nat) (ports : Nat → List Nat)
    (derived : Nat → Prop) (balance : ∀ v, nodes.count v + tips.count v =
      roots.count v + (nodes.flatMap ports).count v)
    (casesFor : ∀ v, derived v →
      nodes.count v = 1 ∨
      (tips.count v = 0 ∧ roots.count v = 0 ∧ ∃ u, u < v ∧ derived u ∧
        ∀ x ∈ nodes, (ports x).count v = if x = u then 1 else 0)) :
    ∀ v, derived v → nodes.count v = 1 := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv
    rcases casesFor v hv with done | ⟨tip,seed,u,lt,hu,sole⟩
    · exact done
    · have incoming := countParentsSingle nodes ports v u sole
      have earlier := ih u lt hu
      have h := balance v
      omega

end PCX150
