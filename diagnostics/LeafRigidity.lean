import PEqualNP.Defs

namespace PEqualNP.Outside.Pcx9792Expansion
abbrev L := Fin 11
abbrev P := Fin 13
def rows : List Nat := [1284, 520, 1041, 35, 70, 141, 282, 564, 1128, 208, 416, 833, 1666]
def touch (s : Fin 2048) : Nat :=
  (rows.filter (fun t => (s.val &&& t) != 0)).length
def count (s : Fin 2048) : Nat :=
  ((List.finRange 11).filter (fun j => s.val.testBit j.val)).length
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem price : ∀ s : Fin 2048, s≠0 →
    count s + (if s.val=2047 then 2 else 3) ≤ touch s := by decide +kernel

/-- The charged local rows confine deviations to one point at 56 leaves. -/
theorem firstBand {C : Fin 2048} {D leaves : Nat} (sub : touch C ≤ D)
    (budget : 55+D ≤ leaves+count C) (bound : leaves≤56) :
    C=0 ∧ 55+D≤leaves := by
  have empty : C=0 := by
    by_contra ne
    have p := price C ne
    split at p <;> omega
  subst C
  have z : count 0=0 := by decide
  exact ⟨rfl,by omega⟩

/-- With two surplus leaves, the alternative to zero fully modified lines
is the extreme opposite orientation on all eleven lines. -/
theorem secondBand {C : Fin 2048} {D leaves : Nat} (sub : touch C ≤ D)
    (budget : 55+D ≤ leaves+count C) (bound : leaves≤57) :
    (C=0 ∧ 55+D≤leaves) ∨ (C.val=2047 ∧ 13≤D) := by
  by_cases z : C=0
  · subst C
    have h : count 0=0 := by decide
    exact Or.inl ⟨rfl,by omega⟩
  · have p := price C z
    by_cases full : C.val=2047
    · have eq : C=(2047 : Fin 2048) := Fin.ext full
      have t : touch (2047 : Fin 2048)=13 := by decide
      exact Or.inr ⟨full,by simpa [eq,t] using sub⟩
    · simp [full] at p
      omega
end PEqualNP.Outside.Pcx9792Expansion
