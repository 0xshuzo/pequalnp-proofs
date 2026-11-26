import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9345.Fooling
open Finset
abbrev V := Fin 21
abbrev I := Fin 8
def board : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def ink (r c : V) : Bool := (board.getD r.val 0).testBit c.val
def lineTable : Array V := #[0, 0, 7, 20, 0, 5, 5, 7, 7, 5, 17, 7, 17, 20, 0, 20, 0, 17, 17, 5, 20, 0, 0, 1, 8, 0, 1, 6, 6, 8, 8, 6, 18, 8, 18, 0, 1, 0, 1, 18, 18, 6, 7, 1, 1, 2, 9, 1, 2, 7, 7, 9, 9, 7, 19, 9, 19, 1, 2, 1, 2, 19, 19, 20, 8, 2, 2, 3, 10, 2, 3, 8, 8, 10, 10, 8, 20, 10, 20, 2, 3, 2, 3, 20, 0, 0, 9, 3, 0, 4, 11, 3, 4, 9, 9, 11, 11, 9, 0, 11, 0, 3, 4, 3, 4, 5, 1, 1, 10, 4, 1, 5, 12, 4, 5, 10, 10, 12, 12, 10, 1, 12, 1, 4, 5, 4, 5, 6, 2, 2, 11, 5, 2, 6, 13, 5, 6, 11, 11, 13, 13, 11, 2, 13, 2, 5, 6, 7, 6, 7, 3, 3, 12, 6, 3, 7, 14, 6, 7, 12, 12, 14, 14, 12, 3, 14, 3, 6, 7, 8, 7, 8, 4, 4, 13, 7, 4, 8, 15, 7, 8, 13, 13, 15, 15, 13, 4, 15, 4, 5, 8, 9, 8, 9, 5, 5, 14, 8, 5, 9, 16, 8, 9, 14, 14, 16, 16, 14, 5, 16, 17, 6, 9, 10, 9, 10, 6, 6, 15, 9, 6, 10, 17, 9, 10, 15, 15, 17, 17, 15, 6, 7, 18, 7, 10, 11, 10, 11, 7, 7, 16, 10, 7, 11, 18, 10, 11, 16, 16, 18, 18, 16, 17, 8, 19, 8, 11, 12, 11, 12, 8, 8, 17, 11, 8, 12, 19, 11, 12, 17, 17, 19, 19, 20, 18, 9, 20, 9, 12, 13, 12, 13, 9, 9, 18, 12, 9, 13, 20, 12, 13, 18, 18, 20, 0, 0, 19, 10, 0, 10, 13, 14, 13, 14, 10, 10, 19, 13, 0, 14, 0, 13, 14, 19, 19, 20, 1, 1, 20, 11, 1, 11, 14, 15, 14, 15, 11, 11, 20, 14, 1, 15, 1, 14, 15, 20, 0, 0, 2, 2, 0, 12, 2, 12, 15, 16, 15, 16, 12, 12, 0, 15, 0, 16, 2, 15, 16, 17, 1, 1, 3, 3, 1, 13, 3, 13, 16, 17, 16, 17, 13, 13, 1, 16, 1, 17, 3, 16, 17, 18, 2, 2, 4, 4, 2, 14, 4, 14, 17, 18, 17, 18, 14, 14, 2, 17, 2, 18, 4, 5, 18, 19, 3, 3, 5, 5, 3, 15, 5, 15, 18, 19, 18, 19, 15, 15, 3, 18, 3, 19, 20, 6, 19, 20, 4, 4, 6, 6, 4, 16, 6, 16, 19, 20, 19, 20, 16, 16, 4, 19, 4]
def joinLine (r s : V) : V := lineTable[21*r.val+s.val]!
set_option maxRecDepth 8192
set_option maxHeartbeats 0
theorem uniqueLine : ∀ r s c : V, r≠s → ink r c=true → ink s c=true → c=joinLine r s := by
  decide +kernel
def one (S : Finset I) (i : I) : Nat := if i∈S then 1 else 0
def two (S : Finset I) (i j : I) : Nat := if i≠j ∧ i∈S ∧ j∈S then 1 else 0
theorem loadBound : ∀ S : Finset I, 6*(∑ i : I, one S i) ≤
    12 + ∑ i : I, ∑ j : I, two S i j := by decide +kernel
theorem noEight (R C : I → V) (zero : ∀ i, ink (R i) (C i)=false)
    (bad : ∀ i j, i≠j → ink (R i) (C j)=true ∨ ink (R j) (C i)=true) : False := by
  have rowInj : Function.Injective R := by
    intro i j eq
    by_contra ne
    rcases bad i j ne with h|h
    · rw [eq,zero] at h
      contradiction
    · rw [←eq,zero] at h
      contradiction
  have colInj : Function.Injective C := by
    intro i j eq
    by_contra ne
    rcases bad i j ne with h|h
    · rw [←eq,zero] at h
      contradiction
    · rw [eq,zero] at h
      contradiction
  let S (j : I) := univ.filter (fun i : I => ink (R i) (C j)=true)
  have mem (i j : I) : i∈S j ↔ ink (R i) (C j)=true := by simp [S]
  have paired (i j : I) : (if i=j then 0 else 1 : Nat) ≤ one (S j) i + one (S i) j := by
    by_cases eq : i=j
    · simp [eq]
    · rcases bad i j eq with a|b
      · simp [one,eq,(mem i j).2 a]
      · simp [one,eq,(mem j i).2 b]
  have shape : (∑ i : I, ∑ j : I, (if i=j then 0 else 1 : Nat))=56 := by decide +kernel
  have low := sum_le_sum (fun (i : I) (_ : i∈univ) => sum_le_sum (fun (j : I) (_ : j∈univ) => paired i j))
  rw [shape] at low
  simp only [sum_add_distrib] at low
  have sw : (∑ i : I, ∑ j : I, one (S j) i) = ∑ j : I, ∑ i : I, one (S j) i := sum_comm
  rw [sw] at low
  have atMost (i k : I) : (∑ j : I, two (S j) i k) ≤ (if i=k then 0 else 1 : Nat) := by
    by_cases same : i=k
    · simp [same,two]
    · let l := joinLine (R i) (R k)
      have rowNe : R i≠R k := fun e => same (rowInj e)
      have toLine (j : I) (a : i∈S j) (b : k∈S j) : C j=l :=
        uniqueLine _ _ _ rowNe ((mem i j).1 a) ((mem k j).1 b)
      by_cases ex : ∃ u, C u=l
      · obtain ⟨u,hu⟩ := ex
        have single (j : I) : two (S j) i k ≤ if j=u then 1 else 0 := by
          by_cases a : i∈S j
          · by_cases b : k∈S j
            · have eq : j=u := colInj ((toLine j a b).trans hu.symm)
              simp [two,same,a,b,eq]
            · simp [two,b]
          · simp [two,a]
        have z := sum_le_sum (fun (j : I) (_ : j∈univ) => single j)
        simpa [same] using z
      · have vanish (j : I) : two (S j) i k=0 := by
          unfold two
          split
          · rename_i h
            exact (ex ⟨j,toLine j h.2.1 h.2.2⟩).elim
          · rfl
        simp [vanish,same]
  have upper := sum_le_sum (fun (i : I) (_ : i∈univ) => sum_le_sum (fun (k : I) (_ : k∈univ) => atMost i k))
  rw [shape] at upper
  have cyc : (∑ j : I, ∑ i : I, ∑ k : I, two (S j) i k) =
      ∑ i : I, ∑ k : I, ∑ j : I, two (S j) i k := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    exact sum_comm
  have localBd := sum_le_sum (fun (j : I) (_ : j∈univ) => loadBound (S j))
  simp only [sum_add_distrib,←mul_sum,cyc] at localBd
  have cst : (∑ _ : I, (12 : Nat))=96 := by decide +kernel
  rw [cst] at localBd
  omega
def sevenRows : Fin 7 → V := ![20,19,18,17,12,11,4]
def sevenCols : Fin 7 → V := ![18,17,11,4,16,3,19]
theorem seven : (∀ i, ink (sevenRows i) (sevenCols i)=false) ∧
    ∀ i j, i≠j → ink (sevenRows i) (sevenCols j)=true ∨ ink (sevenRows j) (sevenCols i)=true := by
  decide +kernel
end PEqualNP.Outside.L_meta_9345.Fooling
