import PEqualNP.Defs
open Finset
namespace Crown9348
abbrev V := Fin 21
abbrev B := Finset V × Finset V
abbrev P := V × V
def ink (r c : V) := (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List Nat).getD r.val 0).testBit c.val
def lawful (b : B) := ∀r∈b.1,∀c∈b.2, ink r c=false
def hit (b : B) (p : P) : Prop := p.1∈b.1 ∧ p.2∈b.2
def conflict (p q : P) := ink p.1 q.2 || ink q.1 p.2
def joined (i j : Fin 8) : Bool := decide (i≠j ∧
    (i.val < 3 ∨ j.val < 3 ∨ i.val+1=j.val ∨ j.val+1=i.val ∨
    (i.val=3 ∧ j.val=7) ∨ (i.val=7 ∧ j.val=3)))
def example : Fin 8 → P := ![(1,16),(6,18),(8,6),(20,2),(16,13),(13,8),(20,13),(11,4)]
theorem geometry : (∀i, ink (example i).1 (example i).2=false) ∧
    (∀i j, joined i j=true → conflict (example i) (example j)=true) := by decide +kernel

theorem separates (b : B) (ok : lawful b) (p q : P) (c : conflict p q = true) :
    hit b p → ¬hit b q := by
  intro hp hq
  simp [conflict,ok _ hp.1 _ hq.2,ok _ hq.1 _ hp.2] at c

-- With three distinct universal vertices deleted, five colors leave only two for an odd cycle.
theorem noFive (f : Fin 8 → Fin 5) (sep : ∀i j, joined i j = true → f i ≠ f j) : False := by
  let A : Finset (Fin 5) := {f 0,f 1,f 2}
  have h01 := sep 0 1 (by decide)
  have h02 := sep 0 2 (by decide)
  have h12 := sep 1 2 (by decide)
  have hc : A.card=3 := by simp [A,h01,h02,h12]
  let C := Finset.univ \ A
  have cc : C.card=2 := by
    simp [C,Finset.card_sdiff_of_subset (Finset.subset_univ A),hc]
  have hs (j : Fin 8) (high : 3≤j.val) : f j ∈ C := by
    have a : joined 0 j=true := by simp [joined]; omega
    have b : joined 1 j=true := by simp [joined]; omega
    have c : joined 2 j=true := by simp [joined]; omega
    simp [C,A,Ne.symm (sep 0 j a),Ne.symm (sep 1 j b),Ne.symm (sep 2 j c)]
  have cd := sep 3 4 (by decide)
  have limit : ({f 3,f 4} : Finset (Fin 5))=C := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact hs 3 (by decide)
      · exact hs 4 (by decide)
    · simp [cc,cd]
  have options (j : Fin 8) (h : 3≤j.val) : f j=f 3 ∨ f j=f 4 := by
    have m := hs j h
    rw [← limit] at m
    simpa using m
  have e45 := sep 4 5 (by decide)
  have e56 := sep 5 6 (by decide)
  have e67 := sep 6 7 (by decide)
  have e73 := sep 7 3 (by decide)
  rcases options 5 (by decide) with h5|h5 <;>
    rcases options 6 (by decide) with h6|h6 <;>
    rcases options 7 (by decide) with h7|h7 <;> simp_all

theorem physical (pts : Fin 8 → P) (edges : ∀i j, joined i j=true → conflict (pts i) (pts j)=true)
    (L : Fin 5 → B) (law : ∀ i, lawful (L i)) :
    ¬∀j, ∃i, hit (L i) (pts j) := by
  intro cov
  choose f hf using cov
  apply noFive f
  intro i j hij eq
  have both := hf j
  rw [← eq] at both
  exact separates _ (law _) _ _ (edges i j hij) (hf i) both

theorem nineHit (A : List B) (L : Fin 5 → B) (law : ∀ i,lawful (L i))
    (cov : ∀p : P, ink p.1 p.2=false → (∃b∈A,hit b p) ∨ ∃i,hit (L i) p) :
    ∃j,∃b∈A,hit b (example j) := by
  by_contra! nothing
  apply physical example geometry.2 L law
  intro j
  rcases cov (example j) (geometry.1 j) with ⟨b,hb,hitb⟩|c
  · exact False.elim (nothing j b hb hitb)
  · exact c
end Crown9348
