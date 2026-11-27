import PEqualNP.Defs

namespace Lpcx178TwoHoles
open PEqualNP.ProofComplexity

abbrev Cell := Fin 5 × Fin 4
abbrev Code := Bool × Bool
def zeroCode : Code := (false, false)
def sig (f g : Finset Cell) (i : Cell) : Code := (decide (i ∈ f), decide (i ∈ g))
def mix (c d : Code) (a b : Bool) : Code :=
  (Bool.xor (c.1 && a) (d.1 && b), Bool.xor (c.2 && a) (d.2 && b))

theorem basisTable : ∀ c d : Code, c ≠ zeroCode → d ≠ zeroCode → c ≠ d →
    ∀ t : Code, ∃ a b : Bool, mix c d a b = t := by decide +kernel

theorem crossPair (s : Cell → Code)
    (ind : ∃ i j, s i ≠ zeroCode ∧ s j ≠ zeroCode ∧ s i ≠ s j)
    (wide : ∃ k l : Cell, s k ≠ zeroCode ∧ s l ≠ zeroCode ∧ k.2 ≠ l.2) :
    ∃ i j : Cell, s i ≠ zeroCode ∧ s j ≠ zeroCode ∧ s i ≠ s j ∧ i.2 ≠ j.2 := by
  obtain ⟨i,j,hi,hj,hij⟩ := ind
  by_cases e : i.2 = j.2
  · obtain ⟨k,l,hk,hl,kl⟩ := wide
    have out : ∃ v : Cell, s v ≠ zeroCode ∧ i.2 ≠ v.2 := by
      by_cases h : i.2 = k.2
      · exact ⟨l,hl,fun h' => kl (h.symm.trans h')⟩
      · exact ⟨k,hk,h⟩
    obtain ⟨v,hv,iv⟩ := out
    by_cases c : s i = s v
    · exact ⟨j,v,hj,hv,fun h => hij (c.trans h.symm),fun h => iv (e.trans h)⟩
    · exact ⟨i,v,hi,hv,c,iv⟩
  · exact ⟨i,j,hi,hj,hij,e⟩

def board (x : Cell → Bool) : Prop :=
  ∀ i j : Cell, i.2 = j.2 → x i = true → x j = true → i = j

def select (i j : Cell) (a b : Bool) (v : Cell) : Bool :=
  (decide (v = i) && a) || (decide (v = j) && b)

theorem selectBoard {i j : Cell} (hne : i.2 ≠ j.2) (a b : Bool) :
    board (select i j a b) := by
  intro u v eq hu hv
  have which (w : Cell) (hw : select i j a b w = true) : w = i ∨ w = j := by
    by_contra! bad
    simpa [select,bad.1,bad.2] using hw
  rcases which u hu with rfl|rfl <;> rcases which v hv with rfl|rfl
  · rfl
  · exact (hne eq).elim
  · exact (hne eq.symm).elim
  · rfl

def bit (f : Finset Cell) (x : Cell → Bool) : Bool :=
  decide (Odd (f.filter (fun v => x v = true)).card)

theorem selectBit (f : Finset Cell) {i j : Cell} (ij : i ≠ j) (a b : Bool) :
    bit f (select i j a b) = Bool.xor (decide (i ∈ f) && a) (decide (j ∈ f) && b) := by
  have sf : f.filter (fun v => select i j a b v = true) =
      (if i ∈ f ∧ a = true then {i} else ∅) ∪
      (if j ∈ f ∧ b = true then {j} else ∅) := by
    ext v
    by_cases vi : v = i <;> by_cases vj : v = j <;>
      by_cases fi : i ∈ f <;> by_cases fj : j ∈ f <;>
      cases a <;> cases b <;> simp_all [select]
  unfold bit
  rw [sf]
  cases a <;> cases b <;> by_cases fi : i ∈ f <;> by_cases fj : j ∈ f <;>
    simp [fi,fj,ij,Ne.symm ij] <;> decide

theorem realize {f g : Finset Cell}
    (ind : ∃ i j, sig f g i ≠ zeroCode ∧ sig f g j ≠ zeroCode ∧ sig f g i ≠ sig f g j)
    (wide : ∃ k l : Cell, sig f g k ≠ zeroCode ∧ sig f g l ≠ zeroCode ∧ k.2 ≠ l.2)
    (t : Code) : ∃ x, board x ∧ (bit f x, bit g x) = t := by
  obtain ⟨i,j,hi,hj,hij,cross⟩ := crossPair _ ind wide
  obtain ⟨a,b,hit⟩ := basisTable _ _ hi hj hij t
  have ij : i ≠ j := fun e => cross (congrArg Prod.snd e)
  exact ⟨_,selectBoard cross a b,by
    rw [selectBit f ij,selectBit g ij]
    exact hit⟩

theorem cannotExcludeCell {f g : Finset Cell}
    (ind : ∃ i j, sig f g i ≠ zeroCode ∧ sig f g j ≠ zeroCode ∧ sig f g i ≠ sig f g j)
    (wide : ∃ k l : Cell, sig f g k ≠ zeroCode ∧ sig f g l ≠ zeroCode ∧ k.2 ≠ l.2)
    (t : Code) (K : LinClause Cell)
    (valid : ∀ x, board x → LinClauseSat x K) :
    ¬ (∀ x, (bit f x,bit g x) = t → ¬ LinClauseSat x K) := by
  obtain ⟨x,hx,ht⟩ := realize ind wide t
  exact fun bad => bad x ht (valid x hx)

end Lpcx178TwoHoles
