import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9829.SixPartners
abbrev P := Fin 9
abbrev J := Fin 6
abbrev Word := P → Bool
def mask (i : J) : BitVec 9 := (#[267,149,102,168,304,448] : Array (BitVec 9))[i.val]!
def pin (i : J) : P := (#[3,4,6,3,4,6] : Array P)[i.val]!
def atBit (i : J) (p : P) := (mask i).getLsbD p.val
def residual (i : J) (p : P) := decide (p≠pin i) && atBit i p
def singleton (p : P) : Word := fun k => decide (k = p)
def clear : Word := fun _ => false
def insert (x : Word) (p : P) : Word := Function.update x p true
def cover (i : J) (x : Word) : Bool := (List.finRange 9).any (fun p => atBit i p && x p)
theorem singleEval : ∀ (i : J) (p : P), cover i (singleton p)=atBit i p := by decide +kernel
theorem zeroEval : ∀ i : J, cover i clear=false := by decide +kernel
theorem missing : ∀ (i : J) (j : P), j≠pin i → ∃ t : J,
    cover t (singleton j)=false ∧ cover t (insert (singleton j) (pin i))=true := by decide +kernel
theorem targetPin : ∀ i : J, atBit i (pin i) = true := by decide +kernel
theorem injResidual : ∀ i j : J,(∀ p : P,residual i p=residual j p) → i=j := by decide +kernel
theorem nonsingle : ∀ i : J,∀ p : P, ∃ j : P,
    residual i j ≠ decide (p=j) := by decide +kernel

/-- All output changes on a single pin have to be communicated by its single physical reader. -/
def Carries (h : Word→Bool) (p : P) : Prop :=
  ∀ x : Word, h x=h (insert x p) → ∀ t : J,cover t x=cover t (insert x p)

theorem readerSignature (i : J) (h : Word→Bool) (c : Carries h (pin i))
    (fed : ∀ x : Word,x (pin i)=true → h x=true) :
    ∀ j : P,h (singleton j) = decide (j=pin i) := by
  intro j
  by_cases eq : j=pin i
  · subst j
    simpa using fed (singleton (pin i)) (by simp [singleton])
  · have val : h (singleton j)=false := by
      cases e : h (singleton j) with
      | false => rfl
      | true =>
        obtain ⟨t,off,on⟩ := missing i j eq
        have yes := fed (insert (singleton j) (pin i)) (by simp [insert])
        have same := c (singleton j) (e.trans yes.symm) t
        simpa [off,on] using same
    simpa [eq] using val

/-- Each terminal adds one of the three singleton readers to a signal independent of its pin. -/
theorem otherSignature (i : J) (h g : Word→Bool)
    (c : Carries h (pin i)) (fed : ∀ x : Word,x (pin i)=true → h x=true)
    (terminal : ∀ x, cover i x = (h x || g x))
    (independent : g (singleton (pin i))=g clear) :
    ∀ j, g (singleton j)=residual i j := by
  intro j
  by_cases eq : j=pin i
  · subst j
    have z := terminal clear
    rw [zeroEval] at z
    have off : g clear = false := by cases a : g clear <;> simp_all
    simpa [residual,independent,off]
  · have sig := readerSignature i h c fed j
    have e := terminal (singleton j)
    rw [singleEval,sig] at e
    simpa [residual,eq] using e.symm

/-- The six independent partners cannot be supplied by raw singletons and five hidden signals. -/
theorem noFive (hub other : J → Word → Bool) (hidden : Fin 5 → Word → Bool)
    (c : ∀ i,Carries (hub i) (pin i))
    (fed : ∀ i x,x (pin i)=true → hub i x=true)
    (terminal : ∀ i x,cover i x=(hub i x || other i x))
    (independent : ∀ i,other i (singleton (pin i))=other i clear)
    (pool : ∀ i, (∃ p : P, ∀ j,other i (singleton j)=decide (p=j)) ∨
      ∃ k : Fin 5, ∀ j, other i (singleton j)=hidden k (singleton j)) : False := by
  classical
  have shape := fun i => otherSignature i (hub i) (other i) (c i) (fed i) (terminal i) (independent i)
  have supply : ∀ i, ∃ k : Fin 5, ∀ j, other i (singleton j)=hidden k (singleton j) := by
    intro i
    rcases pool i with ⟨p,hp⟩ | h
    · obtain ⟨j,ne⟩ := nonsingle i p
      exact (ne ((shape i j).symm.trans (hp j))).elim
    · exact h
  choose f hf using supply
  have inj : Function.Injective f := by
    intro i j e
    apply injResidual i j
    intro k
    calc
      residual i k = hidden (f i) (singleton k) := (shape i k).symm.trans (hf i k)
      _ = hidden (f j) (singleton k) := by rw [e]
      _ = residual j k := (hf j k).symm.trans (shape j k)
  have small := Fintype.card_le_of_injective f inj
  simpa using small
end PEqualNP.Outside.L_meta_9829.SixPartners
