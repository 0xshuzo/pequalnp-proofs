import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4889

abbrev Inc (p l : Fin 13) : Prop := (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

def hit (x : Fin 26 → Bool) : Prop :=
  ∃ p l : Fin 13, Inc p l ∧ x (p.castAdd 13) = true ∧ x (Fin.natAdd 13 l) = true

def vec (s t : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)

def off (s : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∀ p ∈ s, ¬ Inc p l

private theorem leftBit (s t : Finset (Fin 13)) (p : Fin 13) :
    vec s t (p.castAdd 13) = true ↔ p ∈ s := by
  have pos : ∀ p : Fin 13, (p.castAdd 13).val < 13 ∧ Fin.ofNat 13 (p.castAdd 13).val = p := by decide
  simp only [vec,if_pos (pos p).1,(pos p).2,decide_eq_true_eq]

private theorem rightBit (s t : Finset (Fin 13)) (l : Fin 13) :
    vec s t (Fin.natAdd 13 l) = true ↔ l ∈ t := by
  have pos : ∀ l : Fin 13, ¬(Fin.natAdd 13 l).val < 13 ∧ Fin.ofNat 13 (Fin.natAdd 13 l).val = l := by decide
  simp only [vec,if_neg (pos l).1,(pos l).2,decide_eq_true_eq]

private theorem leBits {x y : Fin 26 → Bool}
    (a : ∀ p : Fin 13, x (p.castAdd 13) = true → y (p.castAdd 13) = true)
    (b : ∀ l : Fin 13, x (Fin.natAdd 13 l) = true → y (Fin.natAdd 13 l) = true) : x ≤ y := by
  have splitPort : ∀ i : Fin 26, (∃ p : Fin 13, i = p.castAdd 13) ∨ (∃ l : Fin 13, i = Fin.natAdd 13 l) := by decide
  intro i
  rcases splitPort i with ⟨p,rfl⟩ | ⟨l,rfl⟩
  · exact Bool.le_iff_imp.mpr (a p)
  · exact Bool.le_iff_imp.mpr (b l)

private theorem minimalEdge (p l : Fin 13) (h : Inc p l) : Minimal hit (vec {p} {l}) := by
  refine ⟨⟨p,l,h,(leftBit _ _ p).2 (by simp),(rightBit _ _ l).2 (by simp)⟩, ?_⟩
  intro x hx hle
  obtain ⟨j,k,_,hj,hk⟩ := hx
  have jp : j = p := Finset.mem_singleton.mp ((leftBit _ _ j).1 ((Bool.le_iff_imp.mp (hle _)) hj))
  have kl : k = l := Finset.mem_singleton.mp ((rightBit _ _ k).1 ((Bool.le_iff_imp.mp (hle _)) hk))
  subst j
  subst k
  apply leBits
  · intro i hi
    have ei : i = p := Finset.mem_singleton.mp ((leftBit _ _ i).1 hi)
    simpa only [ei] using hj
  · intro i hi
    have ei : i = l := Finset.mem_singleton.mp ((rightBit _ _ i).1 hi)
    simpa only [ei] using hk

private theorem memOff (s : Finset (Fin 13)) (l : Fin 13) :
    l ∈ off s ↔ ∀ p ∈ s, ¬ Inc p l := by simp [off]

private theorem symmInc (p l : Fin 13) (h : Inc p l) : Inc l p := by
  simpa only [Inc,Nat.add_comm l.val p.val] using h

private theorem witnessNotOff (s : Finset (Fin 13)) (l : Fin 13) (h : l ∉ off s) :
    ∃ p ∈ s, Inc p l := by
  by_contra no
  exact h ((memOff s l).2 (fun p hp hadj => no ⟨p,hp,hadj⟩))

private def pencil (p : Fin 13) : Finset (Fin 13) := Finset.univ.filter (Inc p)

private theorem degree : ∀ p : Fin 13, (pencil p).card = 4 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem uniqueLine : ∀ p q : Fin 13, p ≠ q → ∀ a : Fin 13, Inc p a → Inc q a →
    ∀ b : Fin 13, Inc p b → Inc q b → a = b := by decide +kernel

-- A point outside s has four incident lines. Each point of s can block only one.
private theorem escape (s : Finset (Fin 13)) (hs : s.card ≤ 3) (p : Fin 13) (hp : p ∉ s) :
    ∃ l ∈ off s, Inc p l := by
  classical
  by_contra no
  have atP (l : ↥(pencil p)) : Inc p l.val := (Finset.mem_filter.mp l.property).2
  have blocking (l : ↥(pencil p)) : ∃ a : ↥s, Inc a.val l.val := by
    have hn : l.val ∉ off s := fun hl => no ⟨l.val,hl,atP l⟩
    obtain ⟨q,hq,he⟩ := witnessNotOff s l.val hn
    exact ⟨⟨q,hq⟩,he⟩
  choose f hf using blocking
  have inj : Function.Injective f := by
    intro a b eq
    have different : p ≠ (f a).val := by
      intro same
      exact hp (by rw [same]; exact (f a).property)
    have right : Inc (f a).val b.val := by rw [eq]; exact hf b
    exact Subtype.ext (uniqueLine p _ different a.val (atP a) (hf a) b.val (atP b) right)
  have hc : (pencil p).card ≤ s.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inj
  rw [degree] at hc
  omega

private theorem maximalPair (s t : Finset (Fin 13))
    (disjoint : ∀ p ∈ s, ∀ l ∈ t, ¬ Inc p l)
    (rows : ∀ p ∉ s, ∃ l ∈ t, Inc p l)
    (cols : ∀ l ∉ t, ∃ p ∈ s, Inc p l) : Maximal (fun x => ¬ hit x) (vec s t) := by
  constructor
  · rintro ⟨p,l,he,hp,hl⟩
    exact disjoint p ((leftBit s t p).1 hp) l ((rightBit s t l).1 hl) he
  · intro x no hle
    apply leBits
    · intro p hp
      apply (leftBit s t p).2
      by_contra hn
      obtain ⟨l,hl,he⟩ := rows p hn
      exact no ⟨p,l,he,hp,(Bool.le_iff_imp.mp (hle _)) ((rightBit s t l).2 hl)⟩
    · intro l hl
      apply (rightBit s t l).2
      by_contra hn
      obtain ⟨p,hp,he⟩ := cols l hn
      exact no ⟨p,l,he,(Bool.le_iff_imp.mp (hle _)) ((leftBit s t p).2 hp),hl⟩

private theorem bothMax (s : Finset (Fin 13)) (hs : s.card ≤ 3) :
    Maximal (fun x => ¬ hit x) (vec s (off s)) ∧ Maximal (fun x => ¬ hit x) (vec (off s) s) := by
  constructor
  · exact maximalPair s (off s) (fun p hp l hl => (memOff s l).1 hl p hp)
      (escape s hs) (witnessNotOff s)
  · apply maximalPair (off s) s
    · intro p hp l hl e
      exact (memOff s p).1 hp l hl (symmInc p l e)
    · intro p h
      obtain ⟨l,hl,e⟩ := witnessNotOff s p h
      exact ⟨l,hl,symmInc l p e⟩
    · intro l h
      obtain ⟨p,hp,e⟩ := escape s hs l h
      exact ⟨p,hp,symmInc l p e⟩

end PEqualNP.Outside.L_meta_4889

open PEqualNP.Outside.L_meta_4889 in
theorem PEqualNP.Outside.L_meta_4889 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4); have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x1 x6 x5}; (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → Minimal x2 (x3 {x5} {x6})) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x5.card ≤ (3 : ℕ) → Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x2 x7) (x3 x5 (x4 x5)) ∧ Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x2 x7) (x3 (x4 x5) x5) := by
  exact ⟨minimalEdge,bothMax⟩
