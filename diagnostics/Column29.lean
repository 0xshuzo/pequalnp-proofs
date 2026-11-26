import PEqualNP.Defs

namespace PHP169Column

open PEqualNP.ProofComplexity

theorem memD {α : Type} (l : List α) (d : α) (i : ℕ) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

-- resolution lines, newest first; a hint (i, j, v): the premises are entries i and j of the tail, pivot v
def chkR {V : Type} [DecidableEq V] (ax : Clause V → Bool) :
    List (Clause V × Option (ℕ × ℕ × V)) → Bool
  | [] => true
  | (R, none) :: t => ax R && chkR ax t
  | (R, some (i, j, v)) :: t =>
      decide (i < t.length) && decide (j < t.length) &&
      decide ((v, true) ∈ (t.map Prod.fst).getD i ∅ ∧ (v, false) ∈ (t.map Prod.fst).getD j ∅ ∧
        R = ((t.map Prod.fst).getD i ∅).erase (v, true) ∪ ((t.map Prod.fst).getD j ∅).erase (v, false)) &&
      chkR ax t

theorem chkR_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (ax : Clause V → Bool)
    (hax : ∀ C, ax C = true → C ∈ F) :
    ∀ l, chkR ax l = true → IsDerivation F (l.map Prod.fst)
  | [], _ => IsDerivation.nil
  | (R, none) :: t, h => by
    simp only [chkR, Bool.and_eq_true] at h
    exact IsDerivation.ax (chkR_sound F ax hax t h.2) (hax R h.1)
  | (R, some (i, j, v)) :: t, h => by
    simp only [chkR, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, h1, h2, h3⟩, ht⟩ := h
    exact IsDerivation.res (chkR_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨v, h1, h2, h3⟩

abbrev C := Clause (Fin 5)
def basis : List C := [
  {(1, true), (2, true), (3, true), (4, true)},
  {(0, true), (2, true), (3, true), (4, true)},
  {(0, false), (1, false)},
  {(0, true), (1, true), (3, true), (4, true)},
  {(0, false), (2, false)},
  {(1, false), (2, false)},
  {(0, true), (1, true), (2, true), (4, true)},
  {(0, false), (3, false)},
  {(1, false), (3, false)},
  {(2, false), (3, false)},
  {(0, true), (1, true), (2, true), (3, true)},
  {(0, false), (4, false)},
  {(1, false), (4, false)},
  {(2, false), (4, false)},
  {(3, false), (4, false)}
]
def cert : List (C × Option (Nat × Nat × Fin 5)) := [
  (∅, some (9, 0, 4)),
  ({(4, false)}, some (1, 0, 3)),
  ({(3, false), (4, false)}, none),
  ({(3, true), (4, false)}, some (1, 0, 2)),
  ({(2, false), (4, false)}, none),
  ({(2, true), (3, true), (4, false)}, some (1, 0, 1)),
  ({(1, false), (4, false)}, none),
  ({(1, true), (2, true), (3, true), (4, false)}, some (1, 0, 0)),
  ({(0, false), (4, false)}, none),
  ({(0, true), (1, true), (2, true), (3, true)}, none),
  ({(4, true)}, some (7, 0, 3)),
  ({(3, false), (4, true)}, some (1, 0, 2)),
  ({(2, false), (3, false)}, none),
  ({(2, true), (3, false), (4, true)}, some (1, 0, 1)),
  ({(1, false), (3, false)}, none),
  ({(1, true), (2, true), (3, false), (4, true)}, some (1, 0, 0)),
  ({(0, false), (3, false)}, none),
  ({(0, true), (1, true), (2, true), (4, true)}, none),
  ({(3, true), (4, true)}, some (5, 0, 2)),
  ({(2, false), (3, true), (4, true)}, some (1, 0, 1)),
  ({(1, false), (2, false)}, none),
  ({(1, true), (2, false), (3, true), (4, true)}, some (1, 0, 0)),
  ({(0, false), (2, false)}, none),
  ({(0, true), (1, true), (3, true), (4, true)}, none),
  ({(2, true), (3, true), (4, true)}, some (3, 0, 1)),
  ({(1, false), (2, true), (3, true), (4, true)}, some (1, 0, 0)),
  ({(0, false), (1, false)}, none),
  ({(0, true), (2, true), (3, true), (4, true)}, none),
  ({(1, true), (2, true), (3, true), (4, true)}, none)
]
set_option maxRecDepth 4000 in
theorem checked : chkR (fun c => decide (c ∈ basis)) cert = true := by decide +kernel

theorem upper : ∃ π : List C, IsRefutation {c | c ∈ basis} π ∧ π.length = 29 := by
  refine ⟨cert.map Prod.fst, ⟨chkR_sound _ _ (fun c h => of_decide_eq_true h) _ checked, ?_⟩, ?_⟩
  · decide +kernel
  · decide +kernel

def test (a : Fin 32) (i : Fin 5) : Bool := a.val.testBit i.val
def yes (a : Fin 32) (c : C) : Bool := c.any fun l => test a l.1 == l.2

theorem yes_true (a : Fin 32) (c : C) : yes a c = true ↔ ClauseSat (test a) c := by
  simp [yes, Finset.any_eq_true, ClauseSat]

theorem private_all : basis.all (fun c => (List.finRange 32).any (fun a =>
    !yes a c && basis.all (fun d => d == c || yes a d))) = true := by
  decide +kernel

theorem mandatory (S : Finset C) (sub : ∀ c ∈ S, c ∈ basis)
    (un : ∀ a : Fin 32, ¬(∀ c ∈ S, ClauseSat (test a) c)) : 15 ≤ S.card := by
  have ge : basis.toFinset ⊆ S := by
    intro c hc
    have hm : c ∈ basis := List.mem_toFinset.mp hc
    have h := List.all_eq_true.mp private_all c hm
    obtain ⟨a,_,hw⟩ := List.any_eq_true.mp h
    by_contra no
    apply un a
    intro d hd
    have h' := List.all_eq_true.mp (Bool.and_eq_true.mp hw).2 d (sub d hd)
    have dne : d ≠ c := fun he => no (he ▸ hd)
    have hb : (d == c) = false := by simpa using dne
    exact (yes_true a d).mp (by simpa [hb] using h')
  have sz : basis.toFinset.card = 15 := by decide +kernel
  rw [← sz]
  exact Finset.card_le_card ge

end PHP169Column
