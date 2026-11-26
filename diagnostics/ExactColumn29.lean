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
def yes (a : Fin 32) (c : C) : Bool := decide (∃ l ∈ c, test a l.1 = l.2)

theorem yes_true (a : Fin 32) (c : C) : yes a c = true ↔ ClauseSat (test a) c := by
  simp [yes, ClauseSat]

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

namespace PHP169Support
open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

theorem sat_res {C D R : Clause V} (r : IsResolvent C D R) (a : V → Bool)
    (hc : ClauseSat a C) (hd : ClauseSat a D) : ClauseSat a R := by
  obtain ⟨v,_,_,rfl⟩ := r
  cases hv : a v with
  | false =>
    obtain ⟨l,hl,ev⟩ := hc
    have ne : l ≠ (v,true) := by
      intro e
      subst l
      simp [hv] at ev
    exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,hl⟩), ev⟩
  | true =>
    obtain ⟨l,hl,ev⟩ := hd
    have ne : l ≠ (v,false) := by
      intro e
      subst l
      simp [hv] at ev
    exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,hl⟩), ev⟩

-- Walk the requested clauses backwards. A requested axiom is discharged.
-- Replacing a requested conclusion by its two inputs adds at most one
-- request, including when either input is already requested.
theorem support {F : Set (Clause V)} {π : List (Clause V)} (der : IsDerivation F π)
    (G : Finset (Clause V)) (mem : ∀ c ∈ G, c ∈ π) :
    ∃ S : Finset (Clause V), (∀ c ∈ S, c ∈ F) ∧
      (∀ a, (∀ c ∈ S, ClauseSat a c) → ∀ c ∈ G, ClauseSat a c) ∧
      2 * S.card ≤ π.length + G.card := by
  classical
  induction der generalizing G with
  | nil =>
    refine ⟨∅, by simp, ?_, by simp⟩
    intro a _ c hc
    exact False.elim (by simpa using mem c hc)
  | @ax p c _ ax ih =>
    by_cases hc : c ∈ G
    · have rest : ∀ g ∈ G.erase c, g ∈ p := by
        intro g hg
        exact (List.mem_cons.mp (mem g (Finset.mem_of_mem_erase hg))).resolve_left
          (Finset.mem_erase.mp hg).1
      obtain ⟨S,hs,pre,sz⟩ := ih (G.erase c) rest
      refine ⟨insert c S, ?_, ?_, ?_⟩
      · intro g hg
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact ax
        · exact hs _ hg
      · intro a h g hg
        by_cases eq : g = c
        · subst g
          exact h _ (Finset.mem_insert_self _ _)
        · exact pre a (fun k hk => h k (Finset.mem_insert_of_mem hk)) g
            (Finset.mem_erase.mpr ⟨eq,hg⟩)
      · have hi := Finset.card_insert_le c S
        have he := Finset.card_erase_add_one hc
        simp only [List.length_cons]
        omega
    · have rest : ∀ g ∈ G, g ∈ p := fun g hg =>
        (List.mem_cons.mp (mem g hg)).resolve_left (fun e => hc (e ▸ hg))
      obtain ⟨S,hs,pre,sz⟩ := ih G rest
      exact ⟨S,hs,pre,by simp only [List.length_cons]; omega⟩
  | @res p c d r _ cp dp rule ih =>
    by_cases hr : r ∈ G
    · let H := insert c (insert d (G.erase r))
      have rest : ∀ g ∈ H, g ∈ p := by
        intro g hg
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact cp
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact dp
        exact (List.mem_cons.mp (mem g (Finset.mem_of_mem_erase hg))).resolve_left
          (Finset.mem_erase.mp hg).1
      obtain ⟨S,hs,pre,sz⟩ := ih H rest
      refine ⟨S,hs,?_,?_⟩
      · intro a h g hg
        by_cases eq : g = r
        · subst g
          apply sat_res rule a
          · exact pre a h c (Finset.mem_insert_self _ _)
          · exact pre a h d (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        · exact pre a h g (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨eq,hg⟩)))
      · have hi := Finset.card_insert_le c (insert d (G.erase r))
        have hj := Finset.card_insert_le d (G.erase r)
        have he := Finset.card_erase_add_one hr
        dsimp [H] at sz
        simp only [List.length_cons]
        omega
    · have rest : ∀ g ∈ G, g ∈ p := fun g hg =>
        (List.mem_cons.mp (mem g hg)).resolve_left (fun e => hr (e ▸ hg))
      obtain ⟨S,hs,pre,sz⟩ := ih G rest
      exact ⟨S,hs,pre,by simp only [List.length_cons]; omega⟩

theorem unsat_support {F : Set (Clause V)} {π : List (Clause V)} (ref : IsRefutation F π) :
    ∃ S : Finset (Clause V), (∀ c ∈ S, c ∈ F) ∧
      (∀ a, ¬(∀ c ∈ S, ClauseSat a c)) ∧ 2 * S.card ≤ π.length+1 := by
  obtain ⟨S,hs,imp,card⟩ := support ref.1 {(∅ : Clause V)}
    (by intro c hc; have := Finset.mem_singleton.mp hc; subst c; exact ref.2)
  refine ⟨S,hs,?_,by simpa using card⟩
  intro a h
  have z := imp a h ∅ (Finset.mem_singleton_self _)
  simpa [ClauseSat] using z

end PHP169Support

namespace PHP169Column
theorem lower {π : List C} (r : PEqualNP.ProofComplexity.IsRefutation {c | c ∈ basis} π) :
    29 ≤ π.length := by
  obtain ⟨S,hs,un,sz⟩ := PHP169Support.unsat_support r
  have lo := mandatory S hs (fun a => un (test a))
  omega
end PHP169Column
