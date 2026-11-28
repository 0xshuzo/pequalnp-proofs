import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9248.ProjectedDebt
open PEqualNP.ProofComplexity PEqualNP.Search
variable {V : Type} [DecidableEq V]
abbrev C (V : Type) := Clause V

def Below (F : Set (C V)) (r : List (C V)) := F ∪ {d | d∈r}

theorem forcesMono {F H : Set (C V)} {a : Set (Literal V)} {l} (sub : F⊆H)
    (h : UPForces F a l) : UPForces H a l := by
  induction h with
  | hyp h => exact .hyp h
  | unit m hl _ ih => exact .unit (sub m) hl ih

theorem rupMono {F H : Set (C V)} {c} (sub : F⊆H) (h : IsRUP F c) : IsRUP H c := by
  obtain ⟨d,hd,die⟩ := h
  exact ⟨d,sub hd,fun l hl => forcesMono sub (die l hl)⟩

/-- An independently certified closed database forbids every program over the
specified palette, including programs that repeat or freely reorder its entries. -/
theorem closedRun {F B P : Set (C V)} (closed : ∀c∈P, IsRUP (F∪B) c → c∈B)
    {r : List (C V)} (run : IsRUPRun F r) (palette : ∀c∈r,c∈P) : ∀c∈r,c∈B := by
  induction run with
  | nil => simp
  | @learn r c old step ih =>
    have tail := ih (fun q hq => palette q (List.mem_cons_of_mem _ hq))
    have incl : (F ∪ {d | d∈r}) ⊆ F∪B := by
      rintro d (raw|listed)
      · exact Or.inl raw
      · exact Or.inr (tail d listed)
    rintro d hd
    rcases List.mem_cons.mp hd with rfl|hd
    · exact closed _ (palette _ List.mem_cons_self) (rupMono incl step)
    · exact tail d hd

/-- A successful physical run must buy at least one member outside each
certified failing subbank, even when its paid clauses have unrestricted order. -/
theorem mustBuy {F B P : Set (C V)} (closed : ∀c∈P, IsRUP (F∪B) c → c∈B)
    (noEmpty : ∅∉B) {r : List (C V)} (run : IsRUPRun F r) (empty : (∅ : C V)∈r) :
    ∃c∈r, c∉P := by
  classical
  by_contra deny
  push_neg at deny
  exact noEmpty (closedRun closed run deny _ empty)

end PEqualNP.Outside.L_meta_9248.ProjectedDebt
