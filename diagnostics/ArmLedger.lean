import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9792.ArmLedger

/-- A dyad counted on both shores creates a second contribution to the count. -/
theorem footprintCount {E : Type} [DecidableEq E]
    (left right pivots edges : Finset E)
    (cover : edges ⊆ left ∪ right) (both : pivots ⊆ left ∩ right) :
    edges.card + pivots.card ≤ left.card + right.card := by
  have joint := Finset.card_le_card cover
  have shared := Finset.card_le_card both
  have count := Finset.card_union_add_card_inter left right
  omega

/-- The supports of several wire outputs of a shared binary OR circuit.
An OR instruction consumes two available subsets and emits their union.
A list of selected outputs starts with at most one contributor per output.
Walking backwards can add at most one contributor per OR instruction. -/
theorem joinPrice (inputs outputs gates : Nat)
    (witness : ∃ increments : List Nat, increments.length = gates ∧
      (∀ q ∈ increments, q ≤ 1) ∧ inputs ≤ outputs + increments.sum) :
    inputs ≤ outputs + gates := by
  obtain ⟨inc,len,small,bound⟩ := witness
  have step (l : List Nat) (h : ∀ q ∈ l, q ≤ 1) : l.sum ≤ l.length := by
    induction l with
    | nil => simp
    | cons a t ih =>
      have one := h a (by simp)
      have rest := ih (fun x hx => h x (by simp [hx]))
      simp only [List.sum_cons, List.length_cons]
      omega
  have total := step inc small
  omega

/-- Each matched dyad needs a distinct center. A two-arm product with a given
pivot can supply at most two centers independently of the number of such products. -/
theorem matchingLedger
    (outside single pivots : Nat)
    (occupied : 11 ≤ outside + single + 2 * pivots) :
    6 ≤ outside + single + pivots := by omega

/-- The gate sum has distinct charges for pure union banks, product ANDs,
inside ORs, the guard ANDs and mixed disjunctions, and the outer join. -/
theorem physicalBudget
    (total pure products inside guards outside single double pivots footprint : Nat)
    (leaves : single + double ≤ products)
    (inner : products ≤ inside + guards)
    (outer : pure + products + inside + 3 * guards + 2 * outside ≤ total + 1)
    (regional : footprint ≤ pure + outside + single + 2 * double)
    (covered : 44 + pivots ≤ footprint) :
    43 + 2 * guards + outside + single + pivots ≤ total := by omega

theorem atLeast55
    (total pure products inside guards outside single double pivots footprint : Nat)
    (many : 3 ≤ guards) (occupied : 11 ≤ outside + single + 2 * pivots)
    (leaves : single + double ≤ products)
    (inner : products ≤ inside + guards)
    (outer : pure + products + inside + 3 * guards + 2 * outside ≤ total + 1)
    (regional : footprint ≤ pure + outside + single + 2 * double)
    (covered : 44 + pivots ≤ footprint) : 55 ≤ total := by
  have a := matchingLedger outside single pivots occupied
  have b := physicalBudget total pure products inside guards outside single double pivots footprint
    leaves inner outer regional covered
  omega

end PEqualNP.Outside.L_meta_9792.ArmLedger
