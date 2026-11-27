import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7290.HallDyads
abbrev I := Fin 13
def D : Finset I := {0,1,3,9}
def adjacent (dual : Bool) (p l : I) : Bool :=
  if dual then decide (l-p∈D) else decide (p-l∈D)
def degree (dual : Bool) (p : I) (L : Finset I) := (L.filter (fun l => adjacent dual p l=true)).card
def incidences (dual : Bool) (P L : Finset I) := ∑ p ∈ P, degree dual p L
def extra (dual : Bool) (L : Finset I) := ∑ p : I, (degree dual p L-1)
theorem four (d : Bool) (p : I) : degree d p Finset.univ = 4 := by decide +revert
theorem partition (d : Bool) (p : I) (L : Finset I) :
    degree d p L + degree d p Lᶜ = 4 := by
  have hu : L.filter (fun l => adjacent d p l=true) ∪ Lᶜ.filter (fun l => adjacent d p l=true) =
      Finset.univ.filter (fun l => adjacent d p l=true) := by ext l; simp; tauto
  have hd : Disjoint (L.filter (fun l => adjacent d p l=true)) (Lᶜ.filter (fun l => adjacent d p l=true)) := by
    apply Finset.disjoint_left.mpr
    intro l h h'; simp_all
  change _ + _ = _
  unfold degree
  rw [← Finset.card_union_of_disjoint hd, hu]
  exact four d p

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem small_excess : ∀ (d : Bool) (K : Finset I), K.card ≤ 6 →
    2 * extra d K ≤ K.card * (K.card-1) := by decide +kernel

theorem arithmetic (a k e : ℕ) (ha : 2≤a) (hA : a≤7) (hk : k<a)
    (he : 2*e ≤ k*(k-1)) : e+6≤3*a := by
  have hkk : k≤6 := by omega
  interval_cases k <;> omega

theorem low (d : Bool) (P L : Finset I) (hp : 2≤P.card) (hp' : P.card≤7)
    (hs : 14≤P.card+L.card) : 6≤incidences d P L := by
  have csum : Lᶜ.card+L.card=13 := by simpa using Finset.card_compl_add_card L
  have hk : Lᶜ.card<P.card := by omega
  have cap := small_excess d Lᶜ (by omega)
  have budget := arithmetic P.card Lᶜ.card (extra d Lᶜ) hp hp' hk cap
  have sub : (∑ p ∈ P, (degree d p Lᶜ - 1)) ≤ extra d Lᶜ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intros; exact Nat.zero_le _
  have up : incidences d P Lᶜ ≤ P.card + ∑ p ∈ P, (degree d p Lᶜ - 1) := by
    calc
      _ ≤ ∑ p ∈ P, (1 + (degree d p Lᶜ - 1)) := Finset.sum_le_sum fun p _ => by omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have total : incidences d P L + incidences d P Lᶜ = 4*P.card := by
    unfold incidences
    rw [← Finset.sum_add_distrib]
    simp [partition, Nat.mul_comm]
  omega

theorem incidence_mono (d : Bool) {A P : Finset I} (sub : A⊆P) (L : Finset I) :
    incidences d A L ≤ incidences d P L := by
  apply Finset.sum_le_sum_of_subset_of_nonneg sub
  intros; exact Nat.zero_le _

theorem away_from_pencil (d : Bool) (P L : Finset I) (hp : 2≤P.card) (hl : 7≤L.card)
    (hs : 14≤P.card+L.card) : 6≤incidences d P L := by
  by_cases h : P.card ≤ 7
  · exact low d P L hp h hs
  · obtain ⟨A,sub,sz⟩ := Finset.exists_subset_card_eq (show 7≤P.card by omega)
    exact (low d A L (by omega) (by omega) (by omega)).trans (incidence_mono d sub L)

end PEqualNP.Outside.L_meta_7290.HallDyads
