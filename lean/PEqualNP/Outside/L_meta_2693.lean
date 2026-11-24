import Mathlib
import PEqualNP.Defs

open Sym2

namespace PEqualNP.Outside.L_meta_2693

private lemma representatives (D : Finset (Sym2 (Fin 11))) :
    ∃ T : Finset (Fin 11), T.card ≤ D.card ∧
      ∀ u v : Fin 11, s(u, v) ∈ D → u ∈ T ∨ v ∈ T := by
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert e D he ih =>
    obtain ⟨T, hT, hhit⟩ := ih
    induction e using Sym2.inductionOn with
    | _ a b =>
      refine ⟨insert a T, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem he]
        exact (Finset.card_insert_le a T).trans (Nat.add_le_add_right hT 1)
      · intro u v huv
        rcases Finset.mem_insert.mp huv with h | h
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        · rcases hhit u v h with h | h
          · exact Or.inl (Finset.mem_insert_of_mem h)
          · exact Or.inr (Finset.mem_insert_of_mem h)

set_option maxHeartbeats 6000000 in
private lemma lower (S : Finset (Fin 11))
    (h0_9 : 0 ∈ S ∨ 9 ∈ S)
    (h0_10 : 0 ∈ S ∨ 10 ∈ S)
    (h1_4 : 1 ∈ S ∨ 4 ∈ S)
    (h1_8 : 1 ∈ S ∨ 8 ∈ S)
    (h2_5 : 2 ∈ S ∨ 5 ∈ S)
    (h2_10 : 2 ∈ S ∨ 10 ∈ S)
    (h3_6 : 3 ∈ S ∨ 6 ∈ S)
    (h3_7 : 3 ∈ S ∨ 7 ∈ S)
    (h4_8 : 4 ∈ S ∨ 8 ∈ S)
    (h4_10 : 4 ∈ S ∨ 10 ∈ S)
    (h5_8 : 5 ∈ S ∨ 8 ∈ S)
    (h5_9 : 5 ∈ S ∨ 9 ∈ S)
    (h6_7 : 6 ∈ S ∨ 7 ∈ S)
    (h6_10 : 6 ∈ S ∨ 10 ∈ S)
    (h7_9 : 7 ∈ S ∨ 9 ∈ S)
    (h8_9 : 8 ∈ S ∨ 9 ∈ S)
    : 7 ≤ S.card := by
  rcases h0_9 with m0 | m9
  · rcases h1_4 with m1 | m4
    · rcases h2_5 with m2 | m5
      · rcases h3_6 with m3 | m6
        · rcases h4_8 with m4 | m8
          · rcases h5_8 with m5 | m8
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m6⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m7⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h5_9 with m5 | m9
              · have sub : ({0, 1, 2, 3, 4, 5, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m8, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h4_10 with m4 | m10
            · rcases h5_9 with m5 | m9
              · have sub : ({0, 1, 2, 3, 4, 5, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m8, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h5_9 with m5 | m9
              · have sub : ({0, 1, 2, 3, 5, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m5, m8, m10⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 5, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m8, m9, m10⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
        · rcases h3_7 with m3 | m7
          · rcases h4_8 with m4 | m8
            · rcases h5_8 with m5 | m8
              · have sub : ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m6⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 4, 6, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m6, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 6, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h4_10 with m4 | m10
              · have sub : ({0, 1, 2, 3, 4, 6, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m6, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 6, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 6, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m6, m8, m10⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 6, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h4_8 with m4 | m8
            · rcases h5_8 with m5 | m8
              · have sub : ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m4, m5, m6, m7⟩
                exact (show 7 ≤ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 4, 6, 7, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m4, m6, m7, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 4, 6, 7, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h4_10 with m4 | m10
              · have sub : ({0, 1, 2, 4, 6, 7, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m4, m6, m7, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 4, 6, 7, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 6, 7, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m6, m7, m8, m10⟩
                exact (show 7 ≤ ({0, 1, 2, 6, 7, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
      · rcases h2_10 with m2 | m10
        · rcases h3_6 with m3 | m6
          · rcases h4_8 with m4 | m8
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m6⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m7⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h4_10 with m4 | m10
              · have sub : ({0, 1, 2, 3, 4, 5, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 5, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m5, m8, m10⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 5, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_7 with m3 | m7
            · rcases h4_8 with m4 | m8
              · have sub : ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m6⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 5, 6, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m5, m6, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 5, 6, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h4_8 with m4 | m8
              · have sub : ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m4, m5, m6, m7⟩
                exact (show 7 ≤ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 5, 6, 7, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m5, m6, m7, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 5, 6, 7, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
        · rcases h3_6 with m3 | m6
          · rcases h4_8 with m4 | m8
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 1, 3, 4, 5, 6, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m4, m5, m6, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 4, 5, 6, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 3, 4, 5, 7, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m4, m5, m7, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 4, 5, 7, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 1, 3, 5, 6, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m5, m6, m8, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 5, 6, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 3, 5, 7, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m5, m7, m8, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 5, 7, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_7 with m3 | m7
            · rcases h4_8 with m4 | m8
              · have sub : ({0, 1, 3, 4, 5, 6, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m4, m5, m6, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 4, 5, 6, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 3, 5, 6, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m5, m6, m8, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 5, 6, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h4_8 with m4 | m8
              · have sub : ({0, 1, 4, 5, 6, 7, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m4, m5, m6, m7, m10⟩
                exact (show 7 ≤ ({0, 1, 4, 5, 6, 7, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 5, 6, 7, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m5, m6, m7, m8, m10⟩
                exact (show 7 ≤ ({0, 1, 5, 6, 7, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
    · rcases h1_8 with m1 | m8
      · rcases h2_5 with m2 | m5
        · rcases h3_6 with m3 | m6
          · rcases h5_8 with m5 | m8
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m6⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m7⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h5_9 with m5 | m9
              · have sub : ({0, 1, 2, 3, 4, 5, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m8, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_7 with m3 | m7
            · rcases h5_8 with m5 | m8
              · have sub : ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m6⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 4, 6, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m6, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 6, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h5_8 with m5 | m8
              · have sub : ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m4, m5, m6, m7⟩
                exact (show 7 ≤ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 4, 6, 7, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m4, m6, m7, m8⟩
                exact (show 7 ≤ ({0, 1, 2, 4, 6, 7, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
        · rcases h2_10 with m2 | m10
          · rcases h3_6 with m3 | m6
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m6⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m7⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m6⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m4, m5, m6, m7⟩
                exact (show 7 ≤ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_6 with m3 | m6
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 1, 3, 4, 5, 6, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m4, m5, m6, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 4, 5, 6, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 3, 4, 5, 7, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m4, m5, m7, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 4, 5, 7, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({0, 1, 3, 4, 5, 6, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m4, m5, m6, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 4, 5, 6, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 4, 5, 6, 7, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m4, m5, m6, m7, m10⟩
                exact (show 7 ≤ ({0, 1, 4, 5, 6, 7, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
      · rcases h2_5 with m2 | m5
        · rcases h3_6 with m3 | m6
          · rcases h5_9 with m5 | m9
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 2, 3, 4, 5, 6, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m5, m6, m8⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 5, 6, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 2, 3, 4, 5, 7, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m5, m7, m8⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 5, 7, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 2, 3, 4, 6, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m6, m8, m9⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 6, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 2, 3, 4, 7, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m7, m8, m9⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 7, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_7 with m3 | m7
            · rcases h5_9 with m5 | m9
              · have sub : ({0, 2, 3, 4, 5, 6, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m5, m6, m8⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 5, 6, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 2, 3, 4, 6, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m6, m8, m9⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 6, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h5_9 with m5 | m9
              · have sub : ({0, 2, 4, 5, 6, 7, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m4, m5, m6, m7, m8⟩
                exact (show 7 ≤ ({0, 2, 4, 5, 6, 7, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 2, 4, 6, 7, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m4, m6, m7, m8, m9⟩
                exact (show 7 ≤ ({0, 2, 4, 6, 7, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
        · rcases h2_10 with m2 | m10
          · rcases h3_6 with m3 | m6
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 2, 3, 4, 5, 6, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m5, m6, m8⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 5, 6, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 2, 3, 4, 5, 7, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m5, m7, m8⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 5, 7, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({0, 2, 3, 4, 5, 6, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m5, m6, m8⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 5, 6, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 2, 4, 5, 6, 7, 8} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m4, m5, m6, m7, m8⟩
                exact (show 7 ≤ ({0, 2, 4, 5, 6, 7, 8} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_6 with m3 | m6
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 3, 4, 5, 6, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m3, m4, m5, m6, m8, m10⟩
                exact (show 7 ≤ ({0, 3, 4, 5, 6, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 3, 4, 5, 7, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m3, m4, m5, m7, m8, m10⟩
                exact (show 7 ≤ ({0, 3, 4, 5, 7, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({0, 3, 4, 5, 6, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m3, m4, m5, m6, m8, m10⟩
                exact (show 7 ≤ ({0, 3, 4, 5, 6, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 4, 5, 6, 7, 8, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m4, m5, m6, m7, m8, m10⟩
                exact (show 7 ≤ ({0, 4, 5, 6, 7, 8, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
  · rcases h0_10 with m0 | m10
    · rcases h1_4 with m1 | m4
      · rcases h2_5 with m2 | m5
        · rcases h3_6 with m3 | m6
          · rcases h4_8 with m4 | m8
            · rcases h5_8 with m5 | m8
              · have sub : ({0, 1, 2, 3, 4, 5, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m8, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h4_10 with m4 | m10
              · have sub : ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m8, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m8, m9, m10⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_7 with m3 | m7
            · rcases h4_8 with m4 | m8
              · have sub : ({0, 1, 2, 3, 4, 6, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m6, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 6, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 6, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m6, m8, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 6, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h4_8 with m4 | m8
              · have sub : ({0, 1, 2, 4, 6, 7, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m4, m6, m7, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 4, 6, 7, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 6, 7, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m6, m7, m8, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 6, 7, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
        · rcases h2_10 with m2 | m10
          · rcases h3_6 with m3 | m6
            · rcases h4_8 with m4 | m8
              · have sub : ({0, 1, 2, 3, 4, 5, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 5, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m5, m8, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 5, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({0, 1, 2, 3, 5, 6, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m5, m6, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 5, 6, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 5, 6, 7, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m5, m6, m7, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 5, 6, 7, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_6 with m3 | m6
            · rcases h4_8 with m4 | m8
              · have sub : ({0, 1, 3, 4, 5, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m4, m5, m9, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 4, 5, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 3, 5, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m5, m8, m9, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 5, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({0, 1, 3, 5, 6, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m5, m6, m9, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 5, 6, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 5, 6, 7, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m5, m6, m7, m9, m10⟩
                exact (show 7 ≤ ({0, 1, 5, 6, 7, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
      · rcases h1_8 with m1 | m8
        · rcases h2_5 with m2 | m5
          · rcases h3_6 with m3 | m6
            · rcases h5_8 with m5 | m8
              · have sub : ({0, 1, 2, 3, 4, 5, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m8, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({0, 1, 2, 3, 4, 6, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m6, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 6, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 4, 6, 7, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m4, m6, m7, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 4, 6, 7, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h2_10 with m2 | m10
            · rcases h3_6 with m3 | m6
              · have sub : ({0, 1, 2, 3, 4, 5, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m3, m4, m5, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 3, 4, 5, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 2, 4, 5, 6, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m2, m4, m5, m6, m9⟩
                exact (show 7 ≤ ({0, 1, 2, 4, 5, 6, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_6 with m3 | m6
              · have sub : ({0, 1, 3, 4, 5, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m3, m4, m5, m9, m10⟩
                exact (show 7 ≤ ({0, 1, 3, 4, 5, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 1, 4, 5, 6, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m1, m4, m5, m6, m9, m10⟩
                exact (show 7 ≤ ({0, 1, 4, 5, 6, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
        · rcases h2_5 with m2 | m5
          · rcases h3_6 with m3 | m6
            · rcases h6_7 with m6 | m7
              · have sub : ({0, 2, 3, 4, 6, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m6, m8, m9⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 6, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 2, 3, 4, 7, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m7, m8, m9⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 7, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({0, 2, 3, 4, 6, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m6, m8, m9⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 6, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 2, 4, 6, 7, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m4, m6, m7, m8, m9⟩
                exact (show 7 ≤ ({0, 2, 4, 6, 7, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h2_10 with m2 | m10
            · rcases h3_6 with m3 | m6
              · have sub : ({0, 2, 3, 4, 5, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m3, m4, m5, m8, m9⟩
                exact (show 7 ≤ ({0, 2, 3, 4, 5, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 2, 4, 5, 6, 8, 9} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m2, m4, m5, m6, m8, m9⟩
                exact (show 7 ≤ ({0, 2, 4, 5, 6, 8, 9} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_6 with m3 | m6
              · have sub : ({0, 3, 4, 5, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m3, m4, m5, m8, m9, m10⟩
                exact (show 7 ≤ ({0, 3, 4, 5, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({0, 4, 5, 6, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m0, m4, m5, m6, m8, m9, m10⟩
                exact (show 7 ≤ ({0, 4, 5, 6, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
    · rcases h1_4 with m1 | m4
      · rcases h2_5 with m2 | m5
        · rcases h3_6 with m3 | m6
          · rcases h4_8 with m4 | m8
            · rcases h5_8 with m5 | m8
              · have sub : ({1, 2, 3, 4, 5, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m3, m4, m5, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 3, 4, 5, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 2, 3, 4, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m3, m4, m8, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 3, 4, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h6_7 with m6 | m7
              · have sub : ({1, 2, 3, 6, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m3, m6, m8, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 3, 6, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 2, 3, 7, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m3, m7, m8, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 3, 7, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_7 with m3 | m7
            · rcases h4_8 with m4 | m8
              · have sub : ({1, 2, 3, 4, 6, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m3, m4, m6, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 3, 4, 6, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 2, 3, 6, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m3, m6, m8, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 3, 6, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h4_8 with m4 | m8
              · have sub : ({1, 2, 4, 6, 7, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m4, m6, m7, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 4, 6, 7, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 2, 6, 7, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m6, m7, m8, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 6, 7, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
        · rcases h3_6 with m3 | m6
          · rcases h4_8 with m4 | m8
            · rcases h6_7 with m6 | m7
              · have sub : ({1, 3, 4, 5, 6, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m3, m4, m5, m6, m9, m10⟩
                exact (show 7 ≤ ({1, 3, 4, 5, 6, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 3, 4, 5, 7, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m3, m4, m5, m7, m9, m10⟩
                exact (show 7 ≤ ({1, 3, 4, 5, 7, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h6_7 with m6 | m7
              · have sub : ({1, 3, 5, 6, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m3, m5, m6, m8, m9, m10⟩
                exact (show 7 ≤ ({1, 3, 5, 6, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 3, 5, 7, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m3, m5, m7, m8, m9, m10⟩
                exact (show 7 ≤ ({1, 3, 5, 7, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_7 with m3 | m7
            · rcases h4_8 with m4 | m8
              · have sub : ({1, 3, 4, 5, 6, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m3, m4, m5, m6, m9, m10⟩
                exact (show 7 ≤ ({1, 3, 4, 5, 6, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 3, 5, 6, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m3, m5, m6, m8, m9, m10⟩
                exact (show 7 ≤ ({1, 3, 5, 6, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h4_8 with m4 | m8
              · have sub : ({1, 4, 5, 6, 7, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m4, m5, m6, m7, m9, m10⟩
                exact (show 7 ≤ ({1, 4, 5, 6, 7, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 5, 6, 7, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m5, m6, m7, m8, m9, m10⟩
                exact (show 7 ≤ ({1, 5, 6, 7, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
      · rcases h1_8 with m1 | m8
        · rcases h2_5 with m2 | m5
          · rcases h3_6 with m3 | m6
            · rcases h5_8 with m5 | m8
              · have sub : ({1, 2, 3, 4, 5, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m3, m4, m5, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 3, 4, 5, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 2, 3, 4, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m3, m4, m8, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 3, 4, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({1, 2, 3, 4, 6, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m3, m4, m6, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 3, 4, 6, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 2, 4, 6, 7, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m2, m4, m6, m7, m9, m10⟩
                exact (show 7 ≤ ({1, 2, 4, 6, 7, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_6 with m3 | m6
            · rcases h6_7 with m6 | m7
              · have sub : ({1, 3, 4, 5, 6, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m3, m4, m5, m6, m9, m10⟩
                exact (show 7 ≤ ({1, 3, 4, 5, 6, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 3, 4, 5, 7, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m3, m4, m5, m7, m9, m10⟩
                exact (show 7 ≤ ({1, 3, 4, 5, 7, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({1, 3, 4, 5, 6, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m3, m4, m5, m6, m9, m10⟩
                exact (show 7 ≤ ({1, 3, 4, 5, 6, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({1, 4, 5, 6, 7, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m1, m4, m5, m6, m7, m9, m10⟩
                exact (show 7 ≤ ({1, 4, 5, 6, 7, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
        · rcases h2_5 with m2 | m5
          · rcases h3_6 with m3 | m6
            · rcases h6_7 with m6 | m7
              · have sub : ({2, 3, 4, 6, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m2, m3, m4, m6, m8, m9, m10⟩
                exact (show 7 ≤ ({2, 3, 4, 6, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({2, 3, 4, 7, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m2, m3, m4, m7, m8, m9, m10⟩
                exact (show 7 ≤ ({2, 3, 4, 7, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({2, 3, 4, 6, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m2, m3, m4, m6, m8, m9, m10⟩
                exact (show 7 ≤ ({2, 3, 4, 6, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({2, 4, 6, 7, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m2, m4, m6, m7, m8, m9, m10⟩
                exact (show 7 ≤ ({2, 4, 6, 7, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
          · rcases h3_6 with m3 | m6
            · rcases h6_7 with m6 | m7
              · have sub : ({3, 4, 5, 6, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m3, m4, m5, m6, m8, m9, m10⟩
                exact (show 7 ≤ ({3, 4, 5, 6, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({3, 4, 5, 7, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m3, m4, m5, m7, m8, m9, m10⟩
                exact (show 7 ≤ ({3, 4, 5, 7, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
            · rcases h3_7 with m3 | m7
              · have sub : ({3, 4, 5, 6, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m3, m4, m5, m6, m8, m9, m10⟩
                exact (show 7 ≤ ({3, 4, 5, 6, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)
              · have sub : ({4, 5, 6, 7, 8, 9, 10} : Finset (Fin 11)) ⊆ S := by
                  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                  exact ⟨m4, m5, m6, m7, m8, m9, m10⟩
                exact (show 7 ≤ ({4, 5, 6, 7, 8, 9, 10} : Finset (Fin 11)).card by decide).trans (Finset.card_le_card sub)

end PEqualNP.Outside.L_meta_2693

theorem PEqualNP.Outside.L_meta_2693 : have x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Finset (Sym2 (Fin (11 : ℕ)))) (x3 : Finset (Fin (11 : ℕ))), (x1.deleteEdges ↑x2).IsVertexCover ↑x3 → (7 : ℕ) ≤ x3.card + x2.card := by
  dsimp only
  intro D S hS
  obtain ⟨T, hT, hit⟩ := PEqualNP.Outside.L_meta_2693.representatives D
  have cover (u v : Fin 11)
      (hadj : (PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]).Adj u v) :
      u ∈ S ∪ T ∨ v ∈ S ∪ T := by
    by_cases h : s(u, v) ∈ D
    · rcases hit u v h with h | h
      · exact Or.inl (Finset.mem_union_right _ h)
      · exact Or.inr (Finset.mem_union_right _ h)
    · rcases hS (SimpleGraph.deleteEdges_adj.mpr ⟨hadj, h⟩) with h | h
      · exact Or.inl (Finset.mem_union_left _ h)
      · exact Or.inr (Finset.mem_union_left _ h)
  have lower : 7 ≤ (S ∪ T).card := by
    apply PEqualNP.Outside.L_meta_2693.lower
    all_goals apply cover <;> decide
  exact lower.trans ((Finset.card_union_le S T).trans (Nat.add_le_add_left hT S.card))
