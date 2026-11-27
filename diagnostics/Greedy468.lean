import PEqualNP.Defs
namespace Greedy468
open scoped BigOperators
open Classical in
theorem find_row {A B : Type} [Fintype B] [Nonempty B]
    (U : Finset A) (hu : U.Nonempty) (G : Finset B) (hit : A → B → Prop)
    (d : ℕ) (mass : ∀ x∈U, Fintype.card B ≤ d * (G.filter (hit x)).card) :
    ∃ y∈G, U.card ≤ d * (U.filter (fun x => hit x y)).card := by
  classical
  let f (y : B) := if y∈G then (U.filter (fun x => hit x y)).card else 0
  have count : (∑ y : B, f y) = ∑ x∈U, (G.filter (hit x)).card := by
    simp only [f,← Finset.sum_filter]
    rw [Finset.filter_mem_eq_inter,Finset.univ_inter]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  obtain ⟨y,_,hy⟩ := Finset.exists_max_image (Finset.univ : Finset B) f Finset.univ_nonempty
  have db (x) (hx : x∈U) := mass x hx
  have lower := Finset.sum_le_sum db
  have upper := Finset.sum_le_sum (fun j hj => hy j hj)
  have bound : U.card * Fintype.card B ≤ (d * f y) * Fintype.card B := calc
    _ ≤ ∑ x∈U, d*(G.filter (hit x)).card := by simpa using lower
    _ = d * ∑ t : B, f t := by rw [Finset.mul_sum,count]
    _ ≤ d * (Fintype.card B * f y) := Nat.mul_le_mul_left d (by simpa using upper)
    _ = _ := by ring
  have gain := Nat.le_of_mul_le_mul_right bound Fintype.card_pos
  by_cases ok : y∈G
  · exact ⟨y,ok,by simpa [f,ok] using gain⟩
  · simp [f,ok] at gain
    have positive := Finset.card_pos.mpr hu
    omega

open Classical in
theorem greedy {A B : Type} [Fintype B] [Nonempty B] (U : Finset A)
    (hit : A → B → Prop) (ok : Finset B → Prop) (start : ok ∅)
    (D N : ℕ) (dpos : 1≤D)
    (extend : ∀ H : Finset B, H.card<N → ok H → ∃ G : Finset B,
      (∀ y∈G, ok (insert y H)) ∧
      ∀ x∈U, Fintype.card B ≤ D * (G.filter (hit x)).card)
    (enough : U.card * (D-1)^N < D^N) :
    ∃ H : Finset B, H.card≤N ∧ ok H ∧ ∀ x∈U, ∃ y∈H, hit x y := by
  classical
  let miss (H : Finset B) := U.filter (fun x => ∀ y∈H, ¬hit x y)
  have iter (t : ℕ) (ht : t≤N) : ∃ H : Finset B, H.card≤t ∧ ok H ∧
        (miss H).card*D^t ≤ U.card*(D-1)^t := by
    induction t with
    | zero => exact ⟨∅,by simp,start,by simp [miss]⟩
    | succ t ih =>
      obtain ⟨H,sz,oh,bound⟩ := ih (by omega)
      by_cases nz : (miss H).Nonempty
      · obtain ⟨G,extend,mass⟩ := extend H (by omega) oh
        obtain ⟨y,hy,gain⟩ := find_row (miss H) nz G hit D (fun x hx => mass x (Finset.mem_filter.mp hx).1)
        have split : (miss (insert y H)).card + ((miss H).filter (fun x => hit x y)).card = (miss H).card := by
          have eq : miss (insert y H) = (miss H).filter (fun x => ¬hit x y) := by
            ext x; simp [miss]; tauto
          rw [eq,add_comm]
          exact Finset.card_filter_add_card_filter_not ..
        have step : (miss (insert y H)).card * D ≤ (miss H).card*(D-1) := by
          have eq := congrArg (fun c : ℕ => c*D) split
          have pos : D-1+1=D := by omega
          have lift := congrArg (fun c : ℕ => (miss H).card*c) pos
          simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one] at eq lift
          nlinarith only [eq,lift,gain]
        refine ⟨insert y H,(Finset.card_insert_le ..).trans (by omega),extend y hy,?_⟩
        calc
          _ = ((miss (insert y H)).card*D)*D^t := by rw [pow_succ]; ring
          _ ≤ ((miss H).card*(D-1))*D^t := Nat.mul_le_mul_right _ step
          _ = ((miss H).card*D^t)*(D-1) := by ring
          _ ≤ (U.card*(D-1)^t)*(D-1) := Nat.mul_le_mul_right _ bound
          _ = _ := by rw [pow_succ]; ring
      · refine ⟨H,by omega,oh,?_⟩
        simp [Finset.not_nonempty_iff_eq_empty.mp nz]
  obtain ⟨H,sz,oh,bound⟩ := iter N le_rfl
  have empty : miss H=∅ := by
    by_contra h
    have pos : 1≤(miss H).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)
    have le := Nat.mul_le_mul_right (D^N) pos
    simp at le; omega
  refine ⟨H,sz,oh,?_⟩
  intro x hx
  by_contra! no
  have mem : x∈miss H := Finset.mem_filter.mpr ⟨hx,no⟩
  simpa [empty] using mem
end Greedy468
