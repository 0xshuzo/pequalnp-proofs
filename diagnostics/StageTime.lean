import PEqualNP.Defs
-- The packed checker derives from the published L_meta_8405.
-- Six-bit budget lanes allow a gate budget of twenty. Input data and graph are local.

-- The search engine is adapted from PEqualNP.Outside.L_meta_1673 by Trey Kind (pull request 6929, Apache License 2.0).
-- This file declares its own data types (records for the search state and inductive predicates).

namespace PEqualNP.Outside.L_meta_9732
variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
lemma Al.symm {d : Bool} {a b : ℕ} (h : Al R d a b) : Al R d b a := by unfold Al at *; rwa [Nat.and_comm]
def Z0 : ℕ → ℕ := fun _ => 0
lemma al0 (d : Bool) (a b : ℕ) : Al Z0 d a b := by simp [Al, Z0]
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol R m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R' : ℕ → ℕ} {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Sol R' m T q S := by
  induction h with
  | done h => exact .done h
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) : Sol Z0 m T q S := h.rel fun d a b _ => al0 d a b
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
lemma Live.zeroUnary {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : t = 0 := by
  induction h with
  | stop => rfl
  | bi _ _ _ ih => exact ih
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : Sol Z0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @bi q S d a b ha hb hal _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left
def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := False
def Bi (R : ℕ → ℕ) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) (t + 1) S := False.elim h
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl, hal⟩ := h; exact .bi hab hal hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') : Bi R d b a S S' := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm], hal.symm⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := False.elim h
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
def Min (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live R m T k t S ∧ ∀ q < k, ¬ Sol Z0 m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := False.elim h
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (al0 _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : a ^^^ m ∉ C m S := False.elim h
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min R m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := False.elim h
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi R d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_, hal⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := False.elim h
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := False.elim h
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min R m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi R d a b S S1 ∧ Live R m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi R d (a ^^^ m) c S1 S2 ∧ Live R m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi R d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live R m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hal hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl, hal⟩, hl⟩
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := False.elim h
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (al0 _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) : Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min R m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩
def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @bi k t d a b U _ _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hal : Al R d a b) (hl : Live R m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min R m T k t (insert (op d a b) U) := by
  have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live R m T k 0 S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @bi k t d x y U hxy hal hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @bi k t d x y U hxy hal hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @bi k t d x y U hxy hal hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect
section chrom
variable {N m T : ℕ}
def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
lemma Ht.symm {e : Bool} {S : Finset ℕ} {a b : ℕ} (h : Ht N m T e S a b) : Ht N m T e S b a := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  exact ⟨i2, i1, j2, j1, l2, l1, l4, l3, fun w hw => (r1 w hw).symm, fun w hw => (r2 w hw).symm, u2, u1, u4, u3, p2, p1⟩
lemma bi_uq2 {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hi : Lg N m T i) (hc : c ∈ insert a (insert b U)) (h1 : c = a → a ∉ U) (h2 : c = b → b ∉ U)
    (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hcU : c ∉ U := by
      rcases hcc with rfl | rfl; exacts [h1 rfl, h2 rfl]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl; exact hcU hx
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma pol_op {a b i : ℕ} {d e : Bool} (ha : sepb N e a i = true) (hb : sepb N e b i = false) (ho : sepb N e (op d a b) i = true) :
    (op d a b).testBit i = a.testBit i := by
  revert ha hb ho; unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
    cases b.testBit (N + i) <;> simp
lemma pol_phi {a b c i : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (h : Uq N e (insert a (insert b U)) c i)
    (hu : Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i) :
    (if c = a ∨ c = b then op d a b else c).testBit i = c.testBit i := by
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc] at hu ⊢
    rcases hcc with rfl | rfl
    · exact pol_op h.1 (h.2 b (by simp) (Ne.symm hab)) hu.1
    · rw [op_comm] at hu ⊢
      exact pol_op h.1 (h.2 a (by simp) hab) hu.1
  · rw [ite_eq_right hcc]
lemma ht_bi {a b k t c1 c2 : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hc1 : c1 ∈ insert a (insert b U)) (hc2 : c2 ∈ insert a (insert b U))
    (h1 : c1 = a → a ∉ U) (h1' : c1 = b → b ∉ U) (h2 : c2 = a → a ∉ U) (h2' : c2 = b → b ∉ U)
    (h : Ht N m T e (insert a (insert b U)) c1 c2) :
    Ht N m T e (insert (op d a b) U) (if c1 = a ∨ c1 = b then op d a b else c1) (if c2 = a ∨ c2 = b then op d a b else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := bi_uq2 he hl l1 hc1 h1 h1' u1
  have v2 := bi_uq2 he hl l2 hc2 h2 h2' u2
  have v3 := bi_uq2 he hl l3 hc1 h1 h1' u3
  have v4 := bi_uq2 he hl l4 hc2 h2 h2' u4
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, v1, v2, v3, v4, ?_, ?_⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r1 a (by simp), r1 b (by simp)]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r2 a (by simp), r2 b (by simp)]
    · exact r2 w (by simp [hw])
  · rw [pol_phi hab u1 v1, pol_phi hab u3 v3, p1]
  · rw [pol_phi hab u2 v2, pol_phi hab u4 v4, p2]
lemma ht_merge {a b k t : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (h : Ht N m T e (insert a (insert b U)) a b) : False := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := (bi_uq2 he hl l1 (by simp) (fun _ => ha) (fun _ => hb) u1).1
  have v2 := (bi_uq2 he hl l2 (by simp) (fun _ => ha) (fun _ => hb) u2).1
  have v3 := (bi_uq2 he hl l3 (by simp) (fun _ => ha) (fun _ => hb) u3).1
  have v4 := (bi_uq2 he hl l4 (by simp) (fun _ => ha) (fun _ => hb) u4).1
  simp only [true_or, or_true, if_true] at v1 v2 v3 v4
  have e1 := r1 a (by simp); have e2 := r2 a (by simp); have e1b := r1 b (by simp); have e2b := r2 b (by simp)
  have n1 := u1.2 b (by simp) (Ne.symm hab); have n3 := u3.2 b (by simp) (Ne.symm hab)
  have n2 := u2.2 a (by simp) hab; have n4 := u4.2 a (by simp) hab
  have s1 := u1.1; have s2 := u2.1; have s3 := u3.1; have s4 := u4.1
  revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 v1 v2 v3 v4 p1 p2
  unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> simp <;> grind
lemma un_uq2 {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (h1 : c = a → a ∉ U) (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  by_cases hca : c = a
  · exact un_uq hi (h1 hca) hc h
  · rw [ite_eq_right hca]
    have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
    · exact h.2 x (by simp [hx]) hne
lemma ht_un {a c1 c2 : ℕ} {U : Finset ℕ} (hc1 : c1 ∈ insert a U) (hc2 : c2 ∈ insert a U) (h1 : c1 = a → a ∉ U) (h2 : c2 = a → a ∉ U)
    (h : Ht N m T true (insert a U) c1 c2) :
    Ht N m T true (insert (a ^^^ m) U) (if c1 = a then a ^^^ m else c1) (if c2 = a then a ^^^ m else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
      (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
    intro c i j m1 m2 p
    split_ifs with h
    · subst h; simp [m1, m2, p]
    · exact p
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, un_uq2 l1 h1 hc1 u1, un_uq2 l2 h2 hc2 u2, un_uq2 l3 h1 hc1 u3, un_uq2 l4 h2 hc2 u4,
    pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r1 a (by simp), l1.1, l2.1]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r2 a (by simp), l3.2.1, l4.2.1]
    · exact r2 w (by simp [hw])
lemma chrom {e : Bool} {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (he : e = true ∨ t = 0) :
    ∃ (x : ℕ) (f : ℕ → ℕ), S.card + t + x = k + 1 ∧ (∀ a ∈ S, f a ≤ x) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Ht N m T e S a b → f a ≠ f b := by
  induction hl with
  | stop =>
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hu.fresh hl hm (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have hmin := hu.min hl hm
    have he2 : e = true ∨ e = pos' t := by
      rcases he with h | h
      · exact Or.inl h
      · subst h; cases e <;> simp [pos']
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 he
    rw [Finset.card_insert_of_notMem hf] at hx
    have mem : ∀ {c : ℕ}, c ∈ insert a (insert b U) → (if c = a ∨ c = b then op d a b else c) ∈ insert (op d a b) U := fun h => phi_mem h
    by_cases ha : a ∈ U
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = U := by rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
        refine ⟨x + 2, fun c => if c = a then x + 2 else if c = b then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
        · intro c hcS
          rw [eS] at hcS
          have := hfx c (by simp [hcS])
          dsimp only; split_ifs <;> omega
        · intro c1 h1 c2 h2 h12 hh
          have k1 := h1; have k2 := h2
          rw [eS] at h1 h2
          have f1 := hfx c1 (by simp [h1]); have f2 := hfx c2 (by simp [h2])
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
            · by_cases q3 : c1 = b
              · have q4 : c2 ≠ b := fun e => h12 (q3.trans e.symm)
                simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
              · by_cases q4 : c2 = b
                · simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
                · simp only [q1, q2, q3, q4, if_false]
                  have := ht_bi hab he2 hl k1 k2 (fun e => absurd e q1) (fun e => absurd e q3) (fun e => absurd e q2) (fun e => absurd e q4) hh
                  simp only [q1, q2, q3, q4, or_self, if_false] at this
                  exact hc c1 (by simp [h1]) c2 (by simp [h2]) h12 this
      · have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
        refine ⟨x + 1, fun c => if c = a then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem hb]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = a
          · simp [hca]
          · simp only [hca, if_false, false_or] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, false_or] at f2 ⊢; omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false, false_or] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun e => absurd e q1) (fun _ => hb) (fun e => absurd e q2) (fun _ => hb) hh
              simp only [q1, q2, if_false, false_or] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = b ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = b ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = insert a U := by rw [Finset.insert_eq_of_mem hb]
        refine ⟨x + 1, fun c => if c = b then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem ha]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = b
          · simp [hca]
          · simp only [hca, if_false, or_false] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = b
          · have q2 : c2 ≠ b := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, or_false] at f2 ⊢; omega
          · by_cases q2 : c2 = b
            · simp only [q1, q2, if_true, if_false, or_false] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun e => absurd e q1) (fun _ => ha) (fun e => absurd e q2) hh
              simp only [q1, q2, if_false, or_false] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = a ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = a ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
      · refine ⟨x, fun c => f (if c = a ∨ c = b then op d a b else c), ?_, fun c hcS => hfx _ (mem hcS), ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]; omega
        · intro c1 h1 c2 h2 h12 hh
          by_cases hab' : (c1 = a ∨ c1 = b) ∧ (c2 = a ∨ c2 = b)
          · exfalso
            have : Ht N m T e (insert a (insert b U)) a b := by
              rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
              · exact absurd rfl h12
              · exact hh
              · exact hh.symm
              · exact absurd rfl h12
            exact ht_merge hab he2 hl ha hb this
          · exact hc _ (mem h1) _ (mem h2) (phi_ne hf h1 h2 h12 hab')
              (ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun _ => hb) (fun _ => ha) (fun _ => hb) hh)
end chrom
open Finset in
def Acc (n T k b : ℕ) (D : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∀ U ⊆ S, ∀ q, q + b < k + ∑ w ∈ S \ U, D w → ¬ Sol Z0 n (T &&& n) q (C n (Im n U))
lemma Acc.start {n T K b L : ℕ} {W : Set ℕ} {S : Finset ℕ} (h : ∀ q < L, ¬ Sol Z0 n (T &&& n) q (C n W)) (hS : Im n S ⊆ W)
    (hb : K ≤ b + L) : Acc n T K b (fun _ => 0) S := by
  intro U hU q hq hs
  simp only [Finset.sum_const_zero] at hq
  refine h q (by omega) (hs.mono le_rfl (C_mono (subset_trans ?_ hS)))
  exact Set.image_mono (by exact_mod_cast hU)
lemma Acc.const {m n T k k' t b : ℕ} {D : ℕ → ℕ} {S : Finset ℕ} (hn : n &&& m = n) (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n)
    (h : Acc n T k b D S) (hm : Min R m T k' t S) (hk : k' ≤ k) : (S.filter (Cst n)).card ≤ b := by
  obtain ⟨q, hq, hs⟩ := hm.const hn hT0 hT1
  by_contra hc
  exact h S subset_rfl q (by simp only [sdiff_self, Finset.bot_eq_empty, Finset.sum_empty]; omega) hs
lemma Acc.step {n T k b δ c' : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (h : Acc n T (k + 1) b D S)
    (H : ∀ U' ⊆ S', ∀ q, Sol Z0 n (T &&& n) q (C n (Im n U')) → ∃ U ⊆ S, ∃ r, Sol Z0 n (T &&& n) r (C n (Im n U)) ∧
      r + δ + ∑ w ∈ S' \ U', D' w ≤ q + 1 + ∑ w ∈ S \ U, D w)
    (he : ∃ q, q + c' ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S'))) : δ + c' ≤ b ∧ Acc n T k (b - δ) D' S' := by
  have hd : δ + c' ≤ b := by
    obtain ⟨q, hq, hs⟩ := he
    obtain ⟨U, hU, r, hr, hle⟩ := H S' subset_rfl q hs
    by_contra hc
    refine h U hU r ?_ hr
    simp only [sdiff_self, Finset.bot_eq_empty, Finset.sum_empty] at hle
    omega
  refine ⟨hd, fun U' hU' q hq hs => ?_⟩
  obtain ⟨U, hU, r, hr, hle⟩ := H U' hU' q hs
  exact h U hU r (by omega) hr
section sums
variable {g a c : ℕ} {U0 U' : Finset ℕ} {D D' : ℕ → ℕ}
lemma sum_child (hg : g ∉ U0) : ∑ w ∈ insert g U0 \ U', D' w = (if g ∈ U' then 0 else D' g) + ∑ w ∈ U0 \ U'.erase g, D' w := by
  have e : U0 \ U'.erase g = U0 \ U' := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_erase, not_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (fun e => hg (e ▸ h1)) h⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
  rw [e]
  by_cases h : g ∈ U'
  · rw [ite_eq_left h, Finset.insert_sdiff_of_mem _ h, zero_add]
  · rw [ite_eq_right h, Finset.insert_sdiff_of_notMem _ h, Finset.sum_insert (by simp [hg])]
lemma sum_parent {V : Finset ℕ} (hV : V ⊆ U0) (hac : a ≠ c) :
    ∑ w ∈ insert a (insert c U0) \ V, D w = ∑ w ∈ U0 \ V, D w + (if a ∈ U0 then 0 else D a) + (if c ∈ U0 then 0 else D c) := by
  have e : insert a (insert c U0) \ V = (insert a (insert c U0)) \ V := rfl
  by_cases ha : a ∈ U0 <;> by_cases hc : c ∈ U0
  · rw [Finset.insert_eq_of_mem (by simp [ha]), Finset.insert_eq_of_mem hc]; simp [ha, hc]
  · rw [Finset.insert_eq_of_mem (by simp [ha]), Finset.insert_sdiff_of_notMem _ (fun h => hc (hV h)), Finset.sum_insert (by simp [hc])]
    simp [ha, hc]; omega
  · rw [Finset.insert_eq_of_mem hc, Finset.insert_sdiff_of_notMem _ (fun h => ha (hV h)), Finset.sum_insert (by simp [ha])]
    simp [ha, hc]; omega
  · rw [Finset.insert_sdiff_of_notMem _ (fun h => ha (hV h)), Finset.insert_sdiff_of_notMem _ (fun h => hc (hV h)),
      Finset.sum_insert (by simp [ha, hac]), Finset.sum_insert (by simp [hc])]
    simp [ha, hc]; omega
lemma sum_mono {A B : Finset ℕ} (hAB : ∀ w ∈ A, w ∉ B → D' w = 0) (hD : ∀ w ∈ A, w ∈ B → D' w ≤ D w) : ∑ w ∈ A, D' w ≤ ∑ w ∈ B, D w := by
  calc ∑ w ∈ A, D' w = ∑ w ∈ A.filter (· ∈ B), D' w := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun w hw => ?_
        split_ifs with h
        · rfl
        · exact hAB w hw h
    _ ≤ ∑ w ∈ A.filter (· ∈ B), D w := Finset.sum_le_sum fun w hw => by simp at hw; exact hD w hw.1 hw.2
    _ ≤ ∑ w ∈ B, D w := Finset.sum_le_sum_of_subset fun w hw => by simp at hw; exact hw.2
end sums
inductive Kd
  | N | K0 | KA | KC
def Kd.ok (n : ℕ) (d : Bool) (a c : ℕ) : Kd → Prop
  | .N => True
  | .K0 => Cst n (op d a c)
  | .KA => op d a c &&& n = a &&& n
  | .KC => op d a c &&& n = c &&& n
def Kd.del (la lc : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => 1 + la + lc
  | .KA => 1 + lc
  | .KC => 1 + la
def Kd.out (la lc : ℕ) : Kd → ℕ
  | .N => 1 + la + lc
  | .K0 => 0
  | .KA => la
  | .KC => lc
def Kd.kpa (x : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => x
  | .KA => 0
  | .KC => x
def Kd.kpc (x : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => x
  | .KA => x
  | .KC => 0
structure DStep (κ : Kd) (D D' : ℕ → ℕ) (g a c : ℕ) (S' : Finset ℕ) : Prop where
  hg : D' g ≤ κ.out (if a ∈ S' then 0 else D a) (if c ∈ S' then 0 else D c)
  ha : a ∈ S' → D' a ≤ κ.kpa (D a)
  hc : c ∈ S' → D' c ≤ κ.kpc (D c)
  ho : ∀ w ∈ S', w ≠ g → w ≠ a → w ≠ c → D' w ≤ D w
lemma kpa_le (κ : Kd) (x : ℕ) : κ.kpa x ≤ x := by cases κ <;> simp [Kd.kpa]
lemma kpc_le (κ : Kd) (x : ℕ) : κ.kpc x ≤ x := by cases κ <;> simp [Kd.kpc]
theorem Acc.bi {m n T k k' t b : ℕ} {d : Bool} {a c : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hn : n &&& m = n) (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n)
    (h : Acc n T (k + 1) b D S) (hb : Bi R d a c S S') (hm : Min R m T (k' + 1) t S) (hl : Live R m T k' t S') (hk : k' ≤ k)
    (κ : Kd) (hκ : κ.ok n d a c) (hD : DStep κ D D' (op d a c) a c S') :
    κ.del (if a ∈ S' then 0 else D a) (if c ∈ S' then 0 else D c) + (S'.filter (Cst n)).card ≤ b ∧
      Acc n T k (b - κ.del (if a ∈ S' then 0 else D a) (if c ∈ S' then 0 else D c)) D' S' := by
  have hfr : op d a c ∉ S := fun h' => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h'))
  have hmin := hb.min hl hm.2
  obtain ⟨hac, U0, hS, hS', hal⟩ := hb
  set g := op d a c with hgdef
  have hgU : g ∉ U0 := fun h' => hfr (by rw [hS]; simp [h'])
  have hga : a ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have hgc : c ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have iffa : a ∈ S' ↔ a ∈ U0 := by rw [hS']; simp [hga]
  have iffc : c ∈ S' ↔ c ∈ U0 := by rw [hS']; simp [hgc]
  have hDa : a ∈ U0 → D' a ≤ κ.kpa (D a) := fun h' => hD.ha (iffa.2 h')
  have hDc : c ∈ U0 → D' c ≤ κ.kpc (D c) := fun h' => hD.hc (iffc.2 h')
  have hDg := hD.hg
  simp only [iffa, iffc] at hDg ⊢
  have hDo : ∀ w ∈ U0, w ≠ a → w ≠ c → D' w ≤ D w := fun w hw h1 h2 => hD.ho w (by rw [hS']; simp [hw]) (fun e => hgU (e ▸ hw)) h1 h2
  have hDle : ∀ w ∈ U0, D' w ≤ D w := by
    intro w hw
    by_cases h1 : w = a
    · subst h1; exact (hDa hw).trans (kpa_le _ _)
    by_cases h2 : w = c
    · subst h2; exact (hDc hw).trans (kpc_le _ _)
    exact hDo w hw h1 h2
  refine Acc.step h ?_ ?_
  · intro U' hU' q hs
    have hV : U'.erase g ⊆ U0 := by
      intro x hx
      rw [Finset.mem_erase] at hx
      have := hU' hx.2; rw [hS', Finset.mem_insert] at this
      exact this.resolve_left hx.1
    have hVS : U'.erase g ⊆ S := hV.trans (by rw [hS]; intro x hx; simp [hx])
    have hUi : U' ⊆ insert g (U'.erase g) := fun x hx => by by_cases e : x = g <;> simp [e, hx]
    rw [hS', sum_child (D' := D') hgU]
    by_cases hgU' : g ∈ U'
    · rw [ite_eq_left hgU', zero_add]
      cases κ with
      | N =>
        refine ⟨insert a (insert c (U'.erase g)), ?_, q + 1, ?_, ?_⟩
        · intro x hx; simp only [Finset.mem_insert] at hx
          rcases hx with rfl | rfl | hx
          · rw [hS]; simp
          · rw [hS]; simp
          · exact hVS hx
        · refine .bi (d := d) (Im_mem (x := a) (by simp)) (Im_mem (x := c) (by simp)) (al0 _ _ _)
            (hs.mono le_rfl (C_Im_sub (S := insert a (insert c (U'.erase g))) (hUi.trans (Finset.insert_subset_insert _ ?_)) ?_ (Set.subset_insert _ _)))
          · intro x hx; simp only [Finset.mem_insert]; exact Or.inr (Or.inr hx)
          · rw [hgdef, and_op]; exact Or.inl rfl
        · have : ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ S \ insert a (insert c (U'.erase g)), D w := by
            refine sum_mono (fun w hw hw2 => ?_) (fun w hw _ => hDle w (Finset.mem_sdiff.1 hw).1)
            rw [Finset.mem_sdiff] at hw
            have : w = a ∨ w = c := by
              by_contra hno; push Not at hno
              exact hw2 (Finset.mem_sdiff.2 ⟨by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; tauto⟩)
            rcases this with rfl | rfl
            · have := hDa hw.1; simpa [Kd.kpa] using this
            · have := hDc hw.1; simpa [Kd.kpc] using this
          simp only [Kd.del]; omega
      | K0 =>
        refine ⟨U'.erase g, hVS, q, hs.mono le_rfl (C_Im_sub hUi (Cst_mem hκ) subset_rfl), ?_⟩
        have h1 : ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ U0 \ U'.erase g, D w := Finset.sum_le_sum fun w hw => hDle w (Finset.mem_sdiff.1 hw).1
        rw [hS, sum_parent hV hac]; simp only [Kd.del]; omega
      | KA =>
        refine ⟨insert a (U'.erase g), ?_, q, hs.mono le_rfl (C_Im_sub (S := insert a (U'.erase g)) (hUi.trans (Finset.insert_subset_insert _ (Finset.subset_insert _ _))) ?_ subset_rfl), ?_⟩
        · intro x hx; simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · rw [hS]; simp
          · exact hVS hx
        · have e : g &&& n = a &&& n := hκ
          rw [e]; exact Im_mem (by simp)
        · have : ∑ w ∈ U0 \ U'.erase g, D' w + (if c ∈ U0 then 0 else D c) ≤ ∑ w ∈ S \ insert a (U'.erase g), D w := by
            have key : ∀ B : Finset ℕ, (∀ w ∈ U0 \ U'.erase g, w ≠ a → w ∈ B) → ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ B, D w := by
              intro B hB
              refine sum_mono (fun w hw hw2 => ?_) (fun w hw _ => hDle w (Finset.mem_sdiff.1 hw).1)
              have : w = a := by by_contra hno; exact hw2 (hB w hw hno)
              subst this
              have := hDa (Finset.mem_sdiff.1 hw).1; simpa [Kd.kpa] using this
            by_cases hc : c ∈ U0
            · rw [ite_eq_left hc, add_zero]
              refine key _ fun w hw hne => ?_
              rw [Finset.mem_sdiff] at hw ⊢
              exact ⟨by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; tauto⟩
            · rw [ite_eq_right hc]
              have hcB : c ∈ S \ insert a (U'.erase g) := by
                rw [Finset.mem_sdiff]
                refine ⟨by rw [hS]; simp, ?_⟩
                simp only [Finset.mem_insert]
                rintro (h1 | h1)
                · exact hac h1.symm
                · exact hc (hV h1)
              rw [← Finset.sum_erase_add _ _ hcB]
              refine Nat.add_le_add_right (key _ fun w hw hne => ?_) _
              rw [Finset.mem_sdiff] at hw
              rw [Finset.mem_erase, Finset.mem_sdiff]
              exact ⟨fun e => hc (e ▸ hw.1), by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; tauto⟩
          simp only [Kd.del]; omega
      | KC =>
        refine ⟨insert c (U'.erase g), ?_, q, hs.mono le_rfl (C_Im_sub (S := insert c (U'.erase g)) (hUi.trans (Finset.insert_subset_insert _ (Finset.subset_insert _ _))) ?_ subset_rfl), ?_⟩
        · intro x hx; simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · rw [hS]; simp
          · exact hVS hx
        · have e : g &&& n = c &&& n := hκ
          rw [e]; exact Im_mem (by simp)
        · have : ∑ w ∈ U0 \ U'.erase g, D' w + (if a ∈ U0 then 0 else D a) ≤ ∑ w ∈ S \ insert c (U'.erase g), D w := by
            have key : ∀ B : Finset ℕ, (∀ w ∈ U0 \ U'.erase g, w ≠ c → w ∈ B) → ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ B, D w := by
              intro B hB
              refine sum_mono (fun w hw hw2 => ?_) (fun w hw _ => hDle w (Finset.mem_sdiff.1 hw).1)
              have : w = c := by by_contra hno; exact hw2 (hB w hw hno)
              subst this
              have := hDc (Finset.mem_sdiff.1 hw).1; simpa [Kd.kpc] using this
            by_cases ha : a ∈ U0
            · rw [ite_eq_left ha, add_zero]
              refine key _ fun w hw hne => ?_
              rw [Finset.mem_sdiff] at hw ⊢
              exact ⟨by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; tauto⟩
            · rw [ite_eq_right ha]
              have haB : a ∈ S \ insert c (U'.erase g) := by
                rw [Finset.mem_sdiff]
                refine ⟨by rw [hS]; simp, ?_⟩
                simp only [Finset.mem_insert]
                rintro (h1 | h1)
                · exact hac h1
                · exact ha (hV h1)
              rw [← Finset.sum_erase_add _ _ haB]
              refine Nat.add_le_add_right (key _ fun w hw hne => ?_) _
              rw [Finset.mem_sdiff] at hw
              rw [Finset.mem_erase, Finset.mem_sdiff]
              exact ⟨fun e => ha (e ▸ hw.1), by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; tauto⟩
          simp only [Kd.del]; omega
    · rw [ite_eq_right hgU']
      have e : U'.erase g = U' := Finset.erase_eq_of_notMem hgU'
      rw [e] at hV hVS ⊢
      refine ⟨U', hVS, q, hs, ?_⟩
      have h1 : ∑ w ∈ U0 \ U', D' w ≤ ∑ w ∈ U0 \ U', D w := Finset.sum_le_sum fun w hw => hDle w (Finset.mem_sdiff.1 hw).1
      rw [hS, sum_parent hV hac]
      cases κ <;> simp only [Kd.del, Kd.out] at hDg ⊢ <;> omega
  · obtain ⟨q, hq, hs⟩ := hmin.const hn hT0 hT1
    exact ⟨q, by omega, hs⟩
theorem Acc.un {m n T k k' t b : ℕ} {a : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hn : n &&& m = n) (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n)
    (h : Acc n T (k + 1) b D S) (hb : Un m a S S') (hm : Min R m T (k' + 1) (t + 1) S) (hl : Live R m T k' t S') (hk : k' ≤ k) (κ : Bool)
    (hκ : κ = true → Cst n a) (hg : D' (a ^^^ m) ≤ (if κ then 0 else 1) + (if a ∈ S' then 0 else D a))
    (hka : a ∈ S' → D' a ≤ if κ then D a else 0) (ho : ∀ w ∈ S', w ≠ a ^^^ m → w ≠ a → D' w ≤ D w) :
    (if κ then 1 else 0) + (S'.filter (Cst n)).card ≤ b ∧ Acc n T k (b - if κ then 1 else 0) D' S' := False.elim hb
lemma Kd.out_le (κ : Kd) (la lc : ℕ) : κ.out la lc ≤ 1 + la + lc := by cases κ <;> simp [Kd.out] <;> omega
lemma DStep.le {κ : Kd} {D D' : ℕ → ℕ} {g a c : ℕ} {S' : Finset ℕ} (h : DStep κ D D' g a c S') : ∀ w ∈ S', w ≠ g → D' w ≤ D w := by
  intro w hw hg
  by_cases h1 : w = a
  · subst h1; exact (h.ha hw).trans (kpa_le _ _)
  by_cases h2 : w = c
  · subst h2; exact (h.hc hw).trans (kpc_le _ _)
  exact h.ho w hw hg h1 h2
lemma DStep.sum_le {κ : Kd} {d : Bool} {a c : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hb : Bi R d a c S S') (hfr : op d a c ∉ S)
    (h : DStep κ D D' (op d a c) a c S') : ∑ w ∈ S', D' w ≤ 1 + ∑ w ∈ S, D w := by
  obtain ⟨hac, U0, hS, hS', hal⟩ := hb
  set g := op d a c with hgdef
  have hgU : g ∉ U0 := fun h' => hfr (by rw [hS]; simp [h'])
  have hga : a ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have hgc : c ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have iffa : a ∈ S' ↔ a ∈ U0 := by rw [hS']; simp [hga]
  have iffc : c ∈ S' ↔ c ∈ U0 := by rw [hS']; simp [hgc]
  have h1 := h.hg.trans (Kd.out_le _ _ _)
  simp only [iffa, iffc] at h1
  have h2 : ∑ w ∈ U0, D' w ≤ ∑ w ∈ U0, D w := Finset.sum_le_sum fun w hw => h.le w (by rw [hS']; simp [hw]) (fun e => hgU (e ▸ hw))
  have h3 := sum_parent (D := D) (U0 := U0) (V := ∅) (by simp) hac
  simp only [Finset.sdiff_empty] at h3
  rw [hS', Finset.sum_insert hgU, hS, h3]
  omega
lemma un_sum_le {m a e : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hb : Un m a S S') (hfr : a ^^^ m ∉ S) (he : e ≤ 1)
    (hg : D' (a ^^^ m) ≤ e + (if a ∈ S' then 0 else D a)) (ho : ∀ w ∈ S', w ≠ a ^^^ m → D' w ≤ D w) : ∑ w ∈ S', D' w ≤ 1 + ∑ w ∈ S, D w := False.elim hb
structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat
  d : Nat
structure Cm where
  a : List Nat
  b : List Nat
def NN : Nat := 4656
def AA : Nat := 0x7ffffefdfbf7efdfbf7efdfbfffffdf7efdfbfdf7efdfbf7efdfffffefbfdf7fffff7dfdf7f7dfffffefefdefefbfbeffffff7f7ef7fffffbfdfdfbfbf7ddfbf7fffff7dfdf7efdfdf7f7dfbf7f7dfffffefefdeffffff7dfefbfffffdfdfbdfffffeff7f7efefdf77effffff7dfdf7fffffbfbf7bf7fbeffffff7f7ef7fffffbfdfdfbfbf7ddfdf7fffffbf7f7bfffffdfbf7bfffffbfbfbf7f7f7efbfbf7ef7efbdbfffffdfdfbdfffffefeff7efefbf77fffff7f7f7f7f7efdf7f7efdf7ef7b7ffffefdfbf7efdfbf7efdfbefdfbf7dfbf7efdfbf7df7df7defbef77efdf7dfbf7df7efdf7befbddfbefbdfbef77def6f76ffff555555555b556aaaaaab55b6ab55ab56ad5ad5ad5ad5b56b6ad6b6b5adad6b6b55aaadab5ad6d6b6b5aad6d55ad6b5ad6b6b5b555556d55ad6db55adb55b5b6d56d6d5b6d555b6d6b6b5b6d6b5ad6b5ad56ab5b5b55aad6d6d56ab5b5b55aaffffffd6d7fffffeffffffd556aadaaaaab6aaadab56ad6d5b6d555b56db56d5b5ad6b6db56db556d5b6d5b56db556b6b5ad56dadb6db56d5b6d5b55556d555b56db56db5556d555bffffff56db56ffffffdbffffff55b6aaadb6adab6daab6db6daab6dab5b6d56b56db6d555b6db56db6d555555b6d555555b6ffffffd55b6db6d55b6ffffffdb6ffffffd55b6db5ad6b556db6db56d5b556db6db6db55556db6db6db6db55556db6dbffffff6db6dbffffff555ad6b6db6db555555555ad6b5ad6bffffff5ad6b5ad6bffffff6db6dbffffff56d5b56d5b56d5b56d5bffffff6db6db6db6dbffffff0000000000000000
def HX : Nat := 0xaaaaaaaaa4aa95555554aa4954aa54a952a52a52a52a4a949529494a52529494aa555254a52929494a55292aa5294a529494a4aaaaa92aa52924aa524aa4a492a9292a492aaa4929494a49294a5294a52a954a4a4aa5529292a954a4a4aa5500000029280000010000002aa95525555549555254a95292a492aaa4a924a92a4a5294924a924aa92a492a4a924aa9494a52a92524924a92a492a4aaaa92aaa4a924a924aaa92aaa4000000a924a900000024000000aa49555249525492554924925549254a492a94a92492aaa4924a92492aaaaaa492aaaaaa490000002aa492492aa490000002490000002aa4924a5294aa924924a92a4aa924924924aaaa924924924924aaaa924924000000924924000000aaa5294924924aaaaaaaaa5294a5294000000a5294a5294000000924924000000a92a4a92a4a92a4a92a40000009249249249240000000000000000000000
def HY : Nat := 0x800001020408102040810204000002081020402081020408102000001040208000008202080820000010102101040410000008081080000040202040408220408000008202081020208082040808200000101021000000820104000002020420000010080810102088100000082020800000404084080410000008081080000040202040408220208000004080840000020408400000404040808081040408108104240000020204200000101008101040880000080808080810208081020810848000010204081020408102041020408204081020408208208210410881020820408208102084104220410420410882109089000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
noncomputable section core
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def join (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hits f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hits f c.b)) (hits f c.a)) cs
def bip (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => join ih f cs [f] [] []) (flag false l o w)) v
def anyE (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hits f t)) m
def rmF (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hit f e)) m
def star (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF f t))) false (hits f (rmF f t))) (anyE t)) (hits f t)) m
def flk (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flag false l o w)) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f : Nat → List W → Bool) (g : Nat) (kb : Bool) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) (st z (fun z => mk (f z))) false kb) (Nat.beq (Nat.land z g) g)
def laneL (w : Nat) (L : List Nat) : Nat := List.rec (motive := fun _ => Nat) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih w) d) L
def WL (N : Nat) : Nat := Nat.succ (Nat.mul 2 N)
def FM2 (N : Nat) : Nat := Nat.sub (Nat.pow 2 (Nat.mul 2 N)) 1
def R16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 1)
def MM16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 (FM2 N))
def GG16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 (Nat.pow 2 (Nat.mul 2 N)))
def MD16 (N : Nat) : Nat := Nat.sub (Nat.pow 2 (WL N)) 64
def U16 : Nat := laneL 6 (List.replicate 16 1)
def zflG (N np q nc : Nat) : Nat := Nat.land (Nat.sub U16 (Nat.mod (Nat.shiftRight (Nat.land (Nat.add (Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np) (MM16 N)) (GG16 N)) (Nat.mul 2 N)) (MD16 N))) nc
def zfl (np q nc : Nat) : Nat := zflG NN np q nc
def MU (f : Nat) : Nat := Nat.mul 63 f
def rmk (sa : Nat) (ka : Bool) (da : Nat) (sc : Nat) (kc : Bool) (dc : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (ih h) (st dc fun d => W.rec (motive := fun _ => Bool) (fun s a b c r0 _ => ih (fun r => h (⟨s, a, b, c, r0, d⟩ :: r))) w) kc) (Nat.beq w.s sc))
    (Bool.rec (motive := fun _ => Bool) (ih h) (st da fun d => W.rec (motive := fun _ => Bool) (fun s a b c r0 _ => ih (fun r => h (⟨s, a, b, c, r0, d⟩ :: r))) w) ka) (Nat.beq w.s sa)) v
def rmkB (sa da sc dc d0 : Nat) (v : List W) (h : List W → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (rmk sa true da sc true dc v h) (h v) (Nat.beq d0 0)
def put (m s x y : Nat) (v : List W) (d : Nat) (h : List W → Bool) : Bool :=
  st s fun s => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (st x fun x1 => st y fun y1 => st (Nat.lor x y) fun w => st d fun d => ins ⟨s, x1, y1, w, 0, d⟩ v h) false (Nat.beq s m)) false (Nat.beq s 0)
def kids (c : Bool → ((List W → Bool) → Bool) → Nat → Bool) (e n z u w fA fC : Nat) (a c' : W) (oa oc ka kc kb : Bool) (mk : Nat → (List W → Bool) → Bool) : Bool :=
  (fun fN sA sC =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
        (c kb (fun h => mk fN (fun r => rmkB a.s (Nat.land sC a.d) c'.s (Nat.land sA c'.d) (Nat.add a.d c'.d) r h)) (Nat.sub (Nat.sub z a.c) c'.c))
        (Nat.ble (Nat.succ (Nat.succ n)) e)) true
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (c kc (fun h => mk (Nat.add fN (Nat.land (MU (Nat.add fN fA)) a.d)) (fun r => rmk a.s false 0 c'.s true (Nat.land sA c'.d) r h)) (Nat.sub (Nat.sub z (Nat.land sC a.d)) c'.c)) oa) true
        (Bool.rec (motive := fun _ => Bool) false
          (c ka (fun h => mk (Nat.add fN (Nat.land (MU (Nat.add fN fC)) c'.d)) (fun r => rmk a.s true (Nat.land sC a.d) c'.s false 0 r h)) (Nat.sub (Nat.sub z a.c) (Nat.land sA c'.d))) oc)) (Nat.ble (Nat.succ n) e))) true
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (c false (fun h => mk (Nat.add (Nat.add fN (Nat.land (MU (Nat.add fN fA)) a.d)) (Nat.land (MU (Nat.add fN fC)) c'.d)) (fun r => rmk a.s false 0 c'.s false 0 r h)) (Nat.sub (Nat.sub z (Nat.land sC a.d)) (Nat.land sA c'.d))) oc) oa))
  (Nat.sub (Nat.sub (Nat.sub u w) fA) fC) (MU (Nat.add w fA)) (MU (Nat.add w fC))
def mid (f : Nat → List W → Bool) (m g np e n z : Nat) (v : List W) (a c : W) (oa oc ka kc kb : Bool) (s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    ((fun u w => (fun nc => st (zfl np (Nat.xor a.s s) nc) fun eA => st (zfl np (Nat.xor c.s s) (Nat.sub nc eA)) fun eC =>
      Bool.rec (motive := fun _ => Bool) false
        (st (Nat.sub (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) (Nat.add eA eC)) fun z =>
          kids (child f g) e n z u w (Nat.add eA (Nat.sub c.c (Nat.land c.c w))) (Nat.add eC (Nat.sub a.c (Nat.land a.c w))) a c oa oc ka kc kb (put m s x y v))
        (Nat.beq (Nat.land (Nat.sub (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) (Nat.add eA eC)) g) g))
      (Nat.sub u (Nat.lor (Nat.lor a.c c.c) w))) (Nat.shiftRight g 5) (Nat.lor x y))
    (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (Bool.rec (motive := fun _ => Bool)
    (st (Nat.xor a.s m) fun s => st (Nat.sub z a.c) fun z => (fun u =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (st u fun d1 => ins ⟨s, a.b, a.a, a.c, 0, d1⟩ v (fun v => child (f s) g false (rmk a.s true 0 a.s true 0 v) (Nat.sub z a.c))) (Nat.ble (Nat.succ n) e)) true
        (Bool.rec (motive := fun _ => Bool) false (st (Nat.add u a.d) fun d1 => ins ⟨s, a.b, a.a, a.c, 0, d1⟩ v (fun v => child (f s) g false (rmk a.s false 0 a.s false 0 v) z)) (Nat.ble n e)))
      (Nat.sub (Nat.shiftRight g 5) a.c)) false (Nat.beq (Nat.succ a.s) q))) r
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this
def segsX : List (ℕ × ℕ) := [(63, 90), (90, 93), (93, 96), (96, 99), (99, 102), (102, 105), (105, 108), (108, 111), (111, 114), (114, 117), (117, 120), (120, 123), (123, 126), (126, 129), (129, 132), (132, 135), (135, 162), (162, 165), (165, 167), (167, 169), (169, 172), (172, 175), (175, 177), (177, 179), (179, 182), (182, 185), (185, 187), (187, 189), (189, 192), (192, 195), (195, 197), (197, 199), (199, 202), (202, 205), (205, 207), (207, 209), (209, 212), (212, 215), (215, 217), (217, 219), (219, 222), (222, 225), (225, 227), (227, 229), (229, 232), (232, 235), (235, 237), (237, 239), (239, 266), (266, 269), (269, 272), (272, 275), (275, 278), (278, 281), (281, 284), (284, 287), (287, 314), (314, 316), (316, 319), (319, 321), (321, 324), (324, 326), (326, 329), (329, 331), (331, 334), (334, 336), (336, 339), (339, 341), (341, 344), (344, 346), (346, 349), (349, 351), (351, 378), (378, 380), (380, 383), (383, 385), (385, 388), (388, 390), (390, 393), (393, 395), (395, 398), (398, 400), (400, 403), (403, 405), (405, 408), (408, 410), (410, 413), (413, 415), (415, 417), (417, 419), (419, 421), (421, 423), (423, 425), (425, 427), (427, 429), (429, 431), (431, 433), (433, 435), (435, 437), (437, 439), (439, 441), (441, 443), (443, 445), (445, 447), (447, 450), (450, 453), (453, 456), (456, 459), (459, 462), (462, 465), (465, 468), (468, 471), (471, 474), (474, 476), (476, 479), (479, 481), (481, 484), (484, 486), (486, 489), (489, 491), (491, 493), (493, 495), (495, 497), (497, 499), (499, 526), (526, 529), (529, 532), (532, 535), (535, 538), (538, 541), (541, 544), (544, 547), (547, 574), (574, 577), (577, 580), (580, 583), (583, 586), (586, 589), (589, 592), (592, 595), (595, 597), (597, 599), (599, 601), (601, 603), (603, 605), (605, 607), (607, 609), (609, 611), (611, 614), (614, 617), (617, 620), (620, 623), (623, 626), (626, 629), (629, 632), (632, 635), (635, 638), (638, 641), (641, 644), (644, 647), (647, 650), (650, 653), (653, 656), (656, 659), (659, 661), (661, 663), (663, 665), (665, 667), (667, 669), (669, 671), (671, 673), (673, 675), (675, 678), (678, 681), (681, 684), (684, 687), (687, 690), (690, 693), (693, 696), (696, 699), (699, 702), (702, 705), (705, 708), (708, 711), (711, 713), (713, 715), (715, 717), (717, 719), (719, 722), (722, 725), (725, 727), (727, 729), (729, 732), (732, 735), (735, 737), (737, 739), (739, 742), (742, 745), (745, 748), (748, 751), (751, 754), (754, 757), (757, 760), (760, 763), (763, 765), (765, 767), (767, 769), (769, 771), (771, 774), (774, 776), (776, 779), (779, 781), (781, 784), (784, 786), (786, 789), (789, 791), (791, 794), (794, 797), (797, 800), (800, 803), (803, 806), (806, 809), (809, 811), (811, 813), (813, 815), (815, 817), (817, 844), (844, 847), (847, 850), (850, 853), (853, 880), (880, 883), (883, 886), (886, 889), (889, 891), (891, 893), (893, 895), (895, 897), (897, 900), (900, 903), (903, 906), (906, 909), (909, 912), (912, 915), (915, 918), (918, 921), (921, 923), (923, 925), (925, 927), (927, 929), (929, 956), (956, 959), (959, 962), (962, 965), (965, 967), (967, 969), (969, 971), (971, 973), (973, 975), (975, 977), (977, 979), (979, 981), (981, 983), (983, 985), (985, 987), (987, 989), (989, 992), (992, 995), (995, 998), (998, 1001), (1001, 1003), (1003, 1005), (1005, 1007), (1007, 1009), (1009, 1011), (1011, 1013), (1013, 1015), (1015, 1017), (1017, 1019), (1019, 1021), (1021, 1023), (1023, 1025), (1025, 1028), (1028, 1031), (1031, 1034), (1034, 1037), (1037, 1040), (1040, 1043), (1043, 1045), (1045, 1047), (1047, 1050), (1050, 1053), (1053, 1056), (1056, 1059), (1059, 1062), (1062, 1065), (1065, 1067), (1067, 1069), (1069, 1071), (1071, 1073), (1073, 1075), (1075, 1077), (1077, 1080), (1080, 1083), (1083, 1086), (1086, 1089), (1089, 1092), (1092, 1095), (1095, 1097), (1097, 1099), (1099, 1102), (1102, 1104), (1104, 1107), (1107, 1109), (1109, 1111), (1111, 1113), (1113, 1116), (1116, 1119), (1119, 1122), (1122, 1125), (1125, 1127), (1127, 1130), (1130, 1132), (1132, 1134), (1134, 1137), (1137, 1140), (1140, 1143), (1143, 1146), (1146, 1148), (1148, 1150), (1150, 1152), (1152, 1154), (1154, 1157), (1157, 1160), (1160, 1163), (1163, 1166), (1166, 1169), (1169, 1172), (1172, 1175), (1175, 1178), (1178, 1180), (1180, 1182), (1182, 1184), (1184, 1186), (1186, 1189), (1189, 1192), (1192, 1195), (1195, 1198), (1198, 1200), (1200, 1202), (1202, 1205), (1205, 1208), (1208, 1210), (1210, 1212), (1212, 1215), (1215, 1218), (1218, 1221), (1221, 1224), (1224, 1226), (1226, 1228), (1228, 1230), (1230, 1232), (1232, 1234), (1234, 1236), (1236, 1239), (1239, 1242), (1242, 1245), (1245, 1247), (1247, 1249), (1249, 1251), (1251, 1278), (1278, 1281), (1281, 1308), (1308, 1311), (1311, 1313), (1313, 1315), (1315, 1318), (1318, 1321), (1321, 1324), (1324, 1327), (1327, 1329), (1329, 1331), (1331, 1358), (1358, 1361), (1361, 1363), (1363, 1365), (1365, 1367), (1367, 1369), (1369, 1371), (1371, 1373), (1373, 1376), (1376, 1379), (1379, 1381), (1381, 1383), (1383, 1385), (1385, 1387), (1387, 1389), (1389, 1391), (1391, 1394), (1394, 1397), (1397, 1400), (1400, 1403), (1403, 1405), (1405, 1407), (1407, 1410), (1410, 1413), (1413, 1416), (1416, 1419), (1419, 1421), (1421, 1423), (1423, 1426), (1426, 1429), (1429, 1431), (1431, 1433), (1433, 1435), (1435, 1437), (1437, 1439), (1439, 1441), (1441, 1444), (1444, 1447), (1447, 1449), (1449, 1451), (1451, 1453), (1453, 1455), (1455, 1457), (1457, 1459), (1459, 1461), (1461, 1463), (1463, 1466), (1466, 1469), (1469, 1471), (1471, 1473), (1473, 1476), (1476, 1479), (1479, 1482), (1482, 1485), (1485, 1487), (1487, 1489), (1489, 1492), (1492, 1495), (1495, 1497), (1497, 1499), (1499, 1502), (1502, 1505), (1505, 1508), (1508, 1511), (1511, 1514), (1514, 1517), (1517, 1520), (1520, 1522), (1522, 1525), (1525, 1528), (1528, 1531), (1531, 1533), (1533, 1535), (1535, 1537), (1537, 1540), (1540, 1542), (1542, 1545), (1545, 1547), (1547, 1550), (1550, 1552), (1552, 1555), (1555, 1558), (1558, 1560), (1560, 1563), (1563, 1565), (1565, 1567), (1567, 1569), (1569, 1571), (1571, 1574), (1574, 1577), (1577, 1580), (1580, 1583), (1583, 1585), (1585, 1587), (1587, 1590), (1590, 1593), (1593, 1595), (1595, 1597), (1597, 1600), (1600, 1603), (1603, 1606), (1606, 1609), (1609, 1611), (1611, 1613), (1613, 1616), (1616, 1619), (1619, 1621), (1621, 1623), (1623, 1625), (1625, 1627), (1627, 1630), (1630, 1633), (1633, 1636), (1636, 1639), (1639, 1641), (1641, 1643), (1643, 1646), (1646, 1649), (1649, 1652), (1652, 1655), (1655, 1658), (1658, 1660), (1660, 1663), (1663, 1665), (1665, 1668), (1668, 1670), (1670, 1673), (1673, 1675), (1675, 1678), (1678, 1681), (1681, 1683), (1683, 1685), (1685, 1688), (1688, 1691), (1691, 1693), (1693, 1695), (1695, 1698), (1698, 1701), (1701, 1704), (1704, 1707), (1707, 1709), (1709, 1711), (1711, 1714), (1714, 1717), (1717, 1719), (1719, 1721), (1721, 1723), (1723, 1725), (1725, 1727), (1727, 1729), (1729, 1732), (1732, 1735), (1735, 1738), (1738, 1741), (1741, 1743), (1743, 1745), (1745, 1748), (1748, 1751), (1751, 1753), (1753, 1756), (1756, 1758), (1758, 1760), (1760, 1763), (1763, 1765), (1765, 1767), (1767, 1770), (1770, 1772), (1772, 1774), (1774, 1777), (1777, 1780), (1780, 1782), (1782, 1784), (1784, 1786), (1786, 1788), (1788, 1790), (1790, 1792), (1792, 1795), (1795, 1798), (1798, 1800), (1800, 1802), (1802, 1804), (1804, 1806), (1806, 1808), (1808, 1810), (1810, 1812), (1812, 1814), (1814, 1816), (1816, 1818), (1818, 1821), (1821, 1824), (1824, 1826), (1826, 1828), (1828, 1830), (1830, 1832), (1832, 1835), (1835, 1837), (1837, 1839), (1839, 1841), (1841, 1843), (1843, 1845), (1845, 1872), (1872, 1899), (1899, 1901), (1901, 1904), (1904, 1907), (1907, 1909), (1909, 1936), (1936, 1938), (1938, 1940), (1940, 1942), (1942, 1945), (1945, 1947), (1947, 1949), (1949, 1951), (1951, 1954), (1954, 1957), (1957, 1959), (1959, 1962), (1962, 1965), (1965, 1967), (1967, 1970), (1970, 1972), (1972, 1974), (1974, 1976), (1976, 1979), (1979, 1981), (1981, 1983), (1983, 1985), (1985, 1988), (1988, 1991), (1991, 1993), (1993, 1996), (1996, 1999), (1999, 2001), (2001, 2004), (2004, 2006), (2006, 2008), (2008, 2010), (2010, 2013), (2013, 2015), (2015, 2017), (2017, 2019), (2019, 2022), (2022, 2025), (2025, 2027), (2027, 2030), (2030, 2033), (2033, 2035), (2035, 2038), (2038, 2040), (2040, 2042), (2042, 2044), (2044, 2047), (2047, 2049), (2049, 2051), (2051, 2053), (2053, 2056), (2056, 2058), (2058, 2061), (2061, 2063), (2063, 2066), (2066, 2068), (2068, 2071), (2071, 2073), (2073, 2076), (2076, 2078), (2078, 2081), (2081, 2083), (2083, 2086), (2086, 2088), (2088, 2091), (2091, 2093), (2093, 2096), (2096, 2099), (2099, 2102), (2102, 2105), (2105, 2107), (2107, 2110), (2110, 2112), (2112, 2115), (2115, 2118), (2118, 2120), (2120, 2123), (2123, 2125), (2125, 2128), (2128, 2131), (2131, 2134), (2134, 2137), (2137, 2139), (2139, 2141), (2141, 2143), (2143, 2145), (2145, 2147), (2147, 2149), (2149, 2152), (2152, 2155), (2155, 2158), (2158, 2161), (2161, 2163), (2163, 2165), (2165, 2168), (2168, 2171), (2171, 2173), (2173, 2176), (2176, 2179), (2179, 2181), (2181, 2183), (2183, 2185), (2185, 2188), (2188, 2191), (2191, 2194), (2194, 2197), (2197, 2199), (2199, 2202), (2202, 2205), (2205, 2207), (2207, 2209), (2209, 2211), (2211, 2214), (2214, 2217), (2217, 2220), (2220, 2222), (2222, 2225), (2225, 2227), (2227, 2229), (2229, 2231), (2231, 2234), (2234, 2237), (2237, 2240), (2240, 2243), (2243, 2245), (2245, 2248), (2248, 2250), (2250, 2253), (2253, 2255), (2255, 2257), (2257, 2259), (2259, 2261), (2261, 2264), (2264, 2267), (2267, 2269), (2269, 2271), (2271, 2273), (2273, 2275), (2275, 2277), (2277, 2279), (2279, 2281), (2281, 2283), (2283, 2285), (2285, 2287), (2287, 2290), (2290, 2293), (2293, 2295), (2295, 2298), (2298, 2300), (2300, 2303), (2303, 2306), (2306, 2308), (2308, 2311), (2311, 2313), (2313, 2316), (2316, 2318), (2318, 2321), (2321, 2323), (2323, 2326), (2326, 2328), (2328, 2331), (2331, 2333), (2333, 2336), (2336, 2338), (2338, 2341), (2341, 2343), (2343, 2345), (2345, 2347), (2347, 2349), (2349, 2352), (2352, 2355), (2355, 2357), (2357, 2360), (2360, 2362), (2362, 2364), (2364, 2366), (2366, 2369), (2369, 2371), (2371, 2374), (2374, 2376), (2376, 2379), (2379, 2382), (2382, 2384), (2384, 2387), (2387, 2389), (2389, 2392), (2392, 2395), (2395, 2397), (2397, 2400), (2400, 2402), (2402, 2405), (2405, 2407), (2407, 2410), (2410, 2412), (2412, 2414), (2414, 2417), (2417, 2420), (2420, 2422), (2422, 2424), (2424, 2426), (2426, 2428), (2428, 2430), (2430, 2433), (2433, 2435), (2435, 2437), (2437, 2439), (2439, 2442), (2442, 2444), (2444, 2447), (2447, 2450), (2450, 2452), (2452, 2455), (2455, 2457), (2457, 2460), (2460, 2462), (2462, 2465), (2465, 2468), (2468, 2470), (2470, 2473), (2473, 2475), (2475, 2478), (2478, 2480), (2480, 2483), (2483, 2486), (2486, 2488), (2488, 2491), (2491, 2493), (2493, 2496), (2496, 2498), (2498, 2500), (2500, 2503), (2503, 2506), (2506, 2508), (2508, 2511), (2511, 2513), (2513, 2515), (2515, 2518), (2518, 2521), (2521, 2523), (2523, 2525), (2525, 2528), (2528, 2530), (2530, 2533), (2533, 2535), (2535, 2537), (2537, 2540), (2540, 2542), (2542, 2545), (2545, 2547), (2547, 2549), (2549, 2552), (2552, 2554), (2554, 2557), (2557, 2559), (2559, 2561), (2561, 2564), (2564, 2566), (2566, 2568), (2568, 2571), (2571, 2573), (2573, 2575), (2575, 2578), (2578, 2580), (2580, 2582), (2582, 2585), (2585, 2587), (2587, 2589), (2589, 2591), (2591, 2594), (2594, 2596), (2596, 2598), (2598, 2600), (2600, 2603), (2603, 2606), (2606, 2609), (2609, 2611), (2611, 2613), (2613, 2615), (2615, 2618), (2618, 2620), (2620, 2622), (2622, 2624), (2624, 2626), (2626, 2628), (2628, 2630), (2630, 2632), (2632, 2634), (2634, 2636), (2636, 2638), (2638, 2640), (2640, 2642), (2642, 2644), (2644, 2647), (2647, 2649), (2649, 2651), (2651, 2653), (2653, 2655), (2655, 2658), (2658, 2661), (2661, 2663), (2663, 2665), (2665, 2667), (2667, 2669), (2669, 2671), (2671, 2673), (2673, 2675), (2675, 2677), (2677, 2679), (2679, 2681), (2681, 2683), (2683, 2685), (2685, 2687), (2687, 2689), (2689, 2691), (2691, 2693), (2693, 2695)]
def segsY : List (ℕ × ℕ) := [(2695, 2712), (2712, 2715), (2715, 2719), (2719, 2724), (2724, 2727), (2727, 2732), (2732, 2737), (2737, 2743), (2743, 2747), (2747, 2752), (2752, 2758), (2758, 2765), (2765, 2770), (2770, 2776), (2776, 2782), (2782, 2789), (2789, 2793), (2793, 2798), (2798, 2804), (2804, 2810), (2810, 2815), (2815, 2821), (2821, 2828), (2828, 2835), (2835, 2841), (2841, 2847), (2847, 2854), (2854, 2861), (2861, 2867), (2867, 2873), (2873, 2880), (2880, 2887), (2887, 2891), (2891, 2896), (2896, 2902), (2902, 2908), (2908, 2913), (2913, 2919), (2919, 2925), (2925, 2931), (2931, 2937), (2937, 2943), (2943, 2950), (2950, 2957), (2957, 2964), (2964, 2971), (2971, 2978), (2978, 2985), (2985, 2991), (2991, 2998), (2998, 3005), (3005, 3012), (3012, 3018), (3018, 3025), (3025, 3032), (3032, 3039), (3039, 3046), (3046, 3053), (3053, 3060), (3060, 3067), (3067, 3074), (3074, 3081), (3081, 3088), (3088, 3111), (3111, 3114), (3114, 3119), (3119, 3124), (3124, 3131), (3131, 3137), (3137, 3144), (3144, 3151), (3151, 3159), (3159, 3165), (3165, 3172), (3172, 3179), (3179, 3187), (3187, 3195), (3195, 3203), (3203, 3211), (3211, 3235), (3235, 3239), (3239, 3246), (3246, 3252), (3252, 3260), (3260, 3267), (3267, 3276), (3276, 3284), (3284, 3309), (3309, 3314), (3314, 3321), (3321, 3329), (3329, 3354), (3354, 3357), (3357, 3362), (3362, 3368), (3368, 3375), (3375, 3380), (3380, 3387), (3387, 3394), (3394, 3402), (3402, 3408), (3408, 3415), (3415, 3423), (3423, 3431), (3431, 3438), (3438, 3446), (3446, 3454), (3454, 3478), (3478, 3483), (3483, 3490), (3490, 3497), (3497, 3522), (3522, 3527), (3527, 3535), (3535, 3542), (3542, 3567), (3567, 3573), (3573, 3581), (3581, 3585), (3585, 3591), (3591, 3598), (3598, 3606), (3606, 3613), (3613, 3621), (3621, 3630), (3630, 3655), (3655, 3660), (3660, 3667), (3667, 3675), (3675, 3700), (3700, 3706), (3706, 3715), (3715, 3722), (3722, 3727), (3727, 3734), (3734, 3742), (3742, 3767), (3767, 3773), (3773, 3781), (3781, 3787), (3787, 3812), (3812, 3819), (3819, 3823), (3823, 3829), (3829, 3836), (3836, 3844), (3844, 3851), (3851, 3859), (3859, 3868), (3868, 3893), (3893, 3898), (3898, 3905), (3905, 3913), (3913, 3938), (3938, 3944), (3944, 3953), (3953, 3959), (3959, 3984), (3984, 3989), (3989, 3996), (3996, 4004), (4004, 4029), (4029, 4035), (4035, 4043), (4043, 4050), (4050, 4057), (4057, 4063), (4063, 4071), (4071, 4077), (4077, 4085), (4085, 4092), (4092, 4099), (4099, 4105), (4105, 4113), (4113, 4119), (4119, 4143), (4143, 4150), (4150, 4157), (4157, 4161), (4161, 4167), (4167, 4174), (4174, 4182), (4182, 4189), (4189, 4197), (4197, 4206), (4206, 4231), (4231, 4236), (4236, 4243), (4243, 4251), (4251, 4276), (4276, 4282), (4282, 4290), (4290, 4296), (4296, 4304), (4304, 4309), (4309, 4316), (4316, 4324), (4324, 4349), (4349, 4355), (4355, 4363), (4363, 4369), (4369, 4377), (4377, 4383), (4383, 4407), (4407, 4413), (4413, 4422), (4422, 4428), (4428, 4453), (4453, 4460), (4460, 4467), (4467, 4474), (4474, 4481), (4481, 4488), (4488, 4495), (4495, 4501), (4501, 4510), (4510, 4517), (4517, 4524), (4524, 4531), (4531, 4537), (4537, 4562), (4562, 4569), (4569, 4576), (4576, 4583), (4583, 4590), (4590, 4597), (4597, 4604), (4604, 4611), (4611, 4618), (4618, 4625), (4625, 4632), (4632, 4655)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (6 * j)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (6 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 64) : pk n f < 2 ^ (6 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 6 * (n + 1) = 6 * n + 6 by ring, pow_add]
    have : 2 ^ (6 * n) * f n ≤ 2 ^ (6 * n) * 63 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 32 ≤ f j ∧ f j < 64) :
    pk n f &&& pk n (fun _ => 32) = pk n (fun _ => 32) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (6 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 32) < 2 ^ (6 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 32 = 32 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 6 = 0 ∧ i / 6 < n
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (6 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (6 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (6 * n) = (x.testBit (6 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (6 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 6 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (6 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (6 * j)).toNat) = x % 2 ^ (6 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 6 * j < 6 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (6 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (6 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (6 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (6 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (6 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def lane (w n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (w * j)
lemma lane_succ (w n : ℕ) (f : ℕ → ℕ) : lane w (n + 1) f = 2 ^ (w * n) * f n + lane w n f := by
  rw [lane, Finset.sum_range_succ, ← lane]; ring
lemma lane_congr {w n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : lane w n f = lane w n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma lane_lt {w n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 2 ^ w) : lane w n f < 2 ^ (w * n) := by
  induction n with
  | zero => simp [lane]
  | succ n ih =>
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [lane_succ, show w * (n + 1) = w * n + w by ring, pow_add]
    have : 2 ^ (w * n) * f n ≤ 2 ^ (w * n) * (2 ^ w - 1) := Nat.mul_le_mul_left _ (by omega)
    have e : 2 ^ (w * n) * 2 ^ w = 2 ^ (w * n) * (2 ^ w - 1) + 2 ^ (w * n) := by
      have : 0 < 2 ^ w := Nat.two_pow_pos w
      conv_lhs => rw [show 2 ^ w = (2 ^ w - 1) + 1 by omega]
      ring
    omega
lemma lane_add (w n : ℕ) (f g : ℕ → ℕ) : lane w n f + lane w n g = lane w n (fun j => f j + g j) := by
  simp [lane, ← Finset.sum_add_distrib, add_mul]
lemma lane_mul (w n q : ℕ) (f : ℕ → ℕ) : q * lane w n f = lane w n (fun j => q * f j) := by
  rw [lane, lane, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
lemma lane_and {w n : ℕ} {f g : ℕ → ℕ} (hf : ∀ j < n, f j < 2 ^ w) (hg : ∀ j < n, g j < 2 ^ w) :
    lane w n f &&& lane w n g = lane w n (fun j => f j &&& g j) := by
  induction n with
  | zero => simp [lane]
  | succ n ih =>
    have i1 := ih (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega))
    have h1 : lane w n f < 2 ^ (w * n) := lane_lt fun j hj => hf j (by omega)
    have h2 : lane w n g < 2 ^ (w * n) := lane_lt fun j hj => hg j (by omega)
    have h3 : lane w n (fun j => f j &&& g j) < 2 ^ (w * n) := lane_lt fun j hj => lt_of_le_of_lt Nat.and_le_left (hf j (by omega))
    rw [lane_succ, lane_succ, lane_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2, Nat.testBit_two_pow_mul_add _ h3]
    split_ifs with hi
    · rw [← Nat.testBit_and, i1]
    · rw [Nat.testBit_and]
lemma lane_mod {w n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) (hw : 6 * n + 7 ≤ w) : lane w n f % (2 ^ w - 64) = pk n f := by
  have h64 : 128 ≤ 2 ^ w := by
    calc 128 = 2 ^ 7 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have base : 2 ^ w ≡ 64 [MOD 2 ^ w - 64] := by
    have : 2 ^ w = (2 ^ w - 64) + 64 := by omega
    conv_lhs => rw [this]
    exact Nat.add_modEq_left
  have key : ∀ n, lane w n f ≡ pk n f [MOD 2 ^ w - 64] := by
    intro n
    induction n with
    | zero => simp [lane, pk]; rfl
    | succ n ih =>
      rw [lane_succ, pk_succ]
      refine Nat.ModEq.add (Nat.ModEq.mul_right _ ?_) ih
      rw [pow_mul, pow_mul]
      exact base.pow n
  have hlt : pk n f < 2 ^ w - 64 := by
    have h1 : pk n f < 2 ^ (6 * n) := pk_lt fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
    have h2 : 2 ^ (6 * n) ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have := key n
  rw [Nat.ModEq, Nat.mod_eq_of_lt hlt] at this
  exact this
lemma lane_testBit {w : ℕ} {f : ℕ → ℕ} {i j : ℕ} (hi : i < w) : ∀ {n : ℕ}, (∀ j < n, f j < 2 ^ w) →
    (lane w n f).testBit (w * j + i) = (decide (j < n) && (f j).testBit i) := by
  intro n
  induction n with
  | zero => intro _; simp [lane]
  | succ n ih =>
    intro h
    have h1 : lane w n f < 2 ^ (w * n) := lane_lt fun j hj => h j (by omega)
    rw [lane_succ, Nat.testBit_two_pow_mul_add _ h1]
    rcases lt_trichotomy j n with hj | rfl | hj
    · have : w * j + i < w * n := by
        have : w * (j + 1) ≤ w * n := Nat.mul_le_mul_left _ hj
        have e : w * (j + 1) = w * j + w := by ring
        omega
      rw [ite_eq_left this, ih fun j hj => h j (by omega)]
      simp [hj, show j < n + 1 by omega]
    · rw [ite_eq_right (by omega), show w * j + i - w * j = i by omega]; simp
    · have e0 : ¬ w * j + i < w * n := by
        have : w * n ≤ w * j := Nat.mul_le_mul_left _ (by omega)
        omega
      have hlt : f n < 2 ^ w := h n (by omega)
      have : w ≤ w * j + i - w * n := by
        have : w * (n + 1) ≤ w * j := Nat.mul_le_mul_left _ hj
        have e : w * (n + 1) = w * n + w := by ring
        omega
      rw [ite_eq_right e0, Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) this))]
      simp [show ¬ j < n + 1 by omega]
lemma laneL_eq (w : ℕ) (L : List ℕ) : laneL w L = lane w L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    change (laneL w L) <<< w + d = _
    rw [ih, Nat.shiftLeft_eq, List.length_cons, lane, lane, Finset.sum_range_succ', Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [List.getD_cons_succ]; rw [mul_assoc, ← pow_add]; congr 2
    · simp
lemma laneL_rep (w n x : ℕ) : laneL w (List.replicate n x) = lane w n (fun _ => x) := by
  rw [laneL_eq, List.length_replicate]
  refine lane_congr fun j hj => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp [hj]
def fb (x j : ℕ) : ℕ := (x.testBit (6 * j)).toNat
lemma fb_le (x j : ℕ) : fb x j ≤ 1 := by unfold fb; cases x.testBit (6 * j) <;> simp
lemma fb_pk {n x : ℕ} (h : isPk n x) : x = pk n (fb x) := pk_of h
lemma pk_bit {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) (j : ℕ) : (pk n f).testBit (6 * j) = (decide (j < n) && decide (f j = 1)) := by
  have h := lane_testBit (w := 6) (f := f) (i := 0) (j := j) (by norm_num) (n := n) fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
  rw [add_zero] at h
  change (lane 6 n f).testBit (6 * j) = _
  rw [h]
  by_cases hj : j < n
  · have := hf j hj
    simp only [hj, decide_true, Bool.true_and]
    generalize f j = x at *
    interval_cases x <;> rfl
  · simp [hj]
lemma pk_isPk {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) : isPk n (pk n f) := by
  intro i hi
  have hlt : pk n f < 2 ^ (6 * n) := pk_lt fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
  have h5 := Nat.mod_lt i (show 0 < 6 by norm_num)
  have e : 6 * (i / 6) + i % 6 = i := Nat.div_add_mod i 6
  have h := lane_testBit (w := 6) (f := f) (i := i % 6) (j := i / 6) h5 (n := n) fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
  rw [e] at h
  change (lane 6 n f).testBit i = true at hi
  rw [h, Bool.and_eq_true, decide_eq_true_eq] at hi
  refine ⟨?_, hi.1⟩
  by_contra hne
  have := hf _ hi.1
  have hx := hi.2
  generalize f (i / 6) = x at *
  interval_cases x
  · simp at hx
  · exact hne (Nat.testBit_one_eq_true_iff_self_eq_zero.1 hx)
lemma fb_of_pk {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) {j : ℕ} (hj : j < n) : fb (pk n f) j = f j := by
  unfold fb; rw [pk_bit hf]
  have := hf j hj
  simp only [hj, decide_true, Bool.true_and]
  generalize f j = x at *
  interval_cases x <;> rfl
lemma fb_one {x j : ℕ} : fb x j = 1 ↔ x.testBit (6 * j) = true := by unfold fb; cases x.testBit (6 * j) <;> simp
lemma MU_land {n : ℕ} {f d : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) (hd : ∀ j < n, d j < 64) :
    Nat.land (MU (pk n f)) (pk n d) = pk n (fun j => f j * d j) := by
  change (63 * lane 6 n f) &&& lane 6 n d = lane 6 n _
  rw [lane_mul, lane_and]
  · refine lane_congr fun j hj => ?_
    have h1 := hf j hj; have h2 := hd j hj
    generalize f j = x at *
    generalize d j = y at *
    interval_cases x
    · simp
    · rw [mul_one, one_mul]
      interval_cases y <;> rfl
  · intro j hj; have := hf j hj; omega
  · intro j hj; exact hd j hj
lemma shr4 (n : ℕ) : Nat.shiftRight (pk n (fun _ => 32)) 5 = pk n (fun _ => 1) := by
  change pk n (fun _ => 32) >>> 5 = _
  have : pk n (fun _ => 32) = 32 * pk n (fun _ => 1) := by
    change lane 6 n _ = 32 * lane 6 n _; rw [lane_mul]
  rw [this, Nat.shiftRight_eq_div_pow]; norm_num
lemma zflG_spec {N np q nc : ℕ} {f : ℕ → ℕ} (hf : ∀ j < 16, f j < 2 ^ (2 * N)) (hnp : np = lane (WL N) 16 f) (hw : 103 ≤ 2 * N + 1) {j : ℕ}
    (h : (zflG N np q nc).testBit (6 * j) = true) : j < 16 ∧ q &&& f j = 0 ∧ nc.testBit (6 * j) = true := by
  have hWL : WL N = 2 * N + 1 := rfl
  have hFM : FM2 N = 2 ^ (2 * N) - 1 := rfl
  have pw : 2 ^ (WL N) = 2 * 2 ^ (2 * N) := by rw [hWL, pow_succ']
  have hpos : 0 < 2 ^ (2 * N) := Nat.two_pow_pos _
  set q' := q &&& (FM2 N) with hq'
  have hq'lt : q' < 2 ^ (2 * N) := lt_of_le_of_lt Nat.and_le_right (by rw [hFM]; omega)
  have hqf : ∀ j < 16, q' &&& f j = q &&& f j := by
    intro j hj
    apply Nat.eq_of_testBit_eq; intro i
    simp only [hq', hFM, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < 2 * N
    · simp [hi]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf j hj) (Nat.pow_le_pow_right (by norm_num) (by omega)))]; simp
  let b : ℕ → ℕ := fun j => if q &&& f j = 0 then 0 else 1
  have hb : ∀ j, b j ≤ 1 := fun j => by simp only [b]; split_ifs <;> simp
  have e1 : Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np = lane (WL N) 16 (fun j => q &&& f j) := by
    change (q' * (R16 N)) &&& np = _
    rw [R16, laneL_rep, lane_mul, hnp, lane_and]
    · refine lane_congr fun j hj => ?_
      rw [mul_one, hqf j hj]
    · intro j hj; rw [mul_one, pw]; omega
    · intro j hj; have := hf j hj; rw [pw]; omega
  have e2 : Nat.land (Nat.add (Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np) (MM16 N)) (GG16 N) = lane (WL N) 16 (fun j => 2 ^ (2 * N) * b j) := by
    rw [e1]
    change (lane (WL N) 16 _ + (MM16 N)) &&& (GG16 N) = _
    have hlt : ∀ j < 16, q &&& f j < 2 ^ (2 * N) := fun j hj => lt_of_le_of_lt Nat.and_le_right (hf j hj)
    rw [MM16, GG16, laneL_rep, laneL_rep, lane_add, lane_and]
    · refine lane_congr fun j hj => ?_
      have h1 := hlt j hj
      change (_ + (2 ^ (2 * N) - 1)) &&& 2 ^ (2 * N) = 2 ^ (2 * N) * b j
      generalize hx : q &&& f j = x at *
      have hbx : b j = if x = 0 then 0 else 1 := by simp only [b, hx]
      rw [hbx]
      split_ifs with h0
      · subst h0
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_and, zero_add, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
        by_cases hi : 2 * N = i <;> simp [hi]
      · have e : x + (2 ^ (2 * N) - 1) = 2 ^ (2 * N) * 1 + (x - 1) := by omega
        rw [e]
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (show x - 1 < 2 ^ (2 * N) by omega), Nat.testBit_two_pow, mul_one, Nat.testBit_two_pow]
        by_cases hi : 2 * N = i
        · subst hi; simp
        · simp [hi]
    · intro j hj; have := hlt j hj
      change _ + (2 ^ (2 * N) - 1) < _; rw [pw]; omega
    · intro j hj
      change 2 ^ (2 * N) < _; rw [pw]; omega
  have e3 : Nat.mod (Nat.shiftRight (Nat.land (Nat.add (Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np) (MM16 N)) (GG16 N)) (Nat.mul 2 N)) (MD16 N) = pk 16 b := by
    rw [e2]
    change (lane (WL N) 16 (fun j => 2 ^ (2 * N) * b j) >>> (2 * N)) % (2 ^ (WL N) - 64) = _
    rw [← lane_mul, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ hpos]
    exact lane_mod (fun j _ => hb j) (by rw [hWL]; omega)
  unfold zflG at h
  rw [e3] at h
  change ((U16 - pk 16 b) &&& nc).testBit (6 * j) = true at h
  have e4 : U16 - pk 16 b = pk 16 (fun j => 1 - b j) := by
    rw [U16, laneL_rep]
    change pk 16 (fun _ => 1) - pk 16 b = _
    exact pk_sub fun j _ => hb j
  rw [e4, Nat.testBit_and, pk_bit (fun j _ => by omega), Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  refine ⟨h.1.1, ?_, h.2⟩
  have := h.1.2
  by_contra hne
  simp [b, hne] at this
lemma zfl_spec {np q nc : ℕ} {f : ℕ → ℕ} (hf : ∀ j < 16, f j < 2 ^ (2 * NN)) (hnp : np = lane (WL NN) 16 f) (hw : 103 ≤ 2 * NN + 1) {j : ℕ}
    (h : (zfl np q nc).testBit (6 * j) = true) : j < 16 ∧ q &&& f j = 0 ∧ nc.testBit (6 * j) = true := zflG_spec hf hnp hw h
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ (b : ℕ → ℕ) (D : ℕ → ℕ → ℕ), (∀ j < P.length, b j ≤ 31) ∧ (∀ j < P.length, Acc (P.getD j 0) T k (b j) (D j) S) ∧
    (∀ w ∈ v, w.d = pk P.length (fun j => D j w.s)) ∧ (∀ j < P.length, k + ∑ s ∈ S, D j s ≤ 31) ∧ z = pk P.length (fun j => 32 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g np T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 32)
  hnp : ∃ f : ℕ → ℕ, (∀ j < 16, f j < 2 ^ (2 * NN)) ∧ np = lane (WL NN) 16 f ∧ ∀ j < P.length, j < 16 → P.getD j 0 &&& f j = P.getD j 0
lemma cnt_card {P : List ℕ} {v : List W} {S : Finset ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w) {j : ℕ} (hj : j < P.length) :
    cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
  have e : cnt v j = (v.filter (fun w => w.c.testBit (6 * j))).length := by
    clear hr hw
    induction v with
    | nil => rfl
    | cons w v ih =>
      rw [cnt_cons, ih, List.filter_cons, fl]
      cases w.c.testBit (6 * j) <;> simp; omega
  rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
  apply Finset.card_le_card
  intro x hx
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
  obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
  rw [Finset.mem_filter]
  exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} {D : ℕ → ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : ∀ j < P.length, Acc (P.getD j 0) T k (b j) (D j) S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  exact (cnt_card hr hw hj).trans ((hc j hj).const p1 p2 p3 hm hk)
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, D, hb, hc, _, _, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ} {kb : Bool}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r) (hkb : kb = false)
    (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g kb mk z = false) : f z r = false := by
  subst hkb
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, cond_false, hmk] at h
  exact h
end sound
lemma StOk.start {P : List ℕ} {T l K : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hrep : Rep v S) (hwok : ∀ w ∈ v, WOk P w) (hgood : ∀ w ∈ v, Good l w.s)
    (hK : K ≤ 31) (hb : ∀ j < P.length, b j ≤ 31) (hd : ∀ w ∈ v, w.d = 0) (hA : ∀ j < P.length, Acc (P.getD j 0) T K (b j) (fun _ => 0) S) :
    StOk P T l K (pk P.length (fun j => 32 + b j - cnt v j)) v S := by
  refine ⟨hrep, hwok, hgood, b, fun _ _ => 0, hb, hA, fun w hw => ?_, fun j _ => by simpa using hK, rfl⟩
  rw [hd w hw]; simp [pk]
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0, 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0, 0⟩
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (6 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (6 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (6 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (6 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (6 * j) <;> cases c.c.testBit (6 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
def wd (w : W) (d : ℕ) : W := ⟨w.s, w.a, w.b, w.c, w.r, d⟩
def upd (sa da sc dc : ℕ) (w : W) : W := bif Nat.beq w.s sa then wd w da else bif Nat.beq w.s sc then wd w dc else w
lemma upd_s (sa da sc dc : ℕ) (w : W) : (upd sa da sc dc w).s = w.s := by
  unfold upd; cases Nat.beq w.s sa <;> cases Nat.beq w.s sc <;> rfl
lemma upd_c (sa da sc dc : ℕ) (w : W) : (upd sa da sc dc w).c = w.c := by
  unfold upd; cases Nat.beq w.s sa <;> cases Nat.beq w.s sc <;> rfl
lemma upd_r (sa da sc dc : ℕ) (w : W) : (upd sa da sc dc w).r = w.r := by
  unfold upd; cases Nat.beq w.s sa <;> cases Nat.beq w.s sc <;> rfl
lemma fl_upd (sa da sc dc : ℕ) (w : W) (j : ℕ) : fl (upd sa da sc dc w) j = fl w j := by unfold fl; rw [upd_c]
lemma WOk.upd {P : List ℕ} {w : W} (h : WOk P w) (sa da sc dc : ℕ) : WOk P (upd sa da sc dc w) := by
  unfold L_meta_9732.upd
  cases Nat.beq w.s sa <;> cases Nat.beq w.s sc
  · exact h
  · exact ⟨h.pa, h.pb, h.ec, h.ca, h.cb⟩
  · exact ⟨h.pa, h.pb, h.ec, h.ca, h.cb⟩
  · exact ⟨h.pa, h.pb, h.ec, h.ca, h.cb⟩
lemma map_upd_s (sa da sc dc : ℕ) (v : List W) : (v.map (upd sa da sc dc)).map W.s = v.map W.s := by
  rw [List.map_map]; exact List.map_congr_left fun w _ => upd_s _ _ _ _ w
lemma cnt_upd (sa da sc dc : ℕ) (v : List W) (j : ℕ) : cnt (v.map (upd sa da sc dc)) j = cnt v j := by
  unfold cnt; rw [List.map_map]; congr 1; exact List.map_congr_left fun w _ => fl_upd _ _ _ _ w j
lemma Rep.upd {v : List W} {S : Finset ℕ} (h : Rep v S) (sa da sc dc : ℕ) : Rep (v.map (L_meta_9732.upd sa da sc dc)) S := by
  unfold Rep; rw [map_upd_s]; exact h
def kp (sa : ℕ) (ka : Bool) (sc : ℕ) (kc : Bool) (w : W) : Bool := bif Nat.beq w.s sa then ka else bif Nat.beq w.s sc then kc else true
lemma rmk_eq (sa : ℕ) (ka : Bool) (da sc : ℕ) (kc : Bool) (dc : ℕ) (v : List W) : ∀ h, rmk sa ka da sc kc dc v h = h ((v.filter (kp sa ka sc kc)).map (upd sa da sc dc)) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    obtain ⟨ws, wa, wb, wc, wr, wd'⟩ := w
    change (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (rmk sa ka da sc kc dc v (fun r => h (⟨ws, wa, wb, wc, wr, wd'⟩ :: r))) (Bool.rec (motive := fun _ => Bool) (rmk sa ka da sc kc dc v h)
        (st dc fun d => rmk sa ka da sc kc dc v (fun r => h (⟨ws, wa, wb, wc, wr, d⟩ :: r))) kc) (Nat.beq ws sc))
      (Bool.rec (motive := fun _ => Bool) (rmk sa ka da sc kc dc v h) (st da fun d => rmk sa ka da sc kc dc v (fun r => h (⟨ws, wa, wb, wc, wr, d⟩ :: r))) ka) (Nat.beq ws sa) : Bool) = _
    simp only [bR, st_eq, ih]
    rw [List.filter_cons]
    unfold kp
    cases h1 : Nat.beq ws sa <;> cases h2 : Nat.beq ws sc <;> cases ka <;> cases kc <;> simp [upd, h1, h2, wd]
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma beq_t (x : ℕ) : Nat.beq x x = true := Nat.beq_refl x
lemma shape_upd {o a c : W} {v r0 : List W} (da dc : ℕ) (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r0.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ka kc : Bool) :
    Shape o (upd a.s da c.s dc a) (upd a.s da c.s dc c) (v.map (upd a.s da c.s dc)) ka kc ((r0.filter (kp a.s ka c.s kc)).map (upd a.s da c.s dc)) := by
  set u := upd a.s da c.s dc with hu
  have us : ∀ w, (u w).s = w.s := fun w => upd_s _ _ _ _ w
  have uo : u o = o := by
    rw [hu]; unfold upd; rw [beq_f (ho a ha).symm, beq_f (ho c hc).symm]; rfl
  have hp' : (r0.map u).Perm (o :: v.map u) := by
    have := hp.map u; rw [List.map_cons, uo] at this; exact this
  have hv' : ((v.map u).map W.s).Nodup := by rw [hu, map_upd_s]; exact hv
  have ho' : ∀ w ∈ v.map u, w.s ≠ o.s := by
    intro w hw
    obtain ⟨w0, h0, rfl⟩ := List.mem_map.1 hw
    rw [us]; exact ho w0 h0
  obtain ⟨s1, s2, s3, s4⟩ := shape_all ho' hp' hv' (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) (by rw [us, us]; exact hac)
  simp only [us, List.filter_map] at s1 s2 s3
  have filt : ∀ q : W → Bool, (∀ w, kp a.s ka c.s kc w = q (u w)) → r0.filter (kp a.s ka c.s kc) = r0.filter (q ∘ u) := by
    intro q hq; congr 1; funext w; exact hq w
  cases ka <;> cases kc
  · rw [filt _ fun w => ?_]
    · exact s1
    · simp only [us, kp]; cases Nat.beq w.s a.s <;> cases Nat.beq w.s c.s <;> rfl
  · rw [filt _ fun w => ?_]
    · exact s3
    · simp only [us, kp]; cases Nat.beq w.s a.s <;> cases Nat.beq w.s c.s <;> rfl
  · rw [filt _ fun w => ?_]
    · exact s2
    · simp only [us, kp]
      by_cases h1 : w.s = a.s
      · rw [h1, beq_t, beq_f hac]; rfl
      · rw [beq_f h1]; cases Nat.beq w.s c.s <;> rfl
  · have : r0.filter (kp a.s true c.s true) = r0 := by
      rw [List.filter_eq_self]; intro w _
      unfold kp; cases Nat.beq w.s a.s <;> cases Nat.beq w.s c.s <;> rfl
    rw [this]; exact s4
def kdOf (fo FA FC : ℕ) : Kd := if fo = 1 then .K0 else if FA = 1 then .KA else if FC = 1 then .KC else .N
lemma num1 {b cv cr fa fc fo ea ec da dc : ℕ} {ka kc : Bool} (hfa : fa ≤ 1) (hfc : fc ≤ 1) (hfo : fo ≤ 1) (h2 : fa = 1 → fc = 1 → fo = 1) (h3 : fo = 1 → fa = 1 ∨ fc = 1)
    (he : ea + ec + max fa (max fc fo) ≤ 1) (hb : b ≤ 31) (hcv : cv ≤ b) (hcnt : cr + (bif ka then 0 else fa) + (bif kc then 0 else fc) = fo + cv)
    (hd : (kdOf fo (ea + (fc - fc * fo)) (ec + (fa - fa * fo))).del (if ka then 0 else da) (if kc then 0 else dc) + cr ≤ b) :
    (fo ≤ 32 + b - cv + fa * fc ∧ 32 ≤ 32 + b - cv + fa * fc - fo ∧ 32 + b - cv + fa * fc - fo < 64 ∧ ea + ec ≤ 32 + b - cv + fa * fc - fo ∧
      32 ≤ 32 + b - cv + fa * fc - fo - (ea + ec) ∧ 32 + b - cv + fa * fc - fo - (ea + ec) < 64) ∧
    (bif ka then fa else (fo + (ec + (fa - fa * fo))) * da) ≤ 32 + b - cv + fa * fc - fo - (ea + ec) ∧
    (bif kc then fc else (fo + (ea + (fc - fc * fo))) * dc) ≤ 32 + b - cv + fa * fc - fo - (ea + ec) - (bif ka then fa else (fo + (ec + (fa - fa * fo))) * da) ∧
    32 + b - cv + fa * fc - fo - (ea + ec) - (bif ka then fa else (fo + (ec + (fa - fa * fo))) * da) - (bif kc then fc else (fo + (ea + (fc - fc * fo))) * dc) =
      32 + (b - (kdOf fo (ea + (fc - fc * fo)) (ec + (fa - fa * fo))).del (if ka then 0 else da) (if kc then 0 else dc)) - cr := by
  have hea : ea ≤ 1 := by omega
  have hec : ec ≤ 1 := by omega
  interval_cases fa <;> interval_cases fc <;> interval_cases fo <;> simp at h2 h3 he <;> interval_cases ea <;> interval_cases ec <;> simp at he <;>
    cases ka <;> cases kc <;> simp [kdOf, Kd.del] at hd hcnt ⊢ <;> omega
lemma num2 {fa fc fo ea ec da dc : ℕ} {ka kc : Bool} (hfa : fa ≤ 1) (hfc : fc ≤ 1) (hfo : fo ≤ 1) (h2 : fa = 1 → fc = 1 → fo = 1)
    (he : ea + ec + max fa (max fc fo) ≤ 1) :
    (ea + (fc - fc * fo) ≤ 1 ∧ ec + (fa - fa * fo) ≤ 1 ∧ fo + (ea + (fc - fc * fo)) + (ec + (fa - fa * fo)) ≤ 1) ∧
    (1 - fo - (ea + (fc - fc * fo)) - (ec + (fa - fa * fo))) + (bif ka then 0 else ((1 - fo - (ea + (fc - fc * fo)) - (ec + (fa - fa * fo))) + (ea + (fc - fc * fo))) * da) +
      (bif kc then 0 else ((1 - fo - (ea + (fc - fc * fo)) - (ec + (fa - fa * fo))) + (ec + (fa - fa * fo))) * dc) =
      (kdOf fo (ea + (fc - fc * fo)) (ec + (fa - fa * fo))).out (if ka then 0 else da) (if kc then 0 else dc) ∧
    (fo + (ec + (fa - fa * fo))) * da = (kdOf fo (ea + (fc - fc * fo)) (ec + (fa - fa * fo))).kpa da ∧
    (fo + (ea + (fc - fc * fo))) * dc = (kdOf fo (ea + (fc - fc * fo)) (ec + (fa - fa * fo))).kpc dc := by
  have hea : ea ≤ 1 := by omega
  have hec : ec ≤ 1 := by omega
  interval_cases fa <;> interval_cases fc <;> interval_cases fo <;> simp at h2 he <;> interval_cases ea <;> interval_cases ec <;> simp at he <;>
    cases ka <;> cases kc <;> simp [kdOf, Kd.out, Kd.kpa, Kd.kpc]
lemma opW_flags {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) (j : ℕ) :
    (fl a j = 1 → fl c j = 1 → fl (opW d a c) j = 1) ∧ (fl (opW d a c) j = 1 → fl a j = 1 ∨ fl c j = 1) := by
  unfold fl
  rw [ha.ec, hc.ec]
  cases d <;> simp only [opW, cond_true, cond_false, Nat.testBit_or, Nat.testBit_and] <;>
    cases a.a.testBit (6 * j) <;> cases a.b.testBit (6 * j) <;> cases c.a.testBit (6 * j) <;> cases c.b.testBit (6 * j) <;> simp
lemma pass_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) {j : ℕ} (hj : j < P.length) (h1 : fl c j = 1) (h0 : fl (opW d a c) j = 0) :
    op d a.s c.s &&& P.getD j 0 = a.s &&& P.getD j 0 := by
  have e1 : c.c.testBit (6 * j) = true := by unfold fl at h1; cases h : c.c.testBit (6 * j) <;> simp_all
  have e0 : (opW d a c).c.testBit (6 * j) = false := by unfold fl at h0; cases h : (opW d a c).c.testBit (6 * j) <;> simp_all
  rw [hc.ec, Nat.testBit_or, Bool.or_eq_true] at e1
  cases d
  · simp only [opW, cond_false, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at e0
    have hb := e1.resolve_left (by simp [e0.1.2])
    rw [and_op, hc.cb j hj hb]
    apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · simp only [opW, cond_true, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at e0
    have hb := e1.resolve_right (by simp [e0.2.2])
    rw [and_op, hc.ca j hj hb]
    apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma opW_symm (d : Bool) (a c : W) : (opW d a c).c = (opW d c a).c := by
  cases d
  · change (a.a ||| c.a) ||| (a.b &&& c.b) = (c.a ||| a.a) ||| (c.b &&& a.b); rw [Nat.or_comm a.a, Nat.and_comm a.b]
  · change (a.a &&& c.a) ||| (a.b ||| c.b) = (c.a &&& a.a) ||| (c.b ||| a.b); rw [Nat.and_comm a.a, Nat.or_comm a.b]
def fAo (e o c : ℕ) : ℕ := Nat.add e (Nat.sub c (Nat.land c o))
def fNo (u w fA fC : ℕ) : ℕ := Nat.sub (Nat.sub (Nat.sub u w) fA) fC
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool} {eA eC w fA fC fN dn : ℕ}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hEA : isPk P.length eA) (hEC : isPk P.length eC)
    (he : ∀ j < P.length, fb eA j + fb eC j + max (fl a j) (max (fl c j) (fl (opW d' a c) j)) ≤ 1)
    (hAo : ∀ j < P.length, fb eA j = 1 → op d' a.s c.s &&& P.getD j 0 = a.s &&& P.getD j 0)
    (hCo : ∀ j < P.length, fb eC j = 1 → op d' a.s c.s &&& P.getD j 0 = c.s &&& P.getD j 0)
    (hw : w = (opW d' a c).c) (hfA : fA = fAo eA w c.c) (hfC : fC = fAo eC w a.c) (hfN : fN = fNo (Nat.shiftRight g 5) w fA fC)
    (hdn : dn = fN + (bif ka then 0 else Nat.land (MU (fN + fA)) a.d) + (bif kc then 0 else Nat.land (MU (fN + fC)) c.d))
    (hsh : Shape (wd (opW d' a c) dn) (upd a.s (Nat.land (MU (w + fC)) a.d) c.s (Nat.land (MU (w + fA)) c.d) a)
      (upd a.s (Nat.land (MU (w + fC)) a.d) c.s (Nat.land (MU (w + fA)) c.d) c)
      (v.map (upd a.s (Nat.land (MU (w + fC)) a.d) c.s (Nat.land (MU (w + fA)) c.d))) ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - w - (eA + eC) - (bif ka then a.c else Nat.land (MU (w + fC)) a.d) -
      (bif kc then c.c else Nat.land (MU (w + fA)) c.d)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - w) g) g = true ∧ Nat.beq (Nat.land (z + (a.c &&& c.c) - w - (eA + eC)) g) g = true := by
  obtain ⟨b, D, hb15, hacc, hdv, hsum, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hacc hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have hfS' : op d' a.s c.s ∉ S := by rw [← opW_s]; exact hfS
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have haS : a.s ∈ S := hs.rep.mem.2 ⟨a, ha, rfl⟩
  have hcS : c.s ∈ S := hs.rep.mem.2 ⟨c, hc, rfl⟩
  set u := upd a.s (Nat.land (MU (w + fC)) a.d) c.s (Nat.land (MU (w + fA)) c.d) with hu
  set N := P.length with hN
  have us : ∀ x, (u x).s = x.s := fun x => upd_s _ _ _ _ x
  have f1 : ∀ j, fl a j ≤ 1 := fl_le a
  have f2 : ∀ j, fl c j ≤ 1 := fl_le c
  have f3 : ∀ j, fl (opW d' a c) j ≤ 1 := fl_le _
  have f4 := opW_flags (P := P) d' wa wc
  let FA : ℕ → ℕ := fun j => fb eA j + (fl c j - fl c j * fl (opW d' a c) j)
  let FC : ℕ → ℕ := fun j => fb eC j + (fl a j - fl a j * fl (opW d' a c) j)
  let FN : ℕ → ℕ := fun j => 1 - fl (opW d' a c) j - FA j - FC j
  have n2 : ∀ j < N, _ := fun j hj => num2 (da := D j a.s) (dc := D j c.s) (ka := ka) (kc := kc) (f1 j) (f2 j) (f3 j) (f4 j).1 (he j hj)
  have pw : w = pk N (fl (opW d' a c)) := by rw [hw]; exact fl_pk wo
  have pa : a.c = pk N (fl a) := fl_pk wa
  have pc : c.c = pk N (fl c) := fl_pk wc
  have peA : eA = pk N (fb eA) := fb_pk hEA
  have peC : eC = pk N (fb eC) := fb_pk hEC
  have mulle : ∀ x y : ℕ, y ≤ 1 → x * y ≤ x := fun x y h => by
    calc x * y ≤ x * 1 := Nat.mul_le_mul_left _ h
      _ = x := mul_one x
  have pfA : fA = pk N FA := by
    rw [hfA]
    change eA + (c.c - (c.c &&& w)) = _
    rw [hw, fl_and wc]
    conv_lhs => rw [peA, pc]
    rw [pk_sub fun j _ => mulle _ _ (f3 j), pk_add]
  have pfC : fC = pk N FC := by
    rw [hfC]
    change eC + (a.c - (a.c &&& w)) = _
    rw [hw, fl_and wa]
    conv_lhs => rw [peC, pa]
    rw [pk_sub fun j _ => mulle _ _ (f3 j), pk_add]
  have pfN : fN = pk N FN := by
    rw [hfN, X.hg]
    change Nat.shiftRight (pk P.length fun _ => 32) 5 - w - fA - fC = _
    rw [shr4, pw, pfA, pfC, pk_sub, pk_sub, pk_sub]
    · intro j hj; obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FA, FC]; omega
    · intro j hj; obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FA]; omega
    · intro j hj; exact f3 j
  have hDb : ∀ j < N, D j a.s + D j c.s ≤ 30 := by
    intro j hj
    have h1 := hsum j hj
    have h2 : ∑ s ∈ ({a.s, c.s} : Finset ℕ), D j s ≤ ∑ s ∈ S, D j s :=
      Finset.sum_le_sum_of_subset fun x hx => by simp at hx; rcases hx with rfl | rfl; exacts [haS, hcS]
    rw [Finset.sum_pair hab] at h2; omega
  have land : ∀ {x : ℕ} {f : ℕ → ℕ} {y : W}, x = pk N f → (∀ j < N, f j ≤ 1) → y ∈ v → (y = a ∨ y = c) →
      Nat.land (MU x) y.d = pk N (fun j => f j * D j y.s) := by
    intro x f y hx hf hy hyac
    rw [hx, hdv y hy]
    refine MU_land hf fun j hj => ?_
    have := hDb j hj
    rcases hyac with rfl | rfl <;> omega
  have lsC : Nat.land (MU (w + fC)) a.d = pk N (fun j => (fl (opW d' a c) j + FC j) * D j a.s) :=
    land (by rw [pw, pfC, pk_add]) (fun j hj => by obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FC]; omega) ha (Or.inl rfl)
  have lsA : Nat.land (MU (w + fA)) c.d = pk N (fun j => (fl (opW d' a c) j + FA j) * D j c.s) :=
    land (by rw [pw, pfA, pk_add]) (fun j hj => by obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FA]; omega) hc (Or.inr rfl)
  have llA : Nat.land (MU (fN + fA)) a.d = pk N (fun j => (FN j + FA j) * D j a.s) :=
    land (by rw [pfN, pfA, pk_add]) (fun j hj => by obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FN, FA, FC]; omega) ha (Or.inl rfl)
  have llC : Nat.land (MU (fN + fC)) c.d = pk N (fun j => (FN j + FC j) * D j c.s) :=
    land (by rw [pfN, pfC, pk_add]) (fun j hj => by obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FN, FA, FC]; omega) hc (Or.inr rfl)
  let κ : ℕ → Kd := fun j => kdOf (fl (opW d' a c) j) (FA j) (FC j)
  let D' : ℕ → ℕ → ℕ := fun j s => if s = op d' a.s c.s then (κ j).out (if ka then 0 else D j a.s) (if kc then 0 else D j c.s)
    else if s = a.s then (κ j).kpa (D j a.s) else if s = c.s then (κ j).kpc (D j c.s) else D j s
  have hao : a.s ≠ op d' a.s c.s := fun e => hfS' (e ▸ haS)
  have hco : c.s ≠ op d' a.s c.s := fun e => hfS' (e ▸ hcS)
  have kaif : ∀ x : ℕ, (if a.s ∈ S' then 0 else x) = if ka then 0 else x := fun x => by
    by_cases h : a.s ∈ S'
    · have e : ka = true := by rw [hka]; exact decide_eq_true h
      rw [e, ite_eq_left h]; rfl
    · have e : ka = false := by rw [hka]; exact decide_eq_false h
      rw [e, ite_eq_right h]; rfl
  have kcif : ∀ x : ℕ, (if c.s ∈ S' then 0 else x) = if kc then 0 else x := fun x => by
    by_cases h : c.s ∈ S'
    · have e : kc = true := by rw [hkc]; exact decide_eq_true h
      rw [e, ite_eq_left h]; rfl
    · have e : kc = false := by rw [hkc]; exact decide_eq_false h
      rw [e, ite_eq_right h]; rfl
  have hDS : ∀ j, DStep (κ j) (D j) (D' j) (op d' a.s c.s) a.s c.s S' := by
    intro j
    refine ⟨?_, fun _ => ?_, fun _ => ?_, fun x _ h1 h2 h3 => ?_⟩
    · simp only [D', ite_true]; rw [kaif, kcif]
    · simp only [D', if_neg hao, if_true]; exact le_rfl
    · simp only [D', if_neg hco, if_neg hab.symm, if_true]; exact le_rfl
    · simp only [D', if_neg h1, if_neg h2, if_neg h3]; exact le_rfl
  have hκ : ∀ j < N, (κ j).ok (P.getD j 0) d' a.s c.s := by
    intro j hj
    have h0 := he j hj
    simp only [κ, kdOf]
    split_ifs with q1 q2 q3
    · refine (?_ : Cst (P.getD j 0) (op d' a.s c.s))
      rw [← opW_s]
      exact wo.cst hj (fb_one.1 q1)
    · refine (?_ : op d' a.s c.s &&& P.getD j 0 = a.s &&& P.getD j 0)
      have q0 : fl (opW d' a c) j = 0 := by have := f3 j; omega
      by_cases h1 : fb eA j = 1
      · exact hAo j hj h1
      · refine pass_ok d' wa wc hj ?_ q0
        have := fb_le eA j; have := f2 j
        simp only [FA, q0] at q2; omega
    · refine (?_ : op d' a.s c.s &&& P.getD j 0 = c.s &&& P.getD j 0)
      have q0 : fl (opW d' a c) j = 0 := by have := f3 j; omega
      by_cases h1 : fb eC j = 1
      · exact hCo j hj h1
      · have q0' : fl (opW d' c a) j = 0 := by rw [← q0]; unfold fl; rw [opW_symm]
        rw [op_comm]
        refine pass_ok d' wc wa hj ?_ q0'
        have := fb_le eC j; have := f1 j
        simp only [FC, q0] at q3; omega
    · trivial
  have hA : ∀ j < N, (κ j).del (if ka then 0 else D j a.s) (if kc then 0 else D j c.s) + (S'.filter (Cst (P.getD j 0))).card ≤ b j ∧
      Acc (P.getD j 0) T k (b j - (κ j).del (if ka then 0 else D j a.s) (if kc then 0 else D j c.s)) (D' j) S' := by
    intro j hj
    obtain ⟨p1, p2, p3⟩ := X.hP j hj
    have := (hacc j hj).bi p1 p2 p3 hb hm hl hk (κ j) (hκ j hj) (hDS j)
    simp only [kaif, kcif] at this
    exact this
  have hrep' : Rep (v.map u) S := hs.rep.upd _ _ _ _
  have hrep : Rep r S' := by
    refine hsh.rep hrep' (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) (by rw [us, us]; exact hab) hfS fun x => ?_
    rw [us, us]
    obtain ⟨_, U, e1, e2, _⟩ := hb
    change x ∈ S' ↔ x = (opW d' a c).s ∨ _
    rw [opW_s, e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, g1, g2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := g1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := g2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hmem : ∀ x ∈ r, x = wd (opW d' a c) dn ∨ ∃ y ∈ v, x = u y := fun x hx => by
    rcases hsh.mem hx with h | h
    · exact Or.inl h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h; exact Or.inr ⟨y, hy, rfl⟩
  have hwok : ∀ x ∈ r, WOk P x := fun x hx => by
    rcases hmem x hx with rfl | ⟨y, hy, rfl⟩
    · exact ⟨wo.pa, wo.pb, wo.ec, wo.ca, wo.cb⟩
    · exact (hs.wok y hy).upd _ _ _ _
  have hgood : ∀ x ∈ r, Good l x.s := fun x hx => by
    rcases hmem x hx with rfl | ⟨y, hy, rfl⟩
    · change Good l (opW d' a c).s
      rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · rw [us]; exact hs.good y hy
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl (opW d' a c) j + cnt v j := by
    intro j
    have := hsh.cnt j
    rw [fl_upd, fl_upd, cnt_upd] at this
    exact this
  have n1 : ∀ j < N, _ := fun j hj => num1 (b := b j) (cv := cnt v j) (cr := cnt r j) (da := D j a.s) (dc := D j c.s) (ka := ka) (kc := kc)
    (f1 j) (f2 j) (f3 j) (f4 j).1 (f4 j).2 (he j hj) (hb15 j hj) (hle j hj) (hcnt j) (by
      have h1 := (hA j hj).1
      have h2 := cnt_card hrep hwok hj
      exact (Nat.add_le_add_left h2 _).trans h1)
  have e1 : z + (a.c &&& c.c) - w = pk N (fun j => 32 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, pw, pk_add, pk_sub]
    intro j hj; exact (n1 j hj).1.1
  have e2 : z + (a.c &&& c.c) - w - (eA + eC) = pk N (fun j => 32 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (fb eA j + fb eC j)) := by
    rw [e1]
    conv_lhs => rw [peA, peC]
    rw [pk_add, pk_sub]
    intro j hj; exact (n1 j hj).1.2.2.2.1
  refine ⟨⟨hrep, hwok, hgood, _, D', fun j hj => ?_, fun j hj => (hA j hj).2, ?_, fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · have := hb15 j hj; omega
  · intro x hx
    rcases hmem x hx with rfl | ⟨y, hy, rfl⟩
    · change dn = pk N (fun j => D' j (opW d' a c).s)
      rw [hdn, pfN]
      have eA' : (bif ka then 0 else Nat.land (MU (fN + fA)) a.d) = pk N (fun j => bif ka then 0 else (FN j + FA j) * D j a.s) := by
        cases ka
        · exact llA
        · simp [pk]
      have eC' : (bif kc then 0 else Nat.land (MU (fN + fC)) c.d) = pk N (fun j => bif kc then 0 else (FN j + FC j) * D j c.s) := by
        cases kc
        · exact llC
        · simp [pk]
      rw [← pfN, eA', eC', pfN, pk_add, pk_add]
      refine pk_congr fun j hj => ?_
      obtain ⟨_, q, _, _⟩ := n2 j hj
      simp only [D', opW_s, if_true]
      exact q
    · by_cases h1 : y.s = a.s
      · have hya := hs.rep.inj hy ha h1
        subst hya
        have : u y = wd y (Nat.land (MU (w + fC)) y.d) := by rw [hu]; unfold upd; rw [beq_t]; rfl
        rw [this]
        change Nat.land (MU (w + fC)) y.d = pk N (fun j => D' j y.s)
        rw [lsC]
        refine pk_congr fun j hj => ?_
        simp only [D', if_neg hao, if_true]
        exact (n2 j hj).2.2.1
      · by_cases h2 : y.s = c.s
        · have hyc := hs.rep.inj hy hc h2
          subst hyc
          have : u y = wd y (Nat.land (MU (w + fA)) y.d) := by rw [hu]; unfold upd; rw [beq_f h1, beq_t]; rfl
          rw [this]
          change Nat.land (MU (w + fA)) y.d = pk N (fun j => D' j y.s)
          rw [lsA]
          refine pk_congr fun j hj => ?_
          simp only [D', if_neg hco, if_neg hab.symm, if_true]
          exact (n2 j hj).2.2.2
        · have : u y = y := by rw [hu]; unfold upd; rw [beq_f h1, beq_f h2]; rfl
          rw [this, hdv y hy]
          refine pk_congr fun j hj => ?_
          have h3 : y.s ≠ op d' a.s c.s := fun e => hfS' (e ▸ hs.rep.mem.2 ⟨y, hy, rfl⟩)
          simp only [D', if_neg h3, if_neg h1, if_neg h2]
  · have h1 := hsum j hj
    have h2 := (hDS j).sum_le hb hfS'
    omega
  · rw [e2]
    have ea : (bif ka then a.c else Nat.land (MU (w + fC)) a.d) = pk N (fun j => bif ka then fl a j else (fl (opW d' a c) j + FC j) * D j a.s) := by
      cases ka
      · exact lsC
      · exact pa
    have ec : (bif kc then c.c else Nat.land (MU (w + fA)) c.d) = pk N (fun j => bif kc then fl c j else (fl (opW d' a c) j + FA j) * D j c.s) := by
      cases kc
      · exact lsA
      · exact pc
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (n1 j hj).2.2.2
    · intro j hj; exact (n1 j hj).2.2.1
    · intro j hj; exact (n1 j hj).2.1
  · rw [e1, nl, X.hg, ← hN, pk_guard]; · simp
    intro j hj; exact ⟨(n1 j hj).1.2.1, (n1 j hj).1.2.2.1⟩
  · rw [e2, nl, X.hg, ← hN, pk_guard]; · simp
    intro j hj; exact ⟨(n1 j hj).1.2.2.2.2.1, (n1 j hj).1.2.2.2.2.2⟩
end sound
lemma upd_irrel {sa sc da dc da' dc' : ℕ} {ka kc : Bool} (h1 : ka = false ∨ da = da') (h2 : kc = false ∨ dc = dc') (v : List W) :
    (v.filter (kp sa ka sc kc)).map (upd sa da sc dc) = (v.filter (kp sa ka sc kc)).map (upd sa da' sc dc') := by
  refine List.map_congr_left fun w hw => ?_
  have hk := (List.mem_filter.1 hw).2
  unfold kp at hk; unfold upd
  cases e1 : Nat.beq w.s sa with
  | true =>
    rw [e1] at hk; simp only [Bool.cond_true] at hk ⊢
    rcases h1 with h | h
    · rw [h] at hk; simp at hk
    · rw [h]
  | false =>
    rw [e1] at hk; simp only [Bool.cond_false] at hk ⊢
    cases e2 : Nat.beq w.s sc with
    | true =>
      rw [e2] at hk; simp only [Bool.cond_true] at hk ⊢
      rcases h2 with h | h
      · rw [h] at hk; simp at hk
      · rw [h]
    | false => rfl
lemma put_eq {m : ℕ} {o : W} {v : List W} {d : ℕ} (ho : Nat.lor o.a o.b = o.c) (hr : o.r = 0) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v d h = ins (wd o d) v h := by
  simp only [put, st_eq, beq_f h0, beq_f h1, ho]
  rw [← hr]; rfl
lemma mid_false {f : ℕ → List W → Bool} {m g np e n z : ℕ} {v : List W} {a c : W} {oa oc ka kc kb : Bool} {s x y w eA eC : ℕ}
    (hw : w = Nat.lor x y) (heA : eA = zfl np (Nat.xor a.s s) (Nat.sub (Nat.shiftRight g 5) (Nat.lor (Nat.lor a.c c.c) w)))
    (heC : eC = zfl np (Nat.xor c.s s) (Nat.sub (Nat.sub (Nat.shiftRight g 5) (Nat.lor (Nat.lor a.c c.c) w)) eA))
    (h : mid f m g np e n z v a c oa oc ka kc kb s x y = false)
    (g1 : Nat.beq (Nat.land (z + (a.c &&& c.c) - w) g) g = true) (g2 : Nat.beq (Nat.land (z + (a.c &&& c.c) - w - (eA + eC)) g) g = true) :
    kids (child f g) e n (z + (a.c &&& c.c) - w - (eA + eC)) (Nat.shiftRight g 5) w (fAo eA w c.c) (fAo eC w a.c) a c oa oc ka kc kb (put m s x y v) = false := by
  simp only [mid, st_eq, bR, ← hw, ← heA, ← heC] at h
  have g1' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) g) g = true := g1
  have g2' : Nat.beq (Nat.land (Nat.sub (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) (Nat.add eA eC)) g) g = true := g2
  rw [g1', g2', Bool.cond_true, Bool.cond_true] at h
  exact h
lemma kids_false {ch : Bool → ((List W → Bool) → Bool) → ℕ → Bool} {e n z u w fA fC fN : ℕ} {a c : W} {oa oc ka kc kb : Bool} {mk : ℕ → (List W → Bool) → Bool}
    (hN : fN = fNo u w fA fC) (h : kids ch e n z u w fA fC a c oa oc ka kc kb mk = false) :
    (oa = true → oc = true → ch false (fun h => mk (fN + Nat.land (MU (fN + fA)) a.d + Nat.land (MU (fN + fC)) c.d) (fun r => rmk a.s false 0 c.s false 0 r h))
      (z - Nat.land (MU (w + fC)) a.d - Nat.land (MU (w + fA)) c.d) = false) ∧
    (oa = true → n + 1 ≤ e → ch kc (fun h => mk (fN + Nat.land (MU (fN + fA)) a.d) (fun r => rmk a.s false 0 c.s true (Nat.land (MU (w + fA)) c.d) r h))
      (z - Nat.land (MU (w + fC)) a.d - c.c) = false) ∧
    (oc = true → n + 1 ≤ e → ch ka (fun h => mk (fN + Nat.land (MU (fN + fC)) c.d) (fun r => rmk a.s true (Nat.land (MU (w + fC)) a.d) c.s false 0 r h))
      (z - a.c - Nat.land (MU (w + fA)) c.d) = false) ∧
    (n + 2 ≤ e → ch kb (fun h => mk fN (fun r => rmkB a.s (Nat.land (MU (w + fC)) a.d) c.s (Nat.land (MU (w + fA)) c.d) (a.d + c.d) r h))
      (z - a.c - c.c) = false) := by
  subst hN
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  have key : ∀ {p q : Bool}, (bif p then true else q) = false → p = false ∧ q = false := fun {p q} h => by cases p <;> simp_all
  obtain ⟨h1, h2⟩ := key h
  obtain ⟨h3, h4⟩ := key h2
  refine ⟨fun p q => ?_, fun p q => ?_, fun p q => ?_, fun q => ?_⟩
  · rw [p, q] at h1; exact h1
  · rw [b1 q, Bool.cond_true] at h3
    have := (key h3).2; rw [p] at this; exact this
  · rw [b1 q, Bool.cond_true] at h3
    have := (key h3).1; rw [p] at this; exact this
  · rw [b2 q] at h4; exact h4
lemma nc_spec {P : List ℕ} {a c o : W} {g w : ℕ} (hg : g = pk P.length (fun _ => 32)) (ha : WOk P a) (hc : WOk P c) (ho : WOk P o) (hw : w = o.c) :
    Nat.sub (Nat.shiftRight g 5) (Nat.lor (Nat.lor a.c c.c) w) = pk P.length (fun j => 1 - max (fl a j) (max (fl c j) (fl o j))) := by
  have hx : isPk P.length ((a.c ||| c.c) ||| w) := by rw [hw]; exact isPk_or (isPk_or ha.pc hc.pc) ho.pc
  have e : (a.c ||| c.c) ||| w = pk P.length (fun j => max (fl a j) (max (fl c j) (fl o j))) := by
    rw [pk_of hx]
    refine pk_congr fun j _ => ?_
    rw [hw, Nat.testBit_or, Nat.testBit_or]; unfold fl
    cases a.c.testBit (6 * j) <;> cases c.c.testBit (6 * j) <;> cases o.c.testBit (6 * j) <;> rfl
  change Nat.shiftRight g 5 - ((a.c ||| c.c) ||| w) = _
  rw [hg, shr4, e, pk_sub]
  intro j _
  have := fl_le a j; have := fl_le c j; have := fl_le o j; omega
lemma zfl_isPk {n np q nc : ℕ} (h : isPk n nc) : isPk n (zfl np q nc) := by
  unfold zfl zflG
  change isPk n (_ &&& nc)
  rw [Nat.and_comm]; exact isPk_and h
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma zfl_eq {q nc j : ℕ} {a o : ℕ} (hj : j < P.length) (hq : q = a ^^^ o) (h : fb (zfl np q nc) j = 1) : o &&& P.getD j 0 = a &&& P.getD j 0 := by
  obtain ⟨f, f1, f2, f3⟩ := X.hnp
  obtain ⟨h16, h0, _⟩ := zfl_spec f1 f2 (by decide) (fb_one.1 h)
  have h1 : q &&& P.getD j 0 = 0 := by
    rw [← f3 j hj h16, Nat.and_comm (P.getD j 0), ← Nat.and_assoc, h0, Nat.zero_and]
  subst hq
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) h1
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at this ⊢
  revert this
  cases a.testBit i <;> cases o.testBit i <;> cases (P.getD j 0).testBit i <;> simp
lemma gate_sound {f : ℕ → List W → Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool} {oa oc ka kc kb : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hoa : a.s ∉ S' → oa = true) (hoc : c.s ∉ S' → oc = true) (hka : a.s ∈ S' → c.s ∉ S' → ka = false) (hkc : c.s ∈ S' → a.s ∉ S' → kc = false)
    (hkb : a.s ∈ S' → c.s ∈ S' → kb = false)
    (hp : mid f m g np e (Nat.pred n) z v a c oa oc ka kc kb (opW d' a c).s (opW d' a c).a (opW d' a c).b = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' a.s c.s ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r := by
  subst hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have hab : a.s ≠ c.s := hb.1
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  have er : (opW d' a c).r = 0 := by cases d' <;> rfl
  obtain ⟨w, hw⟩ : ∃ w, w = Nat.lor (opW d' a c).a (opW d' a c).b := ⟨_, rfl⟩
  have hw' : w = (opW d' a c).c := hw.trans ec
  obtain ⟨nc, hnc⟩ : ∃ nc, nc = Nat.sub (Nat.shiftRight g 5) (Nat.lor (Nat.lor a.c c.c) w) := ⟨_, rfl⟩
  have pnc : nc = pk P.length (fun j => 1 - max (fl a j) (max (fl c j) (fl (opW d' a c) j))) := by rw [hnc]; exact nc_spec X.hg wa wc wo hw'
  have hncP : isPk P.length nc := by rw [pnc]; exact pk_isPk fun j _ => by omega
  have fbnc : ∀ j < P.length, fb nc j = 1 - max (fl a j) (max (fl c j) (fl (opW d' a c) j)) := fun j hj => by
    rw [pnc]; exact fb_of_pk (fun j _ => by omega) hj
  obtain ⟨eA, heA⟩ : ∃ eA, eA = zfl np (Nat.xor a.s (opW d' a c).s) nc := ⟨_, rfl⟩
  have hEA : isPk P.length eA := by rw [heA]; exact zfl_isPk hncP
  have zle : ∀ {q x j : ℕ}, fb (zfl np q x) j ≤ fb x j := by
    intro q x j
    unfold fb zfl zflG
    change ((_ &&& x).testBit (6 * j)).toNat ≤ _
    rw [Nat.testBit_and]
    cases x.testBit (6 * j) <;> simp
    cases Nat.testBit _ _ <;> simp
  have fbA : ∀ j < P.length, fb eA j ≤ 1 - max (fl a j) (max (fl c j) (fl (opW d' a c) j)) := fun j hj => by
    rw [← fbnc j hj, heA]; exact zle
  have pnc2 : nc - eA = pk P.length (fun j => fb nc j - fb eA j) := by
    conv_lhs => rw [fb_pk hncP, fb_pk hEA]
    exact pk_sub fun j hj => by rw [fbnc j hj]; exact fbA j hj
  obtain ⟨eC, heC⟩ : ∃ eC, eC = zfl np (Nat.xor c.s (opW d' a c).s) (Nat.sub nc eA) := ⟨_, rfl⟩
  have hnc2 : isPk P.length (Nat.sub nc eA) := by
    change isPk P.length (nc - eA); rw [pnc2]; exact pk_isPk fun j _ => by have := fb_le nc j; omega
  have hEC : isPk P.length eC := by rw [heC]; exact zfl_isPk hnc2
  have fbC : ∀ j < P.length, fb eC j ≤ fb nc j - fb eA j := fun j hj => by
    rw [heC]
    refine zle.trans ?_
    change fb (nc - eA) j ≤ _
    rw [pnc2, fb_of_pk (fun j _ => by have := fb_le nc j; omega) hj]
  have he : ∀ j < P.length, fb eA j + fb eC j + max (fl a j) (max (fl c j) (fl (opW d' a c) j)) ≤ 1 := fun j hj => by
    have h1 := fbA j hj; have h2 := fbC j hj; rw [fbnc j hj] at h2
    have := fl_le a j; have := fl_le c j; have := fl_le (opW d' a c) j; omega
  have hAo : ∀ j < P.length, fb eA j = 1 → op d' a.s c.s &&& P.getD j 0 = a.s &&& P.getD j 0 := fun j hj h => by
    rw [← opW_s]; rw [heA] at h; exact zfl_eq X hj rfl h
  have hCo : ∀ j < P.length, fb eC j = 1 → op d' a.s c.s &&& P.getD j 0 = c.s &&& P.getD j 0 := fun j hj h => by
    rw [← opW_s]; rw [heC] at h; exact zfl_eq X hj rfl h
  obtain ⟨fA, hfA⟩ : ∃ fA, fA = fAo eA w c.c := ⟨_, rfl⟩
  obtain ⟨fC, hfC⟩ : ∃ fC, fC = fAo eC w a.c := ⟨_, rfl⟩
  obtain ⟨fN, hfN⟩ : ∃ fN, fN = fNo (Nat.shiftRight g 5) w fA fC := ⟨_, rfl⟩
  obtain ⟨da, hda⟩ : ∃ da, da = Nat.land (MU (w + fC)) a.d := ⟨_, rfl⟩
  obtain ⟨dc, hdc⟩ : ∃ dc, dc = Nat.land (MU (w + fA)) c.d := ⟨_, rfl⟩
  have main : ∀ qa qc : Bool, qa = decide (a.s ∈ S') → qc = decide (c.s ∈ S') → ∃ r0 : List W, r0.Perm (wd (opW d' a c) (fN + (bif qa then 0 else Nat.land (MU (fN + fA)) a.d) + (bif qc then 0 else Nat.land (MU (fN + fC)) c.d)) :: v) ∧
      (∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v (fN + (bif qa then 0 else Nat.land (MU (fN + fA)) a.d) + (bif qc then 0 else Nat.land (MU (fN + fC)) c.d)) h = h r0) ∧
      ((r0.filter (kp a.s qa c.s qc)).map (upd a.s da c.s dc)).length = S'.card ∧
      ((r0.filter (kp a.s qa c.s qc)).map (upd a.s da c.s dc)).length + (bif qa then 0 else 1) + (bif qc then 0 else 1) = v.length + 1 ∧
      StOk P T l k (z + (a.c &&& c.c) - w - (eA + eC) - (bif qa then a.c else da) - (bif qc then c.c else dc)) ((r0.filter (kp a.s qa c.s qc)).map (upd a.s da c.s dc)) S' ∧
      (∀ x ∈ (r0.filter (kp a.s qa c.s qc)).map (upd a.s da c.s dc), (x.s = op d' a.s c.s ∧ x.r = 0) ∨ ∃ w' ∈ v, w'.s = x.s ∧ w'.r = x.r) ∧
      Nat.beq (Nat.land (z + (a.c &&& c.c) - w) g) g = true ∧ Nat.beq (Nat.land (z + (a.c &&& c.c) - w - (eA + eC)) g) g = true := by
    intro qa qc h1 h2
    obtain ⟨r0, hr0, hins⟩ := ins_spec (wd (opW d' a c) (fN + (bif qa then 0 else Nat.land (MU (fN + fA)) a.d) + (bif qc then 0 else Nat.land (MU (fN + fC)) c.d))) v hosS
    have hsh := shape_upd (o := wd (opW d' a c) (fN + (bif qa then 0 else Nat.land (MU (fN + fA)) a.d) + (bif qc then 0 else Nat.land (MU (fN + fC)) c.d))) da dc hosS hr0 hs.rep.1 ha hc hab qa qc
    have hst := bi_st X hs hm hk hb hl ha hc h1 h2 hEA hEC he hAo hCo hw' hfA hfC hfN rfl (by rw [← hda, ← hdc]; exact hsh)
    rw [← hda, ← hdc] at hst
    have hlen := hsh.len
    refine ⟨r0, hr0, fun h => ?_, hst.1.rep.card.symm, by rw [List.length_map (as := v)] at hlen; exact hlen, hst.1, fun x hx => ?_, hst.2.1, hst.2.2⟩
    · rw [put_eq ec er ho0 ho1, hins]
    · rcases hsh.mem hx with rfl | hx'
      · exact Or.inl ⟨opW_s _ _ _, er⟩
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx'
        exact Or.inr ⟨y, hy, (upd_s _ _ _ _ _).symm, (upd_r _ _ _ _ _).symm⟩
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hab] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨r0, p0, p1, p2, p3, p4, p5, g1, g2⟩ := main true true (by simp [q1]) (by simp [q2])
    have hkd := (kids_false hfN (by rw [hfA, hfC]; exact mid_false hw (by rw [heA, hnc]) (by rw [heC, hnc]) hp g1 g2)).2.2.2 (by rw [p2] at p3; simp only [Bool.cond_true, Bool.cond_false] at p3; omega)
    rw [← hda, ← hdc] at hkd
    simp only [Bool.cond_true, add_zero] at p0 p1 p3 p4
    refine ⟨_, _, child_sound X (fun h => ?_) (hkb q1 q2) p4 hmin hk hkd, p4, p5⟩
    rw [p1]
    unfold rmkB
    rw [bR]
    cases hz : Nat.beq (a.d + c.d) 0 with
    | false => rw [Bool.cond_false, rmk_eq]
    | true =>
      rw [Bool.cond_true]
      have hz0 : a.d + c.d = 0 := Nat.eq_of_beq_eq_true hz
      have ha0 : a.d = 0 := by omega
      have hc0 : c.d = 0 := by omega
      have e1 : r0.filter (kp a.s true c.s true) = r0 := by
        rw [List.filter_eq_self]; intro x _
        unfold kp; cases Nat.beq x.s a.s <;> cases Nat.beq x.s c.s <;> rfl
      rw [e1]
      congr 1
      have e2 : ∀ x ∈ r0, upd a.s da c.s dc x = x := by
        intro x hx
        have hda0 : da = 0 := by rw [hda, ha0]; exact Nat.and_zero _
        have hdc0 : dc = 0 := by rw [hdc, hc0]; exact Nat.and_zero _
        have hx' := p0.subset hx
        simp only [List.mem_cons] at hx'
        unfold upd
        rcases hx' with rfl | hx'
        · have n1 : (wd (opW d' a c) fN).s ≠ a.s := (hosS a ha).symm
          have n2 : (wd (opW d' a c) fN).s ≠ c.s := (hosS c hc).symm
          rw [beq_f n1, beq_f n2]; rfl
        · by_cases n1 : x.s = a.s
          · have := hs.rep.inj hx' ha n1
            subst this; rw [beq_t, hda0, ← ha0]; rfl
          · by_cases n2 : x.s = c.s
            · have := hs.rep.inj hx' hc n2
              subst this; rw [beq_f n1, beq_t, hdc0, ← hc0]; rfl
            · rw [beq_f n1, beq_f n2]; rfl
      conv_lhs => rw [← List.map_id r0]
      exact List.map_congr_left fun x hx => (e2 x hx).symm
  · obtain ⟨r0, p0, p1, p2, p3, p4, p5, g1, g2⟩ := main true false (by simp [q1]) (by simp [q2])
    have hkd := (kids_false hfN (by rw [hfA, hfC]; exact mid_false hw (by rw [heA, hnc]) (by rw [heC, hnc]) hp g1 g2)).2.2.1 (hoc q2) (by rw [p2] at p3; simp only [Bool.cond_true, Bool.cond_false] at p3; omega)
    rw [← hda, ← hdc] at hkd
    simp only [Bool.cond_true, Bool.cond_false, add_zero] at p0 p1 p3 p4
    refine ⟨_, _, child_sound X (fun h => ?_) (hka q1 q2) p4 hmin hk hkd, p4, p5⟩
    rw [p1, rmk_eq]; congr 1; exact upd_irrel (Or.inr rfl) (Or.inl rfl) _
  · obtain ⟨r0, p0, p1, p2, p3, p4, p5, g1, g2⟩ := main false true (by simp [q1]) (by simp [q2])
    have hkd := (kids_false hfN (by rw [hfA, hfC]; exact mid_false hw (by rw [heA, hnc]) (by rw [heC, hnc]) hp g1 g2)).2.1 (hoa q1) (by rw [p2] at p3; simp only [Bool.cond_true, Bool.cond_false] at p3; omega)
    rw [← hda, ← hdc] at hkd
    simp only [Bool.cond_true, Bool.cond_false, add_zero] at p0 p1 p3 p4
    refine ⟨_, _, child_sound X (fun h => ?_) (hkc q2 q1) p4 hmin hk hkd, p4, p5⟩
    rw [p1, rmk_eq]; congr 1; exact upd_irrel (Or.inl rfl) (Or.inr rfl) _
  · obtain ⟨r0, p0, p1, p2, p3, p4, p5, g1, g2⟩ := main false false (by simp [q1]) (by simp [q2])
    have hkd := (kids_false hfN (by rw [hfA, hfC]; exact mid_false hw (by rw [heA, hnc]) (by rw [heC, hnc]) hp g1 g2)).1 (hoa q1) (hoc q2)
    rw [← hda, ← hdc] at hkd
    simp only [Bool.cond_false] at p0 p1 p3 p4
    refine ⟨_, _, child_sound X (fun h => ?_) rfl p4 hmin hk hkd, p4, p5⟩
    rw [p1, rmk_eq]; congr 1; exact upd_irrel (Or.inl rfl) (Or.inl rfl) _
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0, 0⟩
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma un_st {k k' t z : ℕ} {v r0 : List W} {S S' : Finset ℕ} {a : W} {ka : Bool} {dn : ℕ}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hdn : dn = (Nat.shiftRight g 5 - a.c) + (bif ka then 0 else a.d)) (hr0 : r0.Perm (wd (notW m a) dn :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) ((r0.filter (kp a.s ka a.s ka)).map (upd a.s 0 a.s 0)) S' ∧
    ∀ x ∈ (r0.filter (kp a.s ka a.s ka)).map (upd a.s 0 a.s 0), (x.s = a.s ^^^ m ∧ x.r = 0) ∨ ∃ w' ∈ v, w'.s = x.s ∧ w'.r = x.r := False.elim hb
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) :
    (n ≤ e → ins (wd (notW m a) (Nat.shiftRight g 5 - a.c + a.d)) v (fun v => child (f (a.s ^^^ m)) g false (rmk a.s false 0 a.s false 0 v) (z - a.c)) = false) ∧
    (n + 1 ≤ e → ins (wd (notW m a) (Nat.shiftRight g 5 - a.c)) v (fun v => child (f (a.s ^^^ m)) g false (rmk a.s true 0 a.s true 0 v) (z - a.c - a.c)) = false) := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) fun s => st (Nat.sub z w.c) fun z => (fun u =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (st u fun d1 => ins ⟨s, w.b, w.a, w.c, 0, d1⟩ v (fun v => child (f s) g false (rmk w.s true 0 w.s true 0 v) (Nat.sub z w.c))) (Nat.ble (Nat.succ n) e)) true
        (Bool.rec (motive := fun _ => Bool) false (st (Nat.add u w.d) fun d1 => ins ⟨s, w.b, w.a, w.c, 0, d1⟩ v (fun v => child (f s) g false (rmk w.s false 0 w.s false 0 v) z)) (Nat.ble n e)))
      (Nat.sub (Nat.shiftRight g 5) w.c)) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    simp only [bR, st_eq] at h
    have key : ∀ {p q : Bool}, (bif p then true else q) = false → p = false ∧ q = false := fun {p q} h => by cases p <;> simp_all
    obtain ⟨h1, h2⟩ := key h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have hq' : Nat.beq (Nat.succ a.s) q = false := beq_f hq
      rw [hq', Bool.cond_false] at h1
      obtain ⟨h3, h4⟩ := key h1
      refine ⟨fun hn => ?_, fun hn => ?_⟩
      · rw [show Nat.ble n e = true from Nat.ble_eq_true_of_le hn] at h3
        exact h3
      · rw [show Nat.ble (Nat.succ n) e = true from Nat.ble_eq_true_of_le hn] at h4
        exact h4
    · exact ih h2 ha
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' ∧
      ∀ w ∈ r, (w.s = a.s ^^^ m ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r := False.elim hb
end sound
noncomputable section hitcore
def len (v : List W) : Nat := List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) v
def geo (w n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.add (Nat.shiftLeft ih w) 1) n
def LNN : Nat := Nat.mul 12 NN
def LN2 : Nat := Nat.mul 24 NN
def LN4 : Nat := Nat.mul 48 NN
def LM1 : Nat := Nat.mul 13 NN
def LM2 : Nat := Nat.mul 26 NN
def LM4 : Nat := Nat.mul 52 NN
def RL : Nat := geo NN 12
def PLN : Nat := Nat.pow 2 LNN
def AAR : Nat := Nat.mul AA RL
def HXR : Nat := Nat.mul HX (geo NN 84)
def HYR : Nat := Nat.mul HY (geo NN 84)
def MRR : Nat := Nat.mul (Nat.sub (Nat.pow 2 NN) (Nat.pow 2 64)) (geo NN 84)
def TOPR : Nat := Nat.shiftLeft (geo NN 72) LM1
def GMD : Nat := Nat.sub (Nat.pow 2 (Nat.sub NN 1)) 1
def pkd (d : Bool) (l : Nat) (v : List W) : Nat := List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.shiftLeft (sp d l w.s) (Nat.mul NN (len t))) ih) v
def dbl (m x : Nat) : Nat := Nat.lor x (Nat.shiftLeft x m)
def eg2 (G : Nat) : Nat := Nat.shiftRight (Nat.mod (Nat.land (Nat.land (Nat.add (Nat.land G HXR) MRR) (Nat.add (Nat.land G HYR) MRR)) TOPR) GMD) 1
def eg1 (F : Nat) : Nat := eg2 (Nat.land (dbl LN4 (dbl LN2 (dbl LNN F))) (dbl LM4 (dbl LM2 (dbl LM1 F))))
def edg (d : Bool) (l o : Nat) (v : List W) : Nat := eg1 (Nat.mod (Nat.add (Nat.land (pkd d l v) (Nat.mul o RL)) AAR) PLN)
def f12c (b : Nat) : Nat := Nat.land (Nat.lor b (Nat.shiftRight b 12)) 4095
def f12b (a : Nat) : Nat := f12c (Nat.lor a (Nat.shiftRight a 24))
def f12 (w : Nat) : Nat := f12b (Nat.lor w (Nat.shiftRight w 48))
def f13c (b : Nat) : Nat := Nat.land (Nat.lor b (Nat.shiftRight b 13)) 4095
def f13b (a : Nat) : Nat := f13c (Nat.lor a (Nat.shiftRight a 26))
def f13 (w : Nat) : Nat := f13b (Nat.lor w (Nat.shiftRight w 52))
def nbr (e S : Nat) : Nat := Nat.lor (f12 (Nat.land e (Nat.mul S 302268352895954163081217))) (f13 (Nat.land e (Nat.mul S 4723519685917965029377)))
def bfs (e : Nat) (fuel : Nat) : Nat → Nat → (Nat → Bool) → Bool := Nat.rec (motive := fun _ => Nat → Nat → (Nat → Bool) → Bool) (fun _ _ _ => false)
  (fun _ ih A B k => st (Nat.lor A (nbr e B)) (fun a => st (Nat.lor B (nbr e a)) (fun b => Bool.rec (motive := fun _ => Bool) true
    (Bool.rec (motive := fun _ => Bool) (ih a b k) (k (Nat.lor a b)) (Nat.beq (Nat.lor A B) (Nat.lor a b))) (Nat.beq (Nat.land a b) 0)))) fuel
def nonb (e : Nat) (fuel : Nat) : Nat → Bool := Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
  (fun _ ih r => Bool.rec (motive := fun _ => Bool) (bfs e 12 (Nat.gcd r 2048) 0 (fun c => ih (Nat.sub r (Nat.land r c)))) false (Nat.beq r 0)) fuel
def nonbip (e : Nat) : Bool := nonb e 12 (Nat.lor (f12 e) (f13 e))
def tch (i : Nat) : Nat := Nat.lor (Nat.mul i 302268352895954163081217) (Nat.mul i 4723519685917965029377)
def del (e i : Nat) : Nat := Nat.xor (Nat.lor e (tch i)) (tch i)
def ne0 (e : Nat) : Bool := Bool.rec (motive := fun _ => Bool) true false (Nat.beq e 0)
def kF (_ : Nat) : Bool := false
def kF2 (_ _ : Nat) : Bool := false
def kT2 (_ _ : Nat) : Bool := true
def tst1 (h : Nat) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (F (fun i => ne0 (del h i)) kT2) false (nonbip h)
def tri5 (a L r : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (Nat.lor a (Nat.gcd L 4096)) r (Nat.beq L 0)
def tri4 (h i N k r : Nat) : Nat := tri5 (Nat.lor i k) (Nat.land (nbr h k) N) r
def tri3 (h i N M r : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (tri4 h i N (Nat.gcd M 4096) r) r (Nat.beq M 0)
def tri2 (h i N r : Nat) : Nat := tri3 h i N (Nat.land (nbr h N) N) r
def tri1 (h i r : Nat) : Nat := tri2 h i (nbr h i) r
def tri (h : Nat) (fuel : Nat) : Nat → Nat := Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
  (fun _ ih r => Bool.rec (motive := fun _ => Nat) (tri1 h (Nat.gcd r 2048) (ih (Nat.sub r (Nat.gcd r 2048)))) 0 (Nat.beq r 0)) fuel
def k1 (h i : Nat) : Bool := nonbip (del h i)
def k2 (h i j : Nat) : Bool := ne0 (del (del h i) j)
def k3 (h T i : Nat) : Bool := Bool.rec (motive := fun _ => Bool) (nonbip (del h i)) true (Nat.beq (Nat.land i T) 0)
def k4 (h T i j : Nat) : Bool := Bool.rec (motive := fun _ => Bool) true (ne0 (del (del h i) j)) (Nat.beq (Nat.land (Nat.lor i j) T) (Nat.lor i j))
def tst2 (h : Nat) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool := st (tri h 12 (f12 h)) (fun T => Bool.rec (motive := fun _ => Bool) (F (k3 h T) (k4 h T)) (F (k1 h) (k2 h)) (Nat.beq T 0))
def tsn (d : Bool) (l e : Nat) (v : List W) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool :=
  (fun n => (fun o => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F kF kF2) (st (edg false l o v) (fun h => tst2 h F)) (Nat.beq (Nat.succ (Nat.succ n)) e))
      (st (edg false l o v) (fun h => tst1 h F)) (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) false (F kF kF2) (Nat.beq (edg d l o v) 0)) (Nat.beq n e)) (wst d l v)) (len v)
end hitcore
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
  i : Nat
noncomputable section core12
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w t ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o, Nat.shiftLeft 1 (len t)⟩ :: ih) v
def f0 (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (ia ic da dc s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (h a c true true true true true s x y) (Nat.beq (Nat.lor da dc) 0)
def f1 (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (ia ic da dc s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (h a c false false true true false s x y) false (κ2 ia ic))
      (Bool.rec (motive := fun _ => Bool) (h a c false true false true (κ2 ia ic) s x y) (Bool.rec (motive := fun _ => Bool) (h a c false false true true false s x y) false (κ2 ia ic)) (κ ia)) (Nat.beq dc 0))
    (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (h a c true false true false (κ2 ia ic) s x y) (Bool.rec (motive := fun _ => Bool) (h a c false false true true false s x y) false (κ2 ia ic)) (κ ic))
      (h a c true true (κ ia) (κ ic) (κ2 ia ic) s x y) (Nat.beq dc 0))
    (Nat.beq da 0)
def f2 (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (ia ic da dc s x y : Nat) : Bool :=
  h a c (Nat.beq da 0) (Nat.beq dc 0) false false false s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u i => X.rec (motive := fun _ => Bool) (fun c s' q' u' j => Bool.rec (motive := fun _ => Bool)
    (h a c i j (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) true
    (h a c i j (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : X → X → Bool) (xs : List X) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : X → X → Bool) (xs : List X) : Bool := pairs h (fs xs)
def nodeH (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (d : Bool) (l e n : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 κ κ2 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ (Nat.succ n)) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g np e n z : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (go : (X → X → Bool) → List X → Bool) : Bool :=
  nodeH (mid f m g np e (Nat.pred n) z v) d l e n v κ κ2 go
def forb (fm fh s : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight fh (Nat.mod s fm)) 1) 1
def mid1 (fm fh : Nat) (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (oa oc ka kc kb : Bool) (s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (h a c oa oc ka kc kb s x y) false (forb fm fh s)
def node1 (f : Nat → List W → Bool) (d : Bool) (l m g np fm fh e n z : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (go : (X → X → Bool) → List X → Bool) : Bool :=
  nodeH (mid1 fm fh (mid f m g np e (Nat.pred n) z v)) d l e n v κ κ2 go
def mv (F : Nat → Nat → Nat → List W → Bool) (l m g np k t z : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tsn (pos s) l (Nat.sub k s) v (fun κ κ2 =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tsn (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun κ κ2 =>
          st (Nat.sub k 3) fun k3 => node (F k3 s) (pos s) l m g np (Nat.sub (Nat.sub k 2) s) (len v) z v κ κ2 (pairsQ q q'))))
          m g (Nat.sub (Nat.sub k 1) s) (len v) z (Nat.succ q) v v)) true
        (st (Nat.sub k 2) fun k2 => node (F k2 s) (pos s) l m g np (Nat.sub (Nat.sub k 1) s) (len v) z v κ κ2 (pairsP q)))))
      m g (Nat.sub k s) n z 0 v v)) true
    (st (Nat.sub k 1) fun k1 => node (F k1 t) (pos t) l m g np (Nat.sub k t) n z v κ κ2 pairsN)) (len v)
def look (l m g np : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (Nat.sub (Nat.succ k) t) v (fun κ κ2 => mv ih l m g np k t z v κ κ2)) true (Nat.ble (len v) 1)) fuel
def look1 (l m g np fm fh K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (Nat.sub (Nat.succ k) t) v (fun κ κ2 =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g np k) l m g np k t z v κ κ2) true
        (st (Nat.sub k 1) fun k1 => node1 (ih k1 t) (pos t) l m g np fm fh (Nat.sub k t) (len v) z v κ κ2 pairsS))) true (Nat.ble (len v) 1)) fuel
end core12
def Pos (v : List W) (w : W) (i : ℕ) : Prop := ∃ pre t, v = pre ++ w :: t ∧ t.length = i
structure KP (R : ℕ → ℕ) (m T k' t : ℕ) (S : Finset ℕ) (v : List W) (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool) : Prop where
  g1 : ∀ {d : Bool} {a b : ℕ} {S1 : Finset ℕ} {k0 : ℕ}, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → a ∈ S1 → b ∉ S1 →
    ∀ w i, Pos v w i → w.s = a → κ (2 ^ i) = false
  g2 : ∀ {d : Bool} {a b : ℕ} {S1 : Finset ℕ} {k0 : ℕ}, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → a ∈ S1 → b ∈ S1 →
    ∀ wa i wb j, Pos v wa i → wa.s = a → Pos v wb j → wb.s = b → κ2 (2 ^ i) (2 ^ j) = false
lemma len_eq (v : List W) : len v = v.length := by
  induction v with
  | nil => rfl
  | cons w v ih => change Nat.succ (len v) = _; rw [ih]; rfl
lemma geo_succ (w n : ℕ) : geo w (n + 1) = 2 ^ w * geo w n + 1 := by
  change (geo w n <<< w) + 1 = _; rw [Nat.shiftLeft_eq, Nat.mul_comm]
lemma mul_geo {w x : ℕ} (hx : x < 2 ^ w) : ∀ n i, i < w * n → (x * geo w n).testBit i = x.testBit (i % w) := by
  intro n
  induction n with
  | zero => intro i hi; simp at hi
  | succ n ih =>
    intro i hi
    rw [geo_succ, show x * (2 ^ w * geo w n + 1) = 2 ^ w * (x * geo w n) + x by ring, Nat.testBit_two_pow_mul_add _ hx]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · rw [ih (i - w) (by rw [Nat.mul_succ] at hi; omega), ← Nat.mod_eq_sub_mod (by omega)]
lemma mul_geo_lt {w x : ℕ} (hx : x < 2 ^ w) : ∀ n, x * geo w n < 2 ^ (w * n) := by
  intro n
  induction n with
  | zero => change x * 0 < _; simp
  | succ n ih =>
    rw [geo_succ, show x * (2 ^ w * geo w n + 1) = 2 ^ w * (x * geo w n) + x by ring, Nat.mul_succ, pow_add, Nat.mul_comm (2 ^ (w * n))]
    have : 2 ^ w * (x * geo w n) + 2 ^ w ≤ 2 ^ w * 2 ^ (w * n) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    omega
lemma dbl_bit {m x i : ℕ} (hx : x < 2 ^ m) (hi : i < 2 * m) : (dbl m x).testBit i = x.testBit (i % m) := by
  change (x ||| x <<< m).testBit i = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h : i < m
  · rw [Nat.mod_eq_of_lt h]; simp [show ¬ m ≤ i by omega]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show i - m < m by omega),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [show m ≤ i by omega]
lemma dbl_lt {m x : ℕ} (hx : x < 2 ^ m) : dbl m x < 2 ^ (2 * m) := by
  change x ||| x <<< m < _
  refine Nat.or_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))) ?_
  rw [Nat.shiftLeft_eq, two_mul, pow_add]
  exact Nat.mul_lt_mul_of_pos_right hx (by positivity)
lemma rep3 {m x i : ℕ} (hx : x < 2 ^ m) (hi : i < 8 * m) : (dbl (4 * m) (dbl (2 * m) (dbl m x))).testBit i = x.testBit (i % m) := by
  have h1 := dbl_lt hx
  have h2 := dbl_lt h1
  rw [dbl_bit (by rw [show 4 * m = 2 * (2 * m) by ring]; exact h2) (by omega), dbl_bit h1 (by have := Nat.mod_lt i (show 4 * m > 0 by omega); omega),
    dbl_bit hx (by have := Nat.mod_lt (i % (4 * m)) (show 2 * m > 0 by omega); omega), Nat.mod_mod_of_dvd _ ⟨2, by ring⟩,
    Nat.mod_mod_of_dvd _ ⟨4, by ring⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt1 : AA < 2 ^ NN := by decide +kernel
lemma Pos.mem {v : List W} {w : W} {i : ℕ} (h : Pos v w i) : w ∈ v := by
  obtain ⟨p, t, rfl, _⟩ := h; simp
lemma Pos.uniq {v : List W} {w w' : W} {i : ℕ} (h : Pos v w i) (h' : Pos v w' i) : w = w' := by
  obtain ⟨p, t, rfl, e⟩ := h
  obtain ⟨p', t', e', rfl⟩ := h'
  have := List.append_inj_right' (s₁ := p) (s₂ := p') (t₁ := w :: t) (t₂ := w' :: t') e' (by simp [e])
  exact (List.cons.inj this).1
lemma Pos.cons {v : List W} {w x : W} {i : ℕ} (h : Pos v w i) : Pos (x :: v) w i := by
  obtain ⟨p, t, rfl, e⟩ := h; exact ⟨x :: p, t, rfl, e⟩
lemma Pos.lt {v : List W} {w : W} {i : ℕ} (h : Pos v w i) : i < v.length := by
  obtain ⟨p, t, rfl, rfl⟩ := h; simp; omega
lemma sp_lt {l : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) {d : Bool} {s i : ℕ} (h : (sp d l s).testBit i = true) : i < NN := by
  rw [sp_bit, Bool.and_eq_true] at h
  by_contra hc
  have := hl i h.1
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le AA_lt1 (Nat.pow_le_pow_right (by omega) (by omega)))] at this
  simp at this
lemma pkd_bit {l : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) {d : Bool} {v : List W} {i b : ℕ} (hb : b < NN)
    (h : (pkd d l v).testBit (NN * i + b) = true) : ∃ w, Pos v w i ∧ (sp d l w.s).testBit b = true := by
  induction v with
  | nil => simp [pkd] at h
  | cons w t ih =>
    change (sp d l w.s <<< (NN * len t) ||| pkd d l t).testBit (NN * i + b) = true at h
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, len_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · have h3 := sp_lt hl h2
      have : i = t.length := by
        rcases Nat.lt_trichotomy i t.length with q | q | q
        · have : NN * (i + 1) ≤ NN * t.length := Nat.mul_le_mul_left _ q
          rw [Nat.mul_succ] at this; omega
        · exact q
        · have : NN * (t.length + 1) ≤ NN * i := Nat.mul_le_mul_left _ q
          rw [Nat.mul_succ] at this; omega
      subst this
      refine ⟨w, ⟨[], t, rfl, rfl⟩, ?_⟩
      rwa [Nat.add_sub_cancel_left] at h2
    · obtain ⟨x, hx, h⟩ := ih h
      exact ⟨x, hx.cons, h⟩
lemma twice_sub {d : Bool} {l i : ℕ} {v : List W} (h : (twice d l v).testBit i = true) : l.testBit i = true := by
  induction v with
  | nil => simp [twice] at h
  | cons w v ih =>
    change ((sp d l w.s &&& cov d l v) ||| twice d l v).testBit i = true at h
    rw [Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h
    · have := h.1; rw [sp_bit, Bool.and_eq_true] at this; exact this.1
    · exact ih h
lemma wst_sub {d : Bool} {l i : ℕ} {v : List W} (h : (wst d l v).testBit i = true) : l.testBit i = true := by
  change (l ^^^ twice d l v).testBit i = true at h
  rw [Nat.testBit_xor] at h
  cases h1 : l.testBit i with
  | true => rfl
  | false =>
    rw [h1, Bool.false_xor] at h
    rw [twice_sub h] at h1; simp at h1
lemma lt_of_bits {x n : ℕ} (h : ∀ i, x.testBit i = true → i < n) : x < 2 ^ n := by
  by_contra hc
  obtain ⟨i, hi, hb⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow (Nat.le_of_not_lt hc)
  have := h i hb; omega
lemma bit_lt {x n i : ℕ} (hx : x < 2 ^ n) (h : x.testBit i = true) : i < n := by
  by_contra hc
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))] at h
  simp at h
lemma laneM {a b c k : ℕ} (hb : b < a) : (a * k + b) % (a * c) = a * (k % c) + b := by
  rw [Nat.mod_mul, Nat.mul_add_mod, Nat.mod_eq_of_lt hb, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb, Nat.add_zero, Nat.add_comm]
section lanes
variable {l o : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) (ho : ∀ i, o.testBit i = true → l.testBit i = true)
include hl
lemma o_lt (ho : ∀ i, o.testBit i = true → l.testBit i = true) : o < 2 ^ NN :=
  lt_of_bits fun i hi => bit_lt AA_lt1 (hl i (ho i hi))
include ho
lemma U_bit {d : Bool} {v : List W} {i b : ℕ} (hb : b < NN) (h : (Nat.land (pkd d l v) (Nat.mul o RL)).testBit (NN * i + b) = true) :
    i < 12 ∧ ∃ w, Pos v w i ∧ (Nat.land (sp d l w.s) o).testBit b = true := by
  simp only [nl, Nat.testBit_and, Bool.and_eq_true] at h
  have h2 : (o * geo NN 12).testBit (NN * i + b) = true := h.2
  have hlt := bit_lt (mul_geo_lt (o_lt hl ho) 12) h2
  have hi : i < 12 := by
    by_contra hc
    have : NN * 12 ≤ NN * i := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [mul_geo (o_lt hl ho) _ _ hlt, Nat.mul_add_mod, Nat.mod_eq_of_lt hb] at h2
  obtain ⟨w, hw, hs⟩ := pkd_bit hl hb h.1
  exact ⟨hi, w, hw, by simp only [nl, Nat.testBit_and, hs, h2, Bool.and_self]⟩
end lanes
def segOkR (s : ℕ × ℕ) : Bool := decide (s.2 < NN) && (List.range 12).all (fun i =>
  decide (AAR % 2 ^ (NN * i + s.2) + 2 ^ (NN * i + s.1 + 1) = 2 ^ (NN * i + s.2) + AAR % 2 ^ (NN * i + s.1)) && !AAR.testBit (NN * i + s.2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segXR_ok : segsX.all segOkR = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segYR_ok : segsY.all segOkR = true := by decide +kernel
def laneOk (p : ℕ) : Bool := decide (MRR % 2 ^ (NN * p + NN) + 2 ^ (NN * p + 63 + 1) = 2 ^ (NN * p + NN) + MRR % 2 ^ (NN * p + 63)) &&
  !MRR.testBit (NN * p + NN) && !HXR.testBit (NN * p + NN) && !HXR.testBit (NN * p + 63) && !HYR.testBit (NN * p + NN) && !HYR.testBit (NN * p + 63)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma lanes_ok : (List.range 84).all laneOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HXY_lt : HX < 2 ^ NN ∧ HY < 2 ^ NN ∧ 100 < NN := by decide +kernel
lemma flagR {l o : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) (ho : ∀ i, o.testBit i = true → l.testBit i = true)
    {L : List (ℕ × ℕ)} (hL : L.all segOk = true) (hLR : L.all segOkR = true) {d : Bool} {v : List W} {i : ℕ} {s : ℕ × ℕ} (hs : s ∈ L) (hi : i < 12)
    (h : (Nat.mod (Nat.add (Nat.land (pkd d l v) (Nat.mul o RL)) AAR) PLN).testBit (NN * i + s.2) = true) :
    ∃ w b, Pos v w i ∧ s.1 < b ∧ b < s.2 ∧ (Nat.land (sp d l w.s) o).testBit b = true := by
  have h1 := List.all_eq_true.1 hL s hs
  have h2 := List.all_eq_true.1 hLR s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
  simp only [segOkR, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h2
  obtain ⟨hN, h2⟩ := h2
  obtain ⟨e1, e2⟩ := h2 i hi
  have hh : (Nat.land (pkd d l v) (Nat.mul o RL) + AAR).testBit (NN * i + s.2) = true := by
    have h : ((Nat.land (pkd d l v) (Nat.mul o RL) + AAR) % 2 ^ LNN).testBit (NN * i + s.2) = true := h
    rw [Nat.testBit_mod_two_pow, Bool.and_eq_true] at h; exact h.2
  have nb : ∀ c, c < NN → AA.testBit c = false → (Nat.land (pkd d l v) (Nat.mul o RL)).testBit (NN * i + c) = false := by
    intro c hc hA
    by_contra hb
    obtain ⟨_, w, _, hw⟩ := U_bit hl ho hc (by simpa using hb)
    simp only [nl, Nat.testBit_and, Bool.and_eq_true] at hw
    rw [hl c (ho c hw.2)] at hA; simp at hA
  obtain ⟨t, t1, t2, t3⟩ := carry (u := Nat.land (pkd d l v) (Nat.mul o RL)) (A := AAR) (p := NN * i + s.1) (h := NN * i + s.2) (by omega) e1 e2
    (nb _ hN h1.2) (nb _ (by omega) h1.1.2) hh
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show NN * i ≤ t by omega)
  obtain ⟨_, w, hw, hb⟩ := U_bit hl ho (show b < NN by omega) t3
  exact ⟨w, b, hw, by omega, by omega, hb⟩
lemma one_bit {i : ℕ} (h : (1 : ℕ).testBit i = true) : i = 0 := by
  by_contra hc
  rw [Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hc)] at h; simp at h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma GMD_eq : GMD = 2 ^ (NN - 1) - 1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma PLN_eq : PLN = 2 ^ (NN * 12) := by decide +kernel
lemma laneC {X G p : ℕ} (hp : p < 84) (hX : X.testBit (NN * p + NN) = false) (hX2 : X.testBit (NN * p + 63) = false)
    (h : (Nat.add (Nat.land G X) MRR).testBit (NN * p + NN) = true) : ∃ b < NN, (Nat.land G X).testBit (NN * p + b) = true := by
  have hk := List.all_eq_true.1 lanes_ok p (List.mem_range.2 hp)
  simp only [laneOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hk
  obtain ⟨t, t1, t2, t3⟩ := carry (u := Nat.land G X) (A := MRR) (p := NN * p + 63) (h := NN * p + NN) (by have := HXY_lt.2.2; omega) hk.1.1.1.1.1 hk.1.1.1.1.2
    (by simp only [nl, Nat.testBit_and, hX, Bool.and_false]) (by simp only [nl, Nat.testBit_and, hX2, Bool.and_false]) h
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show NN * p ≤ t by omega)
  exact ⟨b, by omega, t3⟩
lemma gather {w Q E : ℕ} (hQ : Q + 1 < w) (hb : ∀ i, E.testBit i = true → i % w = 0 ∧ i < w * Q) {q : ℕ}
    (h : (E % (2 ^ (w - 1) - 1)).testBit q = true) : E.testBit (w * q) = true := by
  have key : ∀ n, ∃ s, s < 2 ^ n ∧ (E % 2 ^ (w * n)) ≡ s [MOD 2 ^ (w - 1) - 1] ∧ ∀ q, s.testBit q = true → E.testBit (w * q) = true := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp, by rw [Nat.mul_zero, pow_zero, Nat.mod_one], by simp⟩
    | succ n ih =>
      obtain ⟨s, h1, h2, h3⟩ := ih
      have hd : E / 2 ^ (w * n) % 2 ^ w = (E.testBit (w * n)).toNat := by
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
        by_cases hi : i = 0
        · subst hi; cases hE : E.testBit (w * n) <;> simp [hE, show 0 < w by omega]
        · have h0 : E.testBit (w * n + i) = true → ¬ i < w := by
            intro he hlt
            have := (hb _ he).1
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt] at this; exact hi this
          have h1 : ((E.testBit (w * n)).toNat).testBit i = false := by
            cases E.testBit (w * n)
            · simp
            · by_contra hc
              exact hi (one_bit (by simpa using hc))
          rw [h1]
          by_cases hlt : i < w
          · have : E.testBit (w * n + i) = false := by
              by_contra hc; exact h0 (by simpa using hc) hlt
            rw [Nat.add_comm] at this
            simp [this]
          · simp [hlt]
      have he : E % 2 ^ (w * (n + 1)) = 2 ^ (w * n) * (E.testBit (w * n)).toNat + E % 2 ^ (w * n) := by
        rw [Nat.mul_succ, pow_add, Nat.mod_mul, hd, Nat.add_comm]
      refine ⟨2 ^ n * (E.testBit (w * n)).toNat + s, ?_, ?_, ?_⟩
      · rw [pow_succ]
        cases E.testBit (w * n)
        · simp; omega
        · simp; omega
      · rw [he]
        refine Nat.ModEq.add (Nat.ModEq.mul_right _ ?_) h2
        have e1 : 2 ^ (w - 1) ≡ 1 [MOD 2 ^ (w - 1) - 1] := by
          have : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
          exact ((Nat.modEq_iff_dvd' this).2 dvd_rfl).symm
        calc 2 ^ (w * n) = 2 ^ ((w - 1) * n + n) := by congr 1; rw [← Nat.succ_mul]; congr 1; omega
          _ = (2 ^ (w - 1)) ^ n * 2 ^ n := by rw [pow_add, pow_mul]
          _ ≡ 1 ^ n * 2 ^ n [MOD _] := Nat.ModEq.mul_right _ (e1.pow n)
          _ = 2 ^ n := by simp
      · intro q hq
        rw [Nat.testBit_two_pow_mul_add _ h1] at hq
        split_ifs at hq with hlt
        · exact h3 q hq
        · by_cases h0 : q - n = 0
          · have : q = n := by omega
            subst this
            rw [h0] at hq
            cases hE : E.testBit (w * q) with
            | true => rfl
            | false => rw [hE] at hq; simp at hq
          · exfalso
            cases hE : E.testBit (w * n) with
            | true =>
              rw [hE] at hq
              exact h0 (one_bit hq)
            | false => rw [hE] at hq; simp at hq
  obtain ⟨s, h1, h2, h3⟩ := key Q
  have hE : E < 2 ^ (w * Q) := lt_of_bits fun i hi => (hb i hi).2
  rw [Nat.mod_eq_of_lt hE] at h2
  have hs : s < 2 ^ (w - 1) - 1 := by
    have e2 : 2 ^ Q * 2 ≤ 2 ^ (w - 1) := by rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
    rcases Nat.eq_zero_or_pos Q with rfl | hQ0
    · have : 2 ^ 1 ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simp at h1; omega
    · have : 2 ^ 1 ≤ 2 ^ Q := Nat.pow_le_pow_right (by omega) hQ0
      omega
  have : E % (2 ^ (w - 1) - 1) = s := by
    have := h2
    unfold Nat.ModEq at this
    rw [this, Nat.mod_eq_of_lt hs]
  rw [this] at h
  exact h3 q h
def Hq (d : Bool) (l o a b : ℕ) : Prop :=
  (∃ s ∈ segsX, ∃ i1 i2, s.1 < i1 ∧ i1 < s.2 ∧ s.1 < i2 ∧ i2 < s.2 ∧ (Nat.land (sp d l a) o).testBit i1 = true ∧ (Nat.land (sp d l b) o).testBit i2 = true) ∧
  (∃ s ∈ segsY, ∃ i1 i2, s.1 < i1 ∧ i1 < s.2 ∧ s.1 < i2 ∧ i2 < s.2 ∧ (Nat.land (sp d l a) o).testBit i1 = true ∧ (Nat.land (sp d l b) o).testBit i2 = true)
lemma edg_spec {l o : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) (ho : ∀ i, o.testBit i = true → l.testBit i = true)
    {d : Bool} {v : List W} {p : ℕ} (h : (edg d l o v).testBit p = true) :
    12 ≤ p ∧ p < 84 ∧ ∃ a b, Pos v a (p % 13) ∧ Pos v b (p % 12) ∧ Hq d l o a.s b.s := by
  obtain ⟨hHX, hHY, hN⟩ := HXY_lt
  set F := Nat.mod (Nat.add (Nat.land (pkd d l v) (Nat.mul o RL)) AAR) PLN with hF
  have hF1 : F < 2 ^ (NN * 12) := by
    have e0 : PLN = 2 ^ (NN * 12) := PLN_eq
    rw [hF, ← e0]; exact Nat.mod_lt _ (by rw [e0]; exact Nat.two_pow_pos _)
  set G := Nat.land (dbl LN4 (dbl LN2 (dbl LNN F))) (dbl LM4 (dbl LM2 (dbl LM1 F))) with hG
  set E := Nat.land (Nat.land (Nat.add (Nat.land G HXR) MRR) (Nat.add (Nat.land G HYR) MRR)) TOPR with hE
  have hbits : ∀ i, E.testBit i = true → i % NN = 0 ∧ i < NN * 85 ∧ 13 * NN ≤ i := by
    intro i hi
    have hT : (geo NN 72 <<< (13 * NN)).testBit i = true := by
      rw [hE, nl, Nat.testBit_and, Bool.and_eq_true] at hi; exact hi.2
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hT
    obtain ⟨t1, t2⟩ := hT
    have t2 : (1 * geo NN 72).testBit (i - 13 * NN) = true := by rwa [one_mul]
    have h1 : 1 < 2 ^ NN := Nat.one_lt_two_pow (by omega)
    have hlt := bit_lt (mul_geo_lt h1 72) t2
    rw [mul_geo h1 _ _ hlt] at t2
    have t2 := one_bit t2
    refine ⟨?_, by omega, t1⟩
    have : (i - 13 * NN + NN * 13) % NN = 0 := by rw [Nat.add_mul_mod_self_left]; exact t2
    rwa [Nat.mul_comm NN, Nat.sub_add_cancel t1] at this
  have h : ((E % GMD) >>> 1).testBit p = true := h
  rw [Nat.testBit_shiftRight, GMD_eq] at h
  have hp := gather (Q := 85) (by omega) (fun i hi => ⟨(hbits i hi).1, (hbits i hi).2.1⟩) h
  obtain ⟨_, b2, b3⟩ := hbits _ hp
  have p1 : 12 ≤ p := by
    by_contra hc
    have : NN * (1 + p) ≤ NN * 12 := Nat.mul_le_mul_left _ (by omega)
    omega
  have p2 : p < 84 := by
    by_contra hc
    have : NN * 85 ≤ NN * (1 + p) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hp : E.testBit (NN * p + NN) = true := by rwa [show NN * p + NN = NN * (1 + p) by ring]
  rw [hE, nl, nl, Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true] at hp
  obtain ⟨⟨hx, hy⟩, _⟩ := hp
  have hk := List.all_eq_true.1 lanes_ok p (List.mem_range.2 p2)
  simp only [laneOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hk
  obtain ⟨x, hx1, hx2⟩ := laneC p2 hk.1.1.1.2 hk.1.1.2 hx
  obtain ⟨y, hy1, hy2⟩ := laneC p2 hk.1.2 hk.2 hy
  have gb : ∀ b, b < NN → G.testBit (NN * p + b) = true → F.testBit (NN * (p % 12) + b) = true ∧ F.testBit (NN * (p % 13) + b) = true := by
    intro b hb hgb
    rw [hG, nl, Nat.testBit_and, Bool.and_eq_true] at hgb
    obtain ⟨g1, g2⟩ := hgb
    have hlt : NN * p + b < NN * 84 := by
      have : NN * (p + 1) ≤ NN * 84 := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this; omega
    have g1 : (dbl (4 * (NN * 12)) (dbl (2 * (NN * 12)) (dbl (NN * 12) F))).testBit (NN * p + b) = true := by
      have e1 : LN4 = 4 * (NN * 12) := by change 48 * NN = _; ring
      have e2 : LN2 = 2 * (NN * 12) := by change 24 * NN = _; ring
      have e3 : LNN = NN * 12 := by change 12 * NN = _; ring
      rwa [e1, e2, e3] at g1
    have g2 : (dbl (4 * (NN * 13)) (dbl (2 * (NN * 13)) (dbl (NN * 13) F))).testBit (NN * p + b) = true := by
      have e1 : LM4 = 4 * (NN * 13) := by change 52 * NN = _; ring
      have e2 : LM2 = 2 * (NN * 13) := by change 26 * NN = _; ring
      have e3 : LM1 = NN * 13 := by change 13 * NN = _; ring
      rwa [e1, e2, e3] at g2
    rw [rep3 hF1 (by omega), laneM hb] at g1
    rw [rep3 (lt_of_lt_of_le hF1 (Nat.pow_le_pow_right (by omega) (by omega))) (by omega), laneM hb] at g2
    exact ⟨g1, g2⟩
  have big : ∀ {H : ℕ}, H < 2 ^ NN → ∀ {b : ℕ}, b < NN → (Nat.mul H (geo NN 84)).testBit (NN * p + b) = true → H.testBit b = true := by
    intro H hH b hb hh
    have hh : (H * geo NN 84).testBit (NN * p + b) = true := hh
    rw [mul_geo hH _ _ (bit_lt (mul_geo_lt hH 84) hh), Nat.mul_add_mod, Nat.mod_eq_of_lt hb] at hh
    exact hh
  have fin : ∀ {L : List (ℕ × ℕ)} {H : ℕ}, L.all segOk = true → L.all segOkR = true → H < 2 ^ NN → H = bitsOf L → ∀ {x : ℕ}, x < NN →
      (Nat.land G (Nat.mul H (geo NN 84))).testBit (NN * p + x) = true → ∃ a b, Pos v a (p % 13) ∧ Pos v b (p % 12) ∧
      ∃ s ∈ L, ∃ i1 i2, s.1 < i1 ∧ i1 < s.2 ∧ s.1 < i2 ∧ i2 < s.2 ∧ (Nat.land (sp d l a.s) o).testBit i1 = true ∧ (Nat.land (sp d l b.s) o).testBit i2 = true := by
    intro L H q1 q2 q3 q4 x q5 q6
    rw [nl, Nat.testBit_and, Bool.and_eq_true] at q6
    obtain ⟨g1, g2⟩ := gb x q5 q6.1
    have hb := big q3 q5 q6.2
    rw [q4] at hb
    obtain ⟨s, hs, rfl⟩ := bitsOf_bit hb
    obtain ⟨b, i2, w1, w2, w3, w4⟩ := flagR hl ho q1 q2 hs (Nat.mod_lt _ (by omega)) g1
    have hp13 : p % 13 < 12 := by
      by_contra hc
      have e : p % 13 = 12 := by omega
      rw [e] at g2
      have := bit_lt hF1 g2
      omega
    obtain ⟨a, i1, v1, v2, v3, v4⟩ := flagR hl ho q1 q2 hs hp13 g2
    exact ⟨a, b, v1, w1, s, hs, i1, i2, v2, v3, w2, w3, v4, w4⟩
  obtain ⟨a, b, r1, r2, r3⟩ := fin segX_ok segXR_ok hHX HX_eq hx1 hx2
  obtain ⟨a', b', r4, r5, r6⟩ := fin segY_ok segYR_ok hHY HY_eq hy1 hy2
  obtain rfl := r4.uniq r1
  obtain rfl := r5.uniq r2
  exact ⟨p1, p2, a', b', r1, r2, r3, r6⟩
lemma f12_bit {w x : ℕ} (h : (f12 w).testBit x = true) : x < 12 ∧ ∃ k < 8, w.testBit (12 * k + x) = true := by
  have h : ((((w ||| w >>> 48) ||| (w ||| w >>> 48) >>> 24) ||| ((w ||| w >>> 48) ||| (w ||| w >>> 48) >>> 24) >>> 12) &&& (2 ^ 12 - 1)).testBit x = true := h
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h := h.1
  simp only [Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true] at h
  rcases h with ((h | h) | (h | h)) | ((h | h) | (h | h))
  · exact ⟨0, by omega, by simpa using h⟩
  · exact ⟨4, by omega, by convert h using 2⟩
  · exact ⟨2, by omega, by convert h using 2⟩
  · exact ⟨6, by omega, by convert h using 2; omega⟩
  · exact ⟨1, by omega, by convert h using 2⟩
  · exact ⟨5, by omega, by convert h using 2; omega⟩
  · exact ⟨3, by omega, by convert h using 2; omega⟩
  · exact ⟨7, by omega, by convert h using 2; omega⟩
lemma f13_bit {w x : ℕ} (h : (f13 w).testBit x = true) : x < 12 ∧ ∃ k < 8, w.testBit (13 * k + x) = true := by
  have h : ((((w ||| w >>> 52) ||| (w ||| w >>> 52) >>> 26) ||| ((w ||| w >>> 52) ||| (w ||| w >>> 52) >>> 26) >>> 13) &&& (2 ^ 12 - 1)).testBit x = true := h
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h := h.1
  simp only [Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true] at h
  rcases h with ((h | h) | (h | h)) | ((h | h) | (h | h))
  · exact ⟨0, by omega, by simpa using h⟩
  · exact ⟨4, by omega, by convert h using 2⟩
  · exact ⟨2, by omega, by convert h using 2⟩
  · exact ⟨6, by omega, by convert h using 2; omega⟩
  · exact ⟨1, by omega, by convert h using 2⟩
  · exact ⟨5, by omega, by convert h using 2; omega⟩
  · exact ⟨3, by omega, by convert h using 2; omega⟩
  · exact ⟨7, by omega, by convert h using 2; omega⟩
lemma geo13 : geo 13 7 = 302268352895954163081217 := by decide +kernel
lemma geo12 : geo 12 7 = 4723519685917965029377 := by decide +kernel
def Adj (e x y : ℕ) : Prop := ∃ p, e.testBit p = true ∧ ((p % 13 = x ∧ p % 12 = y) ∨ (p % 13 = y ∧ p % 12 = x))
lemma Adj.symm {e x y : ℕ} (h : Adj e x y) : Adj e y x := by
  obtain ⟨p, hp, h⟩ := h; exact ⟨p, hp, h.symm⟩
def Eb (e : ℕ) : Prop := ∀ p, e.testBit p = true → 12 ≤ p ∧ p < 84
lemma Adj.ne {e x y : ℕ} (he : Eb e) (h : Adj e x y) : x ≠ y := by
  obtain ⟨p, hp, h⟩ := h
  obtain ⟨h1, h2⟩ := he p hp
  have key : ∀ p < 84, 12 ≤ p → p % 13 ≠ p % 12 := by decide
  have := key p h2 h1
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact this
  · exact this.symm
lemma nbr_adj {e S x : ℕ} (he : Eb e) (hS : S < 2 ^ 12) (h : (nbr e S).testBit x = true) : x < 12 ∧ ∃ y, S.testBit y = true ∧ Adj e x y := by
  have h : (f12 (e &&& S * 302268352895954163081217) ||| f13 (e &&& S * 4723519685917965029377)).testBit x = true := h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨h1, k, hk, h2⟩ := f12_bit h
    rw [Nat.testBit_and, Bool.and_eq_true, ← geo13] at h2
    have hp := he _ h2.1
    rw [mul_geo (lt_of_lt_of_le hS (by norm_num)) 7 _ (by omega)] at h2
    exact ⟨h1, _, h2.2, _, h2.1, Or.inr ⟨rfl, by omega⟩⟩
  · obtain ⟨h1, k, hk, h2⟩ := f13_bit h
    rw [Nat.testBit_and, Bool.and_eq_true, ← geo12] at h2
    have hp := he _ h2.1
    rw [mul_geo hS 7 _ (by omega)] at h2
    exact ⟨h1, _, h2.2, _, h2.1, Or.inl ⟨by omega, rfl⟩⟩
lemma nbr_lt {e S : ℕ} : nbr e S < 2 ^ 12 := by
  refine lt_of_bits fun i hi => ?_
  have h : (f12 (e &&& S * 302268352895954163081217) ||| f13 (e &&& S * 4723519685917965029377)).testBit i = true := hi
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with h | h
  · exact (f12_bit h).1
  · exact (f13_bit h).1
def Pc (e : ℕ) (c : ℕ → Bool) : Prop := ∀ x y, Adj e x y → c x ≠ c y
lemma bfs_ok {e : ℕ} (he : Eb e) {c : ℕ → Bool} (hc : Pc e c) {κ : Bool} {k : ℕ → Bool} (hk : ∀ C, k C = false) :
    ∀ fuel A B, A < 2 ^ 12 → B < 2 ^ 12 → (∀ y, A.testBit y = true → c y = κ) → (∀ y, B.testBit y = true → c y = !κ) → bfs e fuel A B k = false := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro A B hA hB cA cB
    change (st (Nat.lor A (nbr e B)) fun a => st (Nat.lor B (nbr e a)) fun b => Bool.rec (motive := fun _ => Bool) true
      (Bool.rec (motive := fun _ => Bool) (bfs e fuel a b k) (k (Nat.lor a b)) (Nat.beq (Nat.lor A B) (Nat.lor a b))) (Nat.beq (Nat.land a b) 0)) = false
    rw [st_eq, st_eq, bR, bR]
    set a := Nat.lor A (nbr e B) with ha
    set b := Nat.lor B (nbr e a) with hb
    have ha1 : a < 2 ^ 12 := by rw [ha]; exact Nat.or_lt_two_pow hA nbr_lt
    have hb1 : b < 2 ^ 12 := by rw [hb]; exact Nat.or_lt_two_pow hB nbr_lt
    have ca : ∀ y, a.testBit y = true → c y = κ := by
      intro y hy
      rw [ha, no, Nat.testBit_or, Bool.or_eq_true] at hy
      rcases hy with hy | hy
      · exact cA y hy
      · obtain ⟨_, z, hz, hadj⟩ := nbr_adj he hB hy
        have := hc _ _ hadj; rw [cB z hz] at this
        cases h : c y <;> cases κ <;> simp_all
    have cb : ∀ y, b.testBit y = true → c y = !κ := by
      intro y hy
      rw [hb, no, Nat.testBit_or, Bool.or_eq_true] at hy
      rcases hy with hy | hy
      · exact cB y hy
      · obtain ⟨_, z, hz, hadj⟩ := nbr_adj he ha1 hy
        have := hc _ _ hadj; rw [ca z hz] at this
        cases h : c y <;> cases κ <;> simp_all
    have h0 : Nat.beq (Nat.land a b) 0 = true := by
      rw [Nat.beq_eq]
      by_contra hne
      obtain ⟨y, hy⟩ := Nat.exists_testBit_of_ne_zero hne
      rw [nl, Nat.testBit_and, Bool.and_eq_true] at hy
      have e1 := ca y hy.1; have e2 := cb y hy.2
      rw [e1] at e2; cases κ <;> simp at e2
    rw [h0, cond_true, ih a b ha1 hb1 ca cb, hk]
    cases Nat.beq (Nat.lor A B) (Nat.lor a b) <;> rfl
lemma pow_bit {j y : ℕ} (h : (2 ^ j).testBit y = true) : y = j := by
  rw [Nat.testBit_two_pow, decide_eq_true_eq] at h; exact h.symm
lemma nonb_ok {e : ℕ} (he : Eb e) {c : ℕ → Bool} (hc : Pc e c) : ∀ fuel r, nonb e fuel r = false := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro r
    change (Bool.rec (motive := fun _ => Bool) (bfs e 12 (Nat.gcd r 2048) 0 (fun c => nonb e fuel (Nat.sub r (Nat.land r c)))) false (Nat.beq r 0)) = false
    rw [bR]
    have : bfs e 12 (Nat.gcd r 2048) 0 (fun c => nonb e fuel (Nat.sub r (Nat.land r c))) = false := by
      obtain ⟨j, hj, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.gcd r 2048 ∣ 2 ^ 11 from Nat.gcd_dvd_right r 2048)
      rw [hg]
      refine bfs_ok he hc (κ := c j) (fun C => ih _) 12 _ _ (Nat.pow_lt_pow_right (by omega) (by omega)) (by norm_num) ?_ (by simp)
      intro y hy; rw [pow_bit hy]
    rw [this]; cases Nat.beq r 0 <;> rfl
lemma nonbip_ok {e : ℕ} (he : Eb e) {c : ℕ → Bool} (hc : Pc e c) : nonbip e = false := nonb_ok he hc _ _
lemma del_bit {e j p : ℕ} (he : Eb e) (h : (del e (2 ^ j)).testBit p = true) : e.testBit p = true ∧ p % 13 ≠ j ∧ p % 12 ≠ j := by
  have h : ((e ||| tch (2 ^ j)) ^^^ tch (2 ^ j)).testBit p = true := h
  rw [Nat.testBit_xor, Nat.testBit_or] at h
  have hT : (tch (2 ^ j)).testBit p = false := by
    cases hb : (tch (2 ^ j)).testBit p with
    | false => rfl
    | true => rw [hb] at h; simp at h
  rw [hT] at h
  have hep : e.testBit p = true := by simpa using h
  have hp := he p hep
  have hT : (2 ^ j * 302268352895954163081217 ||| 2 ^ j * 4723519685917965029377).testBit p = false := hT
  rw [Nat.testBit_or, Bool.or_eq_false_iff] at hT
  refine ⟨hep, fun hj => ?_, fun hj => ?_⟩
  · have h1 := hT.1
    have hlt : j < 13 := by omega
    rw [← geo13, mul_geo (Nat.pow_lt_pow_right (by omega) hlt) 7 _ (by omega), hj, Nat.testBit_two_pow_self] at h1
    simp at h1
  · have h1 := hT.2
    have hlt : j < 12 := by omega
    rw [← geo12, mul_geo (Nat.pow_lt_pow_right (by omega) hlt) 7 _ (by omega), hj, Nat.testBit_two_pow_self] at h1
    simp at h1
lemma del_Eb {e j : ℕ} (he : Eb e) : Eb (del e (2 ^ j)) := fun p hp => he p (del_bit he hp).1
lemma del_adj {e j x y : ℕ} (he : Eb e) (h : Adj (del e (2 ^ j)) x y) : Adj e x y ∧ x ≠ j ∧ y ≠ j := by
  obtain ⟨p, hp, h⟩ := h
  obtain ⟨h1, h2, h3⟩ := del_bit he hp
  refine ⟨⟨p, h1, h⟩, ?_⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨h2, h3⟩
  · exact ⟨h3, h2⟩
lemma ne0_adj {e : ℕ} (h : ne0 e = true) : ∃ x y, Adj e x y := by
  unfold ne0 at h
  rw [bR] at h
  cases h0 : Nat.beq e 0 with
  | true => rw [h0] at h; simp at h
  | false =>
    have hne : e ≠ 0 := fun e0 => by rw [e0] at h0; simp at h0
    obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hne
    exact ⟨_, _, p, hp, Or.inl ⟨rfl, rfl⟩⟩
lemma gcd_bit {M : ℕ} (h0 : M ≠ 0) (h1 : M < 2 ^ 12) : ∃ k, k < 12 ∧ Nat.gcd M 4096 = 2 ^ k ∧ M.testBit k = true := by
  obtain ⟨k, hk, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.gcd M 4096 ∣ 2 ^ 12 from Nat.gcd_dvd_right M 4096)
  have hd : 2 ^ k ∣ M := hg ▸ Nat.gcd_dvd_left M 4096
  have hk12 : k < 12 := by
    by_contra hc
    have : 2 ^ 12 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
    omega
  refine ⟨k, hk12, hg, ?_⟩
  by_contra hb
  have hb : M.testBit k = false := by simpa using hb
  have h2 : 2 ^ (k + 1) ∣ M := by
    obtain ⟨q, rfl⟩ := hd
    have hq : (2 ^ k * q + 0).testBit k = q.testBit 0 := by
      rw [Nat.testBit_two_pow_mul_add _ (by positivity)]; simp
    rw [Nat.add_zero] at hq
    rw [hq, Nat.testBit_zero] at hb
    have : q % 2 = 0 := by simp at hb; omega
    obtain ⟨r, rfl⟩ := Nat.dvd_of_mod_eq_zero this
    exact ⟨r, by rw [pow_succ]; ring⟩
  have h3 : 2 ^ (k + 1) ∣ Nat.gcd M 4096 := Nat.dvd_gcd h2 (by
    change 2 ^ (k + 1) ∣ 2 ^ 12
    exact pow_dvd_pow 2 (by omega))
  rw [hg] at h3
  have := Nat.le_of_dvd (by positivity) h3
  rw [pow_succ] at this
  have : 0 < 2 ^ k := by positivity
  omega
lemma bRn (c : Bool) (e t : ℕ) : (Bool.rec (motive := fun _ => ℕ) e t c : ℕ) = bif c then t else e := by cases c <;> rfl
lemma tri_ok {e : ℕ} (he : Eb e) : ∀ fuel r, tri e fuel r = 0 ∨ ∃ x y z, Adj e x y ∧ Adj e x z ∧ Adj e y z ∧ tri e fuel r = 2 ^ x ||| 2 ^ y ||| 2 ^ z := by
  intro fuel
  induction fuel with
  | zero => intro r; exact Or.inl rfl
  | succ fuel ih =>
    intro r
    have e0 : tri e (fuel + 1) r = bif Nat.beq r 0 then 0 else tri1 e (Nat.gcd r 2048) (tri e fuel (Nat.sub r (Nat.gcd r 2048))) := by
      change Bool.rec (motive := fun _ => Nat) (tri1 e (Nat.gcd r 2048) (tri e fuel (Nat.sub r (Nat.gcd r 2048)))) 0 (Nat.beq r 0) = _
      rw [bRn]
    rw [e0]
    cases hr : Nat.beq r 0 with
    | true => exact Or.inl rfl
    | false =>
      rw [cond_false]
      obtain ⟨x, hx, hgx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.gcd r 2048 ∣ 2 ^ 11 from Nat.gcd_dvd_right r 2048)
      have hrest := ih (Nat.sub r (Nat.gcd r 2048))
      generalize tri e fuel (Nat.sub r (Nat.gcd r 2048)) = rest at hrest ⊢
      rw [hgx]
      have hi : 2 ^ x < 2 ^ 12 := Nat.pow_lt_pow_right (by omega) (by omega)
      simp only [tri1, tri2, tri3, tri4, tri5, bRn]
      cases hM : Nat.beq (Nat.land (nbr e (nbr e (2 ^ x))) (nbr e (2 ^ x))) 0 with
      | true => rw [cond_true]; exact hrest
      | false =>
        rw [cond_false]
        have hM0 : nbr e (nbr e (2 ^ x)) &&& nbr e (2 ^ x) ≠ 0 := fun h => by rw [nl, h] at hM; simp at hM
        obtain ⟨y, hy, hgy, hby⟩ := gcd_bit hM0 (lt_of_le_of_lt Nat.and_le_left nbr_lt)
        rw [Nat.testBit_and, Bool.and_eq_true] at hby
        obtain ⟨_, x', hx', axy⟩ := nbr_adj he hi hby.2
        obtain rfl := pow_bit hx'
        have hgy' : Nat.gcd (Nat.land (nbr e (nbr e (2 ^ x'))) (nbr e (2 ^ x'))) 4096 = 2 ^ y := hgy
        rw [hgy']
        cases hL : Nat.beq (Nat.land (nbr e (2 ^ y)) (nbr e (2 ^ x'))) 0 with
        | true => rw [cond_true]; exact hrest
        | false =>
          rw [cond_false]
          have hz0 : nbr e (2 ^ y) &&& nbr e (2 ^ x') ≠ 0 := fun h => by rw [nl, h] at hL; simp at hL
          obtain ⟨z, hz, hgz, hbz⟩ := gcd_bit hz0 (lt_of_le_of_lt Nat.and_le_left nbr_lt)
          rw [Nat.testBit_and, Bool.and_eq_true] at hbz
          obtain ⟨_, y', hy', azy⟩ := nbr_adj he (Nat.pow_lt_pow_right (by omega) hy) hbz.1
          obtain rfl := pow_bit hy'
          obtain ⟨_, x'', hx'', azx⟩ := nbr_adj he hi hbz.2
          obtain rfl := pow_bit hx''
          have hgz' : Nat.gcd (Nat.land (nbr e (2 ^ y')) (nbr e (2 ^ x''))) 4096 = 2 ^ z := hgz
          exact Or.inr ⟨x'', y', z, axy.symm, azx.symm, azy.symm, by rw [hgz']; rfl⟩
lemma pos_cons {x w : W} {t : List W} {i : ℕ} (h : Pos (x :: t) w i) : (w = x ∧ i = t.length) ∨ Pos t w i := by
  obtain ⟨pre, t', e, rfl⟩ := h
  cases pre with
  | nil => simp only [List.nil_append, List.cons.injEq] at e; exact Or.inl ⟨e.1.symm, by rw [e.2]⟩
  | cons y pre => simp only [List.cons_append, List.cons.injEq] at e; exact Or.inr ⟨pre, t', e.2, rfl⟩
lemma pos_inj {v : List W} (hv : (v.map W.s).Nodup) {a b : W} {i j : ℕ} (ha : Pos v a i) (hb : Pos v b j) (e : a.s = b.s) : i = j := by
  induction v with
  | nil => obtain ⟨p, t, h, _⟩ := ha; simp at h
  | cons x t ih =>
    rw [List.map_cons, List.nodup_cons] at hv
    rcases pos_cons ha with ⟨rfl, rfl⟩ | ha' <;> rcases pos_cons hb with ⟨rfl, rfl⟩ | hb'
    · rfl
    · exact absurd (List.mem_map.2 ⟨b, hb'.mem, e.symm⟩) hv.1
    · exact absurd (List.mem_map.2 ⟨a, ha'.mem, e⟩) hv.1
    · exact ih hv.2 ha' hb'
lemma pos_ex {v : List W} {w : W} (h : w ∈ v) : ∃ i, Pos v w i := by
  obtain ⟨p, t, rfl⟩ := List.append_of_mem h
  exact ⟨_, p, t, rfl, rfl⟩
lemma Eb_edg {l o : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) (ho : ∀ i, o.testBit i = true → l.testBit i = true)
    {d : Bool} {v : List W} : Eb (edg d l o v) := fun p hp => by
  obtain ⟨h1, h2, _⟩ := edg_spec hl ho hp; exact ⟨h1, h2⟩
lemma he' (t : ℕ) : pos' t = true ∨ t = 0 := by
  rcases Nat.eq_zero_or_pos t with h | h
  · exact Or.inr h
  · exact Or.inl (by simp [pos', h])
section keep
variable {m T : ℕ}
lemma keep_col {d : Bool} {a b k0 t : ℕ} {S S1 : Finset ℕ} (hb : Bi R d a b S S1) (hl : Live R m T k0 t S1) (hm : Min R m T (k0 + 1) t S) (ha : a ∈ S1) (hbn : b ∉ S1) :
    ∃ (x : ℕ) (g : ℕ → ℕ), S.card + t + x = k0 + 1 ∧ (∀ p ∈ S, p ≠ a → g p ≤ x) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ a → q ≠ a → p ≠ q → Ht NN m T (pos' t) S p q → g p ≠ g q := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := id hb
  have hfS : op d a b ∉ insert a (insert b U) := fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
  have hf : op d a b ∉ U := fun h => hfS (by simp [h])
  have haU : a ∈ U := by
    rcases Finset.mem_insert.1 ha with h | h
    · exact absurd (show op d a b ∈ insert a (insert b U) by rw [← h]; simp) hfS
    · exact h
  have hbU : b ∉ U := fun h => hbn (by simp [h])
  have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [haU])
  obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he' t)
  rw [Finset.card_insert_of_notMem hf] at h1
  refine ⟨x, fun p => f (if p = a ∨ p = b then op d a b else p), ?_, fun p hp _ => h2 _ (phi_mem hp), ?_⟩
  · rw [eS, Finset.card_insert_of_notMem hbU]; exact h1
  · intro p hp q hq hpa hqa hpq hh
    have hh' := ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun _ => hbU) (fun e => absurd e hqa) (fun _ => hbU) hh
    refine h3 _ (phi_mem hp) _ (phi_mem hq) ?_ hh'
    simp only [hpa, hqa, false_or]
    have h1' : p = b ∨ p ∈ U := by simp at hp; tauto
    have h2' : q = b ∨ q ∈ U := by simp at hq; tauto
    split_ifs with r s s
    · exact absurd (r.trans s.symm) hpq
    · intro e; exact hf (e ▸ h2'.resolve_left s)
    · intro e; exact hf (e ▸ h1'.resolve_left r)
    · exact hpq
lemma keep_col2 {d : Bool} {a b k0 t : ℕ} {S S1 : Finset ℕ} (hb : Bi R d a b S S1) (hl : Live R m T k0 t S1) (hm : Min R m T (k0 + 1) t S) (ha : a ∈ S1) (hbn : b ∈ S1) :
    ∃ (x : ℕ) (g : ℕ → ℕ), S.card + t + x + 1 = k0 + 1 ∧ (∀ p ∈ S, p ≠ a → p ≠ b → g p ≤ x) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ a → p ≠ b → q ≠ a → q ≠ b → p ≠ q → Ht NN m T (pos' t) S p q → g p ≠ g q := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := id hb
  have hfS : op d a b ∉ insert a (insert b U) := fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
  have hf : op d a b ∉ U := fun h => hfS (by simp [h])
  have haU : a ∈ U := by
    rcases Finset.mem_insert.1 ha with h | h
    · exact absurd (show op d a b ∈ insert a (insert b U) by rw [← h]; simp) hfS
    · exact h
  have hbU : b ∈ U := by
    rcases Finset.mem_insert.1 hbn with h | h
    · exact absurd (show op d a b ∈ insert a (insert b U) by rw [← h]; simp) hfS
    · exact h
  have eS : insert a (insert b U) = U := by
    rw [Finset.insert_eq_of_mem (by simp [haU]), Finset.insert_eq_of_mem hbU]
  obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he' t)
  rw [Finset.card_insert_of_notMem hf] at h1
  refine ⟨x, f, by rw [eS]; omega, ?_, ?_⟩
  · intro p hp hpa hpb
    have := h2 _ (phi_mem (g := op d a b) hp)
    simpa [hpa, hpb] using this
  · intro p hp q hq hpa hpb hqa hqb hpq hh
    have hh' := ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun e => absurd e hpb) (fun e => absurd e hqa) (fun e => absurd e hqb) hh
    have m1 := phi_mem (g := op d a b) hp
    have m2 := phi_mem (g := op d a b) hq
    simp only [hpa, hpb, hqa, hqb, or_self, if_false] at hh' m1 m2
    exact h3 _ m1 _ m2 hpq hh'
end keep
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma Hq_ht {v : List W} {S : Finset ℕ} {d : Bool} (hr : Rep v S) (hgd : ∀ w ∈ v, Good l w.s) {a b : W} (ha : a ∈ v) (hb : b ∈ v)
    (h : Hq false l (wst d l v) a.s b.s) : Ht NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, i1, i2, a1, a2, b1, b2, a3, b3⟩, ⟨s', hs2, j1, j2, c1, c2, d1, d2, c3, d3⟩⟩ := h
  have uq : ∀ {w : W} {i : ℕ}, w ∈ v → (Nat.land (sp false l w.s) (wst d l v)).testBit i = true →
      l.testBit i = true ∧ Uq NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨l1, u1, p1⟩ := uq ha a3
  obtain ⟨l2, u2, p2⟩ := uq hb b3
  obtain ⟨l3, u3, p3⟩ := uq ha c3
  obtain ⟨l4, u4, p4⟩ := uq hb d3
  refine ⟨i1, i2, j1, j2, (X.lg _ l1).1, (X.lg _ l2).1, (X.lg _ l3).1, (X.lg _ l4).1, ?_, ?_, u1, u2, u3, u4, by rw [p1, p3], by rw [p2, p4]⟩
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.mem.1 hw
    exact (hgd w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.mem.1 hw
    exact (hgd w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
lemma Hq_rect {v : List W} {S : Finset ℕ} {t k k' : ℕ} (hr : Rep v S) (hgd : ∀ w ∈ v, Good l w.s) (hm : Min R m T k' t S) (hk : k' ≤ k)
    (hn : v.length + t = k + 1) {a b : W} (ha : a ∈ v) (hb : b ∈ v) (hab : a.s ≠ b.s) (h : Hq (pos' t) l (wst (pos' t) l v) a.s b.s) : False := by
  obtain ⟨⟨s, hs1, i1, i2, a1, a2, b1, b2, a3, b3⟩, ⟨s', hs2, j1, j2, c1, c2, d1, d2, c3, d3⟩⟩ := h
  have hs := hm.size
  have hcard := hr.card
  have hpos : 0 < S.card := hm.1.pos
  have htight : S.card + t = k' + 1 := by omega
  obtain ⟨l1, u1⟩ := uq_of hr ha a3
  obtain ⟨l2, u2⟩ := uq_of hr hb b3
  obtain ⟨l3, u3⟩ := uq_of hr ha c3
  obtain ⟨l4, u4⟩ := uq_of hr hb d3
  have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
    intro w hw; obtain ⟨w', hw', rfl⟩ := hr.mem.1 hw
    exact (hgd w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
  have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
    intro w hw; obtain ⟨w', hw', rfl⟩ := hr.mem.1 hw
    exact (hgd w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
  have ma := hr.mem.2 ⟨a, ha, rfl⟩
  have mb := hr.mem.2 ⟨b, hb, rfl⟩
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · have hd' : pos' 0 = false := by simp [pos']
    rw [hd'] at u1 u2 u3 u4
    exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
      ma mb hab g1 g2 u1 u2 u3 u4
  · have hd' : pos' t = true := by simp [pos', htp]
    rw [hd'] at u1 u2 u3 u4
    exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
      ma mb hab g1 g2 u1 u2 u3 u4
lemma adj_ht {v : List W} {S : Finset ℕ} {d : Bool} (hr : Rep v S) (hgd : ∀ w ∈ v, Good l w.s) {x y : ℕ} (h : Adj (edg false l (wst d l v) v) x y) :
    ∃ a b, Pos v a x ∧ Pos v b y ∧ a.s ≠ b.s ∧ Ht NN m T d S a.s b.s := by
  have hl : ∀ i, l.testBit i = true → AA.testBit i = true := fun i hi => (X.lg i hi).2
  have hadj := h.ne (Eb_edg hl (fun i hi => wst_sub hi))
  obtain ⟨p, hp, hxy⟩ := h
  obtain ⟨_, _, a, b, pa, pb, hq⟩ := edg_spec hl (fun i hi => wst_sub hi) hp
  have hh := Hq_ht X hr hgd pa.mem pb.mem hq
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨a, b, pa, pb, fun e => hadj (pos_inj hr.1 pa pb e), hh⟩
  · exact ⟨b, a, pb, pa, fun e => hadj (pos_inj hr.1 pb pa e), hh.symm⟩
omit X in
open Classical in
lemma pc_of {v : List W} {A : ℕ → ℕ → Prop} {Q : W → Prop} (f : ℕ → ℕ) (h1 : ∀ w ∈ v, Q w → f w.s ≤ 1)
    (h2 : ∀ x y, A x y → ∃ a b, Pos v a x ∧ Pos v b y ∧ Q a ∧ Q b ∧ f a.s ≠ f b.s) :
    ∀ x y, A x y → decide (∃ w, Pos v w x ∧ f w.s = 1) ≠ decide (∃ w, Pos v w y ∧ f w.s = 1) := by
  intro x y hxy
  obtain ⟨a, b, pa, pb, qa, qb, hf⟩ := h2 x y hxy
  have val : ∀ {w i}, Pos v w i → ((∃ w, Pos v w i ∧ f w.s = 1) ↔ f w.s = 1) := by
    intro w i hw
    constructor
    · rintro ⟨w', hw', h⟩; rwa [hw.uniq hw']
    · intro h; exact ⟨w, hw, h⟩
  have e1 := h1 a pa.mem qa; have e2 := h1 b pb.mem qb
  simp only [val pa, val pb]
  intro hc
  have hc' : (f a.s = 1) ↔ (f b.s = 1) := by simpa using hc
  omega
end sound
section kp
variable {m T k k' t : ℕ} {v : List W} {S : Finset ℕ}
lemma tst1_kp {h : ℕ} (hEb : Eb h) (hr : Rep v S) (hm : Min R m T k' t S) (hk : k' ≤ k) (hn : v.length + t = k)
    (hadj : ∀ x y, Adj h x y → ∃ a b, Pos v a x ∧ Pos v b y ∧ a.s ≠ b.s ∧ Ht NN m T (pos' t) S a.s b.s) :
    ∃ (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool), (∀ F, tst1 h F = F κ κ2) ∧ KP R m T k' t S v κ κ2 := by
  classical
  have hcard := hr.card
  have mem : ∀ {w i}, Pos v w i → w.s ∈ S := fun hw => hr.mem.2 ⟨_, hw.mem, rfl⟩
  have pne : ∀ {a b i j}, Pos v a i → Pos v b j → i ≠ j → a.s ≠ b.s := fun ha hb hij e => hij (pos_inj hr.1 ha hb e)
  have hb : nonbip h = false := by
    obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := NN) (e := pos' t) hm.1 hm.2 (he' t)
    refine nonbip_ok hEb (c := fun i => decide (∃ w, Pos v w i ∧ f w.s = 1)) (pc_of (v := v) (Q := fun _ => True) f (fun w hw _ => ?_) fun x y hxy => ?_)
    · have := q2 w.s (hr.mem.2 ⟨w, hw, rfl⟩); omega
    · obtain ⟨a, b, pa, pb, hne, hht⟩ := hadj x y hxy
      exact ⟨a, b, pa, pb, trivial, trivial, q3 _ (mem pa) _ (mem pb) hne hht⟩
  refine ⟨fun i => ne0 (del h i), kT2, fun F => ?_, ?_, ?_⟩
  · unfold tst1; rw [hb]
  · rintro d a b S1 k0 rfl hbi hlv ha hbn w i hw rfl
    by_contra hc
    obtain ⟨x, y, hxy⟩ := ne0_adj (by simpa using hc)
    obtain ⟨hxy, hx, hy⟩ := del_adj hEb hxy
    obtain ⟨a', b', pa, pb, hne, hht⟩ := hadj x y hxy
    obtain ⟨x0, g, g1, g2, g3⟩ := keep_col hbi hlv hm ha hbn
    have e1 := g2 _ (mem pa) (pne pa hw hx)
    have e2 := g2 _ (mem pb) (pne pb hw hy)
    have := g3 _ (mem pa) _ (mem pb) (pne pa hw hx) (pne pb hw hy) hne hht
    omega
  · rintro d a b S1 k0 rfl hbi hlv ha hbn
    obtain ⟨x0, g, g1, _⟩ := keep_col2 hbi hlv hm ha hbn
    omega
lemma tst2_kp {h : ℕ} (hEb : Eb h) (hr : Rep v S) (hm : Min R m T k' t S) (hk : k' ≤ k) (hn : v.length + t + 1 = k)
    (hadj : ∀ x y, Adj h x y → ∃ a b, Pos v a x ∧ Pos v b y ∧ a.s ≠ b.s ∧ Ht NN m T (pos' t) S a.s b.s) :
    ∃ (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool), (∀ F, tst2 h F = F κ κ2) ∧ KP R m T k' t S v κ κ2 := by
  classical
  have hcard := hr.card
  have mem : ∀ {w i}, Pos v w i → w.s ∈ S := fun hw => hr.mem.2 ⟨_, hw.mem, rfl⟩
  have pne : ∀ {a b i j}, Pos v a i → Pos v b j → i ≠ j → a.s ≠ b.s := fun ha hb hij e => hij (pos_inj hr.1 ha hb e)
  have c1 : ∀ {d : Bool} {a b : ℕ} {S1 : Finset ℕ} {k0 : ℕ}, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → a ∈ S1 → b ∉ S1 →
      ∀ w i, Pos v w i → w.s = a → ∃ c : ℕ → Bool, ∀ x y, (Adj h x y ∧ x ≠ i ∧ y ≠ i) → c x ≠ c y := by
    rintro d a b S1 k0 rfl hbi hlv ha hbn w i hw rfl
    obtain ⟨x0, g, g1, g2, g3⟩ := keep_col hbi hlv hm ha hbn
    refine ⟨fun i => decide (∃ w, Pos v w i ∧ g w.s = 1), pc_of (v := v) (Q := fun x => x.s ≠ w.s) g (fun x hx hq => ?_) fun x y hxy => ?_⟩
    · have := g2 x.s (hr.mem.2 ⟨x, hx, rfl⟩) hq; omega
    · obtain ⟨hxy, hx, hy⟩ := hxy
      obtain ⟨a', b', pa, pb, hne, hht⟩ := hadj x y hxy
      exact ⟨a', b', pa, pb, pne pa hw hx, pne pb hw hy, g3 _ (mem pa) _ (mem pb) (pne pa hw hx) (pne pb hw hy) hne hht⟩
  have c2 : ∀ {d : Bool} {a b : ℕ} {S1 : Finset ℕ} {k0 : ℕ}, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → a ∈ S1 → b ∈ S1 →
      ∀ wa i wb j, Pos v wa i → wa.s = a → Pos v wb j → wb.s = b → ∀ x y, Adj h x y → x ≠ i → x ≠ j → y ≠ i → y ≠ j → False := by
    rintro d a b S1 k0 rfl hbi hlv ha hbn wa i wb j hwa rfl hwb rfl x y hxy xi xj yi yj
    obtain ⟨x0, g, g1, g2, g3⟩ := keep_col2 hbi hlv hm ha hbn
    obtain ⟨a', b', pa, pb, hne, hht⟩ := hadj x y hxy
    have e1 := g2 _ (mem pa) (pne pa hwa xi) (pne pa hwb xj)
    have e2 := g2 _ (mem pb) (pne pb hwa yi) (pne pb hwb yj)
    have := g3 _ (mem pa) _ (mem pb) (pne pa hwa xi) (pne pa hwb xj) (pne pb hwa yi) (pne pb hwb yj) hne hht
    omega
  have k1ok : ∀ {i}, (∃ c : ℕ → Bool, ∀ x y, (Adj h x y ∧ x ≠ i ∧ y ≠ i) → c x ≠ c y) → nonbip (del h (2 ^ i)) = false :=
    fun ⟨c, hc⟩ => nonbip_ok (del_Eb hEb) (c := c) fun x y hxy => hc x y (del_adj hEb hxy)
  have k2ok : ∀ {i j}, (∀ x y, Adj h x y → x ≠ i → x ≠ j → y ≠ i → y ≠ j → False) → ne0 (del (del h (2 ^ i)) (2 ^ j)) = false := by
    intro i j hn
    by_contra hc
    obtain ⟨x, y, hxy⟩ := ne0_adj (by simpa using hc)
    obtain ⟨hxy, xj, yj⟩ := del_adj (del_Eb hEb) hxy
    obtain ⟨hxy, xi, yi⟩ := del_adj hEb hxy
    exact hn x y hxy xi xj yi yj
  rcases tri_ok hEb 12 (f12 h) with hT | ⟨x, y, z, axy, axz, ayz, hT⟩
  · refine ⟨k1 h, k2 h, fun F => ?_, ?_, ?_⟩
    · unfold tst2; rw [st_eq, hT]; rfl
    · intro d a b S1 k0 q1 q2 q3 q4 q5 w i q6 q7
      exact k1ok (c1 q1 q2 q3 q4 q5 w i q6 q7)
    · intro d a b S1 k0 q1 q2 q3 q4 q5 wa i wb j q6 q7 q8 q9
      exact k2ok (c2 q1 q2 q3 q4 q5 wa i wb j q6 q7 q8 q9)
  · generalize hTm : tri h 12 (f12 h) = Tm at hT
    have hT0 : Nat.beq Tm 0 = false := by
      rw [hT]
      refine Bool.eq_false_iff.2 fun hc => ?_
      have hc := Nat.eq_of_beq_eq_true hc
      have : (2 ^ x ||| 2 ^ y ||| 2 ^ z).testBit x = true := by simp [Nat.testBit_or, Nat.testBit_two_pow_self]
      rw [hc] at this; simp at this
    have bT : ∀ i, Tm.testBit i = true ↔ (i = x ∨ i = y ∨ i = z) := by
      intro i
      rw [hT]
      simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro ((q | q) | q)
        · exact Or.inl q.symm
        · exact Or.inr (Or.inl q.symm)
        · exact Or.inr (Or.inr q.symm)
      · rintro (q | q | q)
        · exact Or.inl (Or.inl q.symm)
        · exact Or.inl (Or.inr q.symm)
        · exact Or.inr q.symm
    have nxy := axy.ne hEb; have nxz := axz.ne hEb; have nyz := ayz.ne hEb
    refine ⟨k3 h Tm, k4 h Tm, fun F => ?_, ?_, ?_⟩
    · unfold tst2; rw [st_eq]; beta_reduce; rw [hTm, bR, hT0]; rfl
    · intro d a b S1 k0 q1 q2 q3 q4 q5 w i q6 q7
      obtain ⟨c, hc⟩ := c1 q1 q2 q3 q4 q5 w i q6 q7
      unfold k3
      rw [bR, k1ok ⟨c, hc⟩]
      cases h0 : Nat.beq (Nat.land (2 ^ i) Tm) 0 with
      | false => rfl
      | true =>
        exfalso
        have h0 : 2 ^ i &&& Tm = 0 := Nat.eq_of_beq_eq_true h0
        have hi : ¬ (i = x ∨ i = y ∨ i = z) := fun hi => by
          have : (2 ^ i &&& Tm).testBit i = true := by rw [Nat.testBit_and, Nat.testBit_two_pow_self, (bT i).2 hi]; rfl
          rw [h0] at this; simp at this
        push Not at hi
        have key : ∀ {p q}, Adj h p q → p ≠ i → q ≠ i → c p ≠ c q := fun hpq hp hq => hc _ _ ⟨hpq, hp, hq⟩
        have e1 := key axy hi.1.symm hi.2.1.symm
        have e2 := key axz hi.1.symm hi.2.2.symm
        have e3 := key ayz hi.2.1.symm hi.2.2.symm
        exact (by decide : ∀ a b d : Bool, a ≠ b → a ≠ d → b ≠ d → False) _ _ _ e1 e2 e3
    · intro d a b S1 k0 q1 q2 q3 q4 q5 wa i wb j q6 q7 q8 q9
      have hn := c2 q1 q2 q3 q4 q5 wa i wb j q6 q7 q8 q9
      unfold k4
      rw [bR, k2ok hn]
      cases h0 : Nat.beq (Nat.land (Nat.lor (2 ^ i) (2 ^ j)) Tm) (Nat.lor (2 ^ i) (2 ^ j)) with
      | true => rfl
      | false =>
        exfalso
        have : ¬ ((i = x ∨ i = y ∨ i = z) ∧ (j = x ∨ j = y ∨ j = z)) := by
          rintro ⟨hi, hj⟩
          have : (2 ^ i ||| 2 ^ j) &&& Tm = 2 ^ i ||| 2 ^ j := by
            apply Nat.eq_of_testBit_eq; intro r
            rw [Nat.testBit_and]
            cases hr : (2 ^ i ||| 2 ^ j).testBit r with
            | false => rfl
            | true =>
              rw [Nat.testBit_or, Bool.or_eq_true] at hr
              rcases hr with hr | hr
              · rw [pow_bit hr, (bT i).2 hi]; rfl
              · rw [pow_bit hr, (bT j).2 hj]; rfl
          have h0 : Nat.beq ((2 ^ i ||| 2 ^ j) &&& Tm) (2 ^ i ||| 2 ^ j) = false := h0
          rw [this, Nat.beq_refl] at h0; simp at h0
        have tr := hn x y axy; have tr2 := hn x z axz; have tr3 := hn y z ayz
        by_cases hi : i = x ∨ i = y ∨ i = z
        · have hj : ¬ (j = x ∨ j = y ∨ j = z) := fun hj => this ⟨hi, hj⟩
          push Not at hj
          rcases hi with rfl | rfl | rfl
          · exact tr3 nxy.symm hj.2.1.symm nxz.symm hj.2.2.symm
          · exact tr2 nxy hj.1.symm nyz.symm hj.2.2.symm
          · exact tr nxz hj.1.symm nyz hj.2.1.symm
        · push Not at hi
          by_cases hjx : x = j
          · subst hjx; exact tr3 hi.2.1.symm nxy.symm hi.2.2.symm nxz.symm
          · by_cases hjy : y = j
            · subst hjy; exact tr2 hi.1.symm nxy hi.2.2.symm nyz.symm
            · exact tr hi.1.symm hjx hi.2.1.symm hjy
end kp
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma tsn_eq (d : Bool) (l e : ℕ) (v : List W) (F : (ℕ → Bool) → (ℕ → ℕ → Bool) → Bool) :
    tsn d l e v F = bif Nat.beq v.length e then (bif Nat.beq (edg d l (wst d l v) v) 0 then F kF kF2 else false) else
      (bif Nat.beq (v.length + 1) e then tst1 (edg false l (wst d l v) v) F else
        (bif Nat.beq (v.length + 2) e then tst2 (edg false l (wst d l v) v) F else F kF kF2)) := by
  unfold tsn
  beta_reduce
  rw [bR, bR, bR, bR, st_eq, st_eq, len_eq]
lemma rect0_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) (hn : v.length + t = k + 1) :
    Nat.beq (edg (pos' t) l (wst (pos' t) l v) v) 0 = true := by
  have hl : ∀ i, l.testBit i = true → AA.testBit i = true := fun i hi => (X.lg i hi).2
  have key : ∀ p < 84, 12 ≤ p → p % 13 ≠ p % 12 := by decide
  rw [Nat.beq_eq]
  by_contra hne
  obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hne
  obtain ⟨q1, q2, a, b, pa, pb, hq⟩ := edg_spec hl (fun i hi => wst_sub hi) hp
  exact Hq_rect X hs.rep hs.good hm hk hn pa.mem pb.mem (fun e => key p q2 q1 (pos_inj hs.rep.1 pa pb e)) hq
lemma tsn_gen (d : Bool) (l e : ℕ) (v : List W) (F : (ℕ → Bool) → (ℕ → ℕ → Bool) → Bool) {h0 h : ℕ}
    (e0 : edg d l (wst d l v) v = h0) (e1 : edg false l (wst d l v) v = h) :
    tsn d l e v F = bif Nat.beq v.length e then (bif Nat.beq h0 0 then F kF kF2 else false) else
      (bif Nat.beq (v.length + 1) e then tst1 h F else (bif Nat.beq (v.length + 2) e then tst2 h F else F kF kF2)) := by
  subst e0 e1
  exact tsn_eq X d l e v F
lemma tsn_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    ∃ (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool), (∀ F, tsn (pos' t) l (k + 1 - t) v F = F κ κ2) ∧ KP R m T k' t S v κ κ2 := by
  have hl : ∀ i, l.testBit i = true → AA.testBit i = true := fun i hi => (X.lg i hi).2
  have hsz := hm.size
  have hcard := hs.rep.card
  have kp0 : KP R m T k' t S v kF kF2 := ⟨fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  obtain ⟨h0, e0⟩ : ∃ h0, edg (pos' t) l (wst (pos' t) l v) v = h0 := ⟨_, rfl⟩
  obtain ⟨h, e1⟩ : ∃ h, edg false l (wst (pos' t) l v) v = h := ⟨_, rfl⟩
  have E := fun F => tsn_gen X (pos' t) l (k + 1 - t) v F e0 e1
  have hz : v.length + t = k + 1 → Nat.beq h0 0 = true := fun hn => by
    have := rect0_ok X hs hm hk hn
    rwa [e0] at this
  have hEb : Eb h := by
    have : Eb (edg false l (wst (pos' t) l v) v) := Eb_edg hl (fun i hi => wst_sub hi)
    rwa [e1] at this
  have hadj : ∀ x y, Adj h x y → ∃ a b, Pos v a x ∧ Pos v b y ∧ a.s ≠ b.s ∧ Ht NN m T (pos' t) S a.s b.s := by
    intro x y hxy
    rw [← e1] at hxy
    exact adj_ht X hs.rep hs.good hxy
  clear e0 e1
  generalize tsn (pos' t) l (k + 1 - t) v = G at E ⊢
  cases h1 : Nat.beq v.length (k + 1 - t) with
  | true =>
    have h1' := Nat.eq_of_beq_eq_true h1
    have h0' := hz (by omega)
    exact ⟨kF, kF2, fun F => by rw [E, h1, h0', cond_true, cond_true], kp0⟩
  | false =>
    cases h2 : Nat.beq (v.length + 1) (k + 1 - t) with
    | true =>
      have h2' := Nat.eq_of_beq_eq_true h2
      obtain ⟨κ, κ2, q1, q2⟩ := tst1_kp hEb hs.rep hm hk (by omega) hadj
      exact ⟨κ, κ2, fun F => by rw [E, h1, h2, cond_false, cond_true, q1], q2⟩
    | false =>
      cases h3 : Nat.beq (v.length + 2) (k + 1 - t) with
      | false => exact ⟨kF, kF2, fun F => by rw [E, h1, h2, h3, cond_false, cond_false, cond_false], kp0⟩
      | true =>
        have h3' := Nat.eq_of_beq_eq_true h3
        obtain ⟨κ, κ2, q1, q2⟩ := tst2_kp hEb hs.rep hm hk (by omega) hadj
        exact ⟨κ, κ2, fun F => by rw [E, h1, h2, h3, cond_false, cond_false, cond_true, q1], q2⟩
end sound
lemma Live.rel {R' : ℕ → ℕ} {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Live R' m T k t S := by
  induction h with
  | stop => exact .stop
  | bi hab hal _ ih => exact .bi hab (hR _ _ _ hal) ih
lemma Bi.rel {R' : ℕ → ℕ} {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hR : ∀ d a b, Al R d a b → Al R' d a b) : Bi R' d a b S S' := by
  obtain ⟨hab, U, e1, e2, hal⟩ := h; exact ⟨hab, U, e1, e2, hR _ _ _ hal⟩
lemma scan_false {p : X → Bool} {xs : List X} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma pairsP_false {h : X → X → Bool} {xs : List X} {q : ℕ} {a c : X} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : X → X → Bool} {xs : List X} {q q' : ℕ} {a c : X} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : X → X → Bool} {xs : List X} (hp : pairsN h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
    (hr : a.w.r = 0 ∨ c.w.r = 0) : h a c = false ∨ h c a = false := by
  simp only [pairsN, bR] at hp
  cases h1 : pairs h (fr xs) with
  | true => rw [h1] at hp; simp at hp
  | false =>
    rw [h1, cond_false] at hp
    by_cases hra : a.w.r = 0
    · by_cases hrc : c.w.r = 0
      · exact pairs_any h1 (fr_mem ha hra) (fr_mem hc hrc) hne
      · exact Or.inl (scan_false (scan_false hp a (fr_mem ha hra)) c (fs_mem hc hrc))
    · have hrc := hr.resolve_left hra
      exact Or.inr (scan_false (scan_false hp c (fr_mem hc hrc)) a (fs_mem ha hra))
def Cod (R : ℕ → ℕ) (v : List W) : Prop := ∀ w ∈ v, w.r = 0 ∨ w.r = R w.s
def RR (R : ℕ → ℕ) : Prop := ∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b
def xof (d : Bool) (l o : ℕ) (w : W) (i : ℕ) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o, 2 ^ i⟩
lemma mkX_of {d : Bool} {l o : ℕ} {v : List W} {w : W} {i : ℕ} (h : Pos v w i) : xof d l o w i ∈ mkX d l o v := by
  obtain ⟨pre, t, rfl, rfl⟩ := h
  induction pre with
  | nil =>
    change _ ∈ (⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o, Nat.shiftLeft 1 (len t)⟩ : X) :: mkX d l o t
    rw [len_eq]
    have : Nat.shiftLeft 1 t.length = 2 ^ t.length := by change 1 <<< _ = _; rw [Nat.shiftLeft_eq, one_mul]
    rw [this]; exact List.mem_cons_self
  | cons x pre ih => exact List.mem_cons_of_mem _ ih
lemma mkX_mem {d : Bool} {l o : ℕ} {v : List W} {p : X} (h : p ∈ mkX d l o v) : ∃ w i, Pos v w i ∧ p = xof d l o w i := by
  induction v with
  | nil => simp [mkX] at h
  | cons x v ih =>
    change p ∈ (⟨x, x.s, Nat.shiftRight x.s NN, Nat.land (sp d l x.s) o, Nat.shiftLeft 1 (len v)⟩ : X) :: mkX d l o v at h
    rw [len_eq] at h
    have e : Nat.shiftLeft 1 v.length = 2 ^ v.length := by change 1 <<< _ = _; rw [Nat.shiftLeft_eq, one_mul]
    rw [e] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨x, v.length, ⟨[], v, rfl, rfl⟩, rfl⟩
    · obtain ⟨w, i, ⟨pre, t, e1, e2⟩, e3⟩ := ih h
      exact ⟨w, i, ⟨x :: pre, t, by rw [e1]; rfl, e2⟩, e3⟩
lemma Pos.ex {v : List W} {w : W} (h : w ∈ v) : ∃ i, Pos v w i := by
  obtain ⟨pre, t, rfl⟩ := List.append_of_mem h; exact ⟨t.length, pre, t, rfl, rfl⟩
def modeH (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (n e : ℕ) (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool) : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ (Nat.succ n)) e then f2 h else f1 κ κ2 h) else f0 h
lemma nodeH_eq (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (d : Bool) (l e n : ℕ) (v : List W) (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool)
    (go : (X → X → Bool) → List X → Bool) : nodeH h d l e n v κ κ2 go = go (pair (modeH h n e κ κ2)) (mkX d l (wst d l v) v) := by
  unfold nodeH modeH
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ (Nat.succ n)) e <;> rfl
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o i j : ℕ} {a c : W}
    (hp : pair h (xof d l o a i) (xof d l o c j) = false) (d' : Bool) :
    h a c (2 ^ i) (2 ^ j) (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, xof, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma modeH_false {h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool} {n e : ℕ} {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} {a c : W} {ia ic da dc s x y : ℕ}
    {A C : Prop} (hf : modeH h n e κ κ2 a c ia ic da dc s x y = false) (hA : ¬ A → da = 0) (hC : ¬ C → dc = 0)
    (h0 : ¬ n ≤ e → ¬ A ∧ ¬ C) (k1 : A → ¬ C → κ ia = false) (k2 : C → ¬ A → κ ic = false) (k3 : A → C → κ2 ia ic = false) :
    ∃ oa oc ka kc kb, (¬ A → oa = true) ∧ (¬ C → oc = true) ∧ (A → ¬ C → ka = false) ∧ (C → ¬ A → kc = false) ∧ (A → C → kb = false) ∧
      h a c oa oc ka kc kb s x y = false := by
  unfold modeH at hf
  cases b1 : Nat.ble n e with
  | false =>
    have hne : ¬ n ≤ e := fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1
    obtain ⟨nA, nC⟩ := h0 hne
    rw [b1] at hf
    simp only [Bool.cond_false, f0, hA nA, hC nC] at hf
    exact ⟨true, true, true, true, true, fun _ => rfl, fun _ => rfl, fun h _ => absurd h nA, fun h _ => absurd h nC, fun h _ => absurd h nA, hf⟩
  | true =>
    rw [b1, Bool.cond_true] at hf
    have bz : ∀ {z : ℕ}, Nat.beq z 0 = false → z ≠ 0 := fun hz e => by rw [e] at hz; simp at hz
    cases b2 : Nat.ble (Nat.succ (Nat.succ n)) e with
    | true =>
      rw [b2, Bool.cond_true] at hf
      refine ⟨Nat.beq da 0, Nat.beq dc 0, false, false, false, fun hn => by rw [hA hn]; rfl, fun hn => by rw [hC hn]; rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, hf⟩
    | false =>
      rw [b2, Bool.cond_false] at hf
      simp only [f1, bR] at hf
      cases z1 : Nat.beq da 0 with
      | true =>
        rw [z1, Bool.cond_true] at hf
        cases z2 : Nat.beq dc 0 with
        | true =>
          rw [z2, Bool.cond_true] at hf
          exact ⟨true, true, κ ia, κ ic, κ2 ia ic, fun _ => rfl, fun _ => rfl, k1, k2, k3, hf⟩
        | false =>
          have hCt : C := by by_contra hn; exact bz z2 (hC hn)
          rw [z2, Bool.cond_false] at hf
          cases z3 : κ ic with
          | false =>
            rw [z3, Bool.cond_false] at hf
            exact ⟨true, false, true, false, κ2 ia ic, fun _ => rfl, fun h => absurd hCt h, fun _ h => absurd hCt h, fun _ _ => rfl, k3, hf⟩
          | true =>
            have hAt : A := by by_contra hn; rw [k2 hCt hn] at z3; simp at z3
            rw [z3, Bool.cond_true, k3 hAt hCt, Bool.cond_false] at hf
            exact ⟨false, false, true, true, false, fun h => absurd hAt h, fun h => absurd hCt h, fun _ h => absurd hCt h, fun _ h => absurd hAt h, fun _ _ => rfl, hf⟩
      | false =>
        have hAt : A := by by_contra hn; exact bz z1 (hA hn)
        rw [z1, Bool.cond_false] at hf
        cases z2 : Nat.beq dc 0 with
        | true =>
          rw [z2, Bool.cond_true] at hf
          cases z3 : κ ia with
          | false =>
            rw [z3, Bool.cond_false] at hf
            exact ⟨false, true, false, true, κ2 ia ic, fun h => absurd hAt h, fun _ => rfl, fun _ _ => rfl, fun _ h => absurd hAt h, k3, hf⟩
          | true =>
            have hCt : C := by by_contra hn; rw [k1 hAt hn] at z3; simp at z3
            rw [z3, Bool.cond_true, k3 hAt hCt, Bool.cond_false] at hf
            exact ⟨false, false, true, true, false, fun h => absurd hAt h, fun h => absurd hCt h, fun _ h => absurd hCt h, fun _ h => absurd hAt h, fun _ _ => rfl, hf⟩
        | false =>
          have hCt : C := by by_contra hn; exact bz z2 (hC hn)
          rw [z2, Bool.cond_false, k3 hAt hCt, Bool.cond_false] at hf
          exact ⟨false, false, true, true, false, fun h => absurd hAt h, fun h => absurd hCt h, fun _ h => absurd hCt h, fun _ h => absurd hAt h, fun _ _ => rfl, hf⟩
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k z v S) (hl : Live R m T k' t S)
    (h : cv (pos' t) l v b = false) : b = false := by
  have hcov : Nat.beq (cov (pos' t) l v) l = true := by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli : l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit, hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
      obtain ⟨w, hw, hs1⟩ := hl.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hs.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hs1]; rfl⟩
  simp only [cv, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
lemma nodeH_bi {f : ℕ → List W → Bool} {h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} {go : (L_meta_9732.X → L_meta_9732.X → Bool) → List L_meta_9732.X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S') (hKP : KP R m T (k' + 1) t S v κ κ2)
    (hh : ∀ (a c : W) (oa oc ka kc kb : Bool) (x1 y1 : ℕ), op d' a.s c.s = op d' x y → h a c oa oc ka kc kb (op d' a.s c.s) x1 y1 = false →
      mid f m g np e (Nat.pred n) z v a c oa oc ka kc kb (op d' a.s c.s) x1 y1 = false)
    (hgo : ∀ h xs, go h xs = false → xs = mkX d l (wst d l v) v → ∀ a c : L_meta_9732.X, a ∈ xs → c ∈ xs → a.w ∈ v → c.w ∈ v → a.s = a.w.s → c.s = c.w.s → a.s = x → c.s = y →
      h a c = false ∨ h c a = false)
    (hp : nodeH h d l e n v κ κ2 go = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r := by
  rw [nodeH_eq] at hp
  have one : ∀ {a c : W} {i j : ℕ}, Pos v a i → Pos v c j → Bi R d' a.s c.s S S' → op d' a.s c.s = op d' x y →
      pair (modeH h n e κ κ2) (xof d l (wst d l v) a i) (xof d l (wst d l v) c j) = false →
      ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r := by
    intro a c i j ha hc hb1 hop hpp
    have hpp := pair_false hpp d'
    have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
        dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
      intro x y hu
      unfold dfc
      generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
      cases d'
      · simp only [Bool.cond_false, nl, nx] at hu ⊢
        apply Nat.eq_of_testBit_eq; intro i
        have := hu i
        rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
      · simp only [Bool.cond_true, nl, nsr] at hu ⊢
        apply Nat.eq_of_testBit_eq; intro i
        have := hu i
        rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
    have fa : a.s ∉ S' → dfc d d' l (wst d l v) a c = 0 := fun h => by
      subst hd; exact filt fun i hi => drop_ok X hs.rep hb1 hl ha.mem h hi
    have fc : c.s ∉ S' → dfc d d' l (wst d l v) c a = 0 := fun h => by
      subst hd; exact filt fun i hi => drop_ok X hs.rep hb1.symm hl hc.mem h hi
    have hfS : op d' a.s c.s ∉ S := fun h => hb1.fresh hl hm.2 (sub_C _ _ (by simpa using h))
    have hcards : (a.s ∈ S' ∨ c.s ∈ S') → v.length ≤ S'.card := by
      intro hor
      rw [← hs.rep.card]
      obtain ⟨hac, U, e1, e2, _⟩ := hb1
      have hf : op d' a.s c.s ∉ U := fun h => hfS (by rw [e1]; simp [h])
      have nga : a.s ≠ op d' a.s c.s := fun h => hfS (by rw [← h, e1]; simp)
      have ngc : c.s ≠ op d' a.s c.s := fun h => hfS (by rw [← h, e1]; simp)
      have hU : a.s ∈ U ∨ c.s ∈ U := by
        rcases hor with h | h
        · left; rw [e2, Finset.mem_insert] at h; exact h.resolve_left nga
        · right; rw [e2, Finset.mem_insert] at h; exact h.resolve_left ngc
      rw [e2, Finset.card_insert_of_notMem hf, e1]
      rcases hU with h | h
      · rw [Finset.insert_eq_of_mem (by simp [h])]; exact Finset.card_insert_le _ _
      · rw [Finset.insert_eq_of_mem h]; exact Finset.card_insert_le _ _
    have hmo := modeH_false (A := a.s ∈ S') (C := c.s ∈ S') hpp fa fc (fun hne => by
        constructor
        · intro h; have := hcards (Or.inl h); omega
        · intro h; have := hcards (Or.inr h); omega)
      (fun hA hC => hKP.g1 rfl hb1 hl hA hC a i ha rfl) (fun hC hA => hKP.g1 rfl hb1.symm hl hC hA c j hc rfl)
      (fun hA hC => hKP.g2 rfl hb1 hl hA hC a i c j ha rfl hc rfl)
    obtain ⟨oa, oc, ka, kc, kb, q1, q2, q3, q4, q5, q6⟩ := hmo
    have hmid := hh a c oa oc ka kc kb (opW d' a c).a (opW d' a c).b hop (by rw [← opW_s]; exact q6)
    obtain ⟨z', r, r1, r2, r3⟩ := gate_sound X hs hm hk hn hSe hb1 hl ha.mem hc.mem q1 q2 q3 q4 q5 (by rw [opW_s]; exact hmid)
    exact ⟨z', r, r1, r2, fun w hw => by rw [← hop]; exact r3 w hw⟩
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  obtain ⟨i, hi⟩ := Pos.ex ha
  obtain ⟨j, hj⟩ := Pos.ex hc
  rcases hgo _ _ hp rfl (xof d l (wst d l v) a i) (xof d l (wst d l v) c j) (mkX_of hi) (mkX_of hj) ha hc rfl rfl rfl rfl with q | q
  · exact one hi hj hb rfl q
  · exact one hj hi hb.symm (op_comm _ _ _) q
lemma mv_false (F : ℕ → ℕ → ℕ → List W → Bool) (l m g np k t z : ℕ) (v : List W) (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool) (h : mv F l m g np k t z v κ κ2 = false) :
    node (F (k - 1) t) (pos' t) l m g np (k - t) v.length z v κ κ2 pairsN = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => cv (pos' s) l v (tsn (pos' s) l (k - s) v (fun κ κ2 =>
      bif node (F (k - 2) s) (pos' s) l m g np (k - 1 - s) v.length z v κ κ2 (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => cv (pos' s) l v (tsn (pos' s) l (k - 1 - s) v (fun κ κ2 =>
        node (F (k - 3) s) (pos' s) l m g np (k - 2 - s) v.length z v κ κ2 (pairsQ q q'))))
        m g (k - 1 - s) v.length z (q + 1) v v)))) m g (k - s) v.length z 0 v v = false := by
  clear X
  simp only [mv, st_eq, len_eq, bR, pos_eq] at h
  have key : ∀ {p q : Bool}, (bif p then true else q) = false → p = false ∧ q = false := fun {p q} h => by cases p <;> simp_all
  obtain ⟨h1, h2⟩ := key h
  refine ⟨h1, ?_⟩
  rintro s rfl
  exact h2
end sound
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} {go : (L_meta_9732.X → L_meta_9732.X → Bool) → List L_meta_9732.X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S') (hKP : KP R m T (k' + 1) t S v κ κ2)
    (hgo : ∀ h xs, go h xs = false → xs = mkX d l (wst d l v) v → ∀ a c : L_meta_9732.X, a ∈ xs → c ∈ xs → a.w ∈ v → c.w ∈ v → a.s = a.w.s → c.s = c.w.s → a.s = x → c.s = y →
      h a c = false ∨ h c a = false)
    (hp : node f d l m g np e n z v κ κ2 go = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r :=
  nodeH_bi X hs hm hk hd hn hSe hb hl hKP (fun _ _ _ _ _ _ _ _ _ _ h => h) hgo hp
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z : ℕ} {v : List W} {S : Finset ℕ} {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} (hs : StOk P T l k z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : mv F l m g np k t z v κ κ2 = false) : ∀ k' ≤ k, Min R m T k' t S → KP R m T k' t S v κ κ2 → False := by
  intro k' hk hm hKP
  obtain ⟨hA, hN⟩ := mv_false X F l m g np k t z v κ κ2 h
  have hcard := hs.rep.card
  have codB : ∀ {v r : List W} {o : ℕ}, Cod R v → (∀ w ∈ r, (w.s = o ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with ⟨_, h⟩ | ⟨w', h1, h2, h3⟩
    · exact Or.inl h
    · rw [← h2, ← h3]; exact hv w' h1
  have sizeB : ∀ {k k' t : ℕ} {S S1 : Finset ℕ} {d : Bool} {a b : ℕ}, Min R m T (k' + 1) t S → k' + 1 ≤ k → Bi R d a b S S1 → Live R m T k' t S1 → S1.card ≤ k - t := by
    intro k k' t S S1 d a b hm hk hb hl
    have hs := (hb.min hl hm.2).size.1; omega
  have sizeU : ∀ {k k' t : ℕ} {S S1 : Finset ℕ} {a : ℕ}, Min R m T (k' + 1) (t + 1) S → k' + 1 ≤ k → Un m a S S1 → Live R m T k' t S1 → S1.card ≤ k - t := by
    intro k k' t S S1 a hm hk hb hl
    have hs := (hb.min hl hm.2).size.1; omega
  rcases first_move k' t S hm (by omega) with
    ⟨k0, d, a, b, S1, rfl, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hm (by omega) rfl rfl (sizeB hm hk hb hl) hb hl hKP (fun h xs hp hxs a c ha hc hav hcv eas ecs hax hcy => by
      refine pairsN_false hp ha hc ?_ ?_
      · rintro rfl
        exact hb.1 (by rw [← hax, ← hcy])
      · by_contra hc'
        push Not at hc'
        obtain ⟨_, U, _, _, hal⟩ := hb
        have h1 : a.w.r = R a.w.s := (hcod _ hav).resolve_left hc'.1
        have h2 : c.w.r = R c.w.s := (hcod _ hcv).resolve_left hc'.2
        rw [← hax, ← hcy, eas, ecs] at hal
        exact hR _ _ _ (by rw [← h1]; exact hc'.1) (by rw [← h2]; exact hc'.2) hal) hA
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN t0 rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl (sizeU hm hk hu hl1) hu hl1 hwa (by omega) hwa h2
    have hm1 := hu.min hl1 hm.2
    have hf1 := cv_ok X hst1 hl1 hf1
    obtain ⟨κ', κ2', hF1, hKP1⟩ := tsn_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (sizeB (k := k + 1) hm1 (by omega) hb hl) hb hl hKP1 (fun h xs hp hxs a c ha hc hav hcv eas ecs hax hcy => by
      refine Or.inl (pairsP_false hp ha hax hc fun e => hb.1 ?_)
      rw [← hcy, e]) hf2
    exact hF _ _ _ _ _ hf hst (codB (codB hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN (t0 + 1) rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl (sizeU hm hk hu hl2) hu hl2 hwa (by omega) hwa h2
    have hm1 := hu.min hl2 hm.2
    have hf1 := cv_ok X hst1 hl2 hf1
    obtain ⟨κ', κ2', hF1, hKP1⟩ := tsn_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2, hmem2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl (sizeU (k := k + 2) hm1 (by omega) hu' hl1) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    have hf3 := cv_ok X hst2 hl1 hf3
    obtain ⟨κ3, κ23, hF3, hKP3⟩ := tsn_sound X hst2 hm2 (by omega)
    have hf3 := (hF3 _).symm.trans hf3
    beta_reduce at hf3
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (sizeB (k := k + 1) hm2 (by omega) hb hl) hb hl hKP3 (fun h xs hp hxs a c ha hc hav hcv eas ecs hax hcy =>
      Or.inl (pairsQ_false hp ha hax hc hcy)) hf3
    exact hF _ _ _ _ _ hf hst (codB (codB (codB hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g np fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (k + 1 - t) v (fun κ κ2 => mv (look l m g np fuel) l m g np k t z v κ κ2)) true (Nat.ble (len v) 1) : Bool) = false at h
    rw [bR, pos_eq, len_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      obtain ⟨κ, κ2, hFy, hKP⟩ := tsn_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hKP
end sound
def rawP : List ℕ := [0x7fffff01fc00001fc07f000007f01fffffe00fc0000000000003fffffc01f81fffffe007f00fe01f00000000001fc07fffff803f0000000ffffff007e07fffff801fc03f807c0000000000000003fffffc03f03fffff803f807f007e03f807e07e03c0000000000000000000000000000007fffff007f007f00fc07f00fc07e0787ffffe01f807e01f807e01f80fc03f01f807e01f807c07c07c0f80f07e01f01f807c07e01f03e03c1f80f81f80f07c0f0f060000000000000800200000000080010000000000400400400000000080102004080100000000004000820000000000401000082041000000000000000084004141001050400000000000000000108085080851088414144221050510884141442200dbb3105006dd9800dbb38002000a222230888c00020005186111184618460000a00005846184461186118461800010142000080161846118611844446111184618461844461111806cecc46184601b3b31806cecc00020000128c230c2230c30c2230c08000410800002511186184618611111118611111118601b733111861861118601b73318601b7330000041421080000024946118446186186184444618618618618444461861806dd8c61861806dd8c004210804104144444444421084210806dd8c421084210806dd8c24924806dd8e4611846118461184611806dd9461861861861806dd949a5fc3f55ff03b45024008040810204081020408048010102040804102040810204024008080410120040404101040240080204202080820120040102100900200404080810440814fe00401fc00205fc07f000817f013fc00800fc010200404020a7f801001f813fc008007f00fe01f00210040405fc04c7e02003f001008298fc04007e04c7b02001fc03f807c004108004201010a623e1003f02623c2003f807f007e03f807e07e03c0400090040842000180201020208114c449a007f007f00fc07f00fc07e0784c449801f807e01f807e01f80fc03f01f807e01f807c07c07c0f80f07e01f01f807c07e01f03e03c1f80f81f80f07c0f0f062004001001001800600200200180030008002000c00c00c0010002008030200c08030008002000c000860008001000c0300008604300011000021000018c0043430010d0c0000440000000840010818d0818d10884343442210d0d10884343442200000010d0000000ffffffc006001a222230888c0006000d186111184618460001a0000d84618446118611846180003034200018036184611861184444611118461846184446111180000004618460000001800000000060000368c230c2230c30c2230c08000c10800006d111861846186111111186111111186000000111861861118600000018600000000000c342108000006db46118446186186184444618618618618444461861800000061861800000000421080c30c344444444421084210800000042108421080000006db6dbffffff461184611846118461180000006186186186180000009a5fc3f55ff03b45,0xffffff000007fffffbf800007f80000000000007fffffbfc0003fbf0000007fffff807f0000000000003fffffbf80007f7f0003fbf0007ef80000000000001fffffe00ff00fe03f000000000000000000000000000000007ffffefc0007efc0007efc000fdf8001fbf0001fbf0007df000fbe007efc001fbf0007efc003ef801fbe001fbe007de00f7000000000000000000000000000000000000000000000000000000000000000000000000000800000009000000040000000000900480000000008400000000048480012120000000000108210000000000000140a0484850281212140a0484850280006d512100036ac0006d5000000400000000004800000200000000050000240000008200000000014024005009000000000104208000000000000050501414050095009505014140001b545009500006d508001b560010888c30000004a8360360283600000211604618600000009000025414141b01414141b0000d55141b01b0141b0000d551b0000d5500002085816044618618501400000000024950506c06c06c06c050506c06c00036946c06c000369400000002082085050505058160581600036a458160581600036a46186180036a4501405014050140501400036a42492492492480036a6f17145503ffbacd70488020810204081020408100910042040810082040810204080488021008202440108082020804880204084041010402440102042012200808081010208810210240104041040804101041020104404802020422044010804108090040408440480201010202041104a9fc010004154fe00bf800027f802104010102154fb00bfc0003fbf00008254c7c0807f008402040810aa63c0bf80007f7f0003fbf0007ef8008401040810953135200ff00fe03f0108003010101010204101020410210954c48afc0007efc0007efc000fdf8001fbf0001fbf0007df000fbe007efc001fbf0007efc003ef801fbe001fbe007de00f704401004004004001000800800400080020008002002002000400080000800020000800200180020000b0002000c0020080000b00580004400018c00004200058580016160000110000108630000004200042140a0585850281616140a0585850280000001617fffffe000000001000c0000280000d8010006000001400500006c004000860000005001406c00501b00080800010c2180000000001405505014140501b501b505014140000000501b500000001bffffff0030888c3000000da836036028360000061160461860000001b00006d414141b01414141b0000000141b01b0141b00000001b00000000000618581604461861850140000000006db50506c06c06c06c050506c06c00000006c06c000000000000006186185050505058160581600000005816058160000000618618000000501405014050140501400000006db6db6db6dbfffffff17145503ffbacd7,0x7fffff01fc07f01fffffe00fc0fe03f80ffffff007e07fffff801fc03f807c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fc07fffffbf0003fffffdf8003fffffbfbfbf00000003fbf7ef000003fffffc01f81fffffefe0000fef8007fffff7f00007f7e0007f7e0007ef007ffffefdfbf00000007efdfbe0000001fbf7efc0000007df7de000007efdf7c0000007efdf7800001fbefbc000007def60000000000000000000000000000000000080020008008008001000201002040081002000800400081002000080020008020420200100444506111a06184581845b006116c01186141186160681861605816058156005b00558016c0156005b0055801e007f16c0f003f81e007f0000000000000000000000000000000000000000001000090000009000149000052400020200001202400005014024090550015400524052405500154007801fc5240521e007f807801fc00800004800001202a800000001248041000005009000140240500901540154001540154001e007f15400092554001e007f0921e007f91186c05ac00506c06c056c00506c06c06c055006db0006db00055006db0007803bc6db0007803bc44581606c06c0550055005ac005ac007803ec5ac005ac007803ec6c06c07803ec56c0056c0056c0056c007803f46c06c06c06c07803f495a0fffaaff0c4ba081100102040810204081020102200408102010408102040810081100201047f088001fc07f01fe110000fc0fe03f80ff0880007e07f8440001fc03f807c0204004880080820810082020820402080091000408400888010082001220008108009100020204040822080208800808201024000810840104020880020420101400040408081045fc0454fc03f00022a7e01f80022a7c03fbfbf00000003fbf7ef0000022a678001f81153350fe0000fef800454c8a7f00007f7e0007f7e0007ef00454c88fdfbf00000007efdfbe0000001fbf7efc0000007df7de000007efdf7c0000007efdf7800001fbefbc000007def60000880010010010004002002001000200180060018018018003000601006040181006001800c00181006000180060018060420600300444506111a06184581845b006116c01186141186160681861605816058156005b00558016c0156005b00558000000016c00000000000000040020000280000a000400100000140000000500030000b000001b00015b000056c00060600001602c0000501406c1b055001540056c056c055001540000000056c056ffffffc00000000180000d800003602a8000000036d804300000501b0001406c0501b0154015400154015400000000154001b6d54000000001b6ffffffd1186c05ac00506c06c056c00506c06c06c055006db0006db00055006db0000000006db00000000044581606c06c0550055005ac005ac000000005ac005ac000000006c06c000000056c0056c0056c0056c000000006c06c06c06c000000095a0fffaaff0c4ba,0xffffff01fe03fffffdfc001fffffeff0000fefc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffdfc001fffffefeff7e0000007fffff7f7f7f00000007f7efdf000007ffffefdfbf7efdfbf00000000000001fbf7efdfbf7df000000000007efdf7dfbf7df000000000001fbefbdfbef70000000000000000000000000000000000000000000000000000000080010000900024000900000000000000000000000000000000000000000000000000000000000000000000000002400000129000001290012900152a9000054aa4000152a9000054aa00380f800001c07800380f000000000000000000010004000024014000090000800020000024000240000090000446b0058116d8006c056c006d4005556c000056db00005556c000001c03c56db0000700f0001c03c0000000000000000000000000000000480000052400001490005240015554000015554000000700f154924001549200700f80000700f0009000000000024900000000550002490005555000000249249555500000001c03c24924801c03e505ac006db000555500005ad6b0000001c06c5ad6b0000001c06c6db00001c06c56d5b0000056d5b0000001c0746db0006db00001c074f4d28aa0cff765ed110240204081020408102040220480810204020810204081020110240402080481201010404100902400810808202080481200408402409001010202041104082081201010410201040410408041081024008108cfe12001fe033f8481fc0019fc240ff0000fefc0010401120101042004900102108020840112004084200290008081010208810420109002021100848010211008500080810101020808102102084b22af81fc001915750feff7e00000064558a7f7f7f00000007f7efdf00000645588fdfbf7efdfbf00000000000001fbf7efdfbf7df000000000007efdf7dfbf7df000000000001fbefbdfbef70000000081200400400400100080080040008004001000400400400180030000b0002c000b00040020004000100004001000401000010008000050000140000050000500000140000006c0000016b0000016b0016b00156ab000055aac000156ab000055aaffffffc000000000000000010008000280000a0003000c00006c0140001b000180006000006c0006c00001b0000446b0058116d8006c056c006d4005556c000056db00005556c000000000056db0000000000000000040000a000002800000000002a80000580000056c000015b00056c00155540000155540000000000155b6c00155b6ffffffc00000000001b00000000006db00000000550006db00055550000006db6db55550000000000006db6dbffffff505ac006db000555500005ad6b000000000005ad6b000000000006db00000000056d5b0000056d5b000000000006db0006db000000000f4d28aa0cff765ed,0x1fffffe03fc0000000000000000000000000000000000ffffff7f0007fffffbfc0003fbf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffff7f0007fffffbfdfdf8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fffff7f7f7f7f7efdf0000000000007ffffefdfbf7efdfbf7efdfbefdfbf7c0000000000000000000000007efdf7dfbf7df7efdf7befbdc0000000000000000000000000000000000000000001000200000000000000000000000000120004800120000000000100004000100040045ac005816b60000000000000000900009000002400000090001402400001b016b5ac0000156ab5b5b00000000156ab5b5b00002601830001300c1826018300000000000000000000000000090000005240000000000000000000000000000000000000000000000000052549000005552555490000000055525554898060e0000002601830098060c00000000000480000000012480000090000129000001415b6db000001555555b6c00000000260303155b6db6c000026030300026030300000000000000000000000005524900000055552492490000005555249248980c0e000000980c0c004a529000000555555550000000000980c0c4a5294a528980c0e000000980c0c56d5b56d5b0000000000980c146db6db000000980c14fb2492a30ff79b9e202090408102040810204080404121020408041020408102041fe209003fc0081048202080820102090102101040410ff10487f0007f88243fc0003fbf0008100110482020820402080820810082002209010210011048201040024120102100120900404080810442004204820208020824020421004108cfc487f000467b243fdfdf800000020802012404042010092020420100a401010202020410102042041090101220102100808600402040410224646aa7f7f7f7f7efdf0000000000004646a8fdfbf7efdfbf7efdfbefdfbf7c0000000000000000000000007efdf7dfbf7df7efdf7befbdc000000000000000000010481001001000400200200300060010004001001001000400080016000580016000100080030000c0003000c0045ac005816b60000500001400001b0001b000006c000001b0001406c00001b016b5ac0000156ab5b5b00000000156ab5b5b0000000000000000000000000004002000280000a000080020001b00000056c0000400010000050000500000140000005000000140000000056d5b000005556d555b000000005556d555bffffff0000000000000000000010000a00000d80000000036d800000b000016b000001415b6db000001555555b6c00000000000000155b6db6c00000000000000000000140000000005500000000000556db00000055556db6db00000055556db6dbffffff000000000000005ad6b0000005555555500000000000000005ad6b5ad6bffffff00000000000056d5b56d5b00000000000000006db6db000000000000fb2492a30ff79b9e,0x3fffffc0000003fc00000000000000000000000000000000000001fffffefe0000000000000000000007fffffbfdfdf800000000000000000000000000000000000001fffffefe00000000000000000000000001fffffeff7f7e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffbfbfbf7f7f7ef80000000000000000000000000000000000000000000000000000000000000000000000007ffffefdfbf7efdfbf7efdfbefdfbf7dfbf7efdfbf7df7df7defbef700000000000000000000000000000000000000000000000000000000010000000000001000000100040015ac0000002000400005adac0000000000000012000000000000000004a4000000000002400002400001b55b5b0000000000001490000000924000000000156ab5b5b55aad6d6c0000000000004a481100025240884a48110000000000001200000000000000000149000000000024000090000056d5b6c0000000000004a400000024900000000005556d555b56db56db0000000012a40440000004a9011012a404400000000000000002a924800000000000000000000000000000000001555554925555554924a901180000000000004a90110004a901100000004a52900000000525490000000000055556db6db6db6db00000000012a40840000012a40840000000000000555555554a5294a5292a408600000000012a40840000012a4084525495254952549525492a40860000000000012a4084fe88615c0ffb5f2b400424810204081020408103fc08480408103fc04081020408020042480410100212404101041fe0424fe0002080820080212081087f81093fdfdf8000001020020212404104080410104102010411fc424fe000020212402080040848204211fc424ff7f7e00000040004212404100011090408420082000221208108000c09010102020411041000220908084001104840842233c93fbfbf7f7f7ef80000000000000104482042000818408040808204400204c02020202040820204082042124464ccfdfbf7efdfbf7efdfbefdfbf7dfbf7efdfbf7df7df7defbef7000000000000000000000000000000000000000000000212400400400300080080080030004003000c0015ac0010006000c00005adac0000400200080016000080020005000005ac000000500006c00006c00001b55b5b00000014000015b0000001b6c000000000156ab5b5b55aad6d6c0000000000000000000000000000000000100080028000360000200080014000015b00000010002c0001b0000056d5b6c0000005000005ac0000006db00000000005556d555b56db56db000000000000000000000000000000000004000a00000a000002ab6d800000002000014000000015400000000001555555b6d555555b6ffffffc00000000000000000000000000014000005ad6b0000000056d5b0000000000055556db6db6db6db00000000000000000000000000005500000000000555555555ad6b5ad6bffffff000000000000000000000000000056d5b56d5b56d5b56d5bffffff000000000000000000fe88615c0ffb5f2b,0x7ffffe01f807e01f807e01f800000007e01f80007e01f807e01fffffef80007fffff7c0007f7c00000000000fef8000ffffff7f7ef0000000000000000001f807fffff7c0007e01fdf0001f807f7c00000000000ffffff7c0003fffffdfdfbc0000000000000000007e00000001fdf000000000003f0000ffffff7f7ef0000000000000000001fdf000000000003fffffdfbf780000000000000000000000000000003fffffdfdfbc0000000000000000007fffff7f7f7f7f7efdf7f7efdf7ef7b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005550005558000aaa000b55800055a800095ac0000015b5000096b6b00000000055a8000b5ac00000b5a800055ad6b0000000005555500000049b55ac00000000000015b6d540000000012496b5ad6b5ac00000000000000000000000000000b4b12a0005a58950b4b12a15560002aaaa8000002b5600015b6d540000000015b5800001256db50000000000000556b6b00000000049256d5b6d5b500000000000000000000000002d584a8000000b5612a02d584a855a6000000adab6900000000000002b5b4c000000001555b6d256db4800000000000000000b5622a0000000000000b5622a000b5622a155b4d3000000000000004812556db6db49200000000000000000000000002d58928000002d58928555ad6b4d34d3000000000000000002d589480000000002d58948000002d5894804812048120481204812d58958492492492492d58958ac3f7d5ff5505c537e000601f807e01f807e01f880000c07e01f88007e01f807e01fe0006f80007f00037c0007f7c20000620000fef8000ff00037f7ef0400018202040000001f8047e0037c0007e01fdf0001f807f7c040006200008fe0037c00023f800dfdfbc0200060808100000007e00800301fdf002001880003f100088fc037f7ef0010018200000408001fdf000401801002223e0dfbf78001018202040404082020400008200222278dfdfbc00020600080010008044448f7f7f7f7f7efdf7f7efdf7ef7b00000e040810204081020408204081040810204081041041042082110204000081000020400020800082000082000420011000035550005558000aaa000b55800055a8000d5ac0000015b50000d6b6b00000000055a8000b5ac00000b5a800055ad6b000000000555550000006db55ac00000000000015b6d54000000001b6d6b5ad6b5ac00000000000000000000000000000000000000000000000000015560002aaaa8000002b5600015b6d540000000015b5800001b56db50000000000000556b6b0000000006db56d5b6d5b5000000000000000000000000000000000000000000000000000055b6000000adab6d80000000000002b5b6c000000001555b6db56db6c000000000000000000000000000000000000000000000000000155b6db000000000000056d5b556db6db6db00000000000000000000000000000000000000000000555ad6b6db6db000000000000000000000000000000000000000000000000000056d5b56d5b56d5b56d5bffffff6db6db6db6dbffffffac3f7d5ff5505c53,0x7ffffefc0007efc0007efc0000000007efc000007efc0007efc000000000007fffff7dfdf000000000000000fefbfbe000000000000000000000000000001fbf000000000007efc0000001fbf000000000000000ffffff7dfef8000000000000000000000000000007effffff7c000000000000003f7fbe000000000000000000000000000001fdf7fffffbf7f78000000000000000000000000000000000000000003fffffdfdfbdfffffefeff7efefbf70000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005555550000000aaaaaa000000055aa56a00000000015b54b6a0000000000000055aaada000000000a5aa96d000000000000000555554955ad00000000000000000001526d5412496b6b400000000000000000000000000000000000000000090244c000481226090244c1554aad000000000002b54ad680000000000000015b5096b680000000000000000000556a6a10956d2da00000000000000000000000000000000000000241113000000090444c0241113055b4aaada40000000000000000000225b6944256db4800000000000000000000000000000090484c000000000000090484c00090484c155b69a10842556db492000000000000000000000000000000000000000002412230000002412230551084269a69a000000001084210842412270108421084241227049249241227000000000000000000002412260000000000002412260f0ff003ff03e327f7e0038fc0007efc0007efc0100007007efc010007efc0007efc400038008007f001c7dfdf000040003840000fefbfbe10001c1000008000e0404080408001fbf04001c008007efc8002001fbf2000080038404008fe01c7dfef8080070008000400381010201000807e88fc1c7c80000400e001003f7fbe00401c1020000200e0402040800201fdf4447ce3f7f78002070010000020e040408080810404000801001022227f1fdfbd1113f8feff7efefbf70000f004040404081040400100080200000f00810204081020408104081020810204081020820820841042204081041020410408108410441000801001008010202001c5555550000000aaaaaa000000055ab56a00000000015b56b6a0000000000000055aaada000000000b5aad6d000000000000000555556d55ad000000000000000000015b6d555b6d6b6b400000000000000000000000000000000000000000000000000000000000000001556aad800000000002b56ad6c0000000000000015b5ad6b6c0000000000000000000556b6b5ad56dadb0000000000000000000000000000000000000000000000000000000000000000055b6aaadb600000000000000000002b5b6d56b56db6c0000000000000000000000000000000000000000000000000000000000000000155b6db5ad6b556db6db000000000000000000000000000000000000000000000000000000000000555ad6b6db6db555555555ad6b5ad6bffffff5ad6b5ad6bffffff6db6dbffffff00000000000000000000000000000000000000000000f0ff003ff03e327f,0x7ffffefdfbf00000007efdfbfffffdf0000000007efdfbf0000000000000007fffff7dfdf7f7dfffffefefde0000000000000000000000000000000000001fbf7fffff7dfdf00000000001fbf7f7dfffffefefde000000000000000000000000000000000000000007effffff7dfdf7fffffbfbf7800000000000000000000000000000000001fdf7fffffbf7f7bfffffdfbf7bfffffbfbfbf7f7f7efbfbf7ef7efbd800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000555555555b556000000000000055ab56ad5ad5ad5ac00000000000000000000055aaadaa5ad696b60000000000000000000000555556d55ad6d255ad255b5b4956d6c000000000000000000000000000000000000000000000000000000000d8c6700006c63380d8c6701556aadaaaaab6aaad80000000000000000000001535ad4b6db549b55495b6d5256db0000000000000000000000000000000000000000000000000000036619c0000000d98670036619c055b6aaadb6a92b6daab6da492ab6d800000000000000000000000000000000000000000000d98c700000000000000d98c70000d98c7015526db5ad6b554926db56d5b004924926db000049249249249200004924936633c04924936633c00000000000000000000000000000003663380000000000366338000000366338000000000000000000003663380000000000003663380a3cfbeaffaa0a3ac7e00c0fdfbf00000007efdfbfc0181f0000000007efdfbf00008000c0010007f00607dfdf7f7dfe00c0fefde0000000200060200001000300800000810001fbf47e0607dfdf00000000001fbf7f7d1fc0c0fefde040060004000100180400000800c02000002020007e88fc607dfdf447e303fbf7800000008060200000040300804080000001fdf4447f03f7f7a223f81fbf7a223f03fbfbf7f7f7efbfbf7ef7efbd800380040000001c00101010000000000700080808081020808082040000000070010204081020408102081020410204081020410400000000000081020820408208102108208820410420421000000000060555555555b556000000000000055ab56ad5ad5ad5ac00000000000000000000055aaadab5ad6d6b60000000000000000000000555556d55ad6db55adb55b5b6d56d6c00000000000000000000000000000000000000000000000000000000000000000000000000000001556aadaaaaab6aaad800000000000000000000015b5ad6b6db56db556d5b6d5b56db0000000000000000000000000000000000000000000000000000000000000000000000000000000055b6aaadb6adab6daab6db6daab6d8000000000000000000000000000000000000000000000000000000000000000000000000000000155b6db5ad6b556db6db56d5b556db6db6db55556db6db6db6db55556db6dbffffff6db6dbffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a3cfbeaffaa0a3ac,0x7ffffefdfbf7efdfbf00000000000000000000007efdfbf7efdfffffefbfdf000000000000000000000000000000000000000000000000000000000000001fbf7fffff7dfdf7efdfdf7f7c000000000000000000000000000000000000000000000000000000000007effffff7dfdf7fffffbfbf7bf7fbeffffff7f7ef7fffffbfdfdfbfbf7dc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000555555555a556aaaaaab55a6ab00000000000000000000000000000000000000552aa9ab52c4d4b6b52ad4d552d4b1094b6a5b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a087800005043c00a087801556aadaaaaaa4aaadaa56a96d5b49541256d256c0000000000000000000000000000000000000000000000000000000000000000000000000000000002841e00000000a1078002841e005536aaa936adaa4d8024936daaa492b126d56b04926d541249b04926c00000124800000124a10f800012492480124a10f80124a10f8000000000000000000000000000000000000000000000000000000000000002843c00000002843c000000000000000000000000000000002843c000000000002843c00000002843c0000000000000000000002843c00000000000002843c00f3303ccff0cdc3f37e0700fdfbf7efdfbf000002000e0000000020007efdfbf7efdfe0700fbfdf200380008002000800700804004001000400380002002001c01008101000201fbf47e3807dfdf7efdfdf7f7c000000010070080000080380008000200e00800001007004020404040007e88ff807dfdf447fc03fbf7bf7fbe88ff807f7ef447fc03fdfdfbfbf7dc80000780010000003c0008000003c000808101010208080810400000003c0008080001e000202020204000007800101010102000010104081040000780020408102040810204102040820408102040820810410820844102041040810410204200000040820840842104220000380555555555b556aaaaaab55b6ab0000000000000000000000000000000000000055aaadab5ad6d6b6b5aad6d55ad6b5ad6b6b5b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001556aadaaaaab6aaadab56ad6d5b6d555b56db56c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000055b6aaadb6adab6daab6db6daab6dab5b6d56b56db6d555b6db56db6d555555b6d555555b6ffffffd55b6db6d55b6ffffffdb6ffffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f3303ccff0cdc3f3,0x7ffffefdfbf7efdfbf7efdfbfffffdf7efdfbfdf0000000000000000000000000000000000000000000000000000000000000000000000000000000000001fbf7fffff7dfdf7efdfdf7f7dfbf7f7dfffffefefdeffffff7dfefbfffffdfdfbdfffffeff7f7efefdf700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000555555555b556aaaaaaa55b4ab552b54ad52d52d52d5a56b4ac4b4b12d2c4b4b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0f800000607c000c0f8001556aa9aaaaab6aaa92b56ad4d526d555b049b5495a5ad624db56d2556c12495b0492554b4b5ad4498936db04812495250004800120492049200048001307e000049204c1f8001307e00000000000000000000000000000000000000000000000000000000000000000000000000000c1f0000000000000000c1f000000c1f0000000000000000000000000000000000000000000000000000000000000000307c00000000307c000000000000000000000000000000000307c000000000000307c00000000307c0000000000000000000000307c00000000000000307c000fcc03f0ff30dfc3c7e3800fdfbf7efdfbf7efdfbfc7001f7efdfbfdf0000000000100380002000401c00010004001003800008008002000801c0040400400e002010002020401fbf47fc007dfdf7efdfdf7f7dfbf7f7d1ff800fefde8ffc007dfefa3ff001fdfbd1ff800ff7f7efefdf7000f000000000078000100000020000f00004000007800010081010100010000780002020003c0001000003c000101020202000010102082040003c0000010001e0000404000408100078000202020204041020200002080007800040810204081020408204081040810204081000020821041000204082081020820408410411081041081000208444201c00555555555b556aaaaaab55b6ab55ab56ad5ad5ad5ad5b56b6ad6b6b5adad6b6b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001556aadaaaaab6aaadab56ad6d5b6d555b56db56d5b5ad6b6db56db556d5b6d5b56db556b6b5ad56dadb6db56d5b6d5b55556d555b56db56db5556d555bffffff56db56ffffffdbffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fcc03f0ff30dfc3c,0x7ffffefdfbf7efdfbf7efdfbfffffdf7efdfbfdf7efdfbf7efdfffffefbfdf7fffff7dfdf7f7dfffffefefdefefbfbeffffff7f7ef7fffffbfdfdfbfbf7dc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005555555553554aaaaaab5536aa55ab56ad5a95a95a95356a6ad626a589a9626a55aaad2b5a96d624b5aad6955a96a5ad624b12555556d55296db5529b512126d448495b49555b6c424a5b6c425284252804021212010084848040212120100ff00000487f80000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f80000000000fe000003f8000000000000000000000000000000000000000000000000000000000000000000000000000000fe00000000000000000fe0000000fe000000000000000000000000000000000000000000000000000000000000000003f80000000003f800000000000000000000000000000000003f800000000000003f80000000003f8000000000000000000000003f80000000000000003f80000ff0fc00ffc0effc07fc000fdfbf7efdfbf7efdfbff8001f7efdfbfdf7efdfbf7efdffc000fbfdf7fe0007dfdf7f7dffc000fefdefefbfbeffe0007f7ef7ff0003fdfdfbfbf7dc00078000001000000100040000004001e0000000800f00000010003c0000101001e0000080400080810000f000000100078000020200004000f00000004007800002010002020400000780000004003c0000002003c000020200040404002020400408203c0000100001e0000080804080020078000040404040008004040810400407800008102040810204081000810200102040810204104104008208040810410204104081002082010208210208441080844e000555555555b556aaaaaab55b6ab55ab56ad5ad5ad5ad5b56b6ad6b6b5adad6b6b55aaadab5ad6d6b6b5aad6d55ad6b5ad6b6b5b555556d55ad6db55adb55b5b6d56d6d5b6d555b6d6b6b5b6d6b5ad6b5ad56ab5b5b55aad6d6d56ab5b5b55aaffffffd6d7fffffeffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff0fc00ffc0effc0]
def TG : ℕ := 0x7ffffefdfbf7efdfbf7efdfbfffffdf7efdfbfdf7efdfbf7efdfffffefbfdf7fffff7dfdf7f7dfffffefefdefefbfbeffffff7f7ef7fffffbfdfdfbfbf7ddfbf7fffff7dfdf7efdfdf7f7dfbf7f7dfffffefefdeffffff7dfefbfffffdfdfbdfffffeff7f7efefdf77effffff7dfdf7fffffbfbf7bf7fbeffffff7f7ef7fffffbfdfdfbfbf7ddfdf7fffffbf7f7bfffffdfbf7bfffffbfbfbf7f7f7efbfbf7ef7efbdbfffffdfdfbdfffffefeff7efefbf77fffff7f7f7f7f7efdf7f7efdf7ef7b7ffffefdfbf7efdfbf7efdfbefdfbf7dfbf7efdfbf7df7df7defbef77efdf7dfbf7df7efdf7befbddfbefbdfbef77def6f76ffff555555555b556aaaaaab55b6ab55ab56ad5ad5ad5ad5b56b6ad6b6b5adad6b6b55aaadab5ad6d6b6b5aad6d55ad6b5ad6b6b5b555556d55ad6db55adb55b5b6d56d6d5b6d555b6d6b6b5b6d6b5ad6b5ad56ab5b5b55aad6d6d56ab5b5b55aaffffffd6d7fffffeffffffd556aadaaaaab6aaadab56ad6d5b6d555b56db56d5b5ad6b6db56db556d5b6d5b56db556b6b5ad56dadb6db56d5b6d5b55556d555b56db56db5556d555bffffff56db56ffffffdbffffff55b6aaadb6adab6daab6db6daab6dab5b6d56b56db6d555b6db56db6d555555b6d555555b6ffffffd55b6db6d55b6ffffffdb6ffffffd55b6db5ad6b556db6db56d5b556db6db6db55556db6db6db6db55556db6dbffffff6db6dbffffff555ad6b6db6db555555555ad6b5ad6bffffff5ad6b5ad6bffffff6db6dbffffff56d5b56d5b56d5b56d5bffffff6db6db6db6dbffffffffffffffffffffff
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def kz (Z : ℕ) : ℕ := (List.range 12).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else
  (bif Nat.testBit Z (i + 12) then Nat.lor x (Nat.xor FULL (Nat.land (rawP.getD i 0) (Nat.lor (Nat.shiftRight (rawP.getD i 0) NN) FPM))) else x)) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
def tw (e : Bool × ℕ × ℕ) : ℕ := op e.1 (rawP.getD e.2.1 0) (rawP.getD e.2.2 0)
def rawL (E : List (Bool × ℕ × ℕ)) : List ℕ := rawP ++ E.map tw
def WZ (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}
def Imp (E : List (Bool × ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt : AA < 2 ^ NN := by decide +kernel
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawP.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma raw_wire_good {w : ℕ} (hw : w ∈ rawP) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 raw_good w hw
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
lemma raw_get (v : ℕ) : rawP.getD v 0 = 0 ∨ rawP.getD v 0 ∈ rawP := by
  rw [List.getD_eq_getElem?_getD]
  cases h : rawP[v]? with
  | none => exact Or.inl rfl
  | some x => exact Or.inr (List.mem_of_getElem? h)
lemma raw_get_good (v Z : ℕ) : Good (lz Z) (rawP.getD v 0 &&& mz Z) := by
  rcases raw_get v with h | h
  · rw [h, Nat.zero_and]; exact ⟨fun i j _ _ _ => by simp, fun i j _ _ _ => by simp⟩
  · exact raw_wire_good h Z
lemma wire_good {E : List (Bool × ℕ × ℕ)} {w : ℕ} (hw : w ∈ rawL E) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  simp only [rawL, List.mem_append, List.mem_map] at hw
  rcases hw with h | ⟨e, _, rfl⟩
  · exact raw_wire_good h Z
  · rw [tw, and_op]; exact op_good _ (raw_get_good _ Z) (raw_get_good _ Z)
lemma raw_avail (E : List (Bool × ℕ × ℕ)) (v Z : ℕ) : rawP.getD v 0 &&& mz Z ∈ C (mz Z) (WZ E Z) := by
  rcases raw_get v with h | h
  · rw [h, Nat.zero_and]; exact Or.inr (by simp)
  · exact Or.inl ⟨_, by simp only [rawL, List.mem_append]; exact Or.inl h, rfl⟩
lemma WZ_nil_sub (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : WZ [] Z ⊆ WZ E Z := by
  rintro x ⟨w, hw, rfl⟩
  refine ⟨w, ?_, rfl⟩
  simp only [rawL, List.map_nil, List.append_nil, List.mem_append] at hw ⊢
  exact Or.inl hw
def trivE (e : Bool × ℕ × ℕ) (Z : ℕ) : Bool :=
  (fun m => (fun s => Nat.beq s 0 || Nat.beq s m || rawP.any (fun w => Nat.beq (Nat.land w m) s)) (Nat.land (tw e) m)) (mz Z)
lemma impA {e : Bool × ℕ × ℕ} {Z L : ℕ} (h : trivE e Z = true) (hI : Imp [] Z L) : Imp [e] Z L := by
  intro q hq hs
  refine hI q hq (hs.mono le_rfl ?_)
  rintro x (⟨w, hw, rfl⟩ | hx)
  · simp only [rawL, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inl ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩
    · simp only [trivE, Bool.or_eq_true, List.any_eq_true, nl] at h
      rcases h with (h | h) | ⟨w, hw, h⟩
      · rw [Nat.eq_of_beq_eq_true h]; exact Or.inr (by simp)
      · rw [Nat.eq_of_beq_eq_true h]; exact Or.inr (by simp)
      · rw [← Nat.eq_of_beq_eq_true h]; exact Or.inl ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩
  · exact Or.inr hx
lemma sol_add {e : Bool × ℕ × ℕ} {E : List (Bool × ℕ × ℕ)} {Z q : ℕ} {S : Set ℕ} (hS : S ⊆ C (mz Z) (WZ E Z))
    (hs : Sol Z0 (mz Z) (tz Z) q (insert (tw e &&& mz Z) S)) : Sol Z0 (mz Z) (tz Z) (q + 1) (C (mz Z) (WZ E Z)) := by
  refine .bi (d := e.1) (raw_avail E e.2.1 Z) (raw_avail E e.2.2 Z) (al0 _ _ _) (hs.mono le_rfl ?_)
  rw [← and_op]
  exact Set.insert_subset_insert hS
lemma impB {e : Bool × ℕ × ℕ} {Z L : ℕ} (hI : Imp [] Z L) : Imp [e] Z (L - 1) := by
  intro q hq hs
  refine hI (q + 1) (by omega) (sol_add (e := e) (S := C (mz Z) (WZ [] Z)) subset_rfl (hs.mono le_rfl ?_))
  rintro x (⟨w, hw, rfl⟩ | hx)
  · simp only [rawL, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inr (Or.inl ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩)
    · exact Or.inl rfl
  · exact Or.inr (Or.inr hx)
lemma forb_ok {E : List (Bool × ℕ × ℕ)} {f : Bool × ℕ × ℕ} {Z L : ℕ} (hE : E.length ≤ 1) (hf : Imp [f] Z (L + E.length)) :
    ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (insert (tw f &&& mz Z) (WZ E Z))) := by
  intro q hq hs
  have hsub : C (mz Z) (insert (tw f &&& mz Z) (WZ [] Z)) ⊆ C (mz Z) (WZ [f] Z) := by
    rintro x ((rfl | hx) | hx)
    · exact Or.inl ⟨tw f, by simp [rawL], rfl⟩
    · exact Or.inl (WZ_nil_sub _ _ hx)
    · exact Or.inr hx
  match E, hE, hf, hs with
  | [], _, hf, hs => exact hf q (by simpa using hq) (hs.mono le_rfl hsub)
  | [e], _, hf, hs =>
    refine hf (q + 1) (by simpa using hq) (sol_add (e := e) (S := C (mz Z) (insert (tw f &&& mz Z) (WZ [] Z))) hsub (hs.mono le_rfl ?_))
    rintro x ((rfl | ⟨w, hw, rfl⟩) | hx)
    · exact Or.inr (Or.inl (Or.inl rfl))
    · simp only [rawL, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inr (Or.inl (Or.inr ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩))
      · exact Or.inl rfl
    · exact Or.inr (Or.inr hx)
lemma Imp.mono {E : List (Bool × ℕ × ℕ)} {Z L L' : ℕ} (h : Imp E Z L) (hL : L' ≤ L) : Imp E Z L' := fun q hq => h q (by omega)
def tabV (e : Bool × ℕ × ℕ) (own : List ℕ) (x : ℕ × ℕ) : ℕ := bif own.any (fun c => Nat.beq c x.1) || trivE e x.1 then x.2 else Nat.sub x.2 1
def tabE (e : Bool × ℕ × ℕ) (own : List ℕ) (raw : List (ℕ × ℕ)) : List (ℕ × ℕ) := raw.map (fun x => (x.1, tabV e own x))
lemma tabE_ok {e : Bool × ℕ × ℕ} {own : List ℕ} {raw : List (ℕ × ℕ)} (hr : ∀ x ∈ raw, Imp [] x.1 x.2)
    (ho : ∀ x ∈ raw, x.1 ∈ own → Imp [e] x.1 x.2) : ∀ y ∈ tabE e own raw, Imp [e] y.1 y.2 := by
  intro y hy
  simp only [tabE, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  change Imp [e] x.1 (tabV e own x)
  unfold tabV
  cases h : own.any (fun c => Nat.beq c x.1) with
  | true =>
    rw [List.any_eq_true] at h
    obtain ⟨c, hc, h⟩ := h
    rw [Nat.eq_of_beq_eq_true h] at hc
    exact ho x hx hc
  | false =>
    cases h2 : trivE e x.1 with
    | true => exact impA h2 (hr x hx)
    | false => exact impB (hr x hx)
def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)
def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {E : List (Bool × ℕ × ℕ)} {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ E Z) : Im (mz Z') S ⊆ WZ E Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma shl_lt {a N : ℕ} (h : a < 2 ^ N) : a <<< N < 2 ^ (2 * N) := by
  rw [Nat.shiftLeft_eq, two_mul, pow_add]; exact Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _)
lemma mz_lt (Z : ℕ) : mz Z < 2 ^ (2 * NN) := by
  have h1 : lz Z < 2 ^ NN := lt_of_le_of_lt Nat.and_le_left AA_lt
  have h2 : fz Z < 2 ^ NN := lt_of_le_of_lt Nat.and_le_left (by
    unfold FPM; exact lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos 64) (by norm_num)) (Nat.pow_le_pow_right (by norm_num) (by unfold NN; norm_num)))
  have h3 : lz Z <<< NN < 2 ^ (2 * NN) := shl_lt h1
  have h4 : (2 : ℕ) ^ NN ≤ 2 ^ (2 * NN) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (lt_of_lt_of_le h1 h4) (lt_of_lt_of_le h2 h4)) h3
def npOf (P : List ℕ) : ℕ := laneL (WL NN) ((List.range 16).map (fun j => P.getD j 0))
lemma npOf_eq (P : List ℕ) : npOf P = lane (WL NN) 16 (fun j => P.getD j 0) := by
  rw [npOf, laneL_eq, List.length_map, List.length_range]
  refine lane_congr fun j hj => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl
lemma PZ_lt (Q : List (ℕ × ℕ)) (j : ℕ) : (PZ Q).getD j 0 < 2 ^ (2 * NN) := by
  rw [PZ, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Q[j]? with
  | none => exact Nat.two_pow_pos _
  | some x => exact mz_lt _
noncomputable section
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 6) d) L
end
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 6 * pL L + d := by
  change (pL L <<< 6) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 6 * (j + 1) = 6 * j + 6 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 6 = 0 ∧ i / 6 < L.length ∧ L.getD (i / 6) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 6 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 6 = (i - 6) / 6 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
noncomputable section
def fl0 (s : ℕ) (P : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun n _ ih => Nat.add (Nat.shiftLeft ih 6) (bit01 (Nat.beq (Nat.land s n) 0))) P
def fl1 (s : ℕ) (P : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun n _ ih => Nat.add (Nat.shiftLeft ih 6) (bit01 (Nat.beq (Nat.land s n) n))) P
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, fl0 s P, fl1 s P, Nat.lor (fl0 s P) (fl1 s P), 3, 0⟩
end
lemma fl0_eq (s : ℕ) (P : List ℕ) : fl0 s P = pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)) := by
  induction P with
  | nil => rfl
  | cons n P ih => rw [List.map_cons, pL_cons, ← ih]; change (fl0 s P) <<< 6 + _ = _; rw [Nat.shiftLeft_eq]; ring
lemma fl1_eq (s : ℕ) (P : List ℕ) : fl1 s P = pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)) := by
  induction P with
  | nil => rfl
  | cons n P ih => rw [List.map_cons, pL_cons, ← ih]; change (fl1 s P) <<< 6 + _ = _; rw [Nat.shiftLeft_eq]; ring
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (6 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 6 * j / 6 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0)
    rw [List.length_map, ← fl0_eq] at this; exact this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n)
    rw [List.length_map, ← fl1_eq] at this; exact this
  · change (fl0 s P).testBit (6 * j) = true at h
    rw [fl0_eq] at h
    exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · change (fl1 s P).testBit (6 * j) = true at h
    rw [fl1_eq] at h
    exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section
def addN (o : ℕ) (v : List ℕ) : List ℕ := List.rec (motive := fun _ => List ℕ) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List ℕ) (w :: ih) (Bool.rec (motive := fun _ => List ℕ) (o :: w :: t) (w :: t) (Nat.beq o w)) (Nat.ble w o)) v
def avl (m : ℕ) (L : List ℕ) : List ℕ := List.rec (motive := fun _ => List ℕ) []
  (fun w _ ih => Bool.rec (motive := fun _ => List ℕ) (Bool.rec (motive := fun _ => List ℕ) (addN (Nat.land w m) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def mkA (P : List ℕ) (L : List ℕ) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun s _ ih h => st s fun s => st (fl0 s P) fun a => st (fl1 s P) fun b => st (Nat.lor a b) fun c => ih fun r => h (⟨s, a, b, c, 3, 0⟩ :: r)) L
def frcP (L : List ℕ) : (List ℕ → Bool) → Bool := List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun h => h [])
  (fun s _ ih h => st s fun s => ih fun r => h (s :: r)) L
def anySub (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (cov d l t)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def fbit (fm fh s : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight fh (Nat.mod s fm)) 1) 1
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
end
lemma mkA_eq (P L : List ℕ) : ∀ h, mkA P L h = h (L.map (mkW P)) := by
  induction L with
  | nil => intro h; rfl
  | cons s L ih =>
    intro h
    change st s (fun s => st (fl0 s P) fun a => st (fl1 s P) fun b => st (Nat.lor a b) fun c => mkA P L fun r => h (⟨s, a, b, c, 3, 0⟩ :: r)) = _
    simp only [st_eq]; rw [ih]; rfl
lemma frcP_eq (L : List ℕ) : ∀ h, frcP L h = h L := by
  induction L with
  | nil => intro h; rfl
  | cons s L ih =>
    intro h
    change st s (fun s => frcP L fun r => h (s :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {d : Bool} {l : ℕ} {v : List W} : ∀ {c : ℕ} {h : List W → Bool}, (∀ i, c.testBit i = true → l.testBit i = true) → anySub d l v c h = false →
    ∀ r, r.Sublist v → (∀ i, l.testBit i = true → c.testBit i = true ∨ (cov d l r).testBit i = true) → h r = false := by
  induction v with
  | nil => intro c h _ hh r hr _; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro c h hcl hh r hr hcov
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (anySub d l v c h) (Nat.beq (Nat.lor c (cov d l v)) l)) true
      (st (Nat.lor c (sp d l w.s)) fun c => anySub d l v c fun r => h (w :: r)) : Bool) = false at hh
    rw [bR, bR, st_eq] at hh
    cases h1 : anySub d l v (Nat.lor c (sp d l w.s)) (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      have hc2 : ∀ i, (cov d l v).testBit i = true → l.testBit i = true := by
        intro i hi
        obtain ⟨w', _, hw'⟩ := (cov_bit _ _ _ _).1 hi
        rw [sp_bit, Bool.and_eq_true] at hw'; exact hw'.1
      cases hr with
      | cons _ hr =>
        have : Nat.beq (Nat.lor c (cov d l v)) l = true := by
          rw [Nat.beq_eq]
          apply Nat.eq_of_testBit_eq; intro i
          rw [no, Nat.testBit_or]
          cases hli : l.testBit i with
          | false =>
            by_contra hc
            rw [Bool.not_eq_false, Bool.or_eq_true] at hc
            rcases hc with h | h
            · rw [hcl i h] at hli; simp at hli
            · rw [hc2 i h] at hli; simp at hli
          | true =>
            rcases hcov i hli with h | h
            · rw [h]; rfl
            · obtain ⟨w', hw', h2⟩ := (cov_bit _ _ _ _).1 h
              rw [(cov_bit d l i v).2 ⟨w', hr.subset hw', h2⟩]; simp
        rw [this, Bool.cond_true] at hh
        exact ih hcl hh r hr hcov
      | cons_cons _ hr =>
        rename_i r'
        refine ih (c := Nat.lor c (sp d l w.s)) ?_ h1 r' hr ?_
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true] at hi
          rcases hi with h | h
          · exact hcl i h
          · rw [sp_bit, Bool.and_eq_true] at h; exact h.1
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true]
          rcases hcov i hi with h | h
          · exact Or.inl (Or.inl h)
          · change (Nat.lor (sp d l w.s) (cov d l r')).testBit i = true at h
            rw [no, Nat.testBit_or, Bool.or_eq_true] at h
            rcases h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
lemma addN_cons (o w : ℕ) (t : List ℕ) : addN o (w :: t) = bif Nat.ble w o then (bif Nat.beq o w then w :: t else o :: w :: t) else w :: addN o t := by
  change Bool.rec (motive := fun _ => List ℕ) (w :: addN o t) (Bool.rec (motive := fun _ => List ℕ) (o :: w :: t) (w :: t) (Nat.beq o w)) (Nat.ble w o) = _
  cases Nat.ble w o <;> cases Nat.beq o w <;> rfl
def Srt (v : List ℕ) : Prop := v.Pairwise (fun a b => b < a)
lemma addN_spec {o : ℕ} {v : List ℕ} (hv : Srt v) : Srt (addN o v) ∧ ∀ w, w ∈ addN o v ↔ w = o ∨ w ∈ v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addN]⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2⟩ := ih hp.2
    rw [addN_cons]
    cases h1 : Nat.ble x o with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o x with
      | true =>
        have e := Nat.eq_of_beq_eq_true h2
        refine ⟨hv, fun w => ?_⟩
        simp only [Bool.cond_true, List.mem_cons]; constructor
        · intro h; exact Or.inr h
        · rintro (rfl | h)
          · exact Or.inl e
          · exact h
      | false =>
        have hne : o ≠ x := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w => by simp⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o < x := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w => ?_⟩
      · rcases (i2 w).1 hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons, i2]; tauto
lemma avl_spec (m : ℕ) (L : List ℕ) : Srt (avl m L) ∧ ∀ w, w ∈ avl m L ↔ w ≠ 0 ∧ w ≠ m ∧ ∃ x ∈ L, w = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl]⟩
  | cons y L ih =>
    obtain ⟨i1, i2⟩ := ih
    have e : avl m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl m L else bif Nat.beq (Nat.land y m) m then avl m L else addN (Nat.land y m) (avl m L) := by
      change Bool.rec (motive := fun _ => List ℕ) (Bool.rec (motive := fun _ => List ℕ) (addN (Nat.land y m) (avl m L)) (avl m L) (Nat.beq (Nat.land y m) m)) (avl m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      have h0 : y &&& m = 0 := Nat.eq_of_beq_eq_true h1
      refine ⟨i1, fun w => ?_⟩
      simp only [Bool.cond_true, i2, List.mem_cons]
      constructor
      · rintro ⟨a, b, x, hx, e⟩; exact ⟨a, b, x, Or.inr hx, e⟩
      · rintro ⟨a, b, x, rfl | hx, e'⟩
        · exact absurd (e'.trans h0) a
        · exact ⟨a, b, x, hx, e'⟩
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        have h0 : y &&& m = m := Nat.eq_of_beq_eq_true h1'
        refine ⟨i1, fun w => ?_⟩
        simp only [Bool.cond_true, Bool.cond_false, i2, List.mem_cons]
        constructor
        · rintro ⟨a, b, x, hx, e⟩; exact ⟨a, b, x, Or.inr hx, e⟩
        · rintro ⟨a, b, x, rfl | hx, e'⟩
          · exact absurd (e'.trans h0) b
          · exact ⟨a, b, x, hx, e'⟩
      | false =>
        have n1 : y &&& m ≠ 0 := fun e => by
          have : Nat.beq (Nat.land y m) 0 = true := by rw [nl, e]; rfl
          rw [this] at h1; simp at h1
        have n2 : y &&& m ≠ m := fun e => by
          have : Nat.beq (Nat.land y m) m = true := by rw [nl, e]; exact Nat.beq_refl m
          rw [this] at h1'; simp at h1'
        obtain ⟨j1, j2⟩ := addN_spec (o := Nat.land y m) i1
        refine ⟨j1, fun w => ?_⟩
        rw [Bool.cond_false, Bool.cond_false, j2, i2]
        constructor
        · rintro (rfl | ⟨a, b, x, hx, e'⟩)
          · exact ⟨n1, n2, y, by simp, rfl⟩
          · exact ⟨a, b, x, by simp [hx], e'⟩
        · rintro ⟨a, b, x, hx, e'⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inl e'
          · exact Or.inr ⟨a, b, x, hx, e'⟩
def mFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
def FF : ℕ := 2 ^ MM - 1
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel
def fbOk (E F : List (Bool × ℕ × ℕ)) (fb : ℕ × ℕ) : Bool :=
  (fun m => (fun W => (fun G => W.all (fun x => W.all (fun y => Nat.beq x y ||
      ((!fbit fb.1 fb.2 (Nat.land x y) || G.any (Nat.beq (Nat.land x y))) && (!fbit fb.1 fb.2 (Nat.lor x y) || G.any (Nat.beq (Nat.lor x y)))))))
    (F.map (fun e => Nat.land (tw e) m))) ((rawL E).map (fun w => Nat.land w m))) (mz 0)
lemma fbOk_spec {E F : List (Bool × ℕ × ℕ)} {fb : ℕ × ℕ} (h : fbOk E F fb = true) {x y : ℕ} (hx : x ∈ WZ E 0) (hy : y ∈ WZ E 0) (hxy : x ≠ y) {d : Bool}
    (hb : fbit fb.1 fb.2 (op d x y) = true) : ∃ f ∈ F, op d x y = tw f &&& mz 0 := by
  obtain ⟨wx, hwx, rfl⟩ := hx
  obtain ⟨wy, hwy, rfl⟩ := hy
  simp only [fbOk, List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, exists_exists_and_eq_and] at h
  have h := (h wx hwx wy hwy).resolve_left fun e => hxy (Nat.eq_of_beq_eq_true e)
  simp only [nl, no] at h
  cases d with
  | false =>
    rcases h.1 with h | ⟨f, hf, h⟩
    · change fbit fb.1 fb.2 (wx &&& mz 0 &&& (wy &&& mz 0)) = true at hb
      rw [h] at hb; simp at hb
    · exact ⟨f, hf, Nat.eq_of_beq_eq_true h⟩
  | true =>
    rcases h.2 with h | ⟨f, hf, h⟩
    · change fbit fb.1 fb.2 (wx &&& mz 0 ||| (wy &&& mz 0)) = true at hb
      rw [h] at hb; simp at hb
    · exact ⟨f, hf, Nat.eq_of_beq_eq_true h⟩
lemma fbit_triv (s : ℕ) : fbit 1 0 s = false := by
  unfold fbit
  change Nat.beq ((0 >>> (s % 1)) &&& 1) 1 = false
  rw [Nat.zero_shiftRight]; rfl
def pwr (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : ℕ := (E.map fun e => Nat.land (tw e) (mz Z)).headD 0
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Q : List (ℕ × ℕ)) (K : ℕ) : pL (Q.map fun e => 32 + (K - e.2)) = pk (PZ Q).length (fun j => 32 + (K - (Q.getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
open Classical in
noncomputable def RZ (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : ℕ → ℕ := fun s => if s ∈ WZ E Z then 3 else 0
lemma RZ_set (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : {x | RZ E Z x ≠ 0} = WZ E Z := by
  ext x; simp only [RZ, Set.mem_ofPred_eq]; split_ifs with h <;> simp [h]
lemma RZ_mem {E : List (Bool × ℕ × ℕ)} {Z x : ℕ} (h : RZ E Z x ≠ 0) : x ∈ WZ E Z := by
  have : x ∈ {x | RZ E Z x ≠ 0} := h
  rwa [RZ_set] at this
lemma RZ_R2 (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : ∀ d a b, (RZ E Z a = 0 ∨ RZ E Z b = 0) → Al (RZ E Z) d a b := by
  intro d a b h
  unfold Al
  rcases h with h | h <;> rw [h] <;> simp
lemma hasP_ok {p : ℕ} {v : List W} (h : p = 0 ∨ ∃ w ∈ v, w.s = p) : hasP p v = true := by
  unfold hasP
  rw [bR]
  rcases h with rfl | ⟨w, hw, rfl⟩
  · rfl
  · have : (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) = true := by
      induction v with
      | nil => simp at hw
      | cons x v ih =>
        change (Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) true (Nat.beq x.s w.s) : Bool) = true
        rw [bR]
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rw [Nat.beq_refl]; rfl
        · rw [ih hw]; cases Nat.beq x.s w.s <;> rfl
    rw [this]; cases Nat.beq w.s 0 <;> rfl
noncomputable section
def frcQ (Q : List (ℕ × ℕ)) : (List (ℕ × ℕ) → Bool) → Bool := List.rec (motive := fun _ => (List (ℕ × ℕ) → Bool) → Bool) (fun h => h [])
  (fun x _ ih h => st x.1 fun c => st x.2 fun L => ih fun r => h ((c, L) :: r)) Q
def lnW (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) v
def anyN (h : ℕ → Bool) (L : List ℕ) : Bool := List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (h a)) L
def pre (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (Z K : ℕ) (h : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) : Bool :=
  frcQ Q fun Q => frcP (PZ Q) fun P => st (lz Z) fun l => st (mz Z) fun m => st (npOf P) fun np => st (pL (Q.map fun _ => 32)) fun g => st (pL (Q.map fun e => 32 + (K - e.2))) fun B =>
    st (pwr E Z) fun p => frcP (avl m (rawL E)) fun sg => mkA P sg fun v => h l m np g B p v
def startG (f : ℕ → List W → Bool) (g B K t p : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child f g false (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble (lnW v) (Nat.sub (Nat.succ K) t))) (hasP p v)
def chkG (top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (fb : ℕ × ℕ) (Z K t H ph : ℕ) : Bool :=
  st fb.1 fun fm => st fb.2 fun fh => pre E Q Z K fun l m np g B p v => anySub (pos t) l v 0 fun r => startG (fun z r => top l m g np fm fh K H ph K t z r) g B K t p r
def chkT (top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (fb : ℕ × ℕ) (Z K : ℕ) (ts : List ℕ) (H ph : ℕ) : Bool :=
  st fb.1 fun fm => st fb.2 fun fh => pre E Q Z K fun l m np g B p v => anyN (fun t => anySub (pos t) l v 0 fun r => startG (fun z r => top l m g np fm fh K H ph K t z r) g B K t p r) ts
end
lemma frcQ_eq (Q : List (ℕ × ℕ)) : ∀ h, frcQ Q h = h Q := by
  induction Q with
  | nil => intro h; rfl
  | cons x Q ih =>
    intro h
    change st x.1 (fun c => st x.2 fun L => frcQ Q fun r => h ((c, L) :: r)) = _
    simp only [st_eq]; rw [ih]
lemma lnW_eq (v : List W) : lnW v = v.length := by
  induction v with
  | nil => rfl
  | cons w v ih => change Nat.succ (lnW v) = _; rw [ih]; rfl
lemma anyN_false {h : ℕ → Bool} {L : List ℕ} (hh : anyN h L = false) : ∀ t ∈ L, h t = false := by
  induction L with
  | nil => simp
  | cons a L ih =>
    change (Bool.rec (motive := fun _ => Bool) (anyN h L) true (h a) : Bool) = false at hh
    rw [bR] at hh
    intro t ht
    cases ha : h a with
    | true => rw [ha] at hh; simp at hh
    | false =>
      rw [ha, Bool.cond_false] at hh
      rcases List.mem_cons.1 ht with rfl | ht
      · exact ha
      · exact ih hh t ht
lemma pre_eq (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (Z K : ℕ) (h : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) :
    pre E Q Z K h = h (lz Z) (mz Z) (npOf (PZ Q)) (pL (Q.map fun _ => 32)) (pL (Q.map fun e => 32 + (K - e.2))) (pwr E Z) ((avl (mz Z) (rawL E)).map (mkW (PZ Q))) := by
  simp only [pre, frcQ_eq, frcP_eq, st_eq, mkA_eq]
lemma chkT_chk {top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool} {E : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {fb : ℕ × ℕ} {Z K : ℕ} {ts : List ℕ} {H ph : ℕ}
    (h : chkT top E Q fb Z K ts H ph = false) : ∀ t ∈ ts, chkG top E Q fb Z K t H ph = false := by
  intro t ht
  simp only [chkT, chkG, st_eq, pre_eq] at h ⊢
  exact anyN_false h t ht
def TopOk (top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) : Prop :=
  ∀ {P : List ℕ} {l m g np T : ℕ}, Ctx P l m g np T → ∀ {R : ℕ → ℕ}, (∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b) → (∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) →
    ∀ {fm fh K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)} {Fs : Set ℕ}, mFull M = true → (∀ p ∈ M, top l m g np fm fh K p.1 p.2 k t z v = false) →
      StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) → ∀ {k' : ℕ}, k' ≤ k → Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) →
      (∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs) →
      (∀ s ∈ Fs, ∀ q < k', ¬ Sol Z0 m T q (C m (insert s ({x | R x ≠ 0} ∪ (S : Set ℕ))))) → False
lemma RZ_RR (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : ∀ d a b, RZ E Z a ≠ 0 → RZ E Z b ≠ 0 → ¬ Al (RZ E Z) d a b := by
  intro d a b ha hb h
  have h3 : ∀ x, RZ E Z x ≠ 0 → RZ E Z x = 3 := by
    intro x hx; unfold RZ at hx ⊢; split_ifs at hx ⊢ with h
    · rfl
    · simp at hx
  unfold Al at h
  rw [h3 a ha, h3 b hb] at h
  cases d <;> simp at h
theorem imp_FK {top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool} (htop : TopOk top)
    {E F : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {fb : ℕ × ℕ} {Z L K : ℕ} (hLK : L ≤ K + 1) (hK : K ≤ 31) (hE : E = [] ∨ ∃ e, E = [e] ∧ e.2.1 < 12 ∧ e.2.2 < 12 ∧ Imp [] Z L)
    (hp : pOk Z Q = true) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hfb : fb = (1, 0) ∨ (Z = 0 ∧ fbOk E F fb = true)) (hF : ∀ e ∈ F, Imp [e] 0 (L - 1 + E.length))
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∀ t < L, t = 0 → ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chkG top E Q fb Z K t p.1 p.2 = false) : Imp E Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE1 : E.length ≤ 1 := by rcases hE with rfl | ⟨e, rfl, _⟩ <;> simp
  classical
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, rfl, _, _, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩
      · have hx : tw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb t (by omega) hl.zeroUnary
  obtain ⟨a1, a2⟩ := avl_spec (mz Z) (rawL E)
  set v := ((avl (mz Z) (rawL E)).filter (fun s => decide (s ∈ S))).map (mkW (PZ Q)) with hv
  have hsub : v.Sublist ((avl (mz Z) (rawL E)).map (mkW (PZ Q))) := List.filter_sublist.map _
  have hvs : v.map W.s = (avl (mz Z) (rawL E)).filter (fun s => decide (s ∈ S)) := by
    rw [hv, List.map_map]; exact List.map_id _
  have hnd : (v.map W.s).Nodup := by
    rw [hvs]
    exact (a1.sublist List.filter_sublist).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, hvs, List.mem_filter, a2]
    constructor
    · rintro ⟨_, hx⟩; simpa using hx
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      exact ⟨⟨fun e => h0 (e ▸ hx), fun e => h1 (e ▸ hx), w, hw, rfl⟩, by simpa using hx⟩
  have hvm : ∀ w ∈ v, ∃ x ∈ rawL E, w = mkW (PZ Q) (x &&& mz Z) := by
    intro w hw
    rw [hv, List.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    obtain ⟨_, _, x, hx, rfl⟩ := (a2 s).1 (List.mem_of_mem_filter hs)
    exact ⟨x, hx, rfl⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := hvm w hw; exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw; exact wire_good hx Z
  have hd0 : ∀ w ∈ v, w.d = 0 := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw; rfl
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, K)).1 ∧ Q.getD j (0, K) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 32)) (npOf (PZ Q)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_, ⟨fun j => (PZ Q).getD j 0, fun j _ => PZ_lt Q j, npOf_eq _, fun j _ _ => Nat.and_self _⟩⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hA : ∀ j < (PZ Q).length, Acc ((PZ Q).getD j 0) (tz Z) K (K - (Q.getD j (0, K)).2) (fun _ => 0) S := by
    intro j hj
    obtain ⟨e1, e2⟩ := hPget j hj
    rw [e1]
    exact Acc.start (L := (Q.getD j (0, K)).2) (hno _ e2) subset_rfl (by omega)
  have hle := cnt_le X (D := fun _ _ => 0) hrep hwok hA hm (by omega)
  have hz : pL (Q.map fun e => 32 + (K - e.2)) - sumc v = pk (PZ Q).length (fun j => 32 + (K - (Q.getD j (0, K)).2) - cnt v j) := by
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hst : StOk (PZ Q) (tz Z) (lz Z) K (pL (Q.map fun e => 32 + (K - e.2)) - sumc v) v S := by
    rw [hz]
    exact StOk.start hrep hwok hgood (by omega) (fun j _ => by omega) hd0 hA
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, show pos t = pos' t by cases t <;> simp [pos, pos'], hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble (lnW v) (Nat.sub (Nat.succ K) t) = true := Nat.ble_eq_true_of_le (by
    rw [lnW_eq]; change v.length ≤ K + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, top (lz Z) (mz Z) (pL (Q.map fun _ => 32)) (npOf (PZ Q)) fb.1 fb.2 K p.1 p.2 K t (pL (Q.map fun e => 32 + (K - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chkG, st_eq, pre_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startG, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => top (lz Z) (mz Z) _ (npOf (PZ Q)) fb.1 fb.2 K p.1 p.2 K t z r) (fun h => rfl) rfl hst hm (by omega) h3
  have hW : {x | RZ E Z x ≠ 0} ∪ (S : Set ℕ) = WZ E Z := by rw [RZ_set]; exact Set.union_eq_self_of_subset_right hSW
  refine htop X (RZ_RR E Z) (RZ_R2 E Z) (Fs := {s | ∃ f ∈ F, s = tw f &&& mz Z ∧ Z = 0}) hMf all hst hcod (by omega) hl ?_ ?_ ?_
  · intro q hq hs
    rw [hW] at hs
    exact Nat.find_min hex (show q < Nat.find hex by omega) hs
  · intro d x y hxy hx hy hbit
    rcases hfb with rfl | ⟨rfl, hfb⟩
    · rw [fbit_triv] at hbit; simp at hbit
    · obtain ⟨f, hf, e⟩ := fbOk_spec hfb (RZ_mem hx) (RZ_mem hy) hxy hbit
      exact ⟨f, hf, e, rfl⟩
  · rintro s ⟨f, hf, rfl, rfl⟩ q hq hs
    rw [hW] at hs
    exact forb_ok hE1 (hF f hf) q (by omega) hs
lemma Live.W {m T k t : ℕ} {S : Finset ℕ} {Q : Set ℕ} (hl : Live R m T k t S) (hQ : (S : Set ℕ) ⊆ Q) : Sol Z0 m T k Q := hl.sol.mono le_rfl hQ
lemma front {m T : ℕ} (hR : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {k t : ℕ} {S : Finset ℕ} (hl : Live Z0 m T k t S)
    (hm : ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) :
    Live R m T k t S ∨ ∃ k0 d a b S1, k = k0 + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ Bi Z0 d a b S S1 ∧ Live Z0 m T k0 t S1 := by
  induction hl with
  | stop => exact Or.inl .stop
  | @bi k t d0 a b U hab hal0 hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hb0 : Bi Z0 d0 a b (insert a (insert b U)) (insert (op d0 a b) U) := ⟨hab, U, rfl, rfl, hal0⟩
    by_cases hW : R a ≠ 0 ∧ R b ≠ 0
    · exact Or.inr ⟨k, d0, a, b, _, rfl, hW.1, hW.2, hb0, hl⟩
    have hal : Al R d0 a b := hR _ _ _ (by
      by_contra hc; push Not at hc; exact hW hc)
    have hfr : op d0 a b ∉ C m (Q ∪ ((insert a (insert b U) : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : op d0 a b ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfa : op d0 a b ≠ a := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfb : op d0 a b ≠ b := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (op d0 a b) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (op d0 a b) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.bi (d := d0) (a := a) (b := b) (Or.inl (Or.inr (by simp))) (Or.inl (Or.inr (by simp))) (al0 _ _ _) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal'⟩, hl1⟩
    · exact Or.inl (.bi hab hal h)
    · set o := op d0 a b with ho
      have nx : x ≠ o := fun e => hx (e ▸ hfR)
      have ny : y ≠ o := fun e => hy (e ▸ hfR)
      have hmV : o ∈ V := by
        have : o ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase o)) := by
        ext z
        by_cases hz : z = o
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert o U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert b (insert (op d x y) (V.erase o))), rfl, hx, hy,
        ⟨hxy, insert a (insert b (V.erase o)), ?_, ?_, hal'⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h | h) <;> simp only [h, true_or, or_true])
      · ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h) <;> simp only [h, true_or, or_true])
      · refine .bi hab hal0 ?_
        have : insert (op d0 a b) (insert (op d x y) (V.erase o)) = insert (op d x y) V := by
          rw [Finset.insert_comm, ← ho, Finset.insert_erase hmV]
        rw [this]; exact hl1
def MW (R : ℕ → ℕ) (m T k : ℕ) (S : Finset ℕ) : Prop := ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))
def MF (R : ℕ → ℕ) (m T k : ℕ) (Fs : Set ℕ) (S : Finset ℕ) : Prop := ∀ s ∈ Fs, ∀ q < k, ¬ Sol Z0 m T q (C m (insert s ({x | R x ≠ 0} ∪ (S : Set ℕ))))
lemma MW.min {m T k t : ℕ} {S : Finset ℕ} (h : MW R m T k S) (hl : Live Z0 m T k t S) : Min Z0 m T k t S :=
  ⟨hl, fun q hq hs => h q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
lemma step_sub {m : ℕ} {A : Set ℕ} {S S1 : Finset ℕ} {g : ℕ} (h : S1 ⊆ insert g S) :
    C m (A ∪ (S1 : Set ℕ)) ⊆ insert g (C m (A ∪ (S : Set ℕ))) := by
  rintro x ((hx | hx) | hx)
  · exact Or.inr (Or.inl (Or.inl hx))
  · have hx' := h hx
    simp only [Finset.mem_insert] at hx'
    rcases hx' with rfl | hx'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (Or.inr hx'))
  · exact Or.inr (Or.inr hx)
lemma MW.bi {m T k a b : ℕ} {d : Bool} {S S1 : Finset ℕ} (h : MW R m T (k + 1) S) (hb : Bi Z0 d a b S S1) : MW R m T k S1 := by
  intro q hq hs
  exact h (q + 1) (by omega) (.bi (d := d) (a := a) (b := b) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (al0 _ _ _) (hs.mono le_rfl (step_sub hb.sub.2.2)))
lemma MF.bi {m T k a b : ℕ} {Fs : Set ℕ} {d : Bool} {S S1 : Finset ℕ} (h : MF R m T (k + 1) Fs S) (hb : Bi Z0 d a b S S1) : MF R m T k Fs S1 := by
  intro s hsF q hq hs
  refine h s hsF (q + 1) (by omega) (.bi (d := d) (a := a) (b := b) (Or.inl (Or.inr (Or.inr hb.sub.1))) (Or.inl (Or.inr (Or.inr hb.sub.2.1))) (al0 _ _ _) (hs.mono le_rfl ?_))
  rw [← Set.insert_union, ← Set.insert_union]
  exact step_sub hb.sub.2.2
lemma MF.gate {m T k t a b : ℕ} {Fs : Set ℕ} {d : Bool} {S S1 : Finset ℕ} (h : MF R m T (k + 1) Fs S) (hb : Bi Z0 d a b S S1) (hl : Live Z0 m T k t S1)
    (hg : op d a b ∈ Fs) : False := by
  refine h _ hg k (by omega) (hl.sol.mono le_rfl fun x hx => ?_)
  have hx' := hb.sub.2.2 hx
  simp only [Finset.mem_insert] at hx'
  rcases hx' with rfl | hx'
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inr hx'))
theorem phase_step (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {P : List ℕ} {m T l k k' t : ℕ} {f : ℕ → List W → Bool} {v : List W} {S : Finset ℕ} {fm fh : ℕ} {Fs : Set ℕ}
    (hrep : Rep v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : MW R m T k' S) (hFb : MF R m T k' Fs S)
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs)
    (hA : ¬ Min R m T k' t S)
    (hB : ∀ (d : Bool) (a c : W) (S1 : Finset ℕ) (k0 : ℕ), a ∈ v → c ∈ v → a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → k' = k0 + 1 → Bi Z0 d a.s c.s S S1 → Live Z0 m T k0 t S1 →
      fbit fm fh (op d a.s c.s) = false → ∃ z' r, f z' r = false ∧ StOk P T l (k - 1) z' r S1 ∧ ∀ w ∈ r, (w.s = op d a.s c.s ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r)
    (hF : ∀ (z' : ℕ) (r : List W) (S1 : Finset ℕ), f z' r = false → StOk P T l (k - 1) z' r S1 → (∀ w ∈ r, w.r = R w.s) → ∀ k0 ≤ k - 1, Live Z0 m T k0 t S1 →
      MW R m T k0 S1 → MF R m T k0 Fs S1 → False) : False := by
  rcases front hR2 hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hb, hl1⟩
  · exact hA ⟨hlR, (hmW.min hl).2⟩
  · obtain ⟨wa, hwa, rfl⟩ := hrep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, rfl⟩ := hrep.mem.1 hb.sub.2.1
    have hnf : fbit fm fh (op d wa.s wb.s) = false := by
      by_contra hc
      exact hFb.gate hb hl1 (hfb d wa.s wb.s hb.1 ha hb' (by simpa using hc))
    obtain ⟨z', r, hf, hst, hmem⟩ := hB d wa wb S1 k0 hwa hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb') rfl hb hl1 hnf
    have hfr : R (op d wa.s wb.s) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF z' r S1 hf hst ?_ k0 (by omega) hl1 (hmW.bi hb) (hFb.bi hb)
    intro w hw
    rcases hmem w hw with ⟨e1, e2⟩ | ⟨w', hw', e1, e2⟩
    · rw [e1, e2, hfr]
    · rw [← e1, ← e2]; exact hcod w' hw'
noncomputable section
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g np fm fh K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (Nat.sub (Nat.succ k) t) v (fun κ κ2 =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g np k) l m g np k t z v κ κ2) (Nat.beq ph 1)) true
      (st (Nat.sub k 1) fun k1 => node1 (look1 l m g np fm fh K K k1 t) (pos t) l m g np fm fh (Nat.sub k t) (len v) z v κ κ2 (fun h xs => pairsC H h (fs xs))))) true (Nat.ble (len v) 1)
end
lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
lemma pairsC_any {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) (hb' : hb H (a.s + c.s) = true) :
    h a c = false ∨ h c a = false := by
  have : Std.Symm (fun a b : X => hb H (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
    ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
  exact ((pairsC_false hp).imp (S := fun a b => hb H (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall ha hc hne hb'
lemma or_f {a b : Bool} (h : (Bool.rec (motive := fun _ => Bool) b true a : Bool) = false) : a = false ∧ b = false := by
  cases a <;> simp_all
lemma KP.toR {m T k' t : ℕ} {S : Finset ℕ} {v : List W} {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} (h : KP Z0 m T k' t S v κ κ2) : KP R m T k' t S v κ κ2 :=
  ⟨fun e hb hl ha hb' => h.g1 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b) ha hb',
    fun e hb hl ha hb' => h.g2 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b) ha hb'⟩
def P1 (R : ℕ → ℕ) (P : List ℕ) (l m T : ℕ) (Fs : Set ℕ) (f : ℕ → ℕ → ℕ → List W → Bool) : Prop :=
  ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
    ∀ k' ≤ k, Live Z0 m T k' t S → MW R m T k' S → MF R m T k' Fs S → False
lemma mid1_false {fm fh : ℕ} {h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool} {a c : W} {oa oc ka kc kb : Bool} {s x y : ℕ}
    (hf : fbit fm fh s = false) (hh : mid1 fm fh h a c oa oc ka kc kb s x y = false) : h a c oa oc ka kc kb s x y = false := by
  have e : forb fm fh s = fbit fm fh s := rfl
  simp only [mid1, e, hf] at hh
  exact hh
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {fm fh fu : ℕ} {Fs : Set ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs)
    (hF : P1 R P l m T Fs f) {k t z : ℕ} {v : List W} {S : Finset ℕ} {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : MW R m T k' S) (hFb : MF R m T k' Fs S) (hKP : KP Z0 m T k' t S v κ κ2)
    (h2 : mv (look l m g np fu) l m g np k t z v κ κ2 = false)
    (h1 : ∀ x y, x ∈ S → y ∈ S → x ≠ y → R x ≠ 0 → R y ≠ 0 → ∃ go : (L_meta_9732.X → L_meta_9732.X → Bool) → List L_meta_9732.X → Bool,
      node1 (f (k - 1) t) (pos' t) l m g np fm fh (k - t) v.length z v κ κ2 go = false ∧
      ∀ h xs, go h xs = false → ∀ a c : L_meta_9732.X, a ∈ xs → c ∈ xs → a.w.r ≠ 0 → c.w.r ≠ 0 → a.s = x → c.s = y → h a c = false ∨ h c a = false) : False := by
  refine phase_step hR2 (P := P) (l := l) (f := f (k - 1) t) (fm := fm) (fh := fh) (Fs := Fs) hs.rep hcod hk hl hmW hFb hfb ?_ ?_ ?_
  · intro hm
    exact mv_sound X hR (look_sound X hR fu) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk hm hKP.toR
  · intro d a c S1 k0 ha hc hne har hcr e hb hl1 hnf
    subst e
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hm := hmW.min hl
    obtain ⟨go, hg1, hg2⟩ := h1 a.s c.s (hs.rep.mem.2 ⟨a, ha, rfl⟩) (hs.rep.mem.2 ⟨c, hc, rfl⟩) hne (by rw [← hcod a ha]; exact har) (by rw [← hcod c hc]; exact hcr)
    have hsz := (hb.min hl1 hm.2).size
    refine nodeH_bi X hs hm (by omega) rfl rfl (by omega) hb hl1 hKP ?_ ?_ hg1
    · intro a' c' oa oc ka kc kb x1 y1 e hh
      rw [e] at hh ⊢
      exact mid1_false hnf hh
    · intro h xs hgo hxs a' c' ha' hc' hav hcv ea ec eax ecy
      refine hg2 h xs hgo a' c' ha' hc' ?_ ?_ eax ecy
      · have : a'.w = a := hs.rep.inj hav ha (by rw [← ea, eax])
        rw [this]; exact har
      · have : c'.w = c := hs.rep.inj hcv hc (by rw [← ec, ecy])
        rw [this]; exact hcr
  · intro z' r S1 hf hst hcod' k0 hk0 hl1 hmW1 hFb1
    exact hF _ _ _ _ _ hf hst hcod' k0 hk0 hl1 hmW1 hFb1
theorem look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {fm fh K : ℕ} {Fs : Set ℕ}
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs) : ∀ fuel : ℕ, P1 R P l m T Fs (look1 l m g np fm fh K fuel) := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW hFb
    change (Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (k + 1 - t) v (fun κ κ2 => Bool.rec (motive := fun _ => Bool) (mv (look l m g np k) l m g np k t z v κ κ2) true
        (st (k - 1) fun k1 => node1 (look1 l m g np fm fh K fuel k1 t) (pos t) l m g np fm fh (k - t) (len v) z v κ κ2 pairsS))) true (Nat.ble (len v) 1) : Bool) = false at h
    rw [bR, pos_eq, len_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin := hmW.min hl
      obtain ⟨κ, κ2, hFy, hKP⟩ := tsn_sound X hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_f hy
      rw [st_eq] at hy1
      refine one_sound X hR hR2 hfb ih hs hcod hlen hk hl hmW hFb hKP hy2 fun x y hx hy hne hxr hyr => ⟨pairsS, hy1, fun h xs hp a c ha hc har hcr ea ec => ?_⟩
      exact pairs_any hp (fs_mem ha har) (fs_mem hc hcr) (fun e => hne (by rw [← ea, ← ec, e]))
theorem topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {fm fh K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)} {Fs : Set ℕ}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g np fm fh K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : MW R m T k' S)
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs) (hFb : MF R m T k' Fs S) : False := by
  simp only [mFull, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hM
  obtain ⟨hM1, p0, hp0, hp1⟩ := hM
  have hmin := hmW.min hl
  obtain ⟨κ, κ2, hFy, hKP⟩ := tsn_sound X hs hmin hk
  have un : ∀ p ∈ M, 2 ≤ v.length ∧ (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g np k) l m g np k t z v κ κ2) (Nat.beq p.2 1)) true
      (st (k - 1) fun k1 => node1 (look1 l m g np fm fh K K k1 t) (pos' t) l m g np fm fh (k - t) v.length z v κ κ2 (fun h xs => pairsC p.1 h (fs xs))) : Bool) = false := by
    intro p hp
    have h := h p hp
    change (Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (k + 1 - t) v (fun κ κ2 =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g np k) l m g np k t z v κ κ2) (Nat.beq p.2 1)) true
      (st (k - 1) fun k1 => node1 (look1 l m g np fm fh K K k1 t) (pos t) l m g np fm fh (k - t) (len v) z v κ κ2 (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble (len v) 1) : Bool) = false at h
    rw [bR, pos_eq, len_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      refine ⟨?_, (hFy _).symm.trans h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  refine one_sound X hR hR2 hfb (look1_sound X hR hR2 (K := K) hfb K) hs hcod (un p0 hp0).1 hk hl hmW hFb hKP (fu := k) ?_ ?_
  · have := (or_f (un p0 hp0).2).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro x y hx hy hne hxr hyr
    obtain ⟨p, hpM, hpb⟩ := hM1 ((x + y) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    have h3 := (or_f (un p hpM).2).1
    rw [st_eq] at h3
    refine ⟨_, h3, fun h xs hp a c ha hc har hcr ea ec => ?_⟩
    exact pairsC_any hp (fs_mem ha har) (fs_mem hc hcr) (fun e => hne (by rw [← ea, ← ec, e])) (by rw [ea, ec]; exact hpb)
end sound
theorem topC_ok : TopOk topC := by
  intro P l m g np T X R hR hR2 fm fh K k t z v S M Fs hM h hs hcod k' hk hl hmW hfb hFb
  exact topC_sound X hR hR2 hM h hs hcod hk hl hmW hfb hFb
abbrev TopT := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool
noncomputable def okR (top : TopT) (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (x : ℕ × ℕ) : Bool :=
  pOk x.1 Q && Nat.ble x.2 31 && (Q.any (fun y => Nat.ble x.2 y.2) || !chkT top E Q (1, 0) x.1 (x.2 - 1) [0] FF 1)
def pr (T : List (ℕ × ℕ)) (c : ℕ) : List (ℕ × ℕ) := T.filter (fun y => Nat.beq (Nat.land c y.1) c && !Nat.beq c y.1)
def pick (T : List (ℕ × ℕ)) (cs : List ℕ) : List (ℕ × ℕ) := cs.filterMap (fun c => T.find? (fun x => Nat.beq x.1 c))
lemma pick_sub {T : List (ℕ × ℕ)} {cs : List ℕ} : ∀ x ∈ pick T cs, x ∈ T := by
  intro x hx
  simp only [pick, List.mem_filterMap] at hx
  obtain ⟨c, _, h⟩ := hx
  exact List.mem_of_find?_eq_some h
noncomputable def okU (top : TopT) (T : List (ℕ × ℕ)) (r : (ℕ × ℕ) × List ℕ) : Bool := okR top [] (pick T r.2) r.1
noncomputable def okO (top : TopT) (e : Bool × ℕ × ℕ) (own : List ℕ) (raw : List (ℕ × ℕ)) (r : (ℕ × ℕ) × List ℕ) : Bool :=
  raw.all (fun x => !Nat.beq x.1 r.1.1 || Nat.beq x.2 r.1.2) && okR top [e] (tabE e own (pick raw r.2)) r.1
def inC (cs : List ℕ) (x : ℕ × ℕ) : Bool := cs.any (fun c => Nat.beq c x.1)
section
variable {top : TopT} (htop : TopOk top)
include htop
lemma okR_imp {E : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {x : ℕ × ℕ} (hE : E = [] ∨ ∃ e, E = [e] ∧ e.2.1 < 12 ∧ e.2.2 < 12 ∧ Imp [] x.1 x.2)
    (h : okR top E Q x = true) (hI : ∀ y ∈ Q, Imp E y.1 y.2) : Imp E x.1 x.2 := by
  simp only [okR, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true'] at h
  have hx15 := Nat.le_of_ble_eq_true h.1.2
  refine imp_FK htop (F := []) (fb := (1, 0)) (K := x.2 - 1) (by omega) (by omega) hE h.1.1 hI (Or.inl rfl) (by simp) (h.2.imp (fun ⟨y, hy, hy2⟩ => ⟨y, hy, Nat.le_of_ble_eq_true hy2⟩) fun h t ht hz =>
    ⟨[(FF, 1)], ffull, fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp
  exact chkT_chk h t (by simp [hz])
end
lemma okLayer {T : List (ℕ × ℕ)} {rs : List ((ℕ × ℕ) × List ℕ)}
    (h : rs.all (okU topC T) = true) (hT : ∀ x ∈ T, Imp [] x.1 x.2) :
    ∀ x ∈ rs.map Prod.fst, Imp [] x.1 x.2 := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  exact okR_imp topC_ok (Or.inl rfl) (List.all_eq_true.1 h r hr) (fun y hy => hT y (pick_sub y hy))
lemma appendImp {T U : List (ℕ × ℕ)} (ht : ∀ x ∈ T, Imp [] x.1 x.2)
    (hu : ∀ x ∈ U, Imp [] x.1 x.2) : ∀ x ∈ T ++ U, Imp [] x.1 x.2 := by
  intro x hx
  exact (List.mem_append.mp hx).elim (ht x) (hu x)
def rho (p : List ℕ) (w : ℕ) : ℕ := p.foldr (fun i x => 2 * x + (w.testBit i).toNat) 0
lemma rho_cons (a : ℕ) (p : List ℕ) (w : ℕ) : rho (a :: p) w = 2 * rho p w + (w.testBit a).toNat := rfl
lemma rho_bit (p : List ℕ) (w i : ℕ) : (rho p w).testBit i = (decide (i < p.length) && w.testBit (p.getD i 0)) := by
  induction p generalizing i with
  | nil => simp [rho]
  | cons a p ih =>
    rw [rho_cons]
    have hb : (w.testBit a).toNat ≤ 1 := by cases w.testBit a <;> simp
    cases i with
    | zero =>
      rw [Nat.testBit_zero]
      have : (2 * rho p w + (w.testBit a).toNat) % 2 = (w.testBit a).toNat := by omega
      rw [this]
      cases hh : w.testBit a <;> simp [hh]
    | succ j =>
      rw [Nat.testBit_succ]
      have : (2 * rho p w + (w.testBit a).toNat) / 2 = rho p w := by omega
      rw [this, ih]
      simp
lemma rho_zero (p : List ℕ) : rho p 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [rho_bit]; simp
lemma rho_or (p : List ℕ) (a b : ℕ) : rho p (a ||| b) = rho p a ||| rho p b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, rho_bit, rho_bit, rho_bit, Nat.testBit_or]
  cases decide (i < p.length) <;> simp
lemma rho_and (p : List ℕ) (a b : ℕ) : rho p (a &&& b) = rho p a &&& rho p b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, rho_bit, rho_bit, rho_bit, Nat.testBit_and]
  cases decide (i < p.length) <;> simp
lemma rho_xor (p : List ℕ) (a b : ℕ) : rho p (a ^^^ b) = rho p a ^^^ rho p b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, rho_bit, rho_bit, rho_bit, Nat.testBit_xor]
  cases decide (i < p.length) <;> simp
lemma rho_op (p : List ℕ) (d : Bool) (a b : ℕ) : rho p (op d a b) = op d (rho p a) (rho p b) := by
  cases d <;> simp [op, rho_or, rho_and]
theorem Sol.pull {m m' T q : ℕ} {S : Set ℕ} (p : List ℕ)
    (h : Sol Z0 m T q S) : Sol Z0 m' (rho p T) q (rho p '' S) := by
  induction h with
  | done h => exact .done (Set.mem_image_of_mem _ h)
  | bi h1 h2 _ _ ih =>
    rw [Set.image_insert_eq, rho_op] at ih
    exact .bi (Set.mem_image_of_mem _ h1) (Set.mem_image_of_mem _ h2) (al0 _ _ _) ih
def readRoute (code : ℕ) : List ℕ :=
  let first := (List.range NN).map fun i => (code >>> (13*i)) &&& 8191
  first ++ first.map (· + NN)
def factors := (List.range 24).map fun i => mz (2^i)
def movedFactors (g : List ℕ) := g.map fun i => mz (2^i)
def combine (z : ℕ) (baseV : ℕ) : List ℕ → ℕ
  | [] => baseV
  | a :: as => bif z.testBit 0 then a &&& combine (z/2) baseV as else combine (z/2) baseV as
lemma rho_combine (p : List ℕ) (baseV z : ℕ) (xs : List ℕ) :
    rho p (combine z baseV xs) = combine z (rho p baseV) (xs.map (rho p)) := by
  induction xs generalizing z with
  | nil => rfl
  | cons a xs ih =>
    cases h : z.testBit 0 <;> simp [combine,h,rho_and,ih]
structure SymData (p g : List ℕ) : Prop where
  mask : rho p (mz 0) = mz 0
  target : rho p TG = TG
  pins : factors.map (rho p) = movedFactors g
  raw : ∀ a ∈ rawP, rho p a ∈ rawP
def symCheck (p g : List ℕ) :=
  Nat.beq (rho p (mz 0)) (mz 0) && Nat.beq (rho p TG) TG &&
  decide (factors.map (rho p) = movedFactors g) &&
  rawP.all (fun a => rawP.contains (rho p a))
lemma symCheck_sound {p g : List ℕ} (h : symCheck p g = true) : SymData p g := by
  simp only [symCheck,Bool.and_eq_true,List.all_eq_true] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1.1.1,Nat.eq_of_beq_eq_true h.1.1.2,of_decide_eq_true h.1.2,?_⟩
  intro a ha
  simpa using h.2 a ha
def passCheck (g : List ℕ) (S : List (ℕ × ℕ)) (r : (ℕ × ℕ) × ℕ) :=
  S.contains (r.2,r.1.2) && Nat.beq (mz r.1.1) (combine r.1.1 (mz 0) factors) &&
  Nat.beq (combine r.1.1 (mz 0) (movedFactors g)) (mz r.2)
lemma pass_sound {p g : List ℕ} {S : List (ℕ × ℕ)} (hSym : SymData p g) (hS : ∀ x ∈ S, Imp [] x.1 x.2)
    {r : (ℕ × ℕ) × ℕ} (hr : passCheck g S r = true) : Imp [] r.1.1 r.1.2 := by
  simp only [passCheck,Bool.and_eq_true] at hr
  have hm : rho p (mz r.1.1) = mz r.2 := by
    rw [Nat.eq_of_beq_eq_true hr.1.2,rho_combine,hSym.mask,hSym.pins]
    exact Nat.eq_of_beq_eq_true hr.2
  have ht : rho p (tz r.1.1) = tz r.2 := by
    change rho p (TG &&& mz r.1.1) = TG &&& mz r.2
    rw [rho_and,hSym.target,hm]
  intro k hk hs
  have hprev : (r.2,r.1.2) ∈ S := by simpa using hr.1.1
  apply hS (r.2,r.1.2) hprev k hk
  have hp := hs.pull (m' := mz r.2) p
  rw [ht] at hp
  refine hp.mono le_rfl ?_
  rintro x ⟨y,hy,rfl⟩
  rcases hy with ⟨w,hw,rfl⟩ | hy
  · have hraw : w ∈ rawP := by simpa [rawL] using hw
    rw [rho_and,hm]
    exact Or.inl ⟨rho p w,by simpa [rawL] using hSym.raw w hraw,rfl⟩
  · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy
    rcases hy with h0 | h0
    · rw [h0,rho_zero]; exact Or.inr (Set.mem_insert _ _)
    · rw [h0,hm]; exact Or.inr (Set.mem_insert_of_mem _ rfl)
lemma passLayer {p g : List ℕ} {S : List (ℕ × ℕ)} {rs : List ((ℕ × ℕ) × ℕ)}
    (hd : SymData p g) (h : rs.all (passCheck g S) = true) (hS : ∀ x ∈ S, Imp [] x.1 x.2) :
    ∀ x ∈ rs.map Prod.fst, Imp [] x.1 x.2 := by
  intro x hx
  obtain ⟨r,hr,rfl⟩ := List.mem_map.1 hx
  exact pass_sound hd hS (List.all_eq_true.1 h r hr)
def symP0 := readRoute 0x2d48b645d22a915c8b2453227914489a445220910c89644722490d486643921d90dc87e43c05a900c80a3fd1ff90047f40b520f908483241b20e905816a3e71f48f847c63e51ef02d485a42f21390a485642405a8fd47ee3ef1f88fcc7d80b5208904c81640d207902016a3d91ed8f4c7aa3d71e802d463631d18a8c5c63231205a8b8c5ca2dd16f8b845b40b517f8c045f22fb17e8bd816a2c91628b1c5862bd15f8b045762b715c8ad455a2a91558acc55e2b114e8a6c5422a314f8a9c5480b514b8a4452629514702d461a30f1838c2461630405a8b545ae2cf1688b4c5980b51788bcc5d62ed1778ba016a28b1438a2450a27f1408a0c4f80b513c89cc4ea27713802d47963cd1e28f1c7923c205a8d8c6ca35d1af8d846b40b51d78ec47523ab1d68e9816a3471a48d0468634519f02d477a3bf1db8ee47763b405a8d546ae34f1a88d4c6980b51d18e7c74239d1cb8e647363951c88e4c71e3871c18e1471a3891c58ddc6ea37b1be8de470237e05a8dc46d636d1b78da016a33b19b8ce466a32f1988ccc6580b51948c8c64a32719002d44d626d13389a44c626513089744be25b129893c4a225912a895c486241123892448a24d12502d447623d11b88e44680b50ce867c33219b0ca865c3240b50c6863c31218b0c302d4426215107884441620d10402d44062050ff88043f80b50b2859c2c21630af856c2ba1590aa855c2a614b0a385242a214d0a784ec27213f0a084f428a14205a84d426213309784ac25a12805a848c24a12108e847c2340b508b844c22a11005a88bc46222b116889c45222405a887c44221b10e886016a1810c185f42fe1790bd85d816a1710b985b42de16a05a87dc3f21f30fa87c43da1ef0f5879c3d21e50ee87643b61e30ef878439a1cb0e8874c39e1d70ea02d438e1c30e2870437a1bf0dd02d436a1b70d986bc3621ac05a86a434a1a70d102d421610d082841c21210108183fc1f60fd07c83c41da0ef07b83cc1ea0e106f83941ce0e307583a016a0d906d834c1aa0d706783441980b505482ac14a0a7050828c13c0b504d825c13209304a824016a0c7064830c18a0bf06082f016a0b905a82dc1620b305702d411608d04382241080b503f82040f80b503b81e40e207303a81b816a0030027ff3ffe000ffd02d40ba05902d815c0aa051029812c09a04f02180fc082049022811c06603101b80e406a03d01d02d405602d012809c0500b4ff47f9bfc5fe4fee7f7bfc00b4feb7f63fa1fd2fea02d40d206b03181940ce06005a7fd3fedfeeff87fcbfd80b5010807c03601d00a805c0300b5007804401200b00602d3f99fcafe37f23f81fc2fe202d3f75fbcfda7edbf700b4ee97753b99dceee87728169d10e89742ba19d0ee8402d3b11d86ec17613af9d7eec002d3aedd78eb875cbae80b4e73738b9c9ce0e6f73539adcd2e66733b9a1ccae6373239b9cd8e6d72eb971cbee6072f3989cc205a72d3961cb2e5772a3955cac05a7293945ca0e4d727393c0b4e4b7243925c9405a771bb85dc4ee076fbb6ddb2eda76bbb61daced5769bb51dbcedc76ebb35d98ecf7683b39da4ed102d3b25d94ec77643b180b4e82740ba01cfce7f73e39f5cf605a73c39e5cece7773a8169d6ceb475abacdd64ead7573aadd58ea97553aa1d4cea7758babdd60ea074fba89d46ea1752ba900b4e9d74e3a6dd32e9a74bba600b4e9574a3a49d26e907488169d1ae8e745ba300b4e467223915c86e4271e38f5c7ce3b71c38e5c74e3671bb905c7ee4071838bdc64e33718b8d5c6805a716b8b1c52e2a715b8a1c4ce2702d3891c46e217113881c3ce1f02d3871c34e1b70cb85dc3005a70ab851c24e13708b83dc2005a706b831c16e0a70438240b4e06702b811c04e0302d3801bfcdff02d3f5dfb0fd47eabf59fa605a7c7be35f1cf8c7c5be05efef807c53e21f12f867c3be15f08f827c1bde5ef0f7b7be3de9efcf7d02d3dd5eecf737ba3dc80b4fca7e4bf1df90fc47e2bf180b4fc17e13ef9f7efc002d3d85ebef607af3d75ea6f517a93d6deb8f597ad3d5deb0f567aa3d55e96f4a7a6bd39e98f507a78169e90f477a33d11e8af427a18169e80f3f79ebcf9e76f3c02d3ce1e72f3679b8169fa0fd17e6bf39f9efcc02d3dc1edef6e7b63db5ed4f6b7b48169eccf677b23d95ec605a7de3ee9f76fb97dc3eb9f58fad7db3eddf6afb27d9bed1f62faf7d83e99f4afa87d4be9df56faa02d3e8df42fa27d03e75f3cf9f02d3e6df34f997cb3e5df3005a7ca3e45f24f9302d3cd1e64f33798bcc1e4cf24792bcb5e5cf2f7963ca5e54f2b793bca1e3cf1d7903c85e3ef237910169e36f1a78bbc61e32f1678a3c540b4f12788bc3de20f0e7863c340b4f0a7843c25e0ef057830169e06f027803c05dfeefd77f0169df6efa77cbbe1decef702d3bd1de6ef27783bc40b4eee7763bb40b4dfb6fe37e5bf4df76fc37d80b4df36fa37c5be4df002d3465a2ed1868b3445a20d0e687b455a28d12689b435a12d0a684341da06d02682b419a08d0c68581699eecf867ab3d99e8cf302d34019fecfe67e33f59f6cfa02d33c19e2cef6770169b82dbf6e036f9b72db86db36ddb7adbc6dd36edb6adb36da36c5b64dab6d536b5b5cdac6d836bc0b4da76d43695b4cda36d20169b42da06cf367db38d9d02d3665b34d976cc0169944ca0650b27d934c9964bb26193cc9d64db271926c96647b23591cc8c648b249920c9564a0169914c88644b21990ec8564201698e4c70638b1b98dec6d63601698d2c6a633b1a18ccc6502d3209900c8163f31fd8fac7c02d31e98f0c7963b31dd8eac7402d318d8c4c60630b17d8bc05a62e31698b6c5962c01698acc5462ab1498a6c51628016989cc4c626b12d894c4902d30e9870c3961bb0d986a05a61930cd862c3002d311d88cc44622b10d88405a62030fd87cc3d61e016985cc2d61630ac0b4c296140169bdcdec6f6b7adbccde56f1b791bd4de96f3b7a1bc4dd86ebb781bc2ddf6ef3769bb6dd96eeb7700b4dce6e6b731b94dcb6e4b7200b4dd46eab749ba6dd16e80169b8adc66e2370c0b4cec67533ad9d2ce4671b3859c4ce8673b3959cccdd66b33559c0cda66cb3719b6cd866bb37d9bc05a65db2e5974cb865b32dd96a05a665b325994cc7664331598ccc402d32b5958cab654b2a995005a669b3459a4cd0667333d99a05a65932cd960cb16578169984cc166032f997ecbd02d329594cca402d3655b26d946c93635b18d8a6c5b645b20d8e6c7b621b00d7f6c4b609b06d816c3b615b0cd8402d35f5af6d7c6bcb5e9af0d7702d3599ac8d656b1358dac2d6002d3579ab8d5d6ad356dab2d5802d35d5ae6d746b8b5c9ae0d6f02d35b1adad6a6b5b5a5ad005a6ab3555aa6d546a935440b4d4f6a6b539a98d4b02d3525a8ed486a2b519a88d4302d3505a7ed4069f34f5a7805a69734b5a56d2c69534a40b4d276933495a48d2302d34e9a70d3969bb4d9a6a05a69934cda62d3002d3485a40d1f68f0169a38d1b02d3099848c25611b07983ac1b60e3089842c1f610304d824c1160bb05582cc1460d306583005a607b03581cc0a605b0300b4bde5ee2f757b2bda5ed81697aebd55eb2f497a6bd402d2fe97f0bf95faafd97ee05a5f9afc57e4bee5f7afc00b4bc35e0af0977cbbf5e00169778bba5ddaedd770bb902d302180cc07601b01180a05a600affd800bfc5feaff80b4bd05e72f3d796bcc5e68169790bc95e2af1978e05a5f62fa97d6be75f42fa40b4be55f1af917c0be15f1016976abb35da2ec1762bb202d2eb575cbaa5d5aeb00b4b465a22d15682b425a1816967eb3d59f2ce9676b3c02d2c49620b11586ac3961e05a585ac25614b06583ac200b4b2c5952cad64eb28594816964ab235922c81642b2202d2be55f0af557b2bdc0b4af35792bbd5e0af102d2ce166cb3759a2cd40b4b325982cc565cb2f02d2c11604b035802c040b4afd57f2bed5f805a58f2c7163ab1a58d8169630b1658bac5162a05a576abb15d4aeb02d2ba15ccae702d2ea174cba75d1ae9174a05a5d0ae7d740b9c5ceae780b4b725b82dc56dcb6f02d2db16d4b6b5b42da40b4b8c5c52e2d70eb885c4816970ab835c22e01702b8202d2d6d6b2b5a5abad600b4b555a9ad516a2b5202d2e69730b995caae5972e05a5c9ae45724b8e5c7ae400b4b665b22d956c4b6302d2d7d6c0b5d5af01696fcb7d5bd2ded6f805a5bc2ddd6e8b755bb016969eb4e5a62d340b4b4a5a42d240b4ae45712b8d5beae057081695baadb56e2b655b405a55b2ad156aab25598169560aae557aab40b4acc5652b2d58eac8564816958aac35622b0558405a551aa89540aa102d2a7953aa9c02d2b5d5aaad6569ab500b4ad1567ab4159c05a555aaa5554aa802d2a9554c05a55faaf9578abd02d2ae9572ab802d2a6953205a54b2a5d52aa91547aa41528a92549aa25510a8b5462a2951ca8d02d48b40b522e02d48a80b522b02d48b00b522902d48040b520202d47f80b51ff02d48000b51fd02d483c0b521002d48300b520d02d48380b520b817016a3e716402d47d00b51f002d47c40b51f202d47bdfe805a90b016a42e05a909816a42805a90a816a42405a8fd016a3f605a8fb816a3f005a8fc816a3ec05a904016a4131d102d48140b520602d481c0b5204808016a3d914502d47b633a05a8f4816a3d405a8f5816a3d0fe602d46340b518e02d46280b518b89a816a31805a8c4816a2e316202d45c80b516e02d45be19c05a8b8016a2da05a8bfc58c0b518002d45f00b517d884816a2fc05a8bdbb100b516102d45780b515f859016a2c005a8aeb9cc0b514b02d45200b5149848816a29405a8a3b9480b518602d461c0b5183771816a30911702d46140b518202d45aa28605a8b5816a2cee8202d45a218005a8b4816a2cc05a8bc45100b50fb02d45e61c605a75b016a2eae9d02d45da1b405a8bb816a2e8e9502d42140b51428360169c8c05a89fb8b40b514082a016a28205a89f38900b506302d44f20b805a70a816a272e0d02d44ea08a05a89d816a270e0602d47940b51e602d47880b51e389b016a3c805a8f0816a36205a8d9016a35c05a8d7c33c0b51b07c7816a35a05a8eb816a3b11cf02d47500b51d5885016a3ac05a8e9bf280b50b302d468e13405a8d2466c0b51a002d468612405a7b0816a344f4802d467de8005a8ef016a3bf1d002d476c0b51dc88c016a3ba05a8ed016a35405a8d5c6700b51a702d46a218205a8d4bdc00b51a602d47380b51b802d472c0b51cc87e016a39a05a8e53ef00b51b502d46da1b605a8db816a368f9b02d42180b519a836816a0aa05a8ca41340b519702d46620c805a79a016a332f1b02d4659e2405a8c8816a32504602d3c0c0b519377d816a320ef402d44cc0b511d02d44d00b511e02d44c40b511b02d44c80b513002d44700b511a02d433216005a86342600b50cd02d431c0b50ca02d43100b50cb68c816a19205a862b4000b50c302d441e16205a880c2640b510887c816a2050e102d44140b50ff02d44180b51046e0816a20005a87f36840b50af841016a12f06902d42b40b509502d32880b50ae645016a158c7202d32080b509663d016a128c6302d42420c205a845c1680b508e02d42240b4c5602d423d89c05a846b0e80b4c4702d422988005a84430b80b511502d443c0b511687d016a2210e202d444dbdc05a886b7380b511402d44480b510e02d44300b508302d41a80b50be829016a17104b02d42fe0c405a85cc16c0b4cec02d42f197605a665816a16ccad02d42f59a605a85d816a16ecc202d42d40b50f8842016a1c106b02d43660a605a86a41300b4d9502d43d9afa05a6b3016a1bcd5e02d43dc0b50f56ba816a1be05a86eb5580b4d4902d435da8205a697016a1a4d2702d43600b50d669d016a1a605a868b4840b4c2602d303c0b4bde02d42017ae05a5fd01697e605a5e1816a0cebbc02d30200b5081600816a0febd002d2fb00b50685f2816a0ccbb502d2d180b4b3f02d2c480b5050585816965805a59281695f205a824abcc0b4b3802d414566405a827ac100b4b1e02d412963005a8242bb40b4ba802d2e840b4b7202d417d6d805a5c6016970a05a5ad816a0b0b5502d2e680b50605c9816a0bcb6602d2df80b50595bc016a0aeb4f02d2b900b4add02d2ad80b5043558016959805a562816954605a913c56e39112e85543ce0fb03f81639c5dc2eb47223e35ebefba799345db7eca06f633a9b26c2454f2a580b4ad702d41115a205a8212aac0b4abf02d48a22b91c9897c2ae1e907e82040b5ce4ee275ab915f1cf607ddbccda30dc0650b7b59d6d94612aae952e05a913456a38f12d854c3ca0f903e815b9c1dc0eb3721be31ebcfb9798b459b7cc9f6f5b3a5b24c2354d2a540b503b02d40f00b503802d40e40b503a02d40de05405a800816a00405a7ff0169ffe05a8003e2c0b4ffd7f9816a05005a80a816a05205a80b016a04a05a809016a04c05a809816a04e05a80a0169fe2e6f02d3fadcb405a7f90169fd805a7f70169fd005a7f78169fd205a7f83d740b4fea7a3816a06805a81a816a062edf02d40c80b503302d40c201e05a7fd0169ff605a7fbba040b4ff802d3fe5ede05a7fb3f940b500d02d401c0b500e7dc016a010fa302d4029d6405a8023a700b500b02d40140b500c02d40180b4e4202d38b00b4fe37118169fbae1c02d3cc00b4f1a02d3f91e2205a7ef3c280b4fe070a0169fb4e0c02d3f840b4fdb02d3f89e0405a7ee3be80b4ee902d3ba80b4ee676d8169dcedfb02d3ba00b4ee57618169cd405a74439600b4e8902d3a15d0005a6888169d0ccf702d3a1d9fe05a74239440b4ec17358169d76e5902d3b080b4ebc02d3af9d5a05a75c3a6c0b4ebf6dc8169d72da702d3b000b4eba02d39a40b4e5702d3999c7805a72a38a40b4c9a02d32200b4e676380169caac6902d39a190005a72b31e00b4e5002d392c0b4e4d7090169c90e0b02d31500b4c4c02d393987005a724b0c80b4e4f6230169c94c3f02d3b640b4ec902d3b680b4eca02d3b5dbcc05a76c0169daceae02d3b1dba805a7640169d8ce9402d38f40b4e7e7150169c4205a73c38680b4e7f02d39e40b4ce402d39f197205a73eb3240b4e7b70981699a205a73b32c80b4e776608169ceae0502d3aadc7c05a74cb8ac0b4e927110169d1ae1b02d36340b4d7b02d3ab1ac805a74d35700b4d7302d35b00b4e936aa8169d1cd4f02d3aa5a8e05a74bb4fc0b4eaa02d3a600b4e9069c0169d16d3202d3a440b4e8c02d30780b4c0d02d2f700b4bd502d2fe00b4bf102d38ed78205a7142ee80b4c0602d2ffc0b4bce02d2f200b4bea02d2f8c0b4e205d98169c32bad02d2d100b4b3d02d38e162005a7132c240b4e395950169c4eb2302d2cd80b4b3002d387960405a70babf40b4e1f58e0169c30b1602d2e980b4b9f02d2dc00b4b6a02d2e280b4b8302d38456b205a7052d4c0b4b9802d2e440b4b6402d2d7c0b4b7d02d2ddc0b4e045a7016a4451568e1c4a614b0ee83c4085ccaed575438e9c00f817a9beb9e4cd106dc3265bcace36c63075694a9102d2b880b4adb02d383d56805a7042ab80b4e105650169c12ac302d2b540b4acf02d380955205a9104552383127851c3b20ed01f731bb4dd4ce366ff3dfdea2fac7923439b6cc976f1b385b14c1b552aa3c0b4e0355f016a4431558e144a21490ed83bc081cc8ed4753b8ddbfef807a93eb5e4ad0f6dbb261bc8ce26c5b071572a9002d3f5c0b4fd802d3f500b4fd56fe0169facf8a02d3f4df9205a7c40169eea05a7c48169eec05a7c30169ee605a7c3b4540b4f7467c0169f0af5b02d3dc9e7e05a7e38169f8205a7e43ed80b4fc27d08169f8805a7df0169f8adbd02d3efdb5005a7e33d700b4fc07a3016993c05a64481698e205a6350169eb2c8102d3d118f205a79eb1880b4f3862e0169eb4f2d02d3d15e2e05a79f3c3c0b4f397840169eae05a7a10169e7605a79b0169eb0c5502d3d0d89a05a79e30e40b4f376198169fa005a7db8169fa2fa202d37a80b4fcd6e68169f9cdd502d3f3dedc05a7e63e680b4f6c02d3d980b4f2e02d3db5e3005a7880169ecef0902d33a00b4cba02d3da999405a7b232b00b4f6b6690169ecacb302d3da5e0005a7b1bbcc0b4fb502d3e800b4f9902d3e500b4d9102d35f00b4fb26b28169f3ad5d02d3ecdae805a7cf35b40b4fb47978169f3ef1902d35200b4d4002d3e59a5a05a7c8b4980b4f9769c8169f24d3302d3e61e0205a7c9bbe40b4c2202d30380b4bdd02d2f580b4bf902d2fc80b4bc202d2eec0b4c0702d30000b4bcf02d2f240b4f2c5f58169e2cbe402d3c3976805a783aeb80b4b4502d2cf80b4b1102d2c280b4b2b02d2c900b4af802d2bc80b4b3702d2cc40b4b0302d2bf80b4eff58e8169df0b1702d3bc95d805a912c56638d12c85443c60f70247373b79d62e417c23d59f62f297773451b78c9d6f4b39db20c215742a500b4ba702d2e800b4b7102d2dac0b4f2a5c58169e28b8402d3c316b405a782ad500b4f2b5cc8169e2ab9202d3c356ca05a7832d800b4ae302d2b700b4ab502d2abc0b4efd5658169decac402d3bc154405a911c55e38912a85343be0f30227363b71d5ee3f7c13d51f5ef277763449b74c9b6f3b395b1cc1f54eaa480b4efe56b0169deead002d3bc555405a912456238b12b853c3c20f5023736bb75d60e407c1bd55f60f28776b44db76c9c6f43399b1ec205532a4c0b4df902d37cc0b4dfa02d37d00b4df76f10169be2dcc02d37e1a1a05a6fb36d40b4df267f0169be0da002d324c0b4d0964301698dc05a67ab19c0b4c7e02d33f18ec05a63001699e0c5a02d34280b4cf602d33f40b4cf102d34219ba05a67a32e00b4cfb66381699decab02d341d8a405a679b0dc0b4cfa62201699dcc2d02d32580b4c8702d36cd8de05a6d2b1a00b4c7f02d31dc0b4d9e6308169b32c5b02d36200b4d7902d35880b4d5a02d36d1ae205a6d335a80b4d9f6a98169b34d4d02d36c5a8a05a6d1b4f80b4d9c6958169b2ed2502d36c98a605a6d2312c0b4d9d6228169b30c3e02d304c0b4c0a02d2f640b4bd202d2fd40b4bee02d2ef80b4bb702d323d80605a642aff00b4c6d5e581698ccbc502d31f57ce05a63aaf800b4c5f5d801698b2baa02d323568205a6422ce80b4c6c58681698cab0602d31f164e05a63a2c800b4c5e57a81698b0aef02d2e8c0b4b9c02d2db80b4b6802d2e1c0b4b8002d2d5c0b4b5102d314572a05a6252e380b4c365b10169862b5d02d310d6f405a61eadd00b4c2c5a6016a43514e8ddc48613b0e68384065cbaecd75038c1ef2f4b7d33c79a06dab64730a5bb0cd66c03049690a8902d31415be05a624ab640b4c355590169860aad02d310958e05a61e2b040b4c2b550016a43314d8dd44821390e5837c061cb8ecc74fb8bdef0f4a7d2bc75a04daa64630a1baecd56bfb045538a8802d37800b4dca02d37480b4dc502d36240b4de16bd0169ac605a6e5b56c0b4d7202d374dad605a6aa0169b8cd4e02d377d9c005a6ef35180b4dc96640169b90d2c02d37459a005a6e834dc0b4dc46600169b86d2002d305c0b4c0b02d2f680b4bd302d2fd80b4bef02d2efc0b4bb802d30100b4bfd02d2f300b4bc602d2fa00b4be102d2ec40b4bab02d2d080b4cda59d816961c05a65b2c1c0b4b2802d331564205a57b0169952af002d2cd00b4cce597016960005a6582bec0b4b1a02d32f962805a575016a4391508dec48e13f0e8839406dcbeecf75138c9ef6f4d7d43c81a0adad648b7699b2ca56c130555cca8b02d2e900b4cdc5ce81696de05a65bada40b4b8802d331970205a5ac0169954b5202d2e580b4ccf5c781696c605a658ad780b4b7b02d32fd6ea05a5a6816a43b1518df44921410e9839c071cc0ed0751b8cdef8f4e7d4bc85a0cdae649376d9b6ca66c1b059692a8c02d33615c005a65aaacc0b4cc45640169950aa102d33355a605a657aaa00b4cbd55e016a43714f8de448a13d0e7838c069cbcece750b8c5ef4f4c7d3bc7da08dac64837659aeca46c0b051532a8a02d30680b4c0c02d361d7b605a6bc2f500b4bf702d2fc00b4d615e00169ab2bb902d30140b4bfe02d35c179a05a6b4af1c0b4be902d2f880b4d525d90169a98bac02d2d0c0b4b3c02d351161e05a69eac200b4b2902d2c880b4d2a57b8169a48af102d2cd40b4b2f02d34d960205a698abf00b4b1b02d2c540b4d1f575816a43f1538e0449a1450eb83ac079cc4ed2752b8d5efcf507d5bc8da18db064ab7759bed8568e30655cea8e02d361974a05a6bbae780b4d605c48169ab0b8202d35bd72e05a6b42e400b4d515be0169a96b7602d350d5c205a69e2b680b4d295648169a46ac202d34d55a805a6982b380b4d1e55e816a43d1528dfc4961430ea83a4075cc2ed175238d1efaf4f7d53c89a16daf64a37719bcd8468db061570a8d01f80f807a03c01c80e007603a01a80d006e03601900cc06003101700bc05802d01500ac04c02701400a4048025010808004602200e807003e01e00d006c02c01700c0064028015009004c022010007003c00c009004001c01800b00500340080050008000006002
def symF0 : List ℕ := [0, 3, 2, 1, 5, 4, 8, 7, 6, 10, 9, 11, 12, 15, 14, 13, 17, 16, 20, 19, 18, 22, 21, 23]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma symValid0 : SymData symP0 symF0 := symCheck_sound (by decide +kernel)
def symP1 := readRoute 0x2d3099844c1e60d305d826c1d60b3049842c1960ab095838c18610306d848c1f608b08d82805a607b03981ac0c605b0280b4c08603b01980ac046018169802c005ffaff97fabfc02d2fe97f2bf85fbafd97ea05a5f9afc97e2bf05f7afb80b4bec5f5afa97d2be85f381697cabe45f1af897c2be002d2f797babdc5edaf697b205a5ebaf597aabd45e9af480b4bd05e7af3979abcc5e5816a10308083fc21a10b084841c20a0f107383841ee0eb07283f41de0e907a83b41f60f306f83e41c40b4bc95e42f1d78cbc502d2f0d784bc15e02efd77c05a5de2eed774bb95dc2edc0b4bb55da2ecd764bb15d8016a0d106783341b60d906b83541a40b4bae5d6aeb1756baa02d2ea174eba65d2ae9174605a5d0ae8173eb9e5ceae700b4b9a5ccae6172eb965ca8169726b925c8ae4171eb8e02d2e31716b8a5c4ae2170e05a5c2ae11706b825c0ae000b4f2c795bca9e68f30797bcb9e5af26790bc79e52f237903ccde4af227943c91e64f2778ebcc5e3e05a5bf2df56f8b7b5bd0169e2cf1578a3c6de34f1978c3c5c0b4b785bbadd96eab7402d361db0cd956c8b635b12d886c6360db00d906c2b609b28d8b6c2363db14d936c735fdb24d8102d2dc96e2b705b7adb80b4d786bbb5f5af8d7b6bd35e40b4b6c5b5ada96d2b6802d35c1aded756ba35cdae4d7102d2d996cab645b1ad880b50f887bc3da1eb0fc87dc3ea1f30ee874c39a1e30eb87443d21db0ea87843b21e70ef872c3ca1ce05a830417e0bd064831c18a0c205a6b4b5a1adad6c6b5b5a80b4b605afad796ba05a6b0b581accd656b2358dac405a5adad696b2b585ab8169ab2d586af3575ab8d5b6ad01696aab545a9ad496a205a7dabed1f66fb27de3ee1f6efb67d73ea5f4cfb17d5bea1f76fad7d53ec1f58fba7d7be95f72fa702d3c39e1af0c7893c45e20f0f02d3549aa2d566aab551aa605a5a7ad3969ab4c02d473a39b1cc8e5c72a3a31d08e7c70e37d1bb8e3470237b1c98e146fe38b1c18e447123751c78de016a3351998cc465e32d19d8ce466c0b50e086fc37a1bb0e387143840b505982c415e0b905b82d0169f40f9f7cf3e75f46fa27d08169e0ef06782bc29e12f0802d3531a96d4f6a735340b4b4a5a4ad200b4b465a2ad11686b425a0816967eb3e59eacf1676b3a02d323d932c926473235944c9e64d3259926c9d64ab245942c9864a327192eca064db23193ec9002d2ce166eb3659aacd00b4c856423229912c88643b2180b4b32598acc165eb2e02d2cb1656b2a594aca164e05a592ac91646b22590ac800b4c7d63e3209902c8063fb1f80b4b1e58eac71636b1a02d31d58e8c7a63cb1e18eec7602d2c6162eb1658aac500b4b12588ac4161eb0e5868169616b0a584ac2160eb0602d31b58d8c72638b1c18dec6e02d2c11606b02580ac000b50af852c28213b0ae856c2b21670b2858c2c21510a284fc2ae1490a1853c28e1550a684e42a613c05a828c14209f05582a414e0a405a63331958d4c69634319c0b4afe57eabf15f605a71db8e9c66e3071cb8e1c8ce4271f38f5c78e4171ab8c9c8ae3771a3901c6ce4471fb8bdc86e3102d2be55f0af757b2bd40b4e28713b899c5ae2c715b8a9c5205a579abc95e2af05778169cd2e657303975cd0e6773339cdcdee6b73539b9cc4e5f7393991cc2e6d731b9c5cd8e5c73839780b4e2070fb879c48e2371138840b4c5f62f318d8c4c6163001695daaec575aba80b51618ab454629d1608afc57a2bb1648b1c58a2b31538a845722ab1528ac45522b71578a6c56a29e05a8a1450628113f89f451628914302d425e12d09584a426a13309802d412a093048826c13209605a72bb959caae5472d3965cb005a70cb861c2ee1c70db8680b4c5962c31718b6c5a02d2ba15ceae602d2b915c6ae2570ab815be05a66e338d9b6cd666d339d9becd966c33b19d0ce467033759d6ce266f33999c2cea672b3559d2cd702d2b755b8adb56d2b640b4c5162831598aac54629b1480b4ad756b2b555a8ad302d3429a20d06681b425a28d0c682b421a0ed1968ab445a1ad18687b42da26d0e68bb449a04d16682016999ecce666b34d9a4cd16680169894c496273135898c4b02d2b455a0acf5670169598acb5652b25590ac702d331998acc4665b329992cc8663816958aac4561ab0958205a7ad3d4de9cf4b7acbd59ea0f4d7ac3d5dec2f5d7ae3d6dec0f527a7bd55ea2f5f7aa3d29ebcf4c02d3bfddfcefd781bc09e02f0002d310d884c47623311588805a55faaf957aabc02d3e25f02f7c7bcbe21f08f7e7bdbe1df0cf857c7be39f16f8a7c03df5f06f7f7c6be09ef0f8c7bd0169edaf6c7b5bda9ed2f707b7bdb80b4f457a23d0de84f487a3bd180b4ef877bbbd9df6efa77c81699facfc67db3e9a00cff67f016997ecbe65eb309982cc002d30f5878c4061fb0f80b4aba55caae00b4d446a1b525a90d476a335140b4ab655aaad1566ab202d3785bcaddb6ec3781bd2ddd6ed377dbdade46ee3779bdcdea6f33789bd0de36f6379dbaedeb6ec8169a7ad3c6a0b501a7ed3e02d32dd96ccb565db2e9972cb802d2ac155eaae5568169b68db86d736adb66dbc6d836b5b64dc06dbb6bdb62dc16deb6e5b6adbb6db36fdb74daa6df36b00b4d3669ab4e9a72d3869b816986cc3561d30e5870c3702d2aad554aa9554016a269129892448626712c893448e26512f894449626313089b44d625712789744aa24112d891016a22d11588a444e22511888b816a211107883441620910a884816a1b30d886bc35a1b70da02d43361990cb865432619f0ce02d42fe17d0bd85e42ee1830c002d424211f08e846c24a12205a822410e0850468228169bf4df96fc37ddbecdfc6fd8169ba6dd26e8b741baadd402d3699b4ada46d1b6a1b4e05a698b4c1a66d3202d33d99eacf4679b3e19ee05a658b2c195ecb36590169862c30619b0c80b4aa65528169d58ea8751ba81d56eb1752ba89d54eb5753ba91d52eb07533ad9d64eae756bad1d5ee9f759ba840b4e11708383dc2ae14709b8480b4d2a694b4b9a5ad2c6958169546aa2550aa800b4eda76abb41d9aed976f3b49d9eed87713b51da2ed776ebb4ddacee3770bb7ddb8edb7663b81d9c05a74d3a65d30e9774eba71d3605a73fb9f9cfae7c73dba09d02e8002d3829c12e08706b831c1605a6e5b729b92dc86e73735b9805a692348da4ed266928169954ca965432b5958cab02d2a7953aa9c02d40a604301c80cc0a204901e80dc09e05b02080ec09a04701f812c0b204501881740ae05501a02d403a01b00c805c02a02100f02d3fc9fe2ff07f7bfb9fe8ff302d3f91fc6fe27f0bf81fccfe502d3f21f8efc67e2bf11f94fc902d3e65f30f977cb3e6df3405a79f3cf5e78f3b7a03cfc0b4ef2778bbc1de8ef302d3b09d82ec075fbaf9d88ec302d3a4dd24e917483a55d2805a728393dc9ce4d72939440b4e04701b809c0ce0502d367db3cd9d6ce3685b4005a68fb479a42d2002d30b1856c2e6168169534a9902d48ba44521d90d48b644b21f90e48b245122190f48ae449220915489e447219914c89a43605a90bc85a42b214909c8480b5210907c83a41b20c905816a413208903c81a40b20402d480a4032008ffc7fa3fa05a8fdc7ea3f31f88fbc7d80b51f48f9c7ca3e31f08f7816a3db1ec8f5c7aa3d31e802d479a3cb1e48f1c78a3c205a8efc77a3bb1dc8edc7680b51d88ebc75a3ab1d48e9816a3711b78db46d636805a8d946c63611af8d746b40b51ab8d546a63511a78d3016a3491a38d1468634119f02d46523271928c8c6400b518e8c6c63231718a8c4816a30f1868c2c61230718202d46022ff17e8bec5f22f605a8bcc5e22ef1768bac5d00b51728b8c5c22df16e8b6816a2d716a8b4c5a22cf16602d452e2951498a4451c0b513c89dc4ea27313802d447a23b11c88dc4680b5110887c43a21b10c02d440a20310087fc3f80b50d4869c34a1a205a863c31a18b0c4861816a1730b885bc2da16a05a845c22a11308802d410207f03e02d40f207703a81cc0e206e05a81ac0d2067032818c0c00b501680ac05202701202d402200f006802c0100b5002800c001ffeffe7fe8169ff6ffa7fcbfe1feeff602d3fb1fd6fea7f4bfa00b4fde7eebf71fb6fda02d3f61faefd67eabf51fa605a7e8bf41f9efce7e6bf300b4fc27e0bf01f7efbe02d3e51f26f927c88169eecf757ba3dcdee405a7b3bd99ecaf647b18169e72f3879bbcd80b4eee776bbb00b4eea774bba1dceee67728169d94ec97643b1dd8c05a75e3aedd74eb975c0169d1ce8d7463a2c0b4e897443a1dd0ce857420169cf2e7873bb9d9cea05a725b929c92e4802d3801bfedfe02d37d1be6df26f8b7c00b4dc66e2b711b8605a6cd3665b30d9702d3471a3605a678b3c19decee02d329994aca402d30a585005a548aa31512a945472a2d52ea90546aa4d51ea965492a2152aa8a02d30980b4c2202d30780b4c1a02d305c0b4c1302d303c0b4c0e02d30340b4c0c02d302c0b4c0a02d30200b4c0702d30180b4c0502d30100b4c03647816980308102d30000b4bff02d2ff80b4bfd02d2ff190a05a5fd01697f205a5fc01697ee05a5fb01697ea05a5f981697e405a5f881697e005a5f781697dc05a5f601697d6f2c02d2fa80b4be902d2fa00b4be763e81697cb06802d2f91e2c05a5f181697c405a5f081697c0c7502d2f780b4bdd02d2f700b4bdb6c381697b405a5ec81697af08002d2f580b4bd502d2f51af005a5e981697a405a5e841fc0b4bcf02d2f380b4bcd6b8016979805a5e5b1b40b508602d42140b508487c016a10605a84142bc0b4bc902d2f200b4bc76b4816978c05a5e2b1980b4bc302d2f080b4bc171d8169780d6102d2efc0b4bbe02d2ef20ce05a5dd8169774e2802d2ee5ab205a5dc016976e05a5dac1980b4fb502d2ed1e1c05a7348169766e2002d2ec9aa405a5d88169760c5f02d47380b506d8cd016a2c205a83645080b506b870016a0d405a834c25c0b4fa002d2eb9e0e05a72b816975ae1902d2eb1a9805a5d58169754c5902d2ea00b4ba702d2e980b4ba56c3016974805a5d1816974205a5d0016973e05a5cf35dc0b4b9d66e016973805a5cd0169732f2b02d2e600b4b976b7816972c05a5cab1440b50f702d2e4e0c005a5c93c540b4b9102d2e41ad005a685016971eccf02d2e3989405a5c60169716f2a02d2e280b4b896b0016971005a5c3816970a05a5c23c500b4b8302d2e09ab005a5c0b3180b4b8002d3cd00b4b7e02d3cc00b4f2f7da0169e5c05a796bd680b4b7d02d2df1aa205a5bd81696f4c4302d47340b4f1b8cc816a1be05a5bc41640b4f1a02d3c65f3e05a7c48169e30f6d02d3c5de8a05a5bb81696ecd4b02d33f40b4b7565f81696e8c3d02d36540b4b7202d36440b4b7102d36340b4b7002d36240b4d8802d2dbc0b4b6e02d35f61ec05a5b6417c0b4d7c02d2dac0b4d7b02d2da80b4d7a6f08169af205a5b4b2dc0b4b6802d35d61ea05a5b341780b4d747d981696caf0d02d35cc0b4b6402d35c80b4d716da01696c605a5b130d80b50fc8e6016a0c919802d43ec0b506302d44d00b50fa88b016a1f310802d43340b506285f816a0c309002d35b5f3c05a5b03c180b4d6c02d2d7c0b4dfa02d35adba605a6b536980b4cf602d2d7996205a5aeb0c40b4d6602d2d6c0b4d657d901696b4f0c02d3591d5805a5acb8440b4d6302d35880b4b5802d2d5c0b51cb02d465c0b4d5e86f01696ab05802d3575f3a05a5aa3c140b4eda02d3571d3405a73f81696a6e0a02d356db9605a6ad01696a4caa02d2d440b4fbc8e50169e2519602d355a1ba05a5a7c15c0b502902d3ee201c05a7f90169e22fe402d3edc0b4fb67e40169e2005a787bcf80b4ec202d3555d2605a728016969ce0402d35500b4d536cf816969a05a5a630b00b522e02d485c0b521002d474641205a901016a3f605a8fa016a33b1ed02d47980b51d08ef816a39f1d802d46c80b519c8d5816a3371a402d46380b518702d46000b50e38bc816a2e405a8b5816a29605a82e44f00b511e02d438a22005a870c4080b50c702d416e17205a82d422c0b503c02d40d40b501602d3e8e01005a8010169ff605a7f60169e14fde02d3f600b4fa27e88169f42fc202d3dd80b4f097b38169e10f3902d3ba80b4eca02d3af00b4d4f7470169d1205a73c8169c9605a60ec1e1e4cd8c8773eba386b4a64cc295c74e658ab338da20f537c0b795b711297543b560432227002a440b4df402d3539b8c05a6a6b6680b4cf102d305a0e6f216c1c3a5f531be5a4b24a140e3373045459b6d067a73df1bb6dae8923a8dda101c90eb29951805a60941c1e3cd808733e9a376b486474275c60e5d8a73359a06f4b7bcb761b571217503b3603321a614aa240b4b4602d2d140b4b4402d2d0c0b4b4202d2d0591a05a59f816967c05a59e816967805a59db3680b4b3a642016994405a59c016993c05a59b816993405a59b016992c05a59a816992605a59a01699150ae02d2cca0a205a644816966205a644016966005a643816965e05a64334240b4b2e667016965805a5958169654e3902d2ca40b4b2802d2c9d8f805a592816964805a591b89c0b4b2202d2c8598a05a59031d00b4c8202d2c780b4c817ac816963aeff02d3201cd005a58e387c0b4c7f02d2c6c0b4c7e02d2c680b516002d45040b4c7a84b016963104a02d3e200b4f6c02d31e5e8805a58bbbe00b4c7872b016962ce1802d31dc0b4b1502d31d99f805a58a32f80b4b1202d2c440b4b1071c016961ed4402d2c380b4b0d636016a15a05a585c1400b4b0a02d2c25c4c05a6f00169610d3d02d2c1d96c05a58331940b4c72856016960904f02d31c40b4b0302d31c1cce05a58138780b4c6f6d98169602d3602d31b80b4b0002d42cc0b505502d42ca2be05a82a45000b513302d44540b50b1883816a0a70d902d42c219805a82942f80b4c6a02d2bf80b4c6972a81695fae1702d37e40b4dd202d31a1b4a05a57e34c40b4c6767a81695f6cb002d39180b4af902d39080b4af802d38f9d5605a71e8169c78e6602d2bdda5405a57b01695eac5e02d45780b4e2d89f816a12a05a579c1240b4e2c02d2bc80b4ed902d38add3205a71539f80b4e2972a0169b9405a578b4900b4af065481695dec5802d39ce2ba05a71244f80b4c6384a01695db04802d40a00b500d02d39bdfe205a711bf8c0b4fc702d3e640b4c6279e81695d8ef202d39add8205a7113a480b4e6a02d38840b4c616cf01695d6d1f02d31800b4aea02d48b40b521602d483c0b520802d48040b51fa02d45923e605a8a2c7b00b51e502d47780b51d702d46e00b51b102d46a80b509a8d1816a09b19402d46340b518602d458e2fe05a8a245e00b51628b8816a28716a02d44740b510f02d426620205a82643500b5098863016a0970b802d40ec0b503402d40540b500702d40040b4ffa02d3969fd605a70e3f740b4fd702d3f400b4fc102d3e500b4f7502d3d980b4c5c79c016984307b794b6421e2fb18e33276150e4173745655d0ce768a3d59f08de96de44b1d62ede8124895ddca9402d3ba40b4ec902d3965d7605a70dba340b4e587440169c34e7802d37cc0b4dc502d316db3205a60cc1d5e46d85875beae380c9585138d5cc5153573b37da18f507bf3775b61126752bb4a03d21f68e2a380b4c5a678016982b072790360a1d0fa88deb24613ee3272fc5415cccd9682bd35ef6dda6d6c48dd44ecf80dc87194aa8b02d2b900b4ae302d2b880b4ae16a181695c0cd802d2b7d8a005a67601695ba05a67401695b805a67201695b605a670377c0b4ada69e01699bad0802d2b6589205a62b01695ae05a62abd600b4ad677f01698a805a56a81698a6db202d2b51a6a05a629341c0b4ad3666816a26405a88a016a20c05a86c0169a330cb02d334e17a05a627423c0b4ad18220169a2af8702d3349ed605a626bd0c0b4ad077b8169a2205a668816989805a5678169a1adf802d3341ba205a625b6900b4ace698016959805a7ab8169596efd02d3aa80b4aca7080169592d2902d2b2198805a563b1080b4ccb02d2b140b4f8602d3329ed405a7a10169588ef602d3b600b4e9802d3325cfa05a561b8240b4cc86e48169584d2302d331d9f605a560b0f00b4f6102d3c0c0b4c4702d2afc0b502702d40300b4f5d7f80169e04fe202d3d71f8c05a780be600b4f5b7c28169e00f6902d3b000b4e9102d3119c9e05a55f380c0b4c456ce816957ad1e02d31119f405a55e32f40b522c02d48540b520e02d481c0b520002d47e40b51f202d47ac0b51e402d47740b51d602d46dc0b4f8f8d80169ee11a902d3d2234405a77dc64c0b518c02d46140b517e02d45dc0b517002d45a40b514a02d44ec0b511c02d44380b510002d434c0b4d0086281699850b702d310211405a612c1f9e66d9487a3eee392ca1855b915ce515c675b461ec0f8e55d37b5b8112f75abb8a05b2288202a5c0b503a02d40cc0b501402d40180b4f8b8000169edeff902d3d1dfd405a77d3f700b4f8a7eb0169edcfcf02d3d19f8005a77cbe4c0b4ee802d3b200b4eba02d3a300b4cff7438169982e7702d30fdc9405a60e41dde4ad8b876beb6384c9885238ddcc9155671343dea4f8055cb791b6f128753bb520412216ffaa400b4cfe6f90169980dc402d30f9b3005a60c41d1e44d848753eaa37ec94850b8d1cc315266f342de9ef7d55c3771b5f1257523b4603b21e68daa340b4d4902d2ad80b4d4802d2ad40b4d477548169568e0f02d3519bbc05a6a2b6c40b4ab365a8169564c3502d44c40b4dee889816a20a05a6a0c35c0b50ca02d32ee17805a847016956104302d37a80b4d4002d32e80b4aaf02d3799dae05a69fba5c0b4cb973e016955ce0802d3789bee05a69f368c0b4cb867a016955ac3002d44c00b511202d370620805a69d43580b50c902d42ec0b4c3a846816955704202d40980b500b02d3fbc0b4fe102d36f5f8a05a69cbe5c0b4c3979e0169554ef102d36e5d7e05a69c3a400b4c387270169552e0202d36d5bec05a69bb7400b4c376798169550caf02d48ac0b521402d48340b520602d47fc0b51f802d47c40b51ea02d44da3c605a88c47700b510a8ea816a1b71b602d433e35e05a860c6a00b50928d0816a08d19202d44d631605a88bc6100b51098be816a1b517602d433a2de05a86045a00b50918a4816a08b13a02d40e40b503202d404c0b500502d3ffc0b4ff802d3fa40b4fdb02d37f1faa05a6eabf380b4da87df8169a66f9202d33e1ee805a659bd940b4c3379b816984107a794363e1e0fb08e2b27214ee40736c5619ccd137aabe0dbd0dbb895aa99d60edd811c891ddaa9302d37eddce05a6ea3b1c0b4da775c8169a64e8b02d33ddd0c05a65939d80b4c327248169837076792362a1d8fac8e0b25e146e36731c5519c2d0e7a8bdfdbc6db6893aa95d4ced380fc881bfca8f02d3ad80b4e1502d34b80b4aa302d40940b4eb28050169fdc05a70a3f800b4fc402d34b5f2c05a79d8169544ef002d3ab9dac05a756baf80b4e1373d8169c24e4d02d34b1b9005a695b6700b4aa16540169540c2b02d48a80b521302d48300b520502d47f80b51f702d47c00b51e902d47880b51db02d47500b51b502d46b80b51a702d46800b519102d46280b4ee38c1816a2f805a74ec5d40b516e02d3a0a2ce05a8a40169c1b13902d446c0b4dce886816a1fe05a693c3480b50c402d32b616c05a844816984907d799364e1e6fba8e43282154e44738c56d9d4d177afbe35bd8dbf8973ad1dc2a9e816489e07ea9602d40e00b4edf818816a02405a74e40100b4ffe02d3a05fee05a7f40169c18fda02d3f500b4dcd7e68169f7c05a6933e440b4f7302d32b1ec805a79b016983f079793b63a1defaf8e2326e14ce3f736455d9cad127aa3e09bcedba8953abddb8a9d811488ddd8a9202d3b6ddcc05a74dbae00b4e807428169c16e4802d3731be205a692b65c0b4cab677816982306f78eb5fe1cafa58dd3232138e2f72e45359aad027a53de1baedaa8903a7dd98a9c80c4865850a8802d48a40b521202d40ba41605a80848100b51fd02d47d80b4ff48f78169fcd1e802d47840b51da02d3f2a3a605a7cdc6d00b51ad02d46980b4f408cf8169de919002d46240b518202d3b122f605a74ac5d00b516d02d45980b4e528a38169c0d13802d44680b510c02d36861fc05a690c3440b50c302d42d40b4c2e844016984707c798b64a1e4fb98e3b27e152e4373845699d2d167af3e31bd6dbe896bacddc102b54d489a07ca9502d40aa06e05a807c0c00b4ff37fe8169fcaff602d3f25fa605a7cd3f300b4f3f7b90169de6f6302d3b0ddca05a74a3b180b4e517420169c0ae7502d3681be005a690370c0b4c2d677016982907178fb6061cefa78de324213ce3172f453d9aed047a63de9bb2dac8913a85d9d01a54cc86d948a8a01f80f807803d01d80e407403701c00d406c03401700a004c02401680cc05e029013809405803201580c405403000d806803201800b805802a014011808804202000f807803a01c0088040026012001802000200b006002401400e002800000e002007801001a006
def symF1 : List ℕ := [6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 18, 19, 20, 21, 22, 23, 12, 13, 14, 15, 16, 17]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma symValid1 : SymData symP1 symF1 := symCheck_sound (by decide +kernel)
def posChoice := 0xda7520941c63f85b7ea0d20ea75300db75210fb75310da85200ea85300dc85210fc85310da76200ea76300db76210fedb7631941c63f85b7ea0d20b76310da96200ea96300dc96210fedc96310c96310da75200ea75400db75210fb75410da85200ea85400cbad8521941c63f85b7ea0d20d85210cbaf85410f8541065da720941c63f85b7ea0d20da720065ea7400ea740065db7210db721065edb741941c63f85b7ea0d20fedb741065b7410b741065da9200da920065ea9400ea940065bad921941c63f85b7ea0d20cbad921065d9210d921065bad941941c63f85b7ea0d20cfbad941065ed9410fed941065ba9410cba94106594109410da75200ea7530019410db752c63f85b7ea0d20db752010fb7530fb7530da85200ea8530010dc8520dc852010fc8530fc8530da76200ea7630010db7620db76201941f0db763c63f85b7ea0d20fedb763010b7630b7630994187da620c63f85b7ea0d20da6200987ea6300ea63001941870dc62c63f85b7ea0d20987dc62010dc620dc6201941870dc63c63f85b7ea0d20987edc6301f0dc630fedc6301870c630987c63010c630c630da7520049413c632ea750f85b7ea0d20ea750010db7520db752019413c6302fb75f85b7ea0d20432fb75010fb750fb750da85200432ea8500ea85001941cc63b0d852f85b7ea0d20cbad852010d8520d852019413c63b02ff8585b7ea0d2043ba2f8501cb0f850cbaf8501302f850432f85010f850f85065da7200da720049413c635f852ea70b7ea0d2065ea700432ea700ea70019416c635f850db72b7ea0d2065db72010db720db72019413c635f8502b7b7ea0d20435e2b701650db7065edb7013f02b7043fe2b701f0db70fedb7013502b704352b701650b7065b701302b70432b7010b70b7099416c635f857b7da20ea0d20987da20065da200da20049413c635f857b72eeaa00d209657ea0043872ea00987ea004352ea0065ea00432ea00ea0019416c635f857b70ea0dd2209657ad201c870d209c87ad20165b0d2065bad201cb0d20cbad2016570d209657d201870d20987d201650d2065d2010d20d2019413c635f857b70ea02d204357a2016570d09657ad013870204387a201c870d09c87ad0135b020435ba20165b0d065bad013fb02043fba201cfb0d0cfbad013570204357e2016570d09657ed013870204387e201870d0987ed0135020435e201650d065ed013f02043fe201f0d0fed013570204357a201657009657a013870204387a201c87009c87a0135b020435ba20165b0065ba013b02043ba201cb00cba013570204357201657009657013870204387201870098701350204352016500650130204320100941c63f85b7ea0d20d0a070502000e0a070503000d0b0705020110ff0b0705030110d0a080502000e0a080503000d0cc0805020110ff0cc0805030110d0a0706602000ee0a0706603000dd0b07066020110b07066030110b07066030110d0a09906602000ee0a09906603000dd060cc0109906602011060cc0109906603011060cc01099066030110d0a0705502000e0a07055044000d0bb0705502011050ff0bb07055010440110d0aa0805502000e0aa08055044000d0d08055020110805502011050ff050ff080550104401108055010440110d0d0a0a0707020002000ee0ee0a0a070704400044000dd0dd0bb0bb070702011020110bb0bb070701044011010440110bb0bb070701044011010440110d0d0aa0aa099099020002000a0a0ee0ee0aa0aa040990409904400044000dd0dd0dd0dd010990109902011020110109901099020110201101040109901040109901044011010440110104010990104010990104401101044011010401099010401099010440110104401101040109901040109999999999999999999999999901044011010444444444444444444444444440111111111111111111111111110d0a0705020000e0a07050330000d0d0b0b0707050502020ff0ff0b0b070705050330330d0a08805020000e0a088050330000d0d0cc0cc0880880505020208080ff0ff03030cc0cc08808805050330330d0a07706602000000ee0a077030660330000dd0dd0b0b07707706606602020b0b07707703030660660330330b0b07707703030660660330330d0d0a0a0660200006602000000ee000ee0a0a03066033000030660330000dd0dd0dd0dd06060cc0cc06060cc0cc066066020206606602020303060603030cc0cc0303060603030cc0cc030306606603303303030660660330330303060603030cc0cc0303060603030cc0cccccccccccccccccccccccccc030306606603303303030660666666666666666666666666660330333333333333333333333333330d0a070550220000e0e0a0a07070550550000000d0d0bb0bb0707055055022022050505050ff0ff0ff0ff0bb0bb0bb0bb070707070550550550550d000aa050880550220000e0e000aa000aa05050880880550550000000d0d0d0d050508808805505502202205050880880550550220220505050508080808050505050ff0ff0ff0ff0505050508080808050505050ff0ff0ff0ffffffffffffffffffffffffff05050505088088088088055055055055050505050880880880888888888888888888888888880550550550555555555555555555555555550d0d0a0a077077022000022000000ee000ee000ee000ee0a0a0a0a07707707707700000000000002020dd0dd02020dd0dd070707070bb0bb0bb0bb07707707707702202202202207070707070707070bb0bb0bb0bb0bb0bb0bb0bb07707707707707707707707707070707070707070bb0bb0bb0bb0bb0bb0bb0bbbbbbbbbbbbbbbbbbbbbbbbbb0770770770770770770770777777777777777777777777770d0d0d0d000aa000aa000aa000aa022000022000022000022000000a000a000a000a000a000a000a000a000ee000ee000ee000ee000ee000ee000ee000eeeeeeeeeeeeeeeeeeeeeeeeee000aa000aa000aa000aa000aa000aa000aa000aaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000000000000000000002020dd0dd02020dd0dd02020dd0dd02020dd0dd02020dd0dd02020dd0dd02020dd0dd02020dd0dddddddddddddddddddddddddd0220220220220220220220220220220220220220220220222222222222222222222222220320161460200000115552625200505050201132520038433500120140526020
def edgePos : List ℕ := [240, 1846, 64, 1252, 1873, 818, 1282, 500, 854, 1910, 288, 548, 1332, 136, 352, 930]
def minRow := (List.range NN).map (fun k => edgePos.getD ((posChoice >>> (4*k)) &&& 15) 0)
def Domin (p : List ℕ) (T a b : ℕ) : Prop :=
  (∀ k, T.testBit k = true → (rho p a).testBit k = true → b.testBit k = true) ∧
  (∀ k, T.testBit k = false → b.testBit k = true → a.testBit k = true)
def dmOk (p : List ℕ) (T a b : ℕ) : Bool :=
  Nat.beq (rho p a &&& T &&& b) (rho p a &&& T) && Nat.beq (b &&& (T ||| a)) b
lemma dm_sound {p : List ℕ} {T a b : ℕ} (h : dmOk p T a b = true) : Domin p T a b := by
  obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp h
  constructor
  · intro k ht ha
    have q := congrArg (fun z : ℕ => z.testBit k) (Nat.eq_of_beq_eq_true h1)
    simpa [Nat.testBit_and,ht,ha] using q
  · intro k ht hb
    have q := congrArg (fun z : ℕ => z.testBit k) (Nat.eq_of_beq_eq_true h2)
    simpa [Nat.testBit_and,Nat.testBit_or,ht,hb] using q
lemma domin_op {p : List ℕ} {T a b a' b' : ℕ} (d : Bool)
    (ha : Domin p T a a') (hb : Domin p T b b') : Domin p T (op d a b) (op d a' b') := by
  constructor
  · intro k ht h
    rw [rho_op,op_bit] at h
    rw [op_bit]
    cases d
    · exact Bool.and_eq_true_iff.mpr ⟨ha.1 k ht (Bool.and_eq_true_iff.mp h).1,hb.1 k ht (Bool.and_eq_true_iff.mp h).2⟩
    · exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp h).imp (ha.1 k ht) (hb.1 k ht))
  · intro k ht h
    rw [op_bit] at h ⊢
    cases d
    · exact Bool.and_eq_true_iff.mpr ⟨ha.2 k ht (Bool.and_eq_true_iff.mp h).1,hb.2 k ht (Bool.and_eq_true_iff.mp h).2⟩
    · exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp h).imp (ha.2 k ht) (hb.2 k ht))
lemma domin_terminal {p : List ℕ} {T b : ℕ} (hf : rho p T &&& T = T) (h : Domin p T T b) : b = T := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases ht : T.testBit k with
  | true =>
    have q := congrArg (fun v : ℕ => v.testBit k) hf
    exact h.1 k ht (by simpa [Nat.testBit_and,ht] using q)
  | false =>
    cases hb : b.testBit k with
    | false => rfl
    | true =>
      have := h.2 k ht hb
      simp_all
lemma Sol.dominated {p : List ℕ} {m T q : ℕ} {S : Set ℕ}
    (hf : rho p T &&& T = T) (h : Sol Z0 m T q S) :
    ∀ {S' : Set ℕ}, (∀ a ∈ S, ∃ b ∈ S', Domin p T a b) → Sol Z0 m T q S' := by
  induction h with
  | done h =>
    intro S' hview
    obtain ⟨v,hv,hq⟩ := hview _ h
    exact .done ((domin_terminal hf hq) ▸ hv)
  | @bi q S d a b ha hb _ _ ih =>
    intro S' hview
    obtain ⟨a',ha',he1⟩ := hview _ ha
    obtain ⟨b',hb',he2⟩ := hview _ hb
    refine .bi (d:=d) ha' hb' (al0 _ _ _) (ih ?_)
    intro v hv
    rcases hv with h | h
    · subst v
      exact ⟨_,Set.mem_insert _ _,domin_op d he1 he2⟩
    · obtain ⟨w,hw,hr⟩ := hview _ h
      exact ⟨w,Or.inr hw,hr⟩
def original := (rawP.map (· &&& mz 0)) ++ [0,mz 0]
lemma original_ok {v : ℕ} : v ∈ original ↔ v ∈ C (mz 0) (WZ [] 0) := by
  simp [original,C,WZ,rawL,eq_comm]
def nonEdges : List (Bool × ℕ × ℕ) := [(false,0,1),(false,0,2),(false,0,3),(false,0,4),(false,0,5),(false,0,6),(false,0,8),(false,0,9),(false,0,10),(false,1,2),(false,1,3),(false,1,4),(false,1,5),(false,1,7),(false,1,8),(false,1,9),(false,2,3),(false,2,4),(false,2,5),(false,2,6),(false,2,7),(false,2,8),(false,2,11),(false,3,4),(false,3,5),(false,3,6),(false,3,7),(false,3,10),(false,4,5),(false,4,6),(false,4,9),(false,4,11),(false,5,8),(false,5,10),(false,5,11),(false,6,7),(false,6,8),(false,6,9),(false,6,10),(false,6,11),(false,7,8),(false,7,9),(false,7,10),(false,7,11),(false,8,9),(false,8,10),(false,8,11),(false,9,10),(false,9,11),(false,10,11)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma minOK : rho minRow (tz 0) &&& tz 0 = tz 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma originalSelf : original.all (fun a => dmOk minRow (tz 0) a a) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma minNonEdge : nonEdges.all (fun e => dmOk minRow (tz 0) (tw e &&& mz 0) 0) = true := by decide +kernel
lemma nonEdge_free {e : Bool × ℕ × ℕ} (he : e ∈ nonEdges) {L : ℕ} (h0 : Imp [] 0 L) : Imp [e] 0 L := by
  intro q hq hs
  apply h0 q hq
  refine hs.dominated minOK ?_
  intro a ha
  have casesA : a ∈ C (mz 0) (WZ [] 0) ∨ a = tw e &&& mz 0 := by
    rcases ha with ⟨w,hw,rfl⟩ | hc
    · simp only [rawL,List.map_cons,List.map_nil,List.mem_append,List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl (Or.inl ⟨w,by simpa [rawL] using hw,rfl⟩)
      · exact Or.inr rfl
    · exact Or.inl (Or.inr hc)
  rcases casesA with h | rfl
  · exact ⟨a,h,dm_sound (List.all_eq_true.1 originalSelf a (original_ok.mpr h))⟩
  · exact ⟨0,Or.inr (Set.mem_insert _ _),dm_sound (List.all_eq_true.1 minNonEdge e he)⟩
abbrev RawGate := Bool × ℕ × ℕ
def gateMoveOk (g : List ℕ) (e f : RawGate) : Bool := decide (e.2.1<12 ∧ e.2.2<12 ∧
  e.1=f.1 ∧ ((g.getD e.2.1 0=f.2.1 ∧ g.getD e.2.2 0=f.2.2)
    ∨ (g.getD e.2.1 0=f.2.2 ∧ g.getD e.2.2 0=f.2.1)))
def rawAct (p g : List ℕ) : Bool := (List.range 12).all (fun i =>
  Nat.beq (rho p (rawP.getD i 0)) (rawP.getD (g.getD i 0) 0))
lemma gateMove {p g : List ℕ} (hd : SymData p g) (hr : rawAct p g=true) {e f : RawGate}
    (hm : gateMoveOk g e f=true) {L : ℕ} (hf : Imp [f] 0 L) : Imp [e] 0 L := by
  obtain ⟨ha,hb,hop,hab⟩ := of_decide_eq_true hm
  have rule := fun i (hi : i<12) => Nat.eq_of_beq_eq_true (List.all_eq_true.1 hr i (List.mem_range.2 hi))
  have he : rho p (tw e) = tw f := by
    simp only [tw,rho_op,rule _ ha,rule _ hb,hop]
    rcases hab with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [h1,h2]
    · rw [h1,h2]; exact op_comm _ _ _
  intro q hq hs
  apply hf q hq
  have hp := hs.pull (m' := mz 0) p
  have hT : rho p (tz 0) = tz 0 := by
    change rho p (TG &&& mz 0) = TG &&& mz 0
    rw [rho_and,hd.target,hd.mask]
  rw [hT] at hp
  refine hp.mono le_rfl ?_
  rintro x ⟨y,hy,rfl⟩
  rcases hy with ⟨w,hw,rfl⟩ | hy
  · rw [rho_and,hd.mask]
    simp only [rawL,List.map_cons,List.map_nil,List.mem_append,List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inl ⟨_,List.mem_append_left _ (hd.raw _ hw),rfl⟩
    · rw [he]; exact Or.inl ⟨_,by simp [rawL],rfl⟩
  · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · rw [h,rho_zero]; exact Or.inr (Set.mem_insert _ _)
    · rw [h,hd.mask]; exact Or.inr (Set.mem_insert_of_mem _ rfl)
lemma blockedStage {e : RawGate} {F : List RawGate} {raw : List (ℕ × ℕ)}
    {fb : ℕ × ℕ} {L : ℕ} (hL : L≤20) (hi : e.2.1<12 ∧ e.2.2<12)
    (h0 : Imp [] 0 L) (prior : ∀ f ∈ F, Imp [f] 0 L)
    (hI : ∀ y ∈ raw, Imp [] y.1 y.2) (hp : pOk 0 (tabE e [] raw)=true)
    (hb : fbOk [e] F fb=true)
    (hc : chkT topC [e] (tabE e [] raw) fb 0 19 [0] FF 1=false) : Imp [e] 0 L := by
  rcases Nat.eq_zero_or_pos L with rfl | hpos
  · intro q hq; omega
  · apply imp_FK topC_ok (by omega : L≤19+1) (by decide) (Or.inr ⟨e,rfl,hi.1,hi.2,h0⟩)
      hp (tabE_ok hI (fun _ _ h => by simp at h)) (Or.inr ⟨rfl,hb⟩)
    · intro f hf
      have heq : L - 1 + [e].length = L := by simp only [List.length_cons,List.length_nil]; omega
      rw [heq]; exact prior f hf
    · right
      intro t _ hz; subst t
      exact ⟨[(FF,1)],ffull,fun v hv => by simp only [List.mem_singleton] at hv; subst v; exact chkT_chk hc 0 (by simp)⟩
lemma blockFinal {F : List RawGate} {raw : List (ℕ × ℕ)} {fb : ℕ × ℕ} {L : ℕ}
    (hL : L≤20) (prior : ∀ f ∈ F, Imp [f] 0 L)
    (hI : ∀ y ∈ raw, Imp [] y.1 y.2) (hp : pOk 0 raw=true) (hb : fbOk [] F fb=true)
    (hc : chkT topC [] raw fb 0 20 [0] FF 1=false) : Imp [] 0 (L+1) := by
  apply imp_FK topC_ok (by omega : L+1≤20+1) (by decide) (Or.inl rfl)
    hp hI (Or.inr ⟨rfl,hb⟩)
  · intro f hf
    simpa using prior f hf
  · right
    intro t _ hz; subst t
    exact ⟨[(FF,1)],ffull,fun v hv => by simp only [List.mem_singleton] at hv; subst v; exact chkT_chk hc 0 (by simp)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawAct0 : rawAct symP0 symF0=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawAct1 : rawAct symP1 symF1=true := by decide +kernel
def samplePrices : List (ℕ × ℕ) := [(1,18),(4,18),(64,18),(256,18),(2,17),(8,17),(16,17),(32,17),(128,17),(512,17),(1024,17),(2048,17),(65,16),(66,16),(68,16),(96,16),(129,16),(257,16),(260,16),(264,16),(272,16),(516,16),(1028,16),(2049,16),(4096,15),(16384,15),(262144,15),(1048576,15),(5,15),(72,15),(80,15),(132,15),(144,15),(160,15),(258,15),(288,15),(320,15),(513,15),(520,15),(544,15),(1025,15),(1026,15),(1040,15),(2050,15),(2052,15),(2056,15),(3,14),(6,14),(9,14),(12,14),(17,14),(20,14),(33,14),(36,14),(130,14),(136,14),(192,14),(384,14),(514,14),(528,14),(576,14),(768,14),(1032,14),(1056,14),(1088,14),(1280,14),(2064,14),(2080,14),(2112,14),(2304,14),(4224,14),(6144,14),(16896,14),(17408,14),(262146,14),(262176,14),(1048584,14),(1048592,14)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem testStage0 : chkT topC [(false,0,7)] (tabE (false,0,7) [] samplePrices) (760,0x10040002101c000400001200000040000101010000000400110001100610000000000000000004000100000000000001000400040000001101000301000000030808000000000001a0000008100100200000090000000000200100002000) 0 19 [0] FF 1=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem testStage10 : chkT topC [(true,1,3)] (tabE (true,1,3) [] samplePrices) (627,0x108a0142090c1400214004808020030c001859c10247911220206200000242000380100220030180012c0218040400201100261036000000000b042340440002015080404004022002240184081) 0 19 [0] FF 1=false := by decide +kernel
end PEqualNP.Outside.L_meta_9732
