import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_118.Bridge

open Relation Classical

abbrev Walk (E : ℕ → ℕ → Prop) := Relation.ReflTransGen E

theorem walk_le {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {i j : ℕ} (w : Walk E i j) : j ≤ i := by
  induction w with
  | refl => exact Nat.le_refl _
  | tail _ e ih => exact (Nat.le_of_lt (dec e)).trans ih

theorem walk_sub {E E' : ℕ → ℕ → Prop} (sub : ∀ {i j}, E i j → E' i j)
    {i j : ℕ} (w : Walk E i j) : Walk E' i j := by
  induction w with
  | refl => exact .refl
  | tail _ e ih => exact .tail ih (sub e)

theorem clash {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    {A : ℕ → Prop} (ac : A c) {x : ℕ}
    (wc : Walk (fun i j => E i j ∧ A j) c x) (wd : Walk E d x) :
    ∃ p q m, (p = r ∨ Walk E c p) ∧ (q = r ∨ Walk E d q) ∧
      E p m ∧ E q m ∧ p ≠ q ∧ A m ∧ Walk E c m ∧ Walk E d m := by
  induction wc with
  | refl =>
    rcases wd.cases_tail with e | ⟨q, wq, eq⟩
    · exact False.elim (ne e)
    · have lt : q < r := (walk_le dec wq).trans_lt (dec rd)
      exact ⟨r, q, c, Or.inl rfl, Or.inr wq, rc, eq, (Ne.symm (ne_of_lt lt)),
        ac, .refl, wd⟩
  | @tail u v wu he ih =>
    have wcu : Walk E c u := walk_sub (fun h => h.1) wu
    have lu : u < r := (walk_le dec wcu).trans_lt (dec rc)
    rcases wd.cases_tail with e | ⟨q, wq, eq⟩
    · subst v
      exact ⟨u, r, d, Or.inr wcu, Or.inl rfl, he.1, rd, ne_of_lt lu, he.2,
        .tail wcu he.1, .refl⟩
    · by_cases hp : u = q
      · subst q
        exact ih wq
      · exact ⟨u, q, v, Or.inr wcu, Or.inr wq, he.1, eq, hp, he.2,
          .tail wcu he.1, wd⟩

theorem same_entry {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d z : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)
    {A : ℕ → Prop} (ac : A c) {x : ℕ}
    (wc : Walk (fun i j => E i j ∧ A j) c x) (wd : Walk E d x) : A z := by
  obtain ⟨p, q, m, hp, hq, ep, eq, neq, am, _, _⟩ := clash dec rc rd ne ac wc wd
  exact unique p q m hp hq ep eq neq ▸ am

theorem swap_entry {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d z : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)
    {A : ℕ → Prop} (ad : A d) {x : ℕ}
    (wd : Walk (fun i j => E i j ∧ A j) d x) (wc : Walk E c x) : A z :=
  same_entry dec rd rc ne.symm
    (fun p q m hp hq ep eq hne => unique q p m hq hp eq ep hne.symm) ad wd wc

section semantic

variable {α κ : Type}
variable {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
variable {r c d : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
variable (bad : α → κ → Prop) (point : κ → α → Prop) (leaf : κ → ℕ)
variable (B : α → ℕ → Prop) (side : α → Bool)
variable (one : ∀ {a k}, point k a → ∀ j, bad a j ↔ j = k)
variable (branch : ∀ a, B a (if side a then c else d))
variable (route : ∀ a i, B a i →
  ∃ j, bad a j ∧ Walk (fun u v => E u v ∧ B a v) i (leaf j))
variable (points : ∀ k, ∃ a, point k a)

def Common (E : ℕ → ℕ → Prop) (c d : ℕ) (u : ℕ) : Prop :=
  Walk E c u ∧ Walk E d u

def Forced (bad : α → κ → Prop) (point : κ → α → Prop) (side : α → Bool) (a : α) : Prop :=
  (∃ k, point k a ∧ ∃ b, point k b ∧ side b ≠ side a) ∨
  (∀ k, bad a k → ∀ b, point k b → side b ≠ side a)

include branch route one in
theorem criticalSide {a k} (ha : point k a) :
    Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
  obtain ⟨j, hj, w⟩ := route a _ (branch a)
  have eq := (one ha j).1 hj
  simpa [eq] using w

include branch route one points in
theorem forced_common {a} (ha : Forced bad point side a) :
    ∃ k, bad a k ∧ Common E c d (leaf k) ∧
      Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
  have mk : ∀ {k b}, bad a k →
      Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) →
      point k b → side b ≠ side a →
      ∃ k, bad a k ∧ Common E c d (leaf k) ∧
        Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
    intro k b bk wa pb hn
    have wb := criticalSide bad point leaf B side one branch route pb
    refine ⟨k, bk, ?_, wa⟩
    have ua := walk_sub (fun h => h.1) wa
    have ub := walk_sub (fun h => h.1) wb
    cases ea : side a <;> cases eb : side b <;> simp_all [Common]
  rcases ha with ⟨k, ka, b, kb, hn⟩ | ha
  · exact mk ((one ka k).2 rfl) (criticalSide bad point leaf B side one branch route ka) kb hn
  · obtain ⟨k, bk, wa⟩ := route a _ (branch a)
    obtain ⟨b, kb⟩ := points k
    exact mk bk wa kb (ha k bk b kb)

include dec rc rd ne branch route one points in
theorem entry_exists {a} (ha : Forced bad point side a) :
    ∃ p q m, (p = r ∨ Walk E c p) ∧ (q = r ∨ Walk E d q) ∧
      E p m ∧ E q m ∧ p ≠ q ∧ B a m ∧ Common E c d m := by
  obtain ⟨k, _, ⟨wc, wd⟩, w⟩ := forced_common bad point leaf B side one branch route points ha
  cases h : side a
  · simp [h] at w
    obtain ⟨q, p, m, hq, hp, eq, ep, neq, b, rd', rc'⟩ :=
      clash dec rd rc ne.symm (by simpa [h] using branch a) w wc
    exact ⟨p, q, m, hp, hq, ep, eq, neq.symm, b, rc', rd'⟩
  · simp [h] at w
    exact clash dec rc rd ne (by simpa [h] using branch a) w wd

variable {z : ℕ}
variable (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)

include dec rc rd ne unique branch route one in
theorem false_on_common {k a}
    (hc : Common E c d (leaf k)) (ha : point k a) : B a z := by
  have w := criticalSide bad point leaf B side one branch route ha
  cases h : side a
  · simp [h] at w
    exact swap_entry dec rc rd ne unique (by simpa [h] using branch a) w hc.1
  · simp [h] at w
    exact same_entry dec rc rd ne unique (by simpa [h] using branch a) w hc.2

include dec rc rd ne unique branch route one points in
theorem false_on_forced {a}
    (ha : Forced bad point side a) : B a z := by
  obtain ⟨p, q, m, hp, hq, ep, eq, neq, hm, _⟩ :=
    entry_exists dec rc rd ne bad point leaf B side one branch route points ha
  exact unique p q m hp hq ep eq neq ▸ hm

include dec rc rd ne unique branch route one points in
theorem one_entry_characterization (fz : Common E c d z) :
    (∀ a, Forced bad point side a → B a z) ∧
    (∀ a, B a z → ∃ k, bad a k ∧ ∀ b, point k b → B b z) ∧
    (∀ a, ¬ B a z → ∃ k, bad a k ∧ ∃ b, point k b ∧ ¬ B b z) := by
  refine ⟨fun a ha => false_on_forced dec rc rd ne bad point leaf B side one branch route points unique ha, ?_, ?_⟩
  · intro a ba
    obtain ⟨k, bk, w⟩ := route a z ba
    have w' := walk_sub (fun h => h.1) w
    have common : Common E c d (leaf k) := ⟨fz.1.trans w', fz.2.trans w'⟩
    exact ⟨k, bk, fun b hb => false_on_common dec rc rd ne bad point leaf B side one branch route unique common hb⟩
  · intro a ba
    obtain ⟨k, bk, wa⟩ := route a _ (branch a)
    by_contra! hall
    have hpk := hall k bk
    -- If every critical point of the routed leaf lies below z, following any such
    -- point from z proves z reaches that leaf. Then both root sides can reach it.
    obtain ⟨b, hb⟩ := points k
    obtain ⟨j, bj, w⟩ := route b z (hpk b hb)
    rcases (one hb j).1 bj with rfl
    have w' := walk_sub (fun h => h.1) w
    have cl : Common E c d (leaf j) := ⟨fz.1.trans w', fz.2.trans w'⟩
    apply ba
    cases h : side a
    · simp [h] at wa
      exact swap_entry dec rc rd ne unique (by simpa [h] using branch a) wa cl.1
    · simp [h] at wa
      exact same_entry dec rc rd ne unique (by simpa [h] using branch a) wa cl.2

end semantic

end PEqualNP.Outside.L_pcx_118.Bridge
open PEqualNP.Outside.L_pcx_118.Bridge PEqualNP.ProofComplexity

namespace PEqualNP.Outside.L_pcx_118.Graph

abbrev ClauseMap (V : Type) := Nat → LinClause V
abbrev Parents := Nat → List Nat

def Rule {V : Type} [DecidableEq V] (F : Set (LinClause V))
    (C : ClauseMap V) (P : Parents) (i : Nat) : Prop :=
    (P i = [] ∧ C i ∈ F) ∨
    (∃ j < i, P i = [j] ∧ (∀ a, LinClauseSat a (C j) → LinClauseSat a (C i))) ∨
    (∃ j < i, ∃ k < i, P i = [j, k] ∧ IsLinResolvent (C j) (C k) (C i))

def Encoded {V : Type} [DecidableEq V] (F : Set (LinClause V))
    (C : ClauseMap V) (P : Parents) (lines : List (LinClause V)) : Prop :=
  (∀ i < lines.length, Rule F C P i) ∧
  (∀ D, D ∈ lines ↔ ∃ i < lines.length, C i = D)

theorem rule_congr {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C D : ClauseMap V} {P Q : Parents} {i : Nat}
    (same : ∀ j ≤ i, D j = C j) (parents : Q i = P i)
    (h : Rule F C P i) : Rule F D Q i := by
  rw [Rule, parents, same i le_rfl]
  rcases h with h | ⟨j, ji, e, weak⟩ | ⟨j, ji, k, ki, e, res⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨j, ji, e, by simpa only [same _ ji.le] using weak⟩)
  · exact Or.inr (Or.inr ⟨j, ji, k, ki, e, by simpa only [same _ ji.le, same _ ki.le] using res⟩)

theorem extend {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} {C : ClauseMap V} {P : Parents} (enc : Encoded F C P π)
    (D : LinClause V) (q : List Nat)
    (hr : Rule F (Function.update C π.length D) (Function.update P π.length q) π.length) :
    Encoded F (Function.update C π.length D) (Function.update P π.length q) (D :: π) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have ib : i ≤ π.length := Nat.lt_succ_iff.1 (by simpa only [List.length_cons] using hi)
    rcases eq_or_lt_of_le ib with rfl | lt
    · exact hr
    · refine rule_congr (fun j ji => Function.update_of_ne (ne_of_lt (ji.trans_lt lt)) _ _) ?_ (enc.1 i lt)
      exact Function.update_of_ne (ne_of_lt lt) _ _
  · intro A
    simp only [List.mem_cons, List.length_cons]
    constructor
    · intro h
      rcases h with rfl | h
      · exact ⟨π.length, Nat.lt_succ_self _, by simp⟩
      · obtain ⟨i, hi, eq⟩ := (enc.2 _).1 h
        exact ⟨i, by omega, by simpa [Function.update_of_ne (ne_of_lt hi)] using eq⟩
    · rintro ⟨i, hi, eq⟩
      have ib : i ≤ π.length := by omega
      rcases eq_or_lt_of_le ib with rfl | lt
      · exact Or.inl (by simpa using eq.symm)
      · exact Or.inr ((enc.2 _).2 ⟨i, lt, by simpa [Function.update_of_ne (ne_of_lt lt)] using eq⟩)

theorem build_graph {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} (der : IsLinDerivation F π) : ∃ C P, Encoded F C P π := by
  induction der with
  | nil => exact ⟨fun _ => ∅, fun _ => [], by simp [Encoded]⟩
  | @ax π D _ hD ih =>
    obtain ⟨C, P, enc⟩ := ih
    refine ⟨_, _, extend enc D [] ?_⟩
    exact Or.inl (by simpa using hD)
  | @res π D H R _ d h res ih =>
    obtain ⟨C, P, enc⟩ := ih
    obtain ⟨i, hi, di⟩ := (enc.2 _).1 d
    obtain ⟨j, hj, ej⟩ := (enc.2 _).1 h
    refine ⟨_, _, extend enc R [i, j] (Or.inr (Or.inr ⟨i, hi, j, hj, by simp, ?_⟩))⟩
    simpa [Function.update_of_ne (ne_of_lt hi), Function.update_of_ne (ne_of_lt hj), di, ej] using res
  | @weak π D R _ hD hw ih =>
    obtain ⟨C, P, enc⟩ := ih
    obtain ⟨i, hi, eq⟩ := (enc.2 _).1 hD
    refine ⟨_, _, extend enc R [i] (Or.inr (Or.inl ⟨i, hi, by simp, ?_⟩))⟩
    simpa [Function.update_of_ne (ne_of_lt hi), eq] using hw

def Edge (P : Parents) (i j : Nat) : Prop := j ∈ P i

theorem edge_desc {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {i j : Nat} (h : Rule F C P i)
    (e : Edge P i j) : j < i := by
  rcases h with ⟨r, _⟩ | ⟨k, ki, r, _⟩ | ⟨k, ki, m, mi, r, _⟩
  · simp [Edge, r] at e
  · have eq : j = k := by simpa [Edge, r] using e
    simpa [eq] using ki
  · simp only [Edge, r, List.mem_cons, List.mem_nil_iff, or_false] at e
    rcases e with rfl | rfl <;> assumption

def FalseAt {V : Type} (C : ClauseMap V) (a : V → Bool) (i : Nat) : Prop :=
  ¬ LinClauseSat a (C i)

theorem resolve_branch {V : Type} [DecidableEq V] {D H R : LinClause V}
    (a : V → Bool) {f : Finset V}
    (rr : R = D.erase (f, false) ∪ H.erase (f, true))
    (fr : ¬ LinClauseSat a R) :
    if Odd (f.filter (fun x => a x = true)).card
    then ¬ LinClauseSat a D else ¬ LinClauseSat a H := by
  subst R
  by_cases h : Odd (f.filter (fun x => a x = true)).card
  · rw [ite_eq_left h]
    rintro ⟨q, hq, sat⟩
    apply fr
    refine ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hq⟩), sat⟩
    rintro rfl
    simp [LinEqSat, h] at sat
  · rw [ite_eq_right h]
    rintro ⟨q, hq, sat⟩
    apply fr
    refine ⟨q, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hq⟩), sat⟩
    rintro rfl
    simp [LinEqSat, h] at sat

theorem follow {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {n : Nat} (rule : ∀ i < n, Rule F C P i) (a : V → Bool)
    {i : Nat} (hi : i < n) (fi : FalseAt C a i) :
    ∃ j, P j = [] ∧ C j ∈ F ∧ FalseAt C a j ∧
      Walk (fun u v => Edge P u v ∧ FalseAt C a v) i j := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have visit : ∀ j < i, Edge P i j → FalseAt C a j →
        ∃ k, P k = [] ∧ C k ∈ F ∧ FalseAt C a k ∧
          Walk (fun u v => Edge P u v ∧ FalseAt C a v) i k := by
      intro j lt ej fj
      obtain ⟨k, p0, fm, fk, w⟩ := ih j lt (lt.trans hi) fj
      exact ⟨k, p0, fm, fk, Relation.ReflTransGen.head ⟨ej, fj⟩ w⟩
    rcases rule i hi with ⟨p0, hF⟩ | ⟨j, ji, pp, hw⟩ | ⟨j, ji, k, ki, pp, f, h1, h2, rr⟩
    · exact ⟨i, p0, hF, fi, .refl⟩
    · exact visit j ji (by simp [Edge, pp]) (fun h => fi (hw a h))
    · have br := resolve_branch a rr fi
      split at br
      · exact visit j ji (by simp [Edge, pp]) br
      · exact visit k ki (by simp [Edge, pp]) br

theorem first_false {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {π : List (LinClause V)}
    (graph : Encoded F C P π) (empty : ∅ ∈ π)
    (axsat : ∀ D ∈ F, ∃ a, LinClauseSat a D) :
    ∃ r < π.length, (∀ a, FalseAt C a r) ∧
      (∀ j < r, ∃ a, LinClauseSat a (C j)) ∧
      ∃ j < r, ∃ k < r, j ≠ k ∧ P r = [j, k] ∧ ∃ f : Finset V,
          f ≠ ∅ ∧ ∀ a, if Odd (f.filter (fun x => a x = true)).card
            then FalseAt C a j else FalseAt C a k := by
  classical
  have existsFalse : ∃ j, j < π.length ∧ ∀ a, FalseAt C a j := by
    obtain ⟨j, hj, he⟩ := (graph.2 _).1 empty
    exact ⟨j, hj, by simp [FalseAt, he, LinClauseSat]⟩
  let r := Nat.find existsFalse
  obtain ⟨ri, fr⟩ := Nat.find_spec existsFalse
  have prev : ∀ j < r, ∃ a, LinClauseSat a (C j) := by
    intro j hj
    by_contra! h
    exact Nat.find_min existsFalse hj ⟨hj.trans ri, h⟩
  refine ⟨r, ri, fr, prev, ?_⟩
  rcases graph.1 r ri with ⟨_, hF⟩ | ⟨j, jr, _, hw⟩ | ⟨j, jr, k, kr, p, f, df, dk, rr⟩
  · obtain ⟨a, ha⟩ := axsat _ hF
    exact (fr a ha).elim
  · obtain ⟨a, ha⟩ := prev j jr
    exact (fr a (hw a ha)).elim
  · have br : ∀ a, if Odd (f.filter (fun x => a x = true)).card
      then FalseAt C a j else FalseAt C a k := fun a => resolve_branch a rr (fr a)
    have ne : j ≠ k := by
      intro eq
      obtain ⟨a, sat⟩ := prev j jr
      have no := br a
      rw [eq] at no sat
      split at no <;> exact no sat
    have nz : f ≠ ∅ := by
      intro eq
      obtain ⟨a, sat⟩ := prev k kr
      exact (by simpa [eq] using br a : FalseAt C a k) sat
    exact ⟨j, jr, k, kr, ne, p, f, nz, br⟩

open scoped BigOperators

def LocalEdge (P : Parents) (r i j : Nat) : Prop := i ≤ r ∧ Edge P i j

noncomputable def Live (P : Parents) (r : Nat) : Finset Nat := by
  classical
  exact (Finset.range (r+1)).filter (fun v => Walk (LocalEdge P r) r v)

theorem bounded_edge {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {i j : Nat} (e : LocalEdge P r i j) : j < i := edge_desc (rules i e.1) e.2

theorem live_iff {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    i ∈ Live P r ↔ Walk (LocalEdge P r) r i := by
  classical
  simp only [Live, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  exact ⟨fun h => h.2, fun w => ⟨walk_le (bounded_edge rules) w, w⟩⟩

theorem live_closed {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i j : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (hi : i ∈ Live P r) (e : Edge P i j) :
    j ∈ Live P r := by
  have w := (live_iff rules).1 hi
  exact (live_iff rules).2 (.tail w ⟨walk_le (bounded_edge rules) w, e⟩)

def InDegree (P : Parents) (s : Finset Nat) (j : Nat) : Nat :=
  ∑ i ∈ s, (P i).count j

theorem count_edges {P : Parents} {s : Finset Nat}
    (hs : ∀ i ∈ s, ∀ j ∈ P i, j ∈ s) :
    ∑ j ∈ s, InDegree P s j = ∑ i ∈ s, (P i).length := by
  unfold InDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j ∈ s, List.count j (P i)) = ∑ j ∈ (P i).toFinset, List.count j (P i) := by
      symm
      apply Finset.sum_subset
      · intro j hj
        exact hs i hi j (List.mem_toFinset.1 hj)
      · intro j hj hnot
        exact List.count_eq_zero_of_not_mem (fun h => hnot (List.mem_toFinset.2 h))
    _ = (P i).length := by
      simpa only [List.toFinset_coe, Multiset.coe_count, Multiset.coe_card] using
        Multiset.toFinset_sum_count_eq ((P i : List Nat) : Multiset Nat)

theorem inDegree_root {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    InDegree P (Live P r) r = 0 := by
  unfold InDegree
  apply Finset.sum_eq_zero
  intro i hi
  have il := walk_le (bounded_edge rules) ((live_iff rules).1 hi)
  apply List.count_eq_zero_of_not_mem
  intro ei
  exact (Nat.not_lt_of_le il) (edge_desc (rules i il) ei)

theorem inDegree_pos {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r j : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (hj : j ∈ Live P r) (ne : j ≠ r) : 1 ≤ InDegree P (Live P r) j := by
  obtain ⟨i, wi, ei⟩ := ((live_iff rules).1 hj).cases_tail.resolve_left ne
  have im : i ∈ Live P r := (live_iff rules).2 wi
  have h := Finset.single_le_sum (f := fun u => (P u).count j) (fun _ _ => Nat.zero_le _) im
  exact (Nat.succ_le_of_lt (List.count_pos_iff.2 ei.2)).trans h

noncomputable def Surplus (P : Parents) (r : Nat) : Nat :=
  ∑ j ∈ (Live P r).erase r, (InDegree P (Live P r) j - 1)

theorem surplus_identity {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    (∑ i ∈ Live P r, (P i).length) + 1 = (Live P r).card + Surplus P r := by
  have h1 := count_edges (fun i hi j hj => live_closed rules hi hj)
  have root : r ∈ Live P r := (live_iff rules).2 .refl
  have hsum := Finset.sum_erase_add (Live P r) (InDegree P (Live P r)) root
  rw [inDegree_root rules, Nat.add_zero, h1] at hsum
  have hc := Finset.card_erase_of_mem root
  have hp := Finset.card_pos.2 ⟨_, root⟩
  have eq : ∑ j ∈ (Live P r).erase r, InDegree P (Live P r) j =
      ∑ j ∈ (Live P r).erase r, (InDegree P (Live P r) j - 1 + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨ne, hm⟩ := Finset.mem_erase.1 hj
    have lb := inDegree_pos rules hm ne
    omega
  have hone : (∑ _ ∈ (Live P r).erase r, (1 : Nat)) = ((Live P r).erase r).card := by simp
  rw [Finset.sum_add_distrib, hone] at eq
  unfold Surplus
  omega

noncomputable def WithArity (P : Parents) (r n : Nat) : Finset Nat :=
  (Live P r).filter (fun j => (P j).length = n)

theorem length_le_two {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {i : Nat} (h : Rule F C P i) :
    (P i).length ≤ 2 := by
  rcases h with ⟨r, _⟩ | ⟨j, _, r, _⟩ | ⟨j, _, k, _, r, _⟩ <;> simp [r]

theorem arity_sum (P : Parents) (r n k : Nat) :
    (∑ i ∈ Live P r, if (P i).length = n then k else 0) = k * (WithArity P r n).card := by
  rw [← Finset.sum_filter]
  simp [WithArity, Nat.mul_comm]
theorem arity_count {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    (Live P r).card + 1 =
      2 * (WithArity P r 0).card + (WithArity P r 1).card + Surplus P r := by
  have hk : ∀ i ∈ Live P r, (P i).length ≤ 2 := by
    intro i hi
    exact length_le_two (rules i (walk_le (bounded_edge rules) ((live_iff rules).1 hi)))
  have decomp :
      (Live P r).card = (WithArity P r 0).card + (WithArity P r 1).card + (WithArity P r 2).card := by
    have h : ∑ i ∈ Live P r, (1 : Nat) = ∑ i ∈ Live P r,
        ((if (P i).length = 0 then 1 else 0) + (if (P i).length = 1 then 1 else 0) +
          (if (P i).length = 2 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hk i hi
      have := show (P i).length = 0 ∨ (P i).length = 1 ∨ (P i).length = 2 by omega
      rcases this with e | e | e <;> simp [e]
    have countOnes : (∑ _ ∈ Live P r, (1 : Nat)) = (Live P r).card := by simp
    rw [countOnes] at h
    simpa only [Finset.sum_add_distrib, arity_sum, one_mul] using h
  have edges :
      (∑ i ∈ Live P r, (P i).length) = (WithArity P r 1).card + 2 * (WithArity P r 2).card := by
    have h : ∑ i ∈ Live P r, (P i).length = ∑ i ∈ Live P r,
        ((if (P i).length = 1 then 1 else 0) + (if (P i).length = 2 then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hk i hi
      have := show (P i).length = 0 ∨ (P i).length = 1 ∨ (P i).length = 2 by omega
      rcases this with e | e | e <;> simp [e]
    simpa only [Finset.sum_add_distrib, arity_sum, one_mul] using h
  have hs := surplus_identity rules
  omega

theorem shared_degree {P : Parents} {s : Finset Nat} {p q m : Nat}
    (hp : p ∈ s) (hq : q ∈ s) (ep : Edge P p m) (eq : Edge P q m) (ne : p ≠ q) :
    2 ≤ InDegree P s m := by
  have tm : ({p, q} : Finset Nat) ⊆ s := by
    intro i hi
    rcases (by simpa using hi : i = p ∨ i = q) with rfl | rfl <;> assumption
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun u => (P u).count m) tm
    (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert (Finset.notMem_singleton.2 ne), Finset.sum_singleton] at hs
  have lp := List.count_pos_iff.2 ep
  have lq := List.count_pos_iff.2 eq
  unfold InDegree
  omega

theorem only_one_share {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r m z : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (budget : Surplus P r ≤ 1)
    (hm : m ∈ Live P r) (hz : z ∈ Live P r)
    (sm : 2 ≤ InDegree P (Live P r) m) (sz : 2 ≤ InDegree P (Live P r) z) :
    m = z := by
  by_contra hne
  have nr := inDegree_root rules
  have mn : m ≠ r := by
    rintro rfl
    omega
  have zn : z ≠ r := by
    rintro rfl
    omega
  have both : ({m,z} : Finset Nat) ⊆ (Live P r).erase r := by
    intro j hj
    rcases (by simpa using hj : j = m ∨ j = z) with rfl | rfl
    · exact Finset.mem_erase.2 ⟨mn,hm⟩
    · exact Finset.mem_erase.2 ⟨zn,hz⟩
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun j => InDegree P (Live P r) j - 1) both (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert (Finset.notMem_singleton.2 hne), Finset.sum_singleton] at hh
  unfold Surplus at budget
  omega

theorem walk_localize {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {a : V → Bool} {i j : Nat} (hi : i ≤ r)
    (w : Walk (fun u v => Edge P u v ∧ FalseAt C a v) i j) :
    Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j ∧ j ≤ r := by
  induction w with
  | refl => exact ⟨.refl, hi⟩
  | tail _ e ih =>
    have next := (edge_desc (rules _ ih.2) e.1).le.trans ih.2
    exact ⟨.tail ih.1 ⟨⟨ih.2, e.1⟩, next, e.2⟩, next⟩

theorem localized_route {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (a : V → Bool) {i : Nat} (hi : i ≤ r) (fi : FalseAt C a i) :
    ∃ j, P j = [] ∧ C j ∈ F ∧ FalseAt C a j ∧
      Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j := by
  obtain ⟨j, h0, ha, ff, w⟩ := follow (n := r+1)
    (fun i hi => rules i (Nat.lt_succ_iff.1 hi)) a (Nat.lt_succ_iff.2 hi) fi
  exact ⟨j, h0, ha, ff, (walk_localize rules hi w).1⟩

theorem live_card_le (P : Parents) (r : Nat) : (Live P r).card ≤ r + 1 := by
  classical
  unfold Live
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem unique_leaves {V κ : Type} [DecidableEq V] [Fintype κ]
    {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (fr : ∀ a, FalseAt C a r)
    (ax : κ → LinClause V) (exh : F = Set.range ax)
    (critical : ∀ k, ∃ a : V → Bool, ∀ j, ¬ LinClauseSat a (ax j) ↔ j = k) :
    ∃ leaf : κ → Nat, Function.Injective leaf ∧
      (∀ k, leaf k ∈ WithArity P r 0 ∧ C (leaf k) = ax k) ∧
      Fintype.card κ ≤ (WithArity P r 0).card ∧
      ((WithArity P r 0).card = Fintype.card κ →
        ∀ j ∈ WithArity P r 0, ∃ k, leaf k = j) := by
  classical
  have located : ∀ k, ∃ j, j ∈ WithArity P r 0 ∧ C j = ax k := by
    intro k
    obtain ⟨a, cert⟩ := critical k
    obtain ⟨j, hj, hc, ff, w⟩ := localized_route rules a le_rfl (fr a)
    rw [exh] at hc
    obtain ⟨k', hk'⟩ := hc
    have h : ¬ LinClauseSat a (ax k') := by simpa [FalseAt, hk'] using ff
    have eq := (cert k').1 h
    subst k'
    refine ⟨j, ?_, hk'.symm⟩
    simp only [WithArity, Finset.mem_filter, hj, List.length_nil, and_true]
    exact (live_iff rules).2 (walk_sub (fun e => e.1) w)
  choose leaf spec using located
  have inj : Function.Injective leaf := by
    intro u v h
    obtain ⟨a, cert⟩ := critical u
    have hEq := (spec u).2.symm.trans ((congrArg C h).trans (spec v).2)
    have no := (cert u).2 rfl
    rw [hEq] at no
    exact ((cert v).1 no).symm
  have ss : Finset.univ.image leaf ⊆ WithArity P r 0 := by
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hj
    exact (spec k).1
  have card : (Finset.univ.image leaf).card = Fintype.card κ := by
    rw [Finset.card_image_of_injective _ inj, Finset.card_univ]
  refine ⟨leaf, inj, spec, by simpa [card] using Finset.card_le_card ss, ?_⟩
  intro eq j hj
  have e : Finset.univ.image leaf = WithArity P r 0 :=
    Finset.eq_of_subset_of_card_le ss (by rw [eq, card])
  rw [← e] at hj
  obtain ⟨k, _, e⟩ := Finset.mem_image.1 hj
  exact ⟨k, e⟩

noncomputable def useful {V : Type} (R : LinClause V) : Bool := by
  classical
  exact decide (∃ a, ¬ LinClauseSat a R)

theorem useful_spec {V : Type} (R : LinClause V) :
    useful R = true ↔ ∃ a, ¬ LinClauseSat a R := by
  classical
  simp [useful]

theorem prune_taut {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} (der : IsLinDerivation F π) :
    IsLinDerivation F (π.filter useful) := by
  induction der with
  | nil => exact .nil
  | @ax π D _ hD ih =>
    simp only [List.filter_cons]
    split
    · exact .ax ih hD
    · exact ih
  | @res π D H R _ d h resolvent ih =>
    simp only [List.filter_cons]
    by_cases ur : useful R = true
    · rw [ite_eq_left ur]
      obtain ⟨f, df, hf, rr⟩ := resolvent
      by_cases ud : useful D = true
      · have md := List.mem_filter.2 ⟨d, ud⟩
        by_cases uh : useful H = true
        · exact .res ih md (List.mem_filter.2 ⟨h, uh⟩) ⟨f, df, hf, rr⟩
        · exact .weak ih md (by
            intro a sat
            by_contra no
            have b := resolve_branch a rr no
            split at b
            · exact b sat
            · exact uh ((useful_spec _).2 ⟨a, b⟩))
      · have weak : ∀ a, LinClauseSat a H → LinClauseSat a R := by
          intro a sat
          by_contra no
          have b := resolve_branch a rr no
          split at b
          · exact ud ((useful_spec _).2 ⟨a, b⟩)
          · exact b sat
        obtain ⟨a, ff⟩ := (useful_spec _).1 ur
        have hu : useful H = true := (useful_spec _).2 ⟨a, fun s => ff (weak a s)⟩
        exact .weak ih (List.mem_filter.2 ⟨h, hu⟩) weak
    · rw [ite_eq_right ur]
      exact ih
  | @weak π D R _ hD hw ih =>
    simp only [List.filter_cons]
    by_cases ur : useful R = true
    · rw [ite_eq_left ur]
      obtain ⟨a, no⟩ := (useful_spec _).1 ur
      exact .weak ih (List.mem_filter.2 ⟨hD, (useful_spec _).2 ⟨a, fun h => no (hw a h)⟩⟩) hw
    · rw [ite_eq_right ur]
      exact ih

theorem encoded_useful {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} {C : ClauseMap V} {P : Parents}
    (h : Encoded F C P (π.filter useful)) {i : Nat} (hi : i < (π.filter useful).length) :
    ∃ a, FalseAt C a i := by
  have mm := (h.2 _).2 ⟨i, hi, rfl⟩
  exact (useful_spec _).1 (List.mem_filter.1 mm).2

theorem walk_keep_live {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {a : V → Bool} {i j : Nat} (hi : i ∈ Live P r)
    (w : Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j) :
    Walk (fun u v => LocalEdge P r u v ∧ (v ∈ Live P r ∧ FalseAt C a v)) i j ∧ j ∈ Live P r := by
  induction w with
  | refl => exact ⟨.refl, hi⟩
  | tail _ e ih =>
    have hm := live_closed rules ih.2 e.1.2
    exact ⟨.tail ih.1 ⟨e.1, hm, e.2.2⟩, hm⟩

theorem high_weak_shared {V κ : Type} [DecidableEq V] [Fintype κ]
    {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents} {r c d : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (fr : ∀ a, FalseAt C a r)
    (rc : LocalEdge P r r c) (rd : LocalEdge P r r d) (ne : c ≠ d)
    (size : (Live P r).card ≤ 47) (wcount : 3 ≤ (WithArity P r 1).card)
    (labels : Fintype.card κ = 22)
    (ax : κ → LinClause V) (exh : F = Set.range ax) (point : κ → (V → Bool) → Prop)
    (point_exists : ∀ k, ∃ a, point k a)
    (one : ∀ {a k}, point k a → ∀ j, (¬ LinClauseSat a (ax j)) ↔ j = k)
    (side : (V → Bool) → Bool)
    (side_choose : ∀ a, FalseAt C a (if side a then c else d))
    (force_exists : ∃ a, Forced (fun a k => ¬ LinClauseSat a (ax k)) point side a) :
    ∃ z < r,
      (∀ a, Forced (fun a k => ¬ LinClauseSat a (ax k)) point side a → FalseAt C a z) ∧
      (∀ a, FalseAt C a z → ∃ k, (¬ LinClauseSat a (ax k)) ∧ ∀ b, point k b → FalseAt C b z) ∧
      (∀ a, ¬ FalseAt C a z → ∃ k, (¬ LinClauseSat a (ax k)) ∧ ∃ b, point k b ∧ ¬ FalseAt C b z) := by
  have crit : ∀ k, ∃ a : V → Bool, ∀ j, (¬ LinClauseSat a (ax j)) ↔ j = k := by
    intro k
    obtain ⟨a, ha⟩ := point_exists k
    exact ⟨a, one ha⟩
  obtain ⟨leaf, _, atLeaf, lb, covers⟩ := unique_leaves rules fr ax exh crit
  have card := arity_count rules
  have ex : (WithArity P r 0).card = Fintype.card κ := by omega
  have su : Surplus P r ≤ 1 := by omega
  let E := LocalEdge P r
  let B := fun a i => i ∈ Live P r ∧ FalseAt C a i
  let bad := fun a k => ¬ LinClauseSat a (ax k)
  have branch : ∀ a, B a (if side a then c else d) := by
    intro a
    refine ⟨?_, side_choose a⟩
    cases h : side a
    · exact (live_iff rules).2 (by simpa [h] using (Relation.ReflTransGen.single rd))
    · exact (live_iff rules).2 (by simpa [h] using (Relation.ReflTransGen.single rc))
  have route : ∀ a i, B a i →
      ∃ k, bad a k ∧ Walk (fun u v => E u v ∧ B a v) i (leaf k) := by
    intro a i bi
    have ir := walk_le (bounded_edge rules) ((live_iff rules).1 bi.1)
    obtain ⟨j, j0, _, jf, w⟩ := localized_route rules a ir bi.2
    obtain ⟨wm, jm⟩ := walk_keep_live rules bi.1 w
    have jax : j ∈ WithArity P r 0 := by simpa [WithArity, j0] using jm
    obtain ⟨k, hk⟩ := covers ex j jax
    have ceq : C j = ax k := hk ▸ (atLeaf k).2
    exact ⟨k, by simpa [bad, FalseAt, ceq] using jf, hk ▸ wm⟩
  have desc : ∀ {i j}, E i j → j < i := bounded_edge rules
  obtain ⟨a, ha⟩ := force_exists
  obtain ⟨p, q, z, hp, hq, ep, eq, pq, _, common⟩ :=
    entry_exists desc rc rd ne bad point leaf B side one branch route point_exists ha
  have from_left : ∀ {p}, p = r ∨ Walk E c p → p ∈ Live P r := by
    intro p hp
    rcases hp with rfl | hp
    · exact (live_iff rules).2 .refl
    · exact (live_iff rules).2 (.head rc hp)
  have from_right : ∀ {p}, p = r ∨ Walk E d p → p ∈ Live P r := by
    intro p hp
    rcases hp with rfl | hp
    · exact (live_iff rules).2 .refl
    · exact (live_iff rules).2 (.head rd hp)
  have zl : z ∈ Live P r := live_closed rules (from_left hp) ep.2
  have zd : 2 ≤ InDegree P (Live P r) z := shared_degree (from_left hp) (from_right hq) ep.2 eq.2 pq
  have one_merge : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z := by
    intro p q m hp hq ep eq pq
    have ml := live_closed rules (from_left hp) ep.2
    exact only_one_share rules su ml zl
      (shared_degree (from_left hp) (from_right hq) ep.2 eq.2 pq) zd
  have lem := one_entry_characterization desc rc rd ne bad point leaf B side one branch route
    point_exists one_merge common
  have zr : z < r := (desc ep).trans_le ep.1
  exact ⟨z, zr, by simpa [B, zl] using lem⟩

end PEqualNP.Outside.L_pcx_118.Graph
namespace PEqualNP.Outside.L_pcx_178.Split
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Bridge PEqualNP.Outside.L_pcx_118.Graph

def Used (P : Parents) (r i j : Nat) : Prop := i ∈ Live P r ∧ Edge P i j
def Stop (P : Parents) (r i : Nat) : Prop := i = r ∨ Edge P r i ∨ 2 ≤ InDegree P (Live P r) i
def Private (P : Parents) (r p i : Nat) : Prop :=
  Used P r p i ∧ ¬ Stop P r i ∧ ∀ q, Used P r q i → q=p

theorem ownerExists {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {k : Nat} (hk : k ∈ Live P r) :
    ∃ u ∈ Live P r, Stop P r u ∧ Walk (Private P r) u k := by
  classical
  suffices aux : ∀ d i, r-i=d → i ∈ Live P r →
      ∃ u ∈ Live P r, Stop P r u ∧ Walk (Private P r) u i from aux _ k rfl hk
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro i eq live
    by_cases stop : Stop P r i
    · exact ⟨i,live,stop,.refl⟩
    have ne : i ≠ r := fun e => stop (Or.inl e)
    obtain ⟨p,wp,ep⟩ := ((live_iff rules).1 live).cases_tail.resolve_left ne
    have lp := (live_iff rules).2 wp
    have ip := bounded_edge rules ep
    have pr := walk_le (bounded_edge rules) wp
    obtain ⟨u,lu,su,path⟩ := ih (r-p) (by omega) p rfl lp
    refine ⟨u,lu,su,.tail path ⟨⟨lp,ep.2⟩,stop,?_⟩⟩
    intro q hq
    by_contra distinct
    exact stop (Or.inr (Or.inr (shared_degree hq.1 lp hq.2 ep.2 distinct)))

theorem retreat {P : Parents} {r u k t : Nat} {B : Nat → Prop}
    (suffix : Walk (Private P r) u k) (st : Stop P r t)
    (path : Walk (fun i j => Used P r i j ∧ B j) t k) :
    Walk (fun i j => Used P r i j ∧ B j) t u := by
  induction suffix with
  | refl => exact path
  | @tail p j _ hp ih =>
    rcases path.cases_tail with eq | ⟨q,w,hq⟩
    · exact False.elim (hp.2.1 (eq.symm ▸ st))
    · have same : q=p := hp.2.2 q hq.1
      subst q
      exact ih w

theorem markEnd {E : Nat → Nat → Prop} {B : Nat → Prop} {i j : Nat} (bi : B i)
    (w : Walk (fun p q => E p q ∧ B q) i j) : B j := by
  induction w with
  | refl => exact bi
  | tail _ last _ => exact last.2

theorem used_desc {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i j : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (e : Used P r i j) : j < i :=
  bounded_edge rules ⟨walk_le (bounded_edge rules) ((live_iff rules).1 e.1),e.2⟩

theorem usedPath {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i j : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (a : V → Bool) (li : i ∈ Live P r)
    (path : Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j) :
    Walk (fun u v => Used P r u v ∧ FalseAt C a v) i j ∧ j ∈ Live P r := by
  induction path with
  | refl => exact ⟨.refl,li⟩
  | tail _ last ih =>
    exact ⟨.tail ih.1 ⟨⟨ih.2,last.1.2⟩,last.2.2⟩,live_closed rules ih.2 last.1.2⟩

abbrev Leaf (P : Parents) (r : Nat) := {i : Nat // i ∈ WithArity P r 0}

theorem owners {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (empty : ∀ a, FalseAt C a r) (head : P r ≠ []) :
    ∃ own : Leaf P r → Nat,
      (∀ k, own k ∈ Live P r ∧ Stop P r (own k) ∧ Walk (Private P r) (own k) k.val ∧ own k < r) ∧
      (∀ a u, (∀ k : Leaf P r, FalseAt C a k.val → own k = u) → FalseAt C a u) ∧
      (∀ a u, u ∈ Live P r → Stop P r u → FalseAt C a u →
        ∃ k : Leaf P r, FalseAt C a k.val ∧
          (own k = u ∨ own k < u ∧ FalseAt C a (own k))) := by
  classical
  have pick (k : Leaf P r) := ownerExists rules (Finset.mem_filter.1 k.property).1
  choose own spec using pick
  have route (a : V → Bool) (u : Nat) (lu : u ∈ Live P r) (fu : FalseAt C a u) :
      ∃ k : Leaf P r, FalseAt C a k.val ∧ Walk (fun i j => Used P r i j ∧ FalseAt C a j) u k.val := by
    have ur := walk_le (bounded_edge rules) ((live_iff rules).1 lu)
    obtain ⟨j,hj,_,fj,w⟩ := localized_route rules a ur fu
    obtain ⟨w',lj⟩ := usedPath rules a lu w
    exact ⟨⟨j,Finset.mem_filter.2 ⟨lj,by simp [hj]⟩⟩,fj,w'⟩
  have small (k : Leaf P r) : own k < r := by
    have le := walk_le (bounded_edge rules) ((live_iff rules).1 (spec k).1)
    by_contra! h
    have eq : own k = r := by omega
    have ww := (spec k).2.2
    rw [eq] at ww
    rcases ww.cases_head with e | ⟨v,edge,_⟩
    · have nil := (Finset.mem_filter.1 k.property).2
      have same : k.val = r := by omega
      rw [same] at nil
      exact head (List.length_eq_zero_iff.mp nil)
    · exact edge.2.1 (Or.inr (Or.inl edge.1.2))
  refine ⟨own,fun k => ⟨(spec k).1,(spec k).2.1,(spec k).2.2,small k⟩,?_,?_⟩
  · intro a u covered
    have lr : r ∈ Live P r := (live_iff rules).2 .refl
    obtain ⟨k,bad,path⟩ := route a r lr (empty a)
    have w := retreat (spec k).2.2 (Or.inl rfl : Stop P r r) path
    exact covered k bad ▸ markEnd (empty a) w
  · intro a u lu su fu
    obtain ⟨k,bad,path⟩ := route a u lu fu
    have w := retreat (spec k).2.2 su path
    have le := walk_le (fun {i j} (h : Used P r i j ∧ FalseAt C a j) => used_desc rules h.1) w
    exact ⟨k,bad,le.eq_or_lt.imp_right (fun lt => ⟨lt,markEnd fu w⟩)⟩

end PEqualNP.Outside.L_pcx_178.Split

namespace Lpcx178ThreeDemands
open PEqualNP.ProofComplexity
section
variable {V : Type} [DecidableEq V]
def flip (x : V→Bool) (v : V) (i : V) := if i=v then !(x i) else x i

theorem opposite {x : V→Bool} {f : Finset V} {v : V} (hv : v∈f) (b : Bool) :
    LinEqSat (flip x v) (f,b) ↔ ¬LinEqSat x (f,b) := by
  let S := (f.erase v).filter (fun i=>x i=true)
  have nv : v∉S := by simp [S]
  have h0 : f.filter (fun i=>x i=true) = (if x v then insert v S else S) := by
    ext i
    by_cases he : i=v
    · subst i
      cases hx : x v <;> simp [hx,hv,S]
    · cases hx : x v <;> simp [hx,S,he]
  have h1 : f.filter (fun i=>flip x v i=true) = (if x v then S else insert v S) := by
    ext i
    by_cases he : i=v
    · subst i
      cases hx : x v <;> simp [hx,hv,S,flip]
    · cases hx : x v <;> simp [hx,S,he,flip]
  unfold LinEqSat
  change (Odd (f.filter (fun i=>flip x v i=true)).card ↔ b=true) ↔
    ¬(Odd (f.filter (fun i=>x i=true)).card ↔ b=true)
  rw [h0,h1]
  cases xx : x v <;> cases b <;> simp [xx,Finset.card_insert_of_notMem nv,Nat.odd_iff] <;> omega


end
abbrev Cell := Fin 5 × Fin 4
def board (x : Cell → Bool) : Prop :=
  ∀ i j : Cell, i.2 = j.2 → x i = true → x j = true → i = j
def served (x : Cell → Bool) (p : Fin 5) := ∃ h, x (p,h) = true
def seed (r : Fin 3 → Fin 5) (k : Fin 3 → Fin 4) (v : Cell) : Bool :=
  decide (∃ n : Fin 3, v = (r n, k n))

theorem freshHoles : ∀ h : Fin 4, ∃ k : Fin 3 → Fin 4,
    Function.Injective k ∧ ∀ n, k n ≠ h := by decide +kernel

theorem seedBoard (r : Fin 3 → Fin 5) {k : Fin 3 → Fin 4} (inj : Function.Injective k) :
    board (seed r k) := by
  intro i j eq hi hj
  obtain ⟨m,ei⟩ := of_decide_eq_true hi
  obtain ⟨n,ej⟩ := of_decide_eq_true hj
  subst i
  subst j
  obtain rfl := inj eq
  rfl

theorem seedServed (r : Fin 3 → Fin 5) (k : Fin 3 → Fin 4) (n : Fin 3) :
    served (seed r k) (r n) :=
  ⟨k n,decide_eq_true ⟨n,rfl⟩⟩

theorem freshFlip (x : Cell → Bool) (i : Cell) (hx : board x)
    (clear : ∀ u : Cell, u.2 = i.2 → x u = false) : board (flip x i) := by
  intro u v eq hu hv
  by_cases ui : u = i
  · by_cases vi : v = i
    · exact ui.trans vi.symm
    · have z := clear v (eq.symm.trans (congrArg Prod.snd ui))
      simp [flip,vi,z] at hv
  · by_cases vi : v = i
    · have z := clear u (eq.trans (congrArg Prod.snd vi))
      simp [flip,ui,z] at hu
    · exact hx u v eq (by simpa [flip,ui] using hu) (by simpa [flip,vi] using hv)

theorem threeDemandFiber {f : Finset Cell} (h : f.Nonempty) (b : Bool)
    (r : Fin 3 → Fin 5) :
    ∃ x : Cell → Bool, board x ∧ (∀ n, served x (r n)) ∧ LinEqSat x (f,b) := by
  obtain ⟨i,hi⟩ := h
  obtain ⟨k,inj,avoid⟩ := freshHoles i.2
  let x := seed r k
  have bx : board x := seedBoard r inj
  have clear (u : Cell) (hu : u.2 = i.2) : x u = false := by
    change decide (∃ n : Fin 3, u = (r n,k n)) = false
    apply decide_eq_false
    rintro ⟨n,e⟩
    exact avoid n ((congrArg Prod.snd e).symm.trans hu)
  by_cases hit : LinEqSat x (f,b)
  · exact ⟨x,bx,seedServed r k,hit⟩
  · refine ⟨flip x i,freshFlip x i bx clear,?_,(opposite hi b).mpr hit⟩
    intro n
    have ne : (r n,k n) ≠ i := fun e => avoid n (congrArg Prod.snd e)
    refine ⟨k n,?_⟩
    have yes : x (r n,k n) = true := decide_eq_true ⟨n,rfl⟩
    simpa [flip,ne] using yes

theorem noThreeDemandFiberClause {f : Finset Cell} (h : f.Nonempty) (b : Bool)
    (r : Fin 3 → Fin 5) (K : LinClause Cell)
    (valid : ∀ x, board x → (∀ n, served x (r n)) → LinClauseSat x K) :
    ¬ (∀ x, LinEqSat x (f,b) → ¬ LinClauseSat x K) := by
  obtain ⟨x,bx,rows,hf⟩ := threeDemandFiber h b r
  exact fun bad => bad x hf (valid x bx rows)


theorem threeRowsSpan (K : LinClause Cell) (r : Fin 3 → Fin 5)
    {z : Cell → Bool} (hz : LinClauseSat z K) :
    ∃ x : Cell → Bool, board x ∧ (∀ n, served x (r n)) ∧ LinClauseSat x K := by
  obtain ⟨⟨f,b⟩,mem,eq⟩ := hz
  by_cases nonempty : f.Nonempty
  · obtain ⟨x,bx,rows,hit⟩ := threeDemandFiber nonempty b r
    exact ⟨x,bx,rows,(f,b),mem,hit⟩
  · have fe : f = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    subst f
    obtain ⟨x,bx,rows,_⟩ := threeDemandFiber
      (f := {((0 : Fin 5),(0 : Fin 4))}) (by simp) false r
    refine ⟨x,bx,rows,(∅,b),mem,?_⟩
    unfold LinEqSat at eq ⊢
    simpa only [Finset.filter_empty] using eq

theorem noProperDominator (K : LinClause Cell) (r : Fin 3 → Fin 5)
    (onlyPaths : ∀ x, board x → (∀ n, served x (r n)) → ¬ LinClauseSat x K) :
    ∀ z, ¬ LinClauseSat z K := by
  intro z hit
  obtain ⟨x,bx,rows,sat⟩ := threeRowsSpan K r hit
  exact onlyPaths x bx rows sat

theorem resolutionSound {x : Cell → Bool} {C D R : LinClause Cell}
    (p : IsLinResolvent C D R) (c : LinClauseSat x C) (d : LinClauseSat x D) :
    LinClauseSat x R := by
  obtain ⟨f,_,_,rfl⟩ := p
  obtain ⟨u,hu,su⟩ := c
  obtain ⟨v,hv,sv⟩ := d
  by_cases e : u = (f,false)
  · by_cases e' : v = (f,true)
    · subst u
      subst v
      have impossible : false = true := su.mp (sv.mpr rfl)
      contradiction
    · exact ⟨v,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨e',hv⟩),sv⟩
  · exact ⟨u,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hu⟩),su⟩

theorem derivationSound {F : Set (LinClause Cell)} {π} {x : Cell → Bool}
    (d : IsLinDerivation F π) (init : ∀ C ∈ F, LinClauseSat x C) :
    ∀ C ∈ π, LinClauseSat x C := by
  induction d with
  | nil => simp
  | ax _ ax ih =>
    intro C hc
    rcases List.mem_cons.mp hc with rfl|old
    · exact init _ ax
    · exact ih _ old
  | res _ hC hD step ih =>
    intro R hr
    rcases List.mem_cons.mp hr with rfl|old
    · exact resolutionSound step (ih _ hC) (ih _ hD)
    · exact ih _ old
  | weak _ hc w ih =>
    intro D hd
    rcases List.mem_cons.mp hd with rfl|old
    · exact w _ (ih _ hc)
    · exact ih _ old

def row (p : Fin 5) : Clause Cell :=
  Finset.univ.image (fun h : Fin 4 => ((p,h),true))
def coll (p q : Fin 5) (h : Fin 4) : Clause Cell :=
  {((p,h),false),((q,h),false)}
def threeAxioms (r : Fin 3 → Fin 5) : Set (LinClause Cell) :=
  {K | (∃ n, K = linOfClause (row (r n))) ∨
       ∃ p q h, p ≠ q ∧ K = linOfClause (coll p q h)}

theorem litEq {x : Cell → Bool} (v : Cell) (b : Bool) (h : x v = b) :
    LinEqSat x ({v},b) := by
  have e : ({v} : Finset Cell).filter (fun u => x u = true) = (if b then {v} else ∅) := by
    ext u
    by_cases eq : u = v
    · subst u
      cases b <;> simp [h]
    · cases b <;> simp [eq]
  unfold LinEqSat
  change (Odd (({v} : Finset Cell).filter (fun u => x u = true)).card ↔ b = true)
  rw [e]
  cases b <;> simp

theorem axiomsTrue {x : Cell → Bool} (r : Fin 3 → Fin 5) (xb : board x)
    (rows : ∀ n, served x (r n)) : ∀ A ∈ threeAxioms r, LinClauseSat x A := by
  intro A ha
  rcases ha with ⟨n,rfl⟩|⟨p,q,h,pq,rfl⟩
  · obtain ⟨h,yes⟩ := rows n
    refine ⟨_,Finset.mem_image.mpr ⟨((r n,h),true),?_,rfl⟩,litEq _ true yes⟩
    exact Finset.mem_image.mpr ⟨h,Finset.mem_univ _,rfl⟩
  · have no : x (p,h) = false ∨ x (q,h) = false := by
      by_cases hp : x (p,h) = true
      · right
        cases hq : x (q,h) with
        | false => rfl
        | true => exact (pq (congrArg Prod.fst (xb (p,h) (q,h) rfl hp hq))).elim
      · left
        cases h : x (p,h) <;> simp_all
    rcases no with no|no
    · exact ⟨_,Finset.mem_image.mpr ⟨((p,h),false),by simp [coll],rfl⟩,litEq _ false no⟩
    · exact ⟨_,Finset.mem_image.mpr ⟨((q,h),false),by simp [coll],rfl⟩,litEq _ false no⟩


end Lpcx178ThreeDemands

namespace PEqualNP.Outside.L_pcx_178.Five
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Graph PEqualNP.Outside.L_pcx_118.Bridge
open PEqualNP.Outside.L_pcx_178.Split Lpcx178ThreeDemands
abbrev F := (linOfClause '' PHP 5 4 : Set (LinClause Cell))
theorem otherThree : ∀ p q : Fin 5, p ≠ q → ∃ a b c : Fin 5,
  ∀ i : Fin 5, i = p ∨ i = q ∨ i = a ∨ i = b ∨ i = c := by decide +kernel

theorem onlyTwo {C : ClauseMap Cell} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule F C P i)
    {p q : Fin 5} {a b c : Fin 5} (cover : ∀ i : Fin 5, i=p ∨ i=q ∨ i=a ∨ i=b ∨ i=c)
    (x : Cell → Bool) (xb : board x) (serv : ∀ t : Fin 3, served x (![a,b,c] t))
    {k : Leaf P r} (ff : FalseAt C x k.val) :
    C k.val = linOfClause (row p) ∨ C k.val = linOfClause (row q) := by
  have live := (Finset.mem_filter.mp k.property).1
  have m := walk_le (bounded_edge rules) ((live_iff rules).1 live)
  have pn : P k.val = [] := List.length_eq_zero_iff.mp (Finset.mem_filter.mp k.property).2
  have ax : C k.val ∈ F := by
    rcases rules k.val m with ⟨_,hm⟩ | ⟨u,_,e,_⟩ | ⟨u,_,v,_,e,_⟩
    · exact hm
    · rw [pn] at e; contradiction
    · rw [pn] at e; contradiction
  obtain ⟨D,hd,eq⟩ := ax
  rcases hd with ⟨i,rfl⟩ | ⟨i,j,h,ne,rfl⟩
  · rcases cover i with e|e|e|e|e
    · exact Or.inl (by simpa [row,e] using eq.symm)
    · exact Or.inr (by simpa [row,e] using eq.symm)
    all_goals
      exfalso
      apply ff
      rw [←eq]
      apply axiomsTrue _ xb serv
      left
    · exact ⟨0,by simp [row,e]⟩
    · exact ⟨1,by simp [row,e]⟩
    · exact ⟨2,by simp [row,e]⟩
  · exfalso
    apply ff
    rw [←eq]
    exact axiomsTrue _ xb serv _ (Or.inr ⟨i,j,h,ne,rfl⟩)

theorem rowNames {C : ClauseMap Cell} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (empty : ∀ x, FalseAt C x r)
    (prev : ∀ i<r, ∃ a, LinClauseSat a (C i)) (head : P r ≠ [])
    (inj : Set.InjOn C (↑(Live P r) : Set Nat))
    (atRow : Fin 5 → Leaf P r) (rows : ∀ i, C (atRow i).val = linOfClause (row i)) (own : Leaf P r → Nat)
    (whereAt : ∀ k, own k ∈ Live P r ∧ Stop P r (own k) ∧ Walk (Private P r) (own k) k.val ∧ own k < r)
    (must : ∀ x u, (∀ k : Leaf P r, FalseAt C x k.val → own k = u) → FalseAt C x u) :
    Function.Injective (fun i => own (atRow i)) := by
  classical
  intro p q eq
  by_contra ne
  obtain ⟨a,b,c,cover⟩ := otherThree p q ne
  let u := own (atRow p)
  obtain ⟨z,hit⟩ := prev u (whereAt (atRow p)).2.2.2
  obtain ⟨x,xb,sv,yes⟩ := threeRowsSpan (C u) (![a,b,c]) hit
  apply (must x u ?_) yes
  intro k bad
  have L (j : Leaf P r) : j.val ∈ Live P r := (Finset.mem_filter.mp j.property).1
  rcases onlyTwo rules cover x xb sv bad with hp|hq
  · have id : k = atRow p := Subtype.ext (inj (L k) (L _) (hp.trans (rows p).symm))
    exact congrArg own id
  · have id : k = atRow q := Subtype.ext (inj (L k) (L _) (hq.trans (rows q).symm))
    exact (congrArg own id).trans eq.symm
theorem rowInj {C : ClauseMap Cell} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (empty : ∀ x, FalseAt C x r)
    (prev : ∀ i<r, ∃ a, LinClauseSat a (C i)) (head : P r ≠ [])
    (inj : Set.InjOn C (↑(Live P r) : Set Nat))
    (atRow : Fin 5 → Leaf P r) (rows : ∀ i, C (atRow i).val = linOfClause (row i)) :
    ∃ f : Fin 5 → Nat, Function.Injective f ∧ ∀ i,
      f i ∈ Live P r ∧ f i < r ∧ (Edge P r (f i) ∨ 2 ≤ InDegree P (Live P r) (f i)) := by
  classical
  obtain ⟨own,whereAt,must,_⟩ := owners rules empty head
  refine ⟨fun i => own (atRow i),?_,?_⟩
  · intro p q eq
    by_contra ne
    obtain ⟨a,b,c,cover⟩ := otherThree p q ne
    let u := own (atRow p)
    obtain ⟨z,hit⟩ := prev u (whereAt (atRow p)).2.2.2
    obtain ⟨x,xb,sv,yes⟩ := threeRowsSpan (C u) (![a,b,c]) hit
    apply (must x u ?_) yes
    intro k bad
    have L (j : Leaf P r) : j.val ∈ Live P r := (Finset.mem_filter.mp j.property).1
    rcases onlyTwo rules cover x xb sv bad with hp|hq
    · have id : k = atRow p := Subtype.ext (inj (L k) (L _) (hp.trans (rows p).symm))
      exact congrArg own id
    · have id : k = atRow q := Subtype.ext (inj (L k) (L _) (hq.trans (rows q).symm))
      exact (congrArg own id).trans eq.symm
  · intro i
    obtain ⟨l,st,_,lt⟩ := whereAt (atRow i)
    exact ⟨l,lt,st.resolve_left (Nat.ne_of_lt lt)⟩

theorem sharedThree {C : ClauseMap Cell} {P : Parents} {r u v : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (empty : ∀ x, FalseAt C x r)
    (prev : ∀ i<r, ∃ a, LinClauseSat a (C i)) (head : P r = [u,v])
    (inj : Set.InjOn C (↑(Live P r) : Set Nat))
    (atRow : Fin 5 → Leaf P r) (rows : ∀ i, C (atRow i).val = linOfClause (row i)) :
    3 ≤ Surplus P r := by
  classical
  obtain ⟨f,inject,sp⟩ := rowInj rules empty prev (by simp [head]) inj atRow rows
  let T := (Live P r).erase r
  let S := T.filter fun j => 2 ≤ InDegree P (Live P r) j
  have cap : S.card ≤ Surplus P r := by
    have low : (∑ j ∈ S, 1) ≤ ∑ j ∈ S, (InDegree P (Live P r) j - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := (Finset.mem_filter.mp hj).2
      omega
    have incl : S ⊆ T := Finset.filter_subset _ _
    have a : S.card ≤ ∑ j ∈ S, (InDegree P (Live P r) j - 1) := by simpa using low
    exact a.trans (Finset.sum_le_sum_of_subset_of_nonneg incl (by intros; omega))
  have inc : Finset.univ.image f ⊆ ({u,v} : Finset Nat) ∪ S := by
    intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨live,lt,e|h⟩ := sp i
    · apply Finset.mem_union_left
      simpa [Edge,head] using e
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨Nat.ne_of_lt lt,live⟩,h⟩)
  have lo := Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ inject,Finset.card_univ,Fintype.card_fin] at lo
  have hi := Finset.card_union_le ({u,v} : Finset Nat) S
  have uv : ({u,v} : Finset Nat).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  omega

def RootChild (P : Parents) (r j : Nat) := Edge P r j

theorem tightNames {C : ClauseMap Cell} {P : Parents} {r u v : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (empty : ∀ x, FalseAt C x r)
    (prev : ∀ i<r, ∃ a, LinClauseSat a (C i)) (head : P r = [u,v])
    (inj : Set.InjOn C (↑(Live P r) : Set Nat))
    (atRow : Fin 5 → Leaf P r) (rows : ∀ i, C (atRow i).val = linOfClause (row i))
    (budget : Surplus P r ≤ 3) :
    ∃ own : Leaf P r → Nat,
      (∀ k, own k ∈ Live P r ∧ Stop P r (own k) ∧ Walk (Private P r) (own k) k.val ∧ own k < r) ∧
      (∀ x u, (∀ k : Leaf P r, FalseAt C x k.val → own k = u) → FalseAt C x u) ∧
      Function.Injective (fun i => own (atRow i)) ∧
      (∀ j, j ∈ Live P r → j < r → Stop P r j → ∃ i, own (atRow i) = j) ∧
      (∀ j, Edge P r j → InDegree P (Live P r) j < 2) := by
  classical
  obtain ⟨own,loc,must,_⟩ := owners rules empty (by simp [head])
  let f := fun i => own (atRow i)
  have fi : Function.Injective f := rowNames rules empty prev (by simp [head]) inj atRow rows own loc must
  let T := (Live P r).erase r
  let S := T.filter (fun j => 2 ≤ InDegree P (Live P r) j)
  let A : Finset Nat := {u,v}
  have cap : S.card ≤ Surplus P r := by
    have low : (∑ j ∈ S, 1) ≤ ∑ j ∈ S, (InDegree P (Live P r) j - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := (Finset.mem_filter.mp hj).2
      omega
    have incl : S ⊆ T := Finset.filter_subset _ _
    have a : S.card ≤ ∑ j ∈ S, (InDegree P (Live P r) j - 1) := by simpa using low
    exact a.trans (Finset.sum_le_sum_of_subset_of_nonneg incl (by intros; omega))
  have parent (i : Nat) : Edge P r i ↔ i ∈ A := by simp [Edge,head,A]
  have incAll (j : Nat) (live : j ∈ Live P r) (lt : j < r) (stop : Stop P r j) : j ∈ A ∪ S := by
    rcases stop with eq|hj|hs
    · omega
    · exact Finset.mem_union_left _ ((parent j).mp hj)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨Nat.ne_of_lt lt,live⟩,hs⟩)
  have inc : Finset.univ.image f ⊆ A ∪ S := by
    intro j hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨live,stop,_,lt⟩ := loc (atRow i)
    exact incAll _ live lt stop
  have countImg : (Finset.univ.image f).card = 5 := by rw [Finset.card_image_of_injective _ fi, Finset.card_univ,Fintype.card_fin]
  have low := Finset.card_le_card inc
  have hi := Finset.card_union_add_card_inter A S
  have ac : A.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have eq : Finset.univ.image f = A ∪ S := Finset.eq_of_subset_of_card_le inc (by omega)
  have nil : A ∩ S = ∅ := Finset.card_eq_zero.mp (by omega)
  refine ⟨own,loc,must,fi,?_,?_⟩
  · intro j live lt stop
    have id := incAll j live lt stop
    rw [←eq] at id
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp id
    exact ⟨i,he⟩
  · intro j e
    by_contra! two
    have lr : r ∈ Live P r := (live_iff rules).2 .refl
    have live := live_closed rules lr e
    have lt := edge_desc (rules r (by omega)) e
    have both : j ∈ A ∩ S := Finset.mem_inter.mpr ⟨(parent j).mp e,
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨Nat.ne_of_lt lt,live⟩,two⟩⟩
    rw [nil] at both
    exact Finset.notMem_empty _ both

theorem exclusiveChild {C : ClauseMap Cell} {P : Parents} {r u j : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (first : Edge P r j)
    (one : InDegree P (Live P r) j < 2) (lt : u < r)
    (path : Walk (Used P r) u j) : u = j := by
  rcases path.cases_tail with h|⟨q,w,last⟩
  · exact h.symm
  · have lr : r ∈ Live P r := (live_iff rules).2 .refl
    have ql := walk_le (fun {i k} (edge : Used P r i k) => used_desc rules edge) w
    have two := shared_degree lr last.1 first last.2 (show r ≠ q by omega)
    omega

theorem traceOwner {C : ClauseMap Cell} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (own : Leaf P r → Nat)
    (loc : ∀ k, Walk (Private P r) (own k) k.val)
    {u : Nat} (lu : u ∈ Live P r) (st : Stop P r u) {x : Cell → Bool} (bad : FalseAt C x u) :
    ∃ k : Leaf P r, FalseAt C x k.val ∧ FalseAt C x (own k) ∧ Walk (Used P r) u (own k) := by
  have ur := walk_le (bounded_edge rules) ((live_iff rules).1 lu)
  obtain ⟨j,hj,_,fj,w⟩ := localized_route rules x ur bad
  obtain ⟨w',lj⟩ := usedPath rules x lu w
  let k : Leaf P r := ⟨j,Finset.mem_filter.2 ⟨lj,by simp [hj]⟩⟩
  have path := retreat (loc k) st w'
  exact ⟨k,fj,markEnd bad path,walk_sub (fun {_ _} h => h.1) path⟩

end PEqualNP.Outside.L_pcx_178.Five
namespace Lpcx178Sort
abbrev R := Fin 5
theorem sortedFive (f : R → Nat) (inj : Function.Injective f) (u v : Nat)
    (ne : u ≠ v) (atU : ∃ i, f i=u) (atV : ∃ i, f i=v) :
    ∃ e : R ≃ R, f (e 3)=u ∧ f (e 4)=v ∧
       ∀ i j : R, i.val<3 → j.val<3 → i.val<j.val → f (e i)<f (e j) := by
  classical
  let A := Finset.univ.image f
  have sizeA : A.card=5 := by
    dsimp [A]
    rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin]
  have mu : u ∈ A := by obtain ⟨i,he⟩:=atU; exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩
  have mv : v ∈ A := by obtain ⟨i,he⟩:=atV; exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩
  let B := (A.erase u).erase v
  have sizeB : B.card=3 := by
    change ((A.erase u).erase v).card=3
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm ne,mv⟩),Finset.card_erase_of_mem mu,sizeA]
  let order := B.orderIsoOfFin sizeB
  let g (i : R) : Nat := if h : i.val<3 then (order ⟨i.val,h⟩).val else if i=3 then u else v
  have low (i : R) (h : i.val<3) : g i∈B := by simpa [g,h] using (order ⟨i.val,h⟩).property
  have high (i : R) (h : ¬i.val<3) : i=3 ∨ i=4 := by
    by_cases eq : i.val=3
    · exact Or.inl (Fin.ext eq)
    · exact Or.inr (Fin.ext (by omega))
  have gu : g 3=u := by simp [g]
  have gv : g 4=v := by simp [g]
  have diff (i : R) (h : i.val<3) : g i≠u ∧ g i≠v := by
    have id := Finset.mem_erase.mp (low i h)
    exact ⟨(Finset.mem_erase.mp id.2).1,id.1⟩
  have increasing (i j : R) (hi : i.val<3) (hj : j.val<3) (lt : i.val<j.val) : g i < g j := by
    have oo := order.strictMono (show (⟨i.val,hi⟩ : Fin 3) < ⟨j.val,hj⟩ from lt)
    simpa [g,hi,hj] using oo
  have gi : Function.Injective g := by
    intro i j eq
    by_cases hi : i.val<3
    · by_cases hj : j.val<3
      · by_contra neq
        rcases lt_or_gt_of_ne neq with lt|gt
        · exact (Nat.ne_of_lt (increasing i j hi hj lt)) eq
        · exact (Nat.ne_of_lt (increasing j i hj hi gt)) eq.symm
      · rcases high j hj with rfl|rfl
        · exact False.elim ((diff _ hi).1 (eq.trans gu))
        · exact False.elim ((diff _ hi).2 (eq.trans gv))
    · by_cases hj : j.val<3
      · rcases high i hi with rfl|rfl
        · exact False.elim ((diff _ hj).1 (eq.symm.trans gu))
        · exact False.elim ((diff _ hj).2 (eq.symm.trans gv))
      · rcases high i hi with rfl|rfl <;> rcases high j hj with rfl|rfl <;> first
          | rfl
          | exact False.elim (ne (gu.symm.trans (eq.trans gv)))
          | exact False.elim (ne (gu.symm.trans (eq.symm.trans gv)))
  have has (i : R) : ∃ j : R, f j=g i := by
    have m : g i∈A := by
      by_cases hi : i.val<3
      · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (low _ hi))
      · rcases high i hi with rfl|rfl
        · simpa only [gu] using mu
        · simpa only [gv] using mv
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp m
    exact ⟨j,eq⟩
  choose a ha using has
  have ai : Function.Injective a := by
    intro i j eq
    exact gi ((ha i).symm.trans ((congrArg f eq).trans (ha j)))
  let e := Equiv.ofBijective a ⟨ai,Finite.injective_iff_surjective.mp ai⟩
  refine ⟨e,(ha 3).trans gu,(ha 4).trans gv,?_⟩
  intro i j hi hj lt
  change f (a i) < f (a j)
  rw [ha i,ha j]
  exact increasing i j hi hj lt
end Lpcx178Sort
namespace PEqualNP.Outside.L_pcx_178_affine


def smear (s a : Nat) : Nat := a ^^^ (a >>> s)

def parity (a q : Nat) : Bool :=
  (smear 1 (smear 2 (smear 4 (smear 8 (smear 16 (a &&& q)))))).testBit 0

theorem smear_xor (s a b : Nat) :
    smear s (a ^^^ b) = smear s a ^^^ smear s b := by
  simp only [smear, Nat.shiftRight_xor_distrib]
  ac_rfl

theorem parity_left (a b q : Nat) :
    parity (a ^^^ b) q = (parity a q ^^ parity b q) := by
  simp only [parity, Nat.and_xor_distrib_right, smear_xor, Nat.testBit_xor]

theorem parity_right (a b q : Nat) :
    parity q (a ^^^ b) = (parity q a ^^ parity q b) := by
  simp only [parity, Nat.and_xor_distrib_left, smear_xor, Nat.testBit_xor]

def span : List Nat -> List Nat
  | [] => [0]
  | b :: bs => let xs := span bs; xs ++ xs.map (fun x => x ^^^ b)

theorem span_map (g : Nat -> Nat) (g0 : g 0 = 0)
    (gxor : ∀ x y, g (x ^^^ y) = g x ^^^ g y)
    (bs : List Nat) (x : Nat) (hx : x ∈ span bs) :
    g x ∈ span (bs.map g) := by
  induction bs generalizing x with
  | nil =>
    simp [span] at hx
    subst x
    simp [span, g0]
  | cons b bs ih =>
    simp only [span, List.map_cons, List.mem_append, List.mem_map] at hx ⊢
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Or.inl (ih x hx)
    · exact Or.inr ⟨g y, ih y hy, (gxor y b).symm⟩

theorem span_filter (bs : List Nat) (x : Nat) (hx : x ∈ span bs) :
    x ∈ span (bs.filter (fun b => b != 0)) := by
  induction bs generalizing x with
  | nil => simpa using hx
  | cons b bs ih =>
    simp only [span, List.mem_append, List.mem_map] at hx
    by_cases hb : b = 0
    · subst b
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false]
      rcases hx with hx | ⟨y, hy, rfl⟩
      · exact ih x hx
      · simpa using ih y hy
    · have hb' : (b != 0) = true := by simpa using hb
      simp only [List.filter_cons, hb', ite_true, span, List.mem_append, List.mem_map]
      rcases hx with hx | ⟨y, hy, rfl⟩
      · exact Or.inl (ih x hx)
      · exact Or.inr ⟨y, ih y hy, rfl⟩

def correct (a b x : Nat) : Nat := if parity a x then x ^^^ b else x

theorem correct_zero (a b : Nat) : correct a b 0 = 0 := by
  simp [correct, parity, smear]

theorem correct_xor (a b x y : Nat) :
    correct a b (x ^^^ y) = correct a b x ^^^ correct a b y := by
  cases hx : parity a x <;> cases hy : parity a y <;>
    simp [correct, parity_right, hx, hy] <;> try ac_rfl
  calc
    x ^^^ y = (x ^^^ y) ^^^ (b ^^^ b) := by simp
    _ = _ := by ac_rfl

def basisStep (a : Nat) (bs : List Nat) : List Nat :=
  match bs.find? (parity a) with
  | none => bs
  | some b => (bs.map (correct a b)).filter (fun v => v != 0)

theorem step_sound (a : Nat) (bs : List Nat) (q : Nat)
    (hmem : q ∈ span bs) (heven : parity a q = false) :
    q ∈ span (basisStep a bs) := by
  unfold basisStep
  split
  next => exact hmem
  next b _ =>
    have h := span_map (correct a b) (correct_zero a b) (correct_xor a b) bs q hmem
    exact span_filter _ _ (by simpa [correct, heven] using h)

open PEqualNP.ProofComplexity
abbrev V := Fin 5 × Fin 4

def idx (v : V) : Nat := 4 * v.1.val + v.2.val
def assignment (a : Nat) (v : V) : Bool := a.testBit (idx v)
def formMask (S : Finset V) : Nat := S.fold (· ^^^ ·) 0 (fun v => 2 ^ idx v)

theorem idx_lt (v : V) : idx v < 20 := by
  have h₁ := v.1.isLt
  have h₂ := v.2.isLt
  unfold idx
  omega

theorem idx_inj : Function.Injective idx := by
  intro v w h
  have hv := v.2.isLt
  have hw := w.2.isLt
  unfold idx at h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem mask_insert (S : Finset V) {v : V} (h : v ∉ S) :
    formMask (insert v S) = 2 ^ idx v ^^^ formMask S := by
  simp [formMask, Finset.fold_insert h]

theorem mask_lt (S : Finset V) : formMask S < 1048576 := by
  change formMask S < 2 ^ 20
  induction S using Finset.induction_on with
  | empty => simp [formMask]
  | @insert v S h ih =>
    rw [mask_insert S h]
    exact Nat.xor_lt_two_pow (Nat.pow_lt_pow_right (by decide : 1 < 2) (idx_lt v)) ih

theorem bit_mask (S : Finset V) (v : V) :
    (formMask S).testBit (idx v) = decide (v ∈ S) := by
  induction S using Finset.induction_on with
  | empty => simp [formMask]
  | @insert w S h ih =>
    rw [mask_insert S h, Nat.testBit_xor, Nat.testBit_two_pow, ih]
    by_cases hw : v = w
    · subst w
      simp [h]
    · have hidx : idx w ≠ idx v := fun e => hw (idx_inj e.symm)
      simp [hidx, hw]

theorem mask_nz {S : Finset V} (h : S.Nonempty) : formMask S ≠ 0 := by
  obtain ⟨v,hv⟩ := h
  intro hz
  have h' := bit_mask S v
  simp [hz,hv] at h'

theorem parity_unit (a j : Nat) (hj : j < 20) : parity a (2 ^ j) = a.testBit j := by
  have hb : a &&& (2 ^ j) = if a.testBit j then 2 ^ j else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases h : j = i
    · subst i
      cases ht : a.testBit j <;> simp [ht, Nat.testBit_two_pow]
    · cases ht : a.testBit j <;> simp [ht, Nat.testBit_two_pow, h]
  have hp : ∀ k : Fin 20, parity (2 ^ k.val) (2 ^ k.val) = true := by decide +kernel
  have hs := hp ⟨j,hj⟩
  unfold parity at hs ⊢
  rw [hb]
  cases ht : a.testBit j
  · simp [smear]
  · simpa only [ht, ite_true, Nat.and_self] using hs

theorem parity_form (a : Nat) (S : Finset V) :
    parity a (formMask S) = decide (Odd (S.filter (fun v => assignment a v = true)).card) := by
  induction S using Finset.induction_on with
  | empty => simp [formMask,parity,smear]
  | @insert v S h ih =>
    rw [mask_insert S h, parity_right, parity_unit _ _ (idx_lt v), ih]
    change (assignment a v ^^ _) = _
    cases hv : assignment a v with
    | false => simp [Finset.filter_insert,hv]
    | true =>
      have hv' : v ∉ S.filter (fun w => assignment a w = true) := by
        intro hh
        exact h (Finset.mem_filter.mp hh).1
      rw [Finset.filter_insert, if_pos hv, Finset.card_insert_of_notMem hv']
      cases hd : decide (Odd (S.filter (fun w => assignment a w = true)).card) with
      | false =>
        have ho : ¬ Odd (S.filter (fun w => assignment a w = true)).card := of_decide_eq_false hd
        have he : Odd ((S.filter (fun w => assignment a w = true)).card + 1) := by
          rw [Nat.odd_iff] at ho ⊢
          omega
        simp [he]
      | true =>
        have ho : Odd (S.filter (fun w => assignment a w = true)).card := of_decide_eq_true hd
        have he : ¬ Odd ((S.filter (fun w => assignment a w = true)).card + 1) := by
          rw [Nat.odd_iff] at ho ⊢
          omega
        simp [he]

theorem linEqSat_iff (a : Nat) (e : LinEq V) :
    LinEqSat (assignment a) e ↔ parity a (formMask e.1) = e.2 := by
  rw [parity_form]
  unfold LinEqSat
  cases he : e.2 <;> simp [he]

theorem flat_closed (D : LinClause V) (x y z : Nat)
    (hx : ¬ LinClauseSat (assignment x) D) (hy : ¬ LinClauseSat (assignment y) D)
    (hz : ¬ LinClauseSat (assignment z) D) :
    ¬ LinClauseSat (assignment (x ^^^ y ^^^ z)) D := by
  rintro ⟨e,he,sat⟩
  have no (a : Nat) (h : ¬ LinClauseSat (assignment a) D) :
      parity a (formMask e.1) ≠ e.2 := fun eq => h ⟨e,he,(linEqSat_iff _ _).2 eq⟩
  have nx := no x hx
  have ny := no y hy
  have nz := no z hz
  have val := (linEqSat_iff _ _).1 sat
  rw [parity_left,parity_left] at val
  cases heq : e.2 <;> cases h1 : parity x (formMask e.1) <;> cases h2 : parity y (formMask e.1) <;>
    cases h3 : parity z (formMask e.1) <;> simp_all



abbrev Key := Fin 45
abbrev Row := Fin 5
abbrev Hole := Fin 4
def rowKey (i : Row) : Key := ⟨i.val,by omega⟩
def pairPos (i j : Row) : Nat :=
  let a := min i.val j.val
  let b := max i.val j.val
  a * (9-a) / 2 + (b-a-1)
def edgeKey (i j : Row) (h : Hole) : Key := ⟨(5 + 10*h.val + pairPos i j)%45,Nat.mod_lt _ (by decide)⟩
theorem edgeSymm (i j : Row) (h : Hole) : edgeKey i j h = edgeKey j i h := by
  simp [edgeKey,pairPos,min_comm,max_comm]
def ij : Array (Row × Row) := #[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def bad (x : Nat) (k : Key) : Bool :=
  if k.val < 5 then ((x >>> (4*k.val)) &&& 15) == 0
  else let v := ij[(k.val-5)%10]!
       let h := (k.val-5)/10
       x.testBit (4*v.1.val+h) && x.testBit (4*v.2.val+h)
def before (i j : Row) : Prop := i=j ∨ (i.val < 3 ∧ i.val < j.val)
def only (x : Nat) (i j : Key) := (List.finRange 45).all fun k => !(bad x k) || k == i || k == j
theorem only_spec {x : Nat} {i j : Key} (h : only x i j = true) (k : Key) (b : bad x k = true) :
    k=i ∨ k=j := by
  have one := List.all_eq_true.mp h k (List.mem_finRange k)
  simpa [b] using one
structure Model where
  K : Row → LinClause V
  owner : Key → Row
  row : ∀ i, owner (rowKey i)=i
  root : ∀ x : Nat, ∃ i : Row, ¬LinClauseSat (assignment x) (K i)
  trace : ∀ x : Nat, ∀ i : Row, ¬LinClauseSat (assignment x) (K i) →
    ∃ k : Key, bad x k = true ∧ before (owner k) i ∧ ¬LinClauseSat (assignment x) (K (owner k))

def coord (e : Row ≃ Row) : V ≃ V := e.prodCongr (Equiv.refl Hole)
def pullEq (e : Row ≃ Row) (q : LinEq V) : LinEq V := (q.1.map (coord e).symm.toEmbedding,q.2)
def pullClause (e : Row ≃ Row) (K : LinClause V) : LinClause V := K.image (pullEq e)
def lift (e : Row ≃ Row) (x : V → Bool) : V → Bool := fun v => x ((coord e).symm v)

theorem pullSat (e : Row ≃ Row) (x : V → Bool) (q : LinEq V) :
    LinEqSat x (pullEq e q) ↔ LinEqSat (lift e x) q := by
  unfold LinEqSat pullEq lift
  simp only [Finset.filter_map,Finset.card_map,Function.comp_def,Equiv.toEmbedding_apply]

theorem pullSatClause (e : Row ≃ Row) (x : V → Bool) (K : LinClause V) :
    LinClauseSat x (pullClause e K) ↔ LinClauseSat (lift e x) K := by
  constructor
  · rintro ⟨q,m,s⟩
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp m
    exact ⟨p,hp,(pullSat e x p).mp s⟩
  · rintro ⟨p,hp,s⟩
    exact ⟨_,Finset.mem_image.mpr ⟨p,hp,rfl⟩,(pullSat e x p).mpr s⟩

open Lpcx178ThreeDemands
def rawAt (e : Row ≃ Row) (k : Key) : LinClause V :=
  if k.val < 5 then linOfClause (row (e ⟨k.val%5,Nat.mod_lt _ (by decide)⟩))
  else let a := ij[(k.val-5)%10]!
       let h : Hole := ⟨((k.val-5)/10)%4,Nat.mod_lt _ (by decide)⟩
       linOfClause (coll (e a.1) (e a.2) h)
theorem rawRow (e : Row ≃ Row) (p : Row) : rawAt e (rowKey p) = linOfClause (row (e p)) := by
  fin_cases p <;> rfl
theorem rawEdge (e : Row ≃ Row) (i j : Row) (h : Hole) (lt : i.val<j.val) :
    rawAt e (edgeKey i j h) = linOfClause (coll (e i) (e j) h) := by
  fin_cases i <;> fin_cases j <;> first | (exfalso; revert lt; decide +kernel) | (fin_cases h <;> rfl)
theorem allKeys : ∀ k : Key, (∃ p, k=rowKey p) ∨
    ∃ i j : Row, ∃ h : Hole, i.val<j.val ∧ k=edgeKey i j h := by decide +kernel
theorem rawIn (e : Row ≃ Row) (k : Key) : rawAt e k ∈ (linOfClause '' PHP 5 4 : Set (LinClause V)) := by
  rcases allKeys k with ⟨p,rfl⟩|⟨i,j,h,lt,rfl⟩
  · rw [rawRow]
    exact ⟨_,Or.inl ⟨e p,rfl⟩,rfl⟩
  · rw [rawEdge e i j h lt]
    exact ⟨_,Or.inr ⟨e i,e j,h,fun w => (Nat.ne_of_lt lt) (congrArg Fin.val (e.injective w)),rfl⟩,rfl⟩
theorem rawCovers (e : Row ≃ Row) {K : LinClause V} (mem : K ∈ (linOfClause '' PHP 5 4 : Set (LinClause V))) :
    ∃ k, rawAt e k = K := by
  obtain ⟨A,ax,rfl⟩ := mem
  rcases ax with ⟨p,rfl⟩|⟨p,q,h,ne,rfl⟩
  · exact ⟨rowKey (e.symm p),by rw [rawRow]; simp [row]⟩
  · let i := e.symm p
    let j := e.symm q
    have neq : i≠j := fun eq => ne (e.symm.injective eq)
    rcases lt_or_gt_of_ne neq with lt|gt
    · exact ⟨edgeKey i j h,by rw [rawEdge _ _ _ _ lt]; simp [i,j,coll]⟩
    · exact ⟨edgeKey j i h,by rw [rawEdge _ _ _ _ gt]; simp [i,j,coll,Finset.pair_comm]⟩

theorem lift_cell (e : Row ≃ Row) (x : Nat) (p : Row) (h : Hole) :
    lift e (assignment x) (e p,h)=x.testBit (4*p.val+h.val) := by
  simp [lift,coord,assignment,idx,Equiv.prodCongr]

theorem rowEmpty (e : Row ≃ Row) (x : Nat) (i : Row)
    (no : ¬LinClauseSat (lift e (assignment x)) (linOfClause (row (e i)))) :
    ((x >>> (4*i.val)) &&& 15)=0 := by
  have bits (h : Hole) : x.testBit (4*i.val+h.val)=false := by
    cases hb : x.testBit (4*i.val+h.val) with
    | false => rfl
    | true =>
      exfalso
      apply no
      refine ⟨_,Finset.mem_image.mpr ⟨((e i,h),true),Finset.mem_image.mpr ⟨h,Finset.mem_univ _,rfl⟩,rfl⟩,litEq _ true ?_⟩
      exact (lift_cell _ _ _ _).trans hb
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_and,Nat.testBit_shiftRight]
  by_cases hn : n<4
  · have z := bits ⟨n,hn⟩
    change x.testBit (4*i.val+n)=false at z
    simp [z,Nat.add_comm n (4*i.val)]
  · have hh : 15 < 2^n := lt_of_lt_of_le (by decide : 15 < 2^4) (Nat.pow_le_pow_right (by decide) (by omega))
    simp [Nat.testBit_eq_false_of_lt hh]

theorem rawBad (e : Row ≃ Row) (x : Nat) (k : Key)
    (ff : ¬LinClauseSat (lift e (assignment x)) (rawAt e k)) :
    bad x k=true := by
  rcases allKeys k with ⟨i,rfl⟩|⟨i,j,h,lt,rfl⟩
  · rw [rawRow] at ff
    have z := rowEmpty e x i ff
    simp [bad,rowKey,i.isLt,z]
  · rw [rawEdge _ _ _ _ lt] at ff
    have both (v : Row) (inV : v=i ∨ v=j) : x.testBit (4*v.val+h.val)=true := by
      cases hb : x.testBit (4*v.val+h.val) with
      | true => rfl
      | false =>
        exfalso
        apply ff
        refine ⟨_,Finset.mem_image.mpr ⟨((e v,h),false),?_,rfl⟩,
          litEq _ false ((lift_cell _ _ _ _).trans hb)⟩
        rcases inV with rfl|rfl <;> simp [coll]
    have yes := show (x.testBit (4*i.val+h.val) && x.testBit (4*j.val+h.val))=true by rw [both i (Or.inl rfl),both j (Or.inr rfl)]; rfl
    have shape : bad x (edgeKey i j h) =
        (x.testBit (4*i.val+h.val) && x.testBit (4*j.val+h.val)) := by
      fin_cases i <;> fin_cases j <;> first | (exfalso; revert lt; decide +kernel) | (fin_cases h <;> rfl)
    exact shape.trans yes
def chooseChild (q : Nat) (b : Bool) (x : Nat) : Row := if parity x q == b then 3 else 4
end PEqualNP.Outside.L_pcx_178_affine
namespace PEqualNP.Outside.L_pcx_178.Upgrade
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Graph PEqualNP.Outside.L_pcx_118.Bridge
open PEqualNP.Outside.L_pcx_178.Split PEqualNP.Outside.L_pcx_178.Five
open PEqualNP.Outside.L_pcx_178_affine
open Lpcx178ThreeDemands
theorem assembleModel {C : ClauseMap Cell} {P : Parents} {r u v : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (bottom : ∀ x, FalseAt C x r)
    (prev : ∀ i<r, ∃ a, LinClauseSat a (C i)) (uv : u ≠ v) (head : P r = [u,v])
    (inj : Set.InjOn C (↑(Live P r) : Set Nat))
    (leaves : ∀ A∈F, ∃ k : Leaf P r, C k.val=A)
    (S : Finset Cell) (pivot : ∀ a, if Odd (S.filter (fun x => a x = true)).card
      then FalseAt C a u else FalseAt C a v) (budget : Surplus P r ≤ 3) :
    ∃ M : Model, ∃ s : Finset Cell, ∀ x : Nat,
      ¬LinClauseSat (assignment x) (M.K (chooseChild (formMask s) true x)) := by
  classical
  have rowLeaf (i : Fin 5) : ∃ k : Leaf P r, C k.val=linOfClause (row i) :=
    leaves _ ⟨_,Or.inl ⟨i,rfl⟩,rfl⟩
  choose atRow atRowEq using rowLeaf
  obtain ⟨own,location,_,fi,onto,restricted⟩ := tightNames rules bottom prev head inj atRow atRowEq budget
  let f := fun i => own (atRow i)
  have lr : r ∈ Live P r := (live_iff rules).2 .refl
  have eu : Edge P r u := by simp [Edge,head]
  have ev : Edge P r v := by simp [Edge,head]
  have named (j : Nat) (hj : Edge P r j) : ∃ i, f i=j :=
    onto j (live_closed rules lr hj) (edge_desc (rules r (by omega)) hj) (Or.inr (Or.inl hj))
  obtain ⟨e,highU,highV,increasing⟩ := Lpcx178Sort.sortedFive f fi u v uv (named _ eu) (named _ ev)
  let pos (i : Fin 5) := f (e i)
  have pi : Function.Injective pos := fi.comp e.injective
  have loc (i : Fin 5) : pos i ∈ Live P r ∧ Stop P r (pos i) ∧ pos i < r := by
    obtain ⟨li,st,_,lt⟩ := location (atRow (e i))
    exact ⟨li,st,lt⟩
  have leafNamed (a : Key) := leaves (rawAt e a) (rawIn e a)
  choose entry enc using leafNamed
  have located (a : Key) : ∃ i : Fin 5, pos i = own (entry a) := by
    obtain ⟨li,st,_,lt⟩ := location (entry a)
    obtain ⟨p,ep⟩ := onto _ li lt st
    exact ⟨e.symm p,by simpa [pos,f] using ep⟩
  choose owner nOwner using located
  have leafLive (z : Leaf P r) : z.val ∈ Live P r := (Finset.mem_filter.mp z.property).1
  have leafEq (j k : Leaf P r) (h : C j.val=C k.val) : j=k :=
    Subtype.ext (inj (leafLive j) (leafLive k) h)
  have namesRow (i : Fin 5) : owner (rowKey i) = i := by
    apply pi
    rw [nOwner]
    apply congrArg own
    apply leafEq
    rw [enc,rawRow,atRowEq]
  have normalize (i j : Fin 5) (path : Walk (Used P r) (pos j) (pos i)) : before i j := by
    by_cases same : i=j
    · exact Or.inl same
    have strict : pos i < pos j := lt_of_le_of_ne
      (walk_le (fun {_ _} edge => used_desc rules edge) path) (fun eq => same (pi eq))
    have notFinal (c : Fin 5) (ec : Edge P r (pos c)) : i≠c := by
      rintro rfl
      have eq := exclusiveChild rules ec (restricted _ ec) (loc j).2.2 path
      omega
    have nu : i≠3 := notFinal 3 (by simpa only [show pos 3=u from highU] using eu)
    have nv : i≠4 := notFinal 4 (by simpa only [show pos 4=v from highV] using ev)
    have early : i.val<3 := by
      have h3 : i.val≠3 := fun he => nu (Fin.ext he)
      have h4 : i.val≠4 := fun he => nv (Fin.ext he)
      omega
    refine Or.inr ⟨early,?_⟩
    by_contra! notLt
    have neq : i.val≠j.val := fun he => same (Fin.ext he)
    have prior : j.val < i.val := by omega
    have below : j.val<3 := by omega
    have back := increasing j i below early prior
    change pos j < pos i at back
    omega
  let K (i : Fin 5) := pullClause e (C (pos i))
  let s := S.map (coord e).symm.toEmbedding
  have cut (x : Nat) : ¬LinClauseSat (assignment x) (K (chooseChild (formMask s) true x)) := by
    let a := lift e (assignment x)
    have eq : parity x (formMask s)=decide (Odd (S.filter (fun v => a v=true)).card) := by
      rw [parity_form]
      simp [s,a,lift,Finset.filter_map,Function.comp_def]
    have br := pivot a
    by_cases plus : Odd (S.filter (fun v => a v=true)).card
    · rw [if_pos plus] at br
      have ch : chooseChild (formMask s) true x=3 := by simp [chooseChild,eq,plus]
      rw [ch]
      intro hs
      have sat := (pullSatClause e (assignment x) (C (pos 3))).mp hs
      exact br ((show pos 3=u from highU) ▸ sat)
    · rw [if_neg plus] at br
      have ch : chooseChild (formMask s) true x=4 := by simp [chooseChild,eq,plus]
      rw [ch]
      intro hs
      have sat := (pullSatClause e (assignment x) (C (pos 4))).mp hs
      exact br ((show pos 4=v from highV) ▸ sat)
  have trace (x : Nat) (i : Fin 5) (ff : ¬LinClauseSat (assignment x) (K i)) :
      ∃ a : Key, bad x a=true ∧ before (owner a) i ∧ ¬LinClauseSat (assignment x) (K (owner a)) := by
    let z := lift e (assignment x)
    have no : FalseAt C z (pos i) := fun h => ff ((pullSatClause e _ _).mpr h)
    obtain ⟨k,badLeaf,badOwner,path⟩ :=
      traceOwner rules own (fun k => (location k).2.2.1) (loc i).1 (loc i).2.1 no
    have ar : P k.val=[] := List.length_eq_zero_iff.mp (Finset.mem_filter.mp k.property).2
    have kl := walk_le (bounded_edge rules) ((live_iff rules).1 (leafLive k))
    have mem : C k.val∈F := by
      rcases rules k.val kl with ⟨_,ax⟩|⟨j,_,es,_⟩|⟨a,_,b,_,es,_⟩
      · exact ax
      · rw [ar] at es; contradiction
      · rw [ar] at es; contradiction
    obtain ⟨a,ae⟩ := rawCovers e mem
    have same : entry a=k := leafEq _ _ ((enc a).trans ae)
    have eq : pos (owner a)=own k := (nOwner a).trans (congrArg own same)
    refine ⟨a,rawBad e x a (fun h => badLeaf (ae ▸ h)),normalize _ _ (eq.symm ▸ path),?_⟩
    intro sat
    have hit := (pullSatClause e (assignment x) (C (pos (owner a)))).mp sat
    exact badOwner (eq ▸ hit)
  let M : Model := ⟨K,owner,namesRow,fun x => ⟨_,cut x⟩,trace⟩
  exact ⟨M,s,cut⟩
end PEqualNP.Outside.L_pcx_178.Upgrade
