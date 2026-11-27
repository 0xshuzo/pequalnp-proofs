import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_121.Bridge

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

end PEqualNP.Outside.L_pcx_121.Bridge
open PEqualNP.Outside.L_pcx_121.Bridge PEqualNP.ProofComplexity

namespace PEqualNP.Outside.L_pcx_121.Graph

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
end PEqualNP.Outside.L_pcx_121.Graph
namespace PEqualNP.Outside.L_pcx_121.Linear

def smear (s a : Nat) : Nat := a ^^^ (a >>> s)

def parity (a q : Nat) : Bool :=
  (smear 1 (smear 2 (smear 4 (smear 8 (a &&& q))))).testBit 0

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
abbrev V := Fin 4 × Fin 3

def idx (v : V) : Nat := 3 * v.1.val + v.2.val
def assignment (a : Nat) (v : V) : Bool := a.testBit (idx v)
def formMask (S : Finset V) : Nat := S.fold (· ^^^ ·) 0 (fun v => 2 ^ idx v)

theorem idx_lt (v : V) : idx v < 12 := by
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

theorem mask_lt (S : Finset V) : formMask S < 4096 := by
  change formMask S < 2 ^ 12
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

theorem parity_unit (a j : Nat) (hj : j < 12) : parity a (2 ^ j) = a.testBit j := by
  have hb : a &&& (2 ^ j) = if a.testBit j then 2 ^ j else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases h : j = i
    · subst i
      cases ht : a.testBit j <;> simp [ht, Nat.testBit_two_pow]
    · cases ht : a.testBit j <;> simp [ht, Nat.testBit_two_pow, h]
  have hp : ∀ k : Fin 12, parity (2 ^ k.val) (2 ^ k.val) = true := by decide +kernel
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
def axioms : List (Nat × Bool) := [(7, false), (56, false), (448, false), (3584, false), (9, true), (18, true), (36, true), (65, true), (130, true), (260, true), (513, true), (1026, true), (2052, true), (72, true), (144, true), (288, true), (520, true), (1040, true), (2080, true), (576, true), (1152, true), (2304, true)]

def support (m : Nat) : Finset V := Finset.univ.filter (fun v => m.testBit (idx v))

def clauseOf (row : Nat × Bool) : Clause V := (support row.1).image (fun v => (v,!row.2))

def linearOf (row : Nat × Bool) : LinClause V := linOfClause (clauseOf row)

theorem idx_cover (n : Nat) (h : n < 12) : ∃ v : V, idx v = n := by
  let v : V := (⟨n/3, by omega⟩, ⟨n%3, by omega⟩)
  exact ⟨v, by change 3 * (n/3) + n%3 = n; omega⟩

theorem singleton_sat (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a ({v}, s) ↔ a v = s := by
  cases hv : a v <;> cases s <;> simp [LinEqSat, Finset.filter_singleton, hv]

theorem linear_iff (a : V → Bool) (C : Clause V) :
    LinClauseSat a (linOfClause C) ↔ ClauseSat a C := by
  simp only [LinClauseSat, linOfClause, Finset.mem_image, ClauseSat]
  constructor
  · rintro ⟨q, ⟨⟨v,s⟩, hs, rfl⟩, hq⟩
    exact ⟨(v,s), hs, (singleton_sat _ _ _).1 hq⟩
  · rintro ⟨⟨v,s⟩, hs, hv⟩
    exact ⟨({v},s), ⟨(v,s), hs, rfl⟩, (singleton_sat _ _ _).2 hv⟩

theorem false_on_spec (a : Nat) (row : Nat × Bool) (hh : row.1 < 4096) :
    (a &&& row.1 = if row.2 then row.1 else 0) ↔
      ¬ LinClauseSat (assignment a) (linearOf row) := by
  rw [linearOf, linear_iff]
  have ht : ClauseSat (assignment a) (clauseOf row) ↔
      ∃ v ∈ support row.1, assignment a v = !row.2 := by
    constructor
    · rintro ⟨l, hl, h⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hl
      exact ⟨v,hv,h⟩
    · rintro ⟨v,hv,h⟩
      exact ⟨(v,!row.2), Finset.mem_image.mpr ⟨v,hv,rfl⟩, h⟩
  rw [ht]
  push_neg
  have he : ∀ v : V, assignment a v ≠ !row.2 ↔ assignment a v = row.2 := by
    intro v
    cases h₁ : assignment a v <;> cases row.2 <;> simp
  simp only [he]
  constructor
  · intro h v hv
    have hm : row.1.testBit (idx v) = true := (Finset.mem_filter.mp hv).2
    have eq := congrArg (fun k : Nat => k.testBit (idx v)) h
    cases hs : row.2 <;> simpa [Nat.testBit_and, hm, hs, assignment] using eq
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hm : row.1.testBit i = true
    · have hi : i < 12 := by
        by_contra hn
        have hp : 2 ^ 12 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        have hw : row.1 < 2 ^ i := lt_of_lt_of_le hh hp
        simp [Nat.testBit_lt_two_pow hw] at hm
      obtain ⟨v,rfl⟩ := idx_cover i hi
      have hv : v ∈ support row.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩
      have hs := h v hv
      cases hr : row.2 <;> simp_all [Nat.testBit_and, assignment]
    · have hn : row.1.testBit i = false := by
        cases ht : row.1.testBit i <;> simp_all
      cases hr : row.2 <;> simp [Nat.testBit_and, hn, hr]

def pigeon (i : Fin 4) : Clause V := Finset.univ.image (fun j : Fin 3 => ((i,j),true))
def collision (i k : Fin 4) (j : Fin 3) : Clause V := {((i,j),false),((k,j),false)}

def axHas (C : Clause V) : Bool := axioms.any (fun row => clauseOf row == C)

theorem all_rows_small : axioms.all (fun row => decide (row.1 < 4096)) = true := by decide +kernel
theorem all_pigeon : ∀ i, axHas (pigeon i) = true := by decide +kernel
theorem all_collision : ∀ i k j, i ≠ k → axHas (collision i k j) = true := by decide +kernel
theorem label_distinct : (axioms.map clauseOf).Nodup := by decide +kernel

theorem php_covered {C : Clause V} (h : C ∈ PHP 4 3) : ∃ row ∈ axioms, clauseOf row = C := by
  have hc : axHas C = true := by
    rcases h with ⟨i,rfl⟩ | ⟨i,k,j,hne,rfl⟩
    · exact all_pigeon i
    · exact all_collision i k j hne
  exact ⟨_, (List.any_eq_true.mp hc).choose_spec.1, beq_iff_eq.mp (List.any_eq_true.mp hc).choose_spec.2⟩

end PEqualNP.Outside.L_pcx_121.Linear

namespace PEqualNP.Outside.L_pcx_121.Packing
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_121.Graph PEqualNP.Outside.L_pcx_121.Linear
def axis : List (Nat × Bool) := [(7,false), (56,false), (448,false), (3584,false), (9,true), (65,true), (72,true), (513,true), (520,true), (576,true), (18,true), (130,true), (144,true), (1026,true), (1040,true), (1152,true), (36,true), (260,true), (288,true), (2052,true), (2080,true), (2304,true)]
def violates (x : Nat) (s : Nat × Bool) : Bool := (x &&& s.1) == (if s.2 then s.1 else 0)
def labels (x : Nat) : List Nat :=
  ((List.range 22).filter (fun i => violates x (axis.getD i (0,false)))).map (fun i => i+1)

def indexedRow (i : Fin 22) := axis.getD i.val (0,false)
def physicalAx (i : Fin 22) := linearOf (indexedRow i)

theorem smallRow : ∀ i : Fin 22, (indexedRow i).1 < 4096 := by decide +kernel
theorem rowIndex : axioms.all (fun row => decide (∃ k : Fin 22, row = indexedRow k)) = true := by decide +kernel
theorem isAx : ∀ i : Fin 22, (∃ p : Fin 4, clauseOf (indexedRow i) = pigeon p) ∨
    ∃ p q : Fin 4, ∃ h : Fin 3, p ≠ q ∧ clauseOf (indexedRow i) = collision p q h := by
  decide +kernel

theorem allAx : (linOfClause '' PHP 4 3) = Set.range physicalAx := by
  ext D
  constructor
  · rintro ⟨A,ha,rfl⟩
    obtain ⟨row,hr,eq⟩ := php_covered ha
    obtain ⟨k,same⟩ : ∃ k : Fin 22, row=indexedRow k := of_decide_eq_true (List.all_eq_true.mp rowIndex _ hr)
    exact ⟨k,by simpa [physicalAx,linearOf,←same,eq]⟩
  · rintro ⟨i,rfl⟩
    refine ⟨clauseOf (indexedRow i),?_,rfl⟩
    rcases isAx i with ⟨p,e⟩ | ⟨p,q,h,ne,e⟩
    · exact Or.inl ⟨p,e⟩
    · exact Or.inr ⟨p,q,h,ne,e⟩

theorem grid_false (x : Nat) (i : Fin 22) :
    (¬ LinClauseSat (assignment x) (physicalAx i)) ↔ i.val+1∈labels x := by
  have v : violates x (indexedRow i)=true ↔ ¬LinClauseSat (assignment x) (physicalAx i) := by
    simpa only [violates,beq_iff_eq,physicalAx] using false_on_spec x (indexedRow i) (smallRow i)
  rw [←v]
  simp only [labels,List.mem_map,List.mem_filter,List.mem_range]
  constructor
  · intro h
    exact ⟨i.val,⟨i.isLt,h⟩,rfl⟩
  · rintro ⟨j,⟨_,h⟩,e⟩
    have eq : j=i.val := by omega
    simpa only [eq,indexedRow] using h

def privatePoints : List Nat := [672, 644, 532, 84, 1289, 1121, 1100, 673, 652, 596, 786, 674, 660, 1122, 1108, 1164, 676, 788, 802, 2132, 2146, 2314]
theorem privatePoint : ∀ i j : Fin 22,
    ((labels (privatePoints.getD i.val 0)).contains (j.val+1)) = decide (i=j) := by decide +kernel

theorem grid_essential (i : Fin 22) : ∃ a, ∀ j,
    ¬ LinClauseSat a (physicalAx j) ↔ j=i := by
  refine ⟨assignment (privatePoints.getD i.val 0),?_⟩
  intro j
  rw [grid_false,←List.contains_iff_mem,privatePoint]
  simp [eq_comm]


theorem leafPacking {C : ClauseMap V} {P : Parents} {r m : Nat}
    (rules : ∀ i≤r,Rule (linOfClause '' PHP 4 3) C P i)
    (x : Fin m→Nat) (bad : ∀i,FalseAt C (assignment (x i)) r)
    (sep : ∀i j : Fin m, ∀ k : Fin 22,
      violates (x i) (indexedRow k)=true → violates (x j) (indexedRow k)=true → i=j) :
    m≤(WithArity P r 0).card := by
  classical
  have located (i : Fin m) : ∃ t, t ∈ WithArity P r 0 ∧
      C t ∈ linOfClause '' PHP 4 3 ∧ FalseAt C (assignment (x i)) t := by
    obtain ⟨t,pt,ax,ff,w⟩:=localized_route rules _ le_rfl (bad i)
    refine ⟨t,?_,ax,ff⟩
    simp only [WithArity,Finset.mem_filter,pt,List.length_nil,and_true]
    exact (live_iff rules).2 (walk_sub (fun e=>e.1) w)
  choose f ff using located
  have inj : Function.Injective f := by
    intro i j e
    have h: C (f i)∈Set.range physicalAx:=allAx ▸ (ff i).2.1
    obtain ⟨k,eq⟩:=h
    apply sep i j k
    · apply (show (_ ↔ ¬LinClauseSat (assignment (x i)) (physicalAx k)) from
        by simpa only [violates,beq_iff_eq,physicalAx] using false_on_spec (x i) (indexedRow k) (smallRow k)).2
      rw [eq]
      exact (ff i).2.2
    · apply (show (_ ↔ ¬LinClauseSat (assignment (x j)) (physicalAx k)) from
        by simpa only [violates,beq_iff_eq,physicalAx] using false_on_spec (x j) (indexedRow k) (smallRow k)).2
      rw [eq,e]
      exact (ff j).2.2
  have ss : Finset.univ.image f ⊆ WithArity P r 0 := by
    intro j hj
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hj
    exact (ff i).1
  simpa only [Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_fin] using Finset.card_le_card ss

end PEqualNP.Outside.L_pcx_121.Packing

namespace PEqualNP.Outside.L_pcx_121.Packing
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_121.Graph PEqualNP.Outside.L_pcx_121.Linear

noncomputable def internalNodes (P : Parents) (r : Nat) := Live P r \ WithArity P r 0

theorem internalSize {C : ClauseMap V} {P : Parents} {r : Nat}
    (rules : ∀i≤r,Rule (linOfClause '' PHP 4 3) C P i) :
    (WithArity P r 0).card+(WithArity P r 1).card ≤ (internalNodes P r).card+1 := by
  have h:=arity_count rules
  have inc : WithArity P r 0 ⊆ Live P r := Finset.filter_subset _ _
  have s:=Finset.card_sdiff_add_card_eq_card inc
  unfold internalNodes
  omega

theorem unaryBirth {C : ClauseMap V} {P : Parents} {r : Nat}
    (rules : ∀i≤r,Rule (linOfClause '' PHP 4 3) C P i) (q : LinEq V)
    (exotic : q.1.card≠1) (ends : q∈C r) : 1≤(WithArity P r 1).card := by
  have reach (i : Nat) (hi : i≤r) (occ : q∈C i) :
      ∃j, Walk (LocalEdge P r) i j ∧ (P j).length=1 := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      rcases rules i hi with ⟨_,ax⟩ | ⟨j,lt,one,_⟩ | ⟨j,lt,k,kt,two,f,_,_,rule⟩
      · obtain ⟨A,_,eq⟩:=ax
        rw [←eq] at occ
        obtain ⟨l,_,leq⟩:=Finset.mem_image.mp occ
        apply False.elim
        apply exotic
        rw [←leq]
        exact Finset.card_singleton _
      · exact ⟨i,.refl,by simp [one]⟩
      · rw [rule] at occ
        rcases Finset.mem_union.mp occ with left|right
        · obtain ⟨t,w,one⟩:=ih j lt (lt.le.trans hi) (Finset.mem_of_mem_erase left)
          exact ⟨t,.head ⟨hi,by simp [Edge,two]⟩ w,one⟩
        · obtain ⟨t,w,one⟩:=ih k kt (kt.le.trans hi) (Finset.mem_of_mem_erase right)
          exact ⟨t,.head ⟨hi,by simp [Edge,two]⟩ w,one⟩
  obtain ⟨j,path,one⟩:=reach r le_rfl ends
  exact Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨(live_iff rules).2 path,one⟩⟩

theorem intersectionBudget {C : ClauseMap V} {P : Parents} {r u v : Nat}
    (rules : ∀i≤r,Rule (linOfClause '' PHP 4 3) C P i) (unsat : ∀a,FalseAt C a r)
    (rootRule : P r=[u,v]) (ur : u<r) (vr : v<r) :
    (internalNodes P u).card + (internalNodes P v).card + 22 ≤
      r + (internalNodes P u ∩ internalNodes P v).card := by
  classical
  let prior := (Finset.range r).filter (fun i=>(P i).length=0)
  obtain ⟨_,_,_,lb,_⟩:=unique_leaves rules unsat physicalAx allAx grid_essential
  have allprior : WithArity P r 0 ⊆ prior := by
    intro i mem
    obtain ⟨live,arity⟩:=Finset.mem_filter.mp mem
    have hi : i<r+1 := Finset.mem_range.mp (Finset.mem_filter.mp live).1
    have neq : i≠r := by rintro rfl; simp [rootRule] at arity
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),arity⟩
  have pb : 22≤prior.card := by
    have base : 22≤(WithArity P r 0).card := by simpa using lb
    exact base.trans (Finset.card_le_card allprior)
  have under (t : Nat) (tr : t<r) : internalNodes P t ⊆ Finset.range r \ prior := by
    intro i hi
    obtain ⟨live,no⟩:=Finset.mem_sdiff.mp hi
    have il : i<t+1 := Finset.mem_range.mp (Finset.mem_filter.mp live).1
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩
    intro mem
    exact no (Finset.mem_filter.mpr ⟨live,(Finset.mem_filter.mp mem).2⟩)
  have cap:=Finset.card_le_card (Finset.union_subset (under u ur) (under v vr))
  have sd:=Finset.card_sdiff_add_card_eq_card (show prior ⊆ Finset.range r from Finset.filter_subset _ _)
  rw [Finset.card_range] at sd
  have sizes:=Finset.card_union_add_card_inter (internalNodes P u) (internalNodes P v)
  omega


structure SideDeck where
  words : List Nat
  owners : List Nat

structure PairDeck where
  mask : Nat
  left : SideDeck
  right : SideDeck

def goodSide (f : Nat) (b : Bool) (d : SideDeck) : Bool :=
  (List.range d.words.length).all (fun i =>
    let x:=d.words.getD i 0
    parity x f == b && (List.range 22).all (fun k =>
      !(violates x (axis.getD k (0,false))) || decide (d.owners.getD k 99 = i)))

theorem deckLeaves {C : ClauseMap V} {P : Parents} {r f : Nat} {b : Bool} (d : SideDeck)
    (rules : ∀ i≤r,Rule (linOfClause '' PHP 4 3) C P i)
    (ok : goodSide f b d=true)
    (bad : ∀x,parity x f=b → FalseAt C (assignment x) r) :
    d.words.length≤(WithArity P r 0).card := by
  let x (i : Fin d.words.length):=d.words.getD i.val 0
  have prop (i : Fin d.words.length) : ((parity (x i) f == b) && (List.range 22).all (fun k=> !(violates (x i) (axis.getD k (0,false))) || decide (d.owners.getD k 99=i.val)))=true := List.all_eq_true.mp ok i.val (List.mem_range.mpr i.isLt)
  have align (i : Fin d.words.length) : parity (x i) f=b := by
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (prop i)).1
  have label (i : Fin d.words.length) (k : Fin 22) (h : violates (x i) (indexedRow k)=true) :
      d.owners.getD k.val 99=i.val := by
    have t:=List.all_eq_true.mp (Bool.and_eq_true_iff.mp (prop i)).2 k.val (List.mem_range.mpr k.isLt)
    change (!violates (x i) (indexedRow k) || decide (d.owners.getD k.val 99=i.val))=true at t
    simpa only [h,Bool.not_true,Bool.false_or,decide_eq_true_eq] using t
  exact leafPacking rules x (fun i=>bad _ (align i))
    (fun i j k hi hj=>Fin.ext ((label i k hi).symm.trans (label j k hj)))

def goodPair (d : PairDeck) := goodSide d.mask false d.left && goodSide d.mask true d.right
def d0 : PairDeck := ⟨3,⟨[596,676,84,660,672,644,652,532,2132,1100,788,1164,1108,2147,1315,675,2323],[4,5,7,2,99,13,9,15,6,0,16,15,3,14,12,11,1,10,14,8,13,16]⟩,⟨[2122,770,786,546,778,2193,1122,673,2314,98,2146,610,1121,1297,1185,1289,674,802],[99,1,3,9,15,12,0,7,4,11,2,16,5,6,13,14,99,99,17,99,10,8]⟩⟩
theorem check0 : goodPair d0=true := by decide +kernel
def d1 : PairDeck := ⟨5,⟨[610,786,98,802,784,770,778,546,1122,2122,674,2314,2146,1109,2197,789,1189],[4,5,7,2,99,13,9,15,6,0,1,10,14,8,13,16,16,15,3,14,12,11]⟩,⟨[1100,644,676,532,652,1313,2132,785,1164,84,1108,596,2129,2209,2321,2185,788,660],[99,1,3,9,15,12,0,7,4,11,99,99,17,99,10,8,2,16,5,6,13,14]⟩⟩
theorem check1 : goodPair d1=true := by decide +kernel
def d2 : PairDeck := ⟨6,⟨[1185,1289,161,1313,1288,1281,1297,1057,673,2193,1121,2321,2209,654,2126,1294,614],[4,5,7,2,1,10,14,8,13,16,99,13,9,15,6,0,16,15,3,14,12,11]⟩,⟨[660,1092,1124,1036,1108,802,2188,1290,596,140,652,1164,2186,2146,2314,2130,1292,1100],[99,1,3,9,99,99,17,99,10,8,15,12,0,7,4,11,2,16,5,6,13,14]⟩⟩
theorem check2 : goodPair d2=true := by decide +kernel
def d3 : PairDeck := ⟨9,⟨[596,1108,676,672,802,788,84,786,2146,2132,660,674,532,1289,644,1122],[3,14,12,6,13,99,99,99,99,0,7,11,10,15,1,99,2,5,4,9,8,99]⟩,⟨[673,2314,2186,140,2188,1313,1036,652,1100,1121,1290,1297,2209,1164,1281,1288,2193,1292],[15,14,6,3,99,9,8,0,7,99,99,2,16,10,11,13,99,17,5,4,12,1]⟩⟩
theorem check3 : goodPair d3=true := by decide +kernel
def d4 : PairDeck := ⟨10,⟨[2186,672,2132,1121,778,596,1290,2314,1108,1313,2209,676,84,532,644,660,1185,2122,673,788],[1,14,13,12,99,3,17,18,4,5,99,0,15,6,8,16,11,19,9,2,10,7]⟩,⟨[1100,2188,610,546,1288,652,1292,674,1289,98,786,802,2146,1122,770,1164],[4,14,3,9,8,99,0,99,5,2,10,7,99,13,99,15,99,6,11,1,12,99]⟩⟩
theorem check4 : goodPair d4=true := by decide +kernel
def d5 : PairDeck := ⟨12,⟨[1292,784,1122,2129,652,610,2188,1164,2146,2193,1297,786,98,546,770,802,2321,1100,785,674],[1,14,13,12,99,3,17,18,4,5,11,19,9,2,10,7,99,0,15,6,8,16]⟩,⟨[2122,1290,596,532,2184,778,2186,788,2185,84,676,660,1108,2132,644,2314],[4,14,3,9,8,99,0,99,5,2,99,6,11,1,12,99,10,7,99,13,99,15]⟩⟩
theorem check5 : goodPair d5=true := by decide +kernel
def d6 : PairDeck := ⟨17,⟨[2129,1120,2188,674,1297,1164,785,2321,652,802,2146,1124,140,1036,1092,1100,610,2193,1122,1292],[1,14,13,12,99,0,15,6,8,16,99,3,17,18,4,5,11,19,9,2,10,7]⟩,⟨[660,2132,1185,1057,784,1108,788,1121,786,161,1289,1313,2209,673,1281,596],[4,14,3,9,10,7,99,13,99,15,8,99,0,99,5,2,99,6,11,1,12,99]⟩⟩
theorem check6 : goodPair d6=true := by decide +kernel
def d7 : PairDeck := ⟨18,⟨[1164,652,1124,1120,1313,1292,140,1289,2209,2188,1100,1121,1036,786,1092,673],[3,14,12,6,7,11,10,15,1,99,13,99,99,99,99,0,2,5,4,9,8,99]⟩,⟨[1122,2321,2129,84,2132,802,532,1108,660,674,785,778,2146,596,770,784,2122,788],[15,14,6,3,99,2,16,10,11,13,99,9,8,0,7,99,99,17,5,4,12,1]⟩⟩
theorem check7 : goodPair d7=true := by decide +kernel
def d8 : PairDeck := ⟨20,⟨[788,1288,673,2186,1108,1185,2132,596,2209,2122,778,1289,161,1057,1281,1313,2314,660,1290,1121],[1,14,13,12,11,19,9,2,10,7,99,3,17,18,4,5,99,0,15,6,8,16]⟩,⟨[2193,785,1164,1036,2128,1297,2129,1292,2130,140,1124,1100,652,2188,1092,2321],[4,14,3,9,99,6,11,1,12,99,8,99,0,99,5,2,10,7,99,13,99,15]⟩⟩
theorem check8 : goodPair d8=true := by decide +kernel
def d9 : PairDeck := ⟨24,⟨[610,676,98,674,644,672,673,546,2146,1121,802,1185,1122,2140,1308,668,2330],[5,4,7,2,99,9,13,6,15,0,16,3,15,12,14,11,1,14,10,13,8,16]⟩,⟨[2129,784,786,532,785,2186,1108,652,2321,84,2132,596,1100,1290,1164,1289,660,788],[1,99,3,9,15,0,12,4,7,11,2,5,16,13,6,14,99,17,99,10,99,8]⟩⟩
theorem check9 : goodPair d9=true := by decide +kernel
def d10 : PairDeck := ⟨33,⟨[1121,2128,1290,788,2209,2314,673,1185,778,660,1108,2130,266,2058,2114,2122,596,1313,2132,2186],[1,14,13,12,99,0,15,6,8,16,11,19,9,2,10,7,99,3,17,18,4,5]⟩,⟨[802,1122,2321,2065,672,2146,674,2129,676,273,2185,2193,1297,785,2177,610],[4,14,3,9,10,7,99,13,99,15,99,6,11,1,12,99,8,99,0,99,5,2]⟩⟩
theorem check10 : goodPair d10=true := by decide +kernel
def d11 : PairDeck := ⟨34,⟨[674,2184,785,1292,2146,2321,1122,610,1297,1100,652,2185,273,2065,2177,2193,1164,802,2188,2129],[1,14,13,12,11,19,9,2,10,7,99,0,15,6,8,16,99,3,17,18,4,5]⟩,⟨[1313,673,2314,2058,1120,2209,1121,2186,1124,266,2130,2122,778,1290,2114,1185],[4,14,3,9,99,6,11,1,12,99,10,7,99,13,99,15,8,99,0,99,5,2]⟩⟩
theorem check11 : goodPair d11=true := by decide +kernel
def d12 : PairDeck := ⟨36,⟨[2314,778,2130,2128,2193,2186,266,2185,1297,1290,2122,2129,2058,676,2114,785],[3,14,12,6,7,11,10,15,1,99,2,5,4,9,8,99,13,99,99,99,99,0]⟩,⟨[2132,1185,1121,98,1122,660,546,2146,802,788,673,652,1108,610,644,672,1100,674],[15,14,6,3,99,2,16,10,11,13,99,17,5,4,12,1,99,9,8,0,7,99]⟩⟩
theorem check12 : goodPair d12=true := by decide +kernel
def d13 : PairDeck := ⟨40,⟨[596,786,84,788,770,784,785,532,1108,2129,660,2321,2132,1130,2218,810,1196],[5,4,7,2,99,9,13,6,15,0,1,14,10,13,8,16,16,3,15,12,14,11]⟩,⟨[1121,672,676,546,673,1292,2146,778,1185,98,1122,610,2122,2188,2314,2185,802,674],[1,99,3,9,15,0,12,4,7,11,99,17,99,10,99,8,2,5,16,13,6,14]⟩⟩
theorem check13 : goodPair d13=true := by decide +kernel
def d14 : PairDeck := ⟨48,⟨[1164,1289,140,1292,1281,1288,1290,1036,652,2186,1100,2314,2188,689,2161,1329,628],[5,4,7,2,1,14,10,13,8,16,99,9,13,6,15,0,16,3,15,12,14,11]⟩,⟨[674,1120,1124,1057,1122,788,2209,1297,610,161,673,1185,2193,2132,2321,2130,1313,1121],[1,99,3,9,99,17,99,10,99,8,15,0,12,4,7,11,2,5,16,13,6,14]⟩⟩
theorem check14 : goodPair d14=true := by decide +kernel
def d15 : PairDeck := ⟨65,⟨[652,1164,788,784,802,676,140,674,2314,2188,660,786,644,1121,532,1290],[3,12,14,6,99,13,99,99,0,99,11,7,10,15,99,1,5,2,4,9,99,8]⟩,⟨[785,2146,2130,84,2132,1313,1092,596,1100,1289,1122,1185,2321,1108,1057,1120,2193,1124],[15,6,14,3,9,99,8,0,99,7,2,99,16,10,13,11,17,99,5,4,1,12]⟩⟩
theorem check15 : goodPair d15=true := by decide +kernel
def d16 : PairDeck := ⟨66,⟨[2130,784,2188,1289,610,652,1122,2146,1164,1313,2321,788,140,644,532,660,1297,2122,785,676],[1,13,14,12,3,99,17,18,5,4,0,99,15,6,16,8,19,11,9,2,7,10]⟩,⟨[1100,2132,778,770,1120,596,1124,786,1121,266,674,802,2314,1290,546,1108],[4,3,14,9,99,8,0,99,2,5,7,10,99,13,15,99,6,99,11,1,99,12]⟩⟩
theorem check16 : goodPair d16=true := by decide +kernel
def d17 : PairDeck := ⟨68,⟨[1124,672,1290,2185,596,778,2132,1108,2314,2193,1185,674,266,770,546,802,2209,1100,673,786],[1,13,14,12,3,99,17,18,5,4,19,11,9,2,7,10,0,99,15,6,16,8]⟩,⟨[2122,1122,652,644,2128,610,2130,676,2129,140,788,660,1164,2188,532,2146],[4,3,14,9,99,8,0,99,2,5,6,99,11,1,99,12,7,10,99,13,15,99]⟩⟩
theorem check17 : goodPair d17=true := by decide +kernel
def d18 : PairDeck := ⟨72,⟨[673,1185,802,770,788,676,161,660,2321,2209,674,786,672,1100,546,1297],[12,3,14,6,99,99,13,0,99,99,11,10,7,99,15,1,5,4,2,99,9,8]⟩,⟨[778,2132,2130,98,2146,1292,1120,610,1121,1289,1108,1164,2314,1122,1036,1092,2186,1124],[6,15,14,3,9,8,99,99,0,7,2,16,99,13,10,11,17,5,99,1,4,12]⟩⟩
theorem check18 : goodPair d18=true := by decide +kernel
def d19 : PairDeck := ⟨80,⟨[2130,770,2209,1289,596,673,1108,2132,1185,1292,2314,802,161,672,546,674,1290,2129,778,676],[13,1,14,12,3,17,99,5,18,4,0,15,99,16,6,8,19,9,11,7,2,10]⟩,⟨[1121,2146,785,784,1092,610,1124,786,1100,273,660,788,2321,1297,532,1122],[3,4,14,9,99,0,8,2,99,5,7,99,10,15,13,99,6,11,99,99,1,12]⟩⟩
theorem check19 : goodPair d19=true := by decide +kernel
def d20 : PairDeck := ⟨96,⟨[1124,644,1297,2185,610,785,2146,1122,2321,2186,1164,660,273,784,532,788,2188,1121,652,786],[13,1,14,12,3,17,99,5,18,4,19,9,11,7,2,10,0,15,99,16,6,8]⟩,⟨[2129,1108,673,672,2114,596,2130,676,2122,161,802,674,1185,2209,546,2132],[3,4,14,9,99,0,8,2,99,5,6,11,99,99,1,12,7,99,10,15,13,99]⟩⟩
theorem check20 : goodPair d20=true := by decide +kernel
def d21 : PairDeck := ⟨129,⟨[2185,1288,2132,786,1185,1108,673,2209,596,802,2314,1292,84,1092,1036,1100,778,2193,1290,1124],[1,13,14,12,0,99,15,6,16,8,3,99,17,18,5,4,19,11,9,2,7,10]⟩,⟨[660,2188,1297,1281,672,1164,676,1289,674,273,1121,1313,2321,785,1057,652],[4,3,14,9,7,10,99,13,15,99,99,8,0,99,2,5,6,99,11,1,99,12]⟩⟩
theorem check21 : goodPair d21=true := by decide +kernel
def d22 : PairDeck := ⟨130,⟨[1108,596,1292,1288,1313,1124,84,1121,2321,2132,1100,1289,1092,674,1036,785],[3,12,14,6,11,7,10,15,99,1,99,13,99,99,0,99,5,2,4,9,99,8]⟩,⟨[1290,2209,2185,140,2188,802,644,1164,660,786,673,610,2314,652,546,672,2122,676],[15,6,14,3,2,99,16,10,13,11,9,99,8,0,99,7,17,99,5,4,1,12]⟩⟩
theorem check22 : goodPair d22=true := by decide +kernel
def d23 : PairDeck := ⟨132,⟨[676,1120,785,2130,1164,1297,2188,652,2321,2122,610,1121,273,1281,1057,1313,2146,660,1122,1289],[1,13,14,12,19,11,9,2,7,10,3,99,17,18,5,4,0,99,15,6,16,8]⟩,⟨[2193,673,1108,1092,2184,1185,2185,1124,2186,84,1292,1100,596,2132,1036,2209],[4,3,14,9,6,99,11,1,99,12,99,8,0,99,2,5,7,10,99,13,15,99]⟩⟩
theorem check23 : goodPair d23=true := by decide +kernel
def d24 : PairDeck := ⟨136,⟨[2185,1281,2146,786,1164,1122,652,2188,610,788,2321,1313,98,1120,1057,1121,785,2186,1297,1124],[13,1,14,12,0,15,99,16,6,8,3,17,99,5,18,4,19,9,11,7,2,10]⟩,⟨[674,2209,1290,1288,644,1185,676,1289,660,266,1100,1292,2314,778,1036,673],[3,4,14,9,7,99,10,15,13,99,99,0,8,2,99,5,6,11,99,99,1,12]⟩⟩
theorem check24 : goodPair d24=true := by decide +kernel
def d25 : PairDeck := ⟨144,⟨[1122,610,1313,1281,1292,1124,98,1100,2314,2146,1121,1289,1120,660,1057,778],[12,3,14,6,11,10,7,99,15,1,99,99,13,0,99,99,5,4,2,99,9,8]⟩,⟨[1297,2188,2185,161,2209,788,672,1185,674,786,652,596,2321,673,532,644,2129,676],[6,15,14,3,2,16,99,13,10,11,9,8,99,99,0,7,17,5,99,1,4,12]⟩⟩
theorem check25 : goodPair d25=true := by decide +kernel
def d26 : PairDeck := ⟨160,⟨[676,1092,778,2130,1185,1290,2209,673,2314,2129,596,1100,266,1288,1036,1292,2132,674,1108,1289],[13,1,14,12,19,9,11,7,2,10,3,17,99,5,18,4,0,15,99,16,6,8]⟩,⟨[2186,652,1122,1120,2177,1164,2185,1124,2193,98,1313,1121,610,2146,1057,2188],[3,4,14,9,6,11,99,99,1,12,99,0,8,2,99,5,7,99,10,15,13,99]⟩⟩
theorem check26 : goodPair d26=true := by decide +kernel
def d27 : PairDeck := ⟨192,⟨[778,788,266,786,532,784,785,770,2314,1289,802,1297,1290,2252,1252,724,2274],[5,7,4,2,9,99,13,6,0,15,3,16,15,12,11,14,14,1,10,13,16,8]⟩,⟨[2185,672,674,644,673,2130,1164,596,2209,140,2188,652,1100,1122,1108,1121,660,676],[1,3,99,9,0,15,12,4,11,7,5,2,16,13,14,6,17,99,99,10,8,99]⟩⟩
theorem check27 : goodPair d27=true := by decide +kernel
def d28 : PairDeck := ⟨257,⟨[1289,2184,1122,676,2321,2146,785,1297,610,660,1164,2186,98,2114,2058,2122,652,1313,2188,2130],[1,13,14,12,0,99,15,6,16,8,19,11,9,2,7,10,3,99,17,18,5,4]⟩,⟨[802,1290,2209,2177,784,2314,786,2185,788,161,2129,2193,1185,673,2065,778],[4,3,14,9,7,10,99,13,15,99,6,99,11,1,99,12,99,8,0,99,2,5]⟩⟩
theorem check28 : goodPair d28=true := by decide +kernel
def d29 : PairDeck := ⟨258,⟨[786,2128,673,1124,2314,2209,1290,778,1185,1100,596,2129,161,2177,2065,2193,1108,802,2132,2185],[1,13,14,12,19,11,9,2,7,10,0,99,15,6,16,8,3,99,17,18,5,4]⟩,⟨[1313,785,2146,2114,1288,2321,1289,2130,1292,98,2186,2122,610,1122,2058,1297],[4,3,14,9,6,99,11,1,99,12,7,10,99,13,15,99,99,8,0,99,2,5]⟩⟩
theorem check29 : goodPair d29=true := by decide +kernel
def d30 : PairDeck := ⟨260,⟨[2146,610,2186,2184,2193,2130,98,2129,1185,1122,2122,2185,2114,788,2058,673],[3,12,14,6,11,7,10,15,99,1,5,2,4,9,99,8,99,13,99,99,0,99]⟩,⟨[2188,1297,1289,266,1290,660,770,2314,802,676,785,596,1164,778,532,784,1100,786],[15,6,14,3,2,99,16,10,13,11,17,99,5,4,1,12,9,99,8,0,99,7]⟩⟩
theorem check30 : goodPair d30=true := by decide +kernel
def d31 : PairDeck := ⟨264,⟨[1289,2177,1108,676,2314,2132,778,1290,596,674,1185,2193,84,2128,2065,2129,673,1292,2209,2130],[13,1,14,12,0,15,99,16,6,8,19,9,11,7,2,10,3,17,99,5,18,4]⟩,⟨[788,1297,2188,2184,770,2321,786,2185,802,140,2122,2186,1164,652,2058,785],[3,4,14,9,7,99,10,15,13,99,6,11,99,99,1,12,99,0,8,2,99,5]⟩⟩
theorem check31 : goodPair d31=true := by decide +kernel
def d32 : PairDeck := ⟨272,⟨[786,2114,652,1124,2321,2188,1297,785,1164,1121,610,2122,140,2184,2058,2186,1122,788,2146,2185],[13,1,14,12,19,9,11,7,2,10,0,15,99,16,6,8,3,17,99,5,18,4]⟩,⟨[1292,778,2132,2128,1281,2314,1289,2130,1313,84,2193,2129,596,1108,2065,1290],[3,4,14,9,6,11,99,99,1,12,7,99,10,15,13,99,99,0,8,2,99,5]⟩⟩
theorem check32 : goodPair d32=true := by decide +kernel
def d33 : PairDeck := ⟨288,⟨[2132,596,2193,2177,2186,2130,84,2122,1164,1108,2129,2185,2128,802,2065,652],[12,3,14,6,11,10,7,99,15,1,5,4,2,99,9,8,99,99,13,0,99,99]⟩,⟨[2209,1290,1289,273,1297,674,784,2321,788,676,778,610,1185,785,546,770,1121,786],[6,15,14,3,2,16,99,13,10,11,17,5,99,1,4,12,9,8,99,99,0,7]⟩⟩
theorem check33 : goodPair d33=true := by decide +kernel
def d34 : PairDeck := ⟨320,⟨[652,674,140,676,546,672,673,644,1164,2185,660,2209,2188,1354,2386,866,1364],[5,7,4,2,9,99,13,6,0,15,14,1,10,13,16,8,3,16,15,12,11,14]⟩,⟨[1289,784,788,770,785,1124,2314,610,1297,266,1290,778,2122,2132,2146,2129,802,786],[1,3,99,9,0,15,12,4,11,7,17,99,99,10,8,99,5,2,16,13,14,6]⟩⟩
theorem check34 : goodPair d34=true := by decide +kernel
def d35 : PairDeck := ⟨384,⟨[1108,1121,84,1124,1057,1120,1122,1092,596,2130,1100,2146,2132,913,2441,1441,908],[5,7,4,2,14,1,10,13,16,8,9,99,13,6,0,15,3,16,15,12,11,14]⟩,⟨[786,1288,1292,1281,1290,676,2321,1185,778,273,785,1297,2193,2188,2209,2186,1313,1289],[1,3,99,9,17,99,99,10,8,99,0,15,12,4,11,7,5,2,16,13,14,6]⟩⟩
theorem check35 : goodPair d35=true := by decide +kernel
def d36 : PairDeck := ⟨513,⟨[1100,1164,2132,2128,2146,1124,1036,1122,2314,1292,1108,2130,1092,673,84,2186],[3,12,6,14,99,99,0,13,99,99,11,15,99,7,10,1,5,9,99,2,4,8]⟩,⟨[2129,802,786,532,788,2209,644,596,652,2185,674,1185,2321,660,161,672,1297,676],[15,6,3,14,9,0,99,99,8,7,2,10,13,99,16,11,17,4,1,99,5,12]⟩⟩
theorem check36 : goodPair d36=true := by decide +kernel
def d37 : PairDeck := ⟨514,⟨[786,2128,1292,2185,610,1100,674,802,1164,2209,2321,2132,1036,1092,84,1108,2193,778,2129,1124],[1,13,12,14,3,18,5,99,17,4,0,6,16,99,15,8,19,2,7,11,9,10]⟩,⟨[652,788,2122,2114,672,596,676,2130,673,2058,1122,2146,2314,2186,98,660],[4,3,9,14,99,99,2,8,0,5,7,13,15,10,99,99,6,1,99,99,11,12]⟩⟩
theorem check37 : goodPair d37=true := by decide +kernel
def d38 : PairDeck := ⟨516,⟨[676,1120,2186,1289,596,2122,788,660,2314,1297,1185,1122,2058,2114,98,2146,1313,652,1121,2130],[1,13,12,14,3,18,5,99,17,4,19,2,7,11,9,10,0,6,16,99,15,8]⟩,⟨[778,674,1100,1092,784,610,786,1124,785,1036,2132,1108,1164,1292,84,802],[4,3,9,14,99,99,2,8,0,5,6,1,99,99,11,12,7,13,15,10,99,99]⟩⟩
theorem check38 : goodPair d38=true := by decide +kernel
def d39 : PairDeck := ⟨520,⟨[1121,1185,2146,2114,2132,1124,1057,1108,2321,1313,1122,2130,1120,652,98,2193],[12,3,6,14,99,0,99,99,13,99,11,99,15,10,7,1,5,99,9,4,2,8]⟩,⟨[2122,788,786,546,802,2188,672,610,673,2185,660,1164,2314,674,140,644,1290,676],[6,15,3,14,9,99,0,8,99,7,2,13,10,16,99,11,17,1,4,5,99,12]⟩⟩
theorem check39 : goodPair d39=true := by decide +kernel
def d40 : PairDeck := ⟨528,⟨[786,2114,1313,2185,596,1121,660,788,1185,2188,2314,2146,1057,1120,98,1122,2186,785,2122,1124],[13,1,12,14,3,5,18,17,99,4,0,16,6,15,99,8,19,7,2,9,11,10]⟩,⟨[673,802,2129,2128,644,610,676,2130,652,2065,1108,2132,2321,2193,84,674],[3,4,9,14,99,2,99,0,8,5,7,15,13,99,10,99,6,99,1,11,99,12]⟩⟩
theorem check40 : goodPair d40=true := by decide +kernel
def d41 : PairDeck := ⟨544,⟨[676,1092,2193,1289,610,2129,802,674,2321,1290,1164,1108,2065,2128,84,2132,1292,673,1100,2130],[13,1,12,14,3,5,18,17,99,4,19,7,2,9,11,10,0,16,6,15,99,8]⟩,⟨[785,660,1121,1120,770,596,786,1124,778,1057,2146,1122,1185,1313,98,788],[3,4,9,14,99,2,99,0,8,5,6,99,1,11,99,12,7,15,13,99,10,99]⟩⟩
theorem check41 : goodPair d41=true := by decide +kernel
def d42 : PairDeck := ⟨576,⟨[1289,1297,2314,2058,2188,1292,1281,1164,2209,1313,1290,2186,1288,596,266,2193],[12,6,3,14,0,99,99,99,99,13,99,11,15,10,1,7,99,5,9,4,8,2]⟩,⟨[2122,676,674,770,802,2132,784,778,785,2129,660,1108,2146,786,84,532,1122,788],[6,3,15,14,99,9,0,8,7,99,13,2,10,16,11,99,1,17,4,5,12,99]⟩⟩
theorem check42 : goodPair d42=true := by decide +kernel
def d43 : PairDeck := ⟨640,⟨[674,2058,1313,2129,652,1289,660,676,1297,2132,2146,2314,1281,1288,266,1290,2130,673,2122,1292],[13,12,1,14,5,3,18,17,4,99,16,0,6,15,8,99,7,19,2,9,10,11]⟩,⟨[785,802,2185,2184,532,778,788,2186,596,2177,1164,2188,2209,2193,140,786],[3,9,4,14,2,99,99,0,5,8,15,7,13,99,99,10,99,6,1,11,12,99]⟩⟩
theorem check43 : goodPair d43=true := by decide +kernel
def d44 : PairDeck := ⟨768,⟨[788,1036,2193,1121,778,2185,802,786,2209,1122,1108,1164,2177,2184,140,2188,1124,785,1100,2186],[13,12,1,14,5,3,18,17,4,99,7,19,2,9,10,11,16,0,6,15,8,99]⟩,⟨[673,660,1289,1288,546,652,674,1292,610,1281,2314,1290,1297,1313,266,676],[3,9,4,14,2,99,99,0,5,8,99,6,1,11,12,99,15,7,13,99,99,10]⟩⟩
theorem check44 : goodPair d44=true := by decide +kernel
def d45 : PairDeck := ⟨1025,⟨[1289,2184,788,2130,1185,660,1121,1313,596,2146,2314,2188,532,644,140,652,2122,1297,2186,676],[1,13,12,14,0,6,16,99,15,8,3,18,5,99,17,4,19,2,7,11,9,10]⟩,⟨[1108,1292,2193,2177,1120,1164,1124,2185,1122,2065,673,2209,2321,2129,161,1100],[4,3,9,14,7,13,15,10,99,99,99,99,2,8,0,5,6,1,99,99,11,12]⟩⟩
theorem check45 : goodPair d45=true := by decide +kernel
def d46 : PairDeck := ⟨1026,⟨[660,596,2188,2184,2209,676,532,673,2321,788,652,2185,644,1122,140,2129],[3,12,6,14,11,15,99,7,10,1,99,99,0,13,99,99,5,9,99,2,4,8]⟩,⟨[2186,1313,1289,1036,1292,2146,1092,1164,1108,2130,1121,610,2314,1100,98,1120,778,1124],[15,6,3,14,2,10,13,99,16,11,9,0,99,99,8,7,17,4,1,99,5,12]⟩⟩
theorem check46 : goodPair d46=true := by decide +kernel
def d47 : PairDeck := ⟨1028,⟨[1124,672,2129,786,1164,2193,1292,1100,2321,778,610,673,2065,2177,161,2209,802,1108,674,2185],[1,13,12,14,19,2,7,11,9,10,3,18,5,99,17,4,0,6,16,99,15,8]⟩,⟨[1297,1121,660,644,1288,1185,1289,676,1290,532,2188,652,596,788,140,1313],[4,3,9,14,6,1,99,99,11,12,99,99,2,8,0,5,7,13,15,10,99,99]⟩⟩
theorem check47 : goodPair d47=true := by decide +kernel
def d48 : PairDeck := ⟨1032,⟨[1289,2177,802,2130,1164,674,1100,1292,610,2132,2321,2209,546,672,161,673,2129,1290,2193,676],[13,1,12,14,0,16,6,15,99,8,3,5,18,17,99,4,19,7,2,9,11,10]⟩,⟨[1122,1313,2186,2184,1092,1185,1124,2185,1108,2058,652,2188,2314,2122,140,1121],[3,4,9,14,7,15,13,99,10,99,99,2,99,0,8,5,6,99,1,11,99,12]⟩⟩
theorem check48 : goodPair d48=true := by decide +kernel
def d49 : PairDeck := ⟨1040,⟨[674,610,2209,2177,2188,676,546,652,2314,802,673,2185,672,1108,161,2122],[12,3,6,14,11,99,15,10,7,1,99,0,99,99,13,99,5,99,9,4,2,8]⟩,⟨[2193,1292,1289,1057,1313,2132,1120,1185,1122,2130,1100,596,2321,1121,84,1092,785,1124],[6,15,3,14,2,13,10,16,99,11,9,99,0,8,99,7,17,1,4,5,99,12]⟩⟩
theorem check49 : goodPair d49=true := by decide +kernel
def d50 : PairDeck := ⟨1056,⟨[1124,644,2122,786,1185,2186,1313,1121,2314,785,596,652,2058,2184,140,2188,788,1122,660,2185],[13,1,12,14,19,7,2,9,11,10,3,5,18,17,99,4,0,16,6,15,99,8]⟩,⟨[1290,1100,674,672,1281,1164,1289,676,1297,546,2209,673,610,802,161,1292],[3,4,9,14,6,99,1,11,99,12,99,2,99,0,8,5,7,15,13,99,10,99]⟩⟩
theorem check50 : goodPair d50=true := by decide +kernel
def d51 : PairDeck := ⟨1088,⟨[1121,2065,802,2186,1108,786,1100,1124,778,2188,2209,2321,770,784,273,785,2185,1122,2193,788],[13,12,1,14,16,0,6,15,8,99,5,3,18,17,4,99,7,19,2,9,10,11]⟩,⟨[1290,1313,2130,2128,1036,1297,1292,2129,1164,2114,596,2132,2146,2122,84,1289],[3,9,4,14,15,7,13,99,99,10,2,99,99,0,5,8,99,6,1,11,12,99]⟩⟩
theorem check51 : goodPair d51=true := by decide +kernel
def d52 : PairDeck := ⟨1152,⟨[786,778,2321,2065,2132,788,770,596,2146,802,785,2129,784,1164,273,2122],[12,6,3,14,99,11,15,10,1,7,0,99,99,99,99,13,99,5,9,4,8,2]⟩,⟨[2193,1124,1121,1281,1313,2188,1288,1297,1290,2186,1100,652,2209,1289,140,1036,673,1292],[6,3,15,14,13,2,10,16,11,99,99,9,0,8,7,99,1,17,4,5,12,99]⟩⟩
theorem check52 : goodPair d52=true := by decide +kernel
def d53 : PairDeck := ⟨1280,⟨[1292,532,2122,674,1297,2130,1313,1289,2146,673,652,596,2114,2128,84,2132,676,1290,660,2129],[13,12,1,14,7,19,2,9,10,11,5,3,18,17,4,99,16,0,6,15,8,99]⟩,⟨[1122,1100,786,784,1057,1108,1121,788,1185,770,2321,785,778,802,273,1124],[3,9,4,14,99,6,1,11,12,99,2,99,99,0,5,8,15,7,13,99,99,10]⟩⟩
theorem check53 : goodPair d53=true := by decide +kernel
def d54 : PairDeck := ⟨1536,⟨[2122,2132,2058,2130,84,2128,2129,2114,2314,2185,2146,2193,2186,1804,1700,1620,1826],[5,7,2,4,9,6,0,99,13,15,3,12,11,16,15,14,14,13,16,1,10,8]⟩,⟨[1289,1120,1122,1092,1121,786,1164,596,1313,1036,1292,1100,652,674,660,673,1108,1124],[1,3,9,99,0,4,11,15,12,7,5,13,14,2,16,6,17,10,8,99,99,99]⟩⟩
theorem check54 : goodPair d54=true := by decide +kernel
def d55 : PairDeck := ⟨2049,⟨[2185,1288,674,1124,2321,802,2129,2193,610,1108,1164,1290,546,770,266,778,1100,2209,1292,786],[1,13,12,14,0,6,16,99,15,8,19,2,7,11,9,10,3,18,5,99,17,4]⟩,⟨[2146,2186,1313,1281,2128,2314,2130,1289,2132,1057,785,1297,1185,1121,273,2122],[4,3,9,14,7,13,15,10,99,99,6,1,99,99,11,12,99,99,2,8,0,5]⟩⟩
theorem check55 : goodPair d55=true := by decide +kernel
def d56 : PairDeck := ⟨2050,⟨[2130,784,1121,676,2314,1313,2186,2122,1185,652,596,785,1057,1281,273,1297,660,2146,788,1289],[1,13,12,14,19,2,7,11,9,10,0,6,16,99,15,8,3,18,5,99,17,4]⟩,⟨[2209,2129,802,770,2184,2321,2185,786,2188,546,1290,778,610,674,266,2193],[4,3,9,14,6,1,99,99,11,12,7,13,15,10,99,99,99,99,2,8,0,5]⟩⟩
theorem check56 : goodPair d56=true := by decide +kernel
def d57 : PairDeck := ⟨2052,⟨[802,610,1290,1288,1297,786,546,785,1185,674,778,1289,770,2132,266,1121],[3,12,6,14,11,15,99,7,10,1,5,9,99,2,4,8,99,99,0,13,99,99]⟩,⟨[1292,2193,2185,2058,2186,1108,2114,2314,2146,1124,2129,596,1164,2122,84,2128,652,2130],[15,6,3,14,2,10,13,99,16,11,17,4,1,99,5,12,9,0,99,99,8,7]⟩⟩
theorem check57 : goodPair d57=true := by decide +kernel
def d58 : PairDeck := ⟨2056,⟨[2185,1281,660,1124,2314,788,2122,2186,596,1122,1185,1297,532,784,273,785,1121,2188,1313,786],[13,1,12,14,0,16,6,15,99,8,19,7,2,9,11,10,3,5,18,17,99,4]⟩,⟨[2132,2193,1292,1288,2114,2321,2130,1289,2146,1036,778,1290,1164,1100,266,2129],[3,4,9,14,7,15,13,99,10,99,6,99,1,11,99,12,99,2,99,0,8,5]⟩⟩
theorem check58 : goodPair d58=true := by decide +kernel
def d59 : PairDeck := ⟨2064,⟨[2130,770,1100,676,2321,1292,2193,2129,1164,673,610,778,1036,1288,266,1290,674,2132,802,1289],[13,1,12,14,19,7,2,9,11,10,0,16,6,15,99,8,3,5,18,17,99,4]⟩,⟨[2188,2122,788,784,2177,2314,2185,786,2209,532,1297,785,596,660,273,2186],[3,4,9,14,6,99,1,11,99,12,7,15,13,99,10,99,99,2,99,0,8,5]⟩⟩
theorem check59 : goodPair d59=true := by decide +kernel
def d60 : PairDeck := ⟨2080,⟨[788,596,1297,1281,1290,786,532,778,1164,660,785,1289,784,2146,273,1100],[12,3,6,14,11,99,15,10,7,1,5,99,9,4,2,8,99,0,99,99,13,99]⟩,⟨[1313,2186,2185,2065,2193,1122,2128,2321,2132,1124,2122,610,1185,2129,98,2114,673,2130],[6,15,3,14,2,13,10,16,99,11,17,1,4,5,99,12,9,99,0,8,99,7]⟩⟩
theorem check60 : goodPair d60=true := by decide +kernel
def d61 : PairDeck := ⟨2112,⟨[2129,1057,660,1292,2146,676,2122,2130,652,1290,1297,1185,644,672,161,673,1289,2132,1313,674],[13,12,1,14,16,0,6,15,8,99,7,19,2,9,10,11,5,3,18,17,4,99]⟩,⟨[2188,2193,1124,1120,2058,2209,2186,1121,2314,1092,610,1122,1108,1100,98,2185],[3,9,4,14,15,7,13,99,99,10,99,6,1,11,12,99,2,99,99,0,5,8]⟩⟩
theorem check61 : goodPair d61=true := by decide +kernel
def d62 : PairDeck := ⟨2176,⟨[2186,546,1100,788,2209,1124,2193,2185,1108,785,778,610,1092,1120,98,1122,786,2188,802,1121],[13,12,1,14,7,19,2,9,10,11,16,0,6,15,8,99,5,3,18,17,4,99]⟩,⟨[2132,2122,676,672,2065,2146,2129,674,2321,644,1185,673,652,660,161,2130],[3,9,4,14,99,6,1,11,12,99,15,7,13,99,99,10,2,99,99,0,5,8]⟩⟩
theorem check62 : goodPair d62=true := by decide +kernel
def d63 : PairDeck := ⟨2304,⟨[676,652,1185,1057,1122,674,644,610,1108,660,673,1121,672,2314,161,1100],[12,6,3,14,99,11,15,10,1,7,99,5,9,4,8,2,0,99,99,99,99,13]⟩,⟨[1313,2130,2129,2177,2193,1290,2184,2209,2188,1292,2122,778,1297,2185,266,2058,785,2186],[6,3,15,14,13,2,10,16,11,99,1,17,4,5,12,99,99,9,0,8,7,99]⟩⟩
theorem check63 : goodPair d63=true := by decide +kernel
def d64 : PairDeck := ⟨2560,⟨[1100,1122,1036,1124,98,1120,1121,1092,1164,1289,1108,1313,1292,2698,2834,2658,2708],[5,7,2,4,9,6,0,99,13,15,14,13,16,1,10,8,3,12,11,16,15,14]⟩,⟨[2185,2128,2132,2114,2129,676,2314,610,2193,2058,2186,2122,778,788,802,785,2146,2130],[1,3,9,99,0,4,11,15,12,7,17,10,8,99,99,99,5,13,14,2,16,6]⟩⟩
theorem check64 : goodPair d64=true := by decide +kernel
def d65 : PairDeck := ⟨3072,⟨[660,673,532,676,161,672,674,644,596,786,652,802,788,3153,3337,3233,3148],[5,7,2,4,14,13,16,1,10,8,9,6,0,99,13,15,3,12,11,16,15,14]⟩,⟨[2130,2184,2188,2177,2186,1124,2321,1185,2122,2065,2129,2193,1297,1292,1313,1290,2209,2185],[1,3,9,99,17,10,8,99,99,99,0,4,11,15,12,7,5,13,14,2,16,6]⟩⟩
theorem check65 : goodPair d65=true := by decide +kernel
def book : List PairDeck := [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15,d16,d17,d18,d19,d20,d21,d22,d23,d24,d25,d26,d27,d28,d29,d30,d31,d32,d33,d34,d35,d36,d37,d38,d39,d40,d41,d42,d43,d44,d45,d46,d47,d48,d49,d50,d51,d52,d53,d54,d55,d56,d57,d58,d59,d60,d61,d62,d63,d64,d65]
theorem checked : ∀ d∈book, goodPair d=true := by
  intro d h
  simp only [book,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35
  · exact check36
  · exact check37
  · exact check38
  · exact check39
  · exact check40
  · exact check41
  · exact check42
  · exact check43
  · exact check44
  · exact check45
  · exact check46
  · exact check47
  · exact check48
  · exact check49
  · exact check50
  · exact check51
  · exact check52
  · exact check53
  · exact check54
  · exact check55
  · exact check56
  · exact check57
  · exact check58
  · exact check59
  · exact check60
  · exact check61
  · exact check62
  · exact check63
  · exact check64
  · exact check65

def getPair (f : Nat) := book.find? (fun d=>d.mask==f)
def amount (u v : V) : Nat := if u.1 = v.1 then 3 else if u.2 = v.2 then 2 else 4

def correctKey (u v : V) : Bool :=
  let f:=formMask {u,v}
  match getPair f with
  | some d=>decide (d.left.words.length+d.right.words.length≥32+amount u v)
  | none=>false

set_option maxHeartbeats 1600000 in
theorem keys : ∀ u v : V, u≠v → correctKey u v=true := by decide +kernel

theorem allPairRoot {C : ClauseMap V} {P : Parents} {r u v : Nat}
    (rules : ∀i≤r,Rule (linOfClause '' PHP 4 3) C P i) (unsat : ∀a,FalseAt C a r)
    (small : r<55) (ur : u<r) (vr : v<r) (rootRule : P r=[u,v])
    (a b : V) (distinct : a≠b) (neg : ({a,b},false)∈C u) (pos : ({a,b},true)∈C v)
    (join : C r=(C u).erase ({a,b},false) ∪ (C v).erase ({a,b},true)) :
    amount a b ≤ (internalNodes P u ∩ internalNodes P v).card := by
  have key:=keys a b distinct
  unfold correctKey at key
  cases he:getPair (formMask {a,b}) with
  | none => simp [he] at key
  | some d =>
    have count : d.left.words.length+d.right.words.length≥32+amount a b := by simpa [he] using key
    have got : book.find? (fun w=>w.mask==formMask {a,b})=some d := he
    have inside : d∈book:=List.mem_of_find?_eq_some got
    have eq : d.mask=formMask {a,b}:=beq_iff_eq.mp (List.find?_some got)
    have good:=Bool.and_eq_true_iff.mp (checked d inside)
    have ru := fun i (hi : i≤u)=>rules i (hi.trans ur.le)
    have rv := fun i (hi : i≤v)=>rules i (hi.trans vr.le)
    have large : ({a,b} : Finset V).card≠1 := by simp [Finset.card_pair distinct]
    have wu:=unaryBirth ru ({a,b},false) large neg
    have wv:=unaryBirth rv ({a,b},true) large pos
    have bu:=internalSize ru
    have bv:=internalSize rv
    have total:=intersectionBudget rules unsat rootRule ur vr
    have zero (x) (h : parity x d.mask=false) : FalseAt C (assignment x) v := by
      have z:=resolve_branch (assignment x) join (unsat _)
      rw [eq,parity_form] at h
      have even : ¬Odd (({a,b}:Finset V).filter (fun v=>assignment x v=true)).card := of_decide_eq_false h
      simpa only [FalseAt,if_neg even] using z
    have one (x) (h : parity x d.mask=true) : FalseAt C (assignment x) u := by
      have z:=resolve_branch (assignment x) join (unsat _)
      rw [eq,parity_form] at h
      have odd : Odd (({a,b}:Finset V).filter (fun v=>assignment x v=true)).card := of_decide_eq_true h
      simpa only [FalseAt,if_pos odd] using z
    have l:=deckLeaves d.left rv good.1 zero
    have s:=deckLeaves d.right ru good.2 one
    omega
end PEqualNP.Outside.L_pcx_121.Packing
