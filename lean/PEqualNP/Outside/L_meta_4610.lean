import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4610_aux

def Step (available : List ℕ) (z : ℕ) : Prop :=
  ∃ a ∈ available, ∃ b ∈ available, z = a &&& b ∨ z = a ||| b

def Valid (A U : List ℕ) : Prop :=
  ∀ i : Fin U.length, Step (A ++ U.take i.val) (U.get i)

lemma snoc {A U : List ℕ} {z : ℕ} (h : Valid A U) (last : Step (A ++ U) z) :
    Valid A (U ++ [z]) := by
  rintro ⟨i,hi⟩
  simp only [List.length_append, List.length_singleton] at hi
  by_cases lt : i < U.length
  · have h' := h ⟨i,lt⟩
    simpa [List.take_append_of_le_length lt.le, List.getElem_append_left lt] using h'
  · have eq : i = U.length := by omega
    subst i
    simpa using last

lemma unsnoc {A U : List ℕ} {z : ℕ} (h : Valid A (U ++ [z])) :
    Valid A U ∧ Step (A ++ U) z := by
  constructor
  · rintro ⟨i,hi⟩
    have h' := h ⟨i, by simp; omega⟩
    simpa [List.take_append_of_le_length hi.le, List.getElem_append_left hi] using h'
  · have h' := h ⟨U.length, by simp⟩
    simpa using h'

lemma lift_step {q z : ℕ} {A : List ℕ} (h : Step (A.map (fun x => x &&& q)) z) :
    ∃ w, Step A w ∧ w &&& q = z := by
  obtain ⟨a, ha, b, hb, op⟩ := h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
  rcases op with rfl | rfl
  · refine ⟨x &&& y, ⟨x,hx,y,hy,Or.inl rfl⟩, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases q.testBit i <;> rfl
  · refine ⟨x ||| y, ⟨x,hx,y,hy,Or.inr rfl⟩, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases x.testBit i <;> cases y.testBit i <;> cases q.testBit i <;> rfl

lemma lift_trace {A U : List ℕ} {q : ℕ} (h : Valid (A.map (fun x => x &&& q)) U) :
    ∃ V, V.length = U.length ∧ Valid A V ∧ V.map (fun x => x &&& q) = U := by
  induction U using List.reverseRecOn with
  | nil => exact ⟨[], rfl, fun i => Fin.elim0 i, rfl⟩
  | append_singleton U z ih =>
    obtain ⟨pre, last⟩ := unsnoc h
    obtain ⟨V, len, val, same⟩ := ih pre
    have last' : Step ((A ++ V).map (fun x => x &&& q)) z := by
      simpa only [List.map_append, same] using last
    obtain ⟨w,hw,eq⟩ := lift_step last'
    exact ⟨V ++ [w], by simp [len], snoc val hw, by simp [same,eq]⟩

lemma monotone_trace {A U : List ℕ} {i j : ℕ} (h : Valid A U)
    (base : ∀ x ∈ A, x.testBit i = true → x.testBit j = true) :
    ∀ x ∈ A ++ U, x.testBit i = true → x.testBit j = true := by
  induction U using List.reverseRecOn with
  | nil => simpa using base
  | append_singleton U z ih =>
    obtain ⟨pre, last⟩ := unsnoc h
    have prev := ih pre
    intro x hx
    rw [← List.append_assoc] at hx
    rcases List.mem_append.mp hx with old | lastMem
    · exact prev x old
    · have eq : x = z := List.mem_singleton.mp lastMem
      subst x
      obtain ⟨a, ha, b, hb, op⟩ := last
      have ma := prev a ha
      have mb := prev b hb
      rcases op with rfl | rfl
      · simp only [Nat.testBit_and, Bool.and_eq_true_iff]
        exact fun hi => ⟨ma hi.1, mb hi.2⟩
      · simp only [Nat.testBit_or, Bool.or_eq_true_iff]
        exact fun hi => hi.imp ma mb

end PEqualNP.Outside.L_meta_4610_aux

open PEqualNP.Outside.L_meta_4610_aux

theorem PEqualNP.Outside.L_meta_4610 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 : ℕ) => ∀ (x5 : ℕ), ∃ (x6 : ℕ), x3.testBit x6 = Bool.true ∧ x4.testBit x6 = x4.testBit x5 ∧ ∀ x7 ∈ x2, if x4.testBit x5 = Bool.true then x7.testBit x6 = Bool.true → x7.testBit x5 = Bool.true else x7.testBit x5 = Bool.true → x7.testBit x6 = Bool.true; ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ),   x2 x3 x4 x5 →     have x8 : List ℕ := List.map (fun (x8 : ℕ) => x8 &&& x4) x3;     x1 x8 x6 → x5 &&& x4 ∈ x8 ++ x6 → ∃ (x11 : List ℕ), x11.length ≤ x6.length ∧ x1 x3 x11 ∧ x5 ∈ x3 ++ x11 := by
  intro valid cover K q t U reps B prog out
  obtain ⟨V, len, leg, same⟩ := lift_trace (A := K) (q := q) (U := U) prog
  have projected : t &&& q ∈ (K ++ V).map (fun x => x &&& q) := by
    simpa only [List.map_append, same] using out
  obtain ⟨w, hw, he⟩ := List.mem_map.mp projected
  have recover : w = t := by
    apply Nat.eq_of_testBit_eq
    intro i
    obtain ⟨j, keep, classEq, order⟩ := reps i
    have equal := congrArg (fun n : ℕ => n.testBit j) he
    change (w &&& q).testBit j = (t &&& q).testBit j at equal
    simp only [Nat.testBit_and, keep, Bool.and_true] at equal
    by_cases on : t.testBit i = true
    · have base (a : ℕ) (ha : a ∈ K) : a.testBit j = true → a.testBit i = true := by
        simpa only [on, ↓reduceIte] using order a ha
      rw [on]
      exact monotone_trace leg base w hw (equal.trans (classEq.trans on))
    · have off : t.testBit i = false := by simpa using on
      have base (a : ℕ) (ha : a ∈ K) : a.testBit i = true → a.testBit j = true := by
        simpa only [off, Bool.false_eq_true, ↓reduceIte] using order a ha
      rw [off]
      apply Bool.eq_false_iff.mpr
      intro hi
      have hj := monotone_trace leg base w hw hi
      exact Bool.noConfusion (hj.symm.trans (equal.trans (classEq.trans off)))
  exact ⟨V, len.le, leg, recover ▸ hw⟩
