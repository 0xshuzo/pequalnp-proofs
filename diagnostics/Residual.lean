import Mathlib
import PEqualNP.Defs

namespace Residual2620

abbrev Sig := BitVec 7

def roots : List Sig := [1,62,66,68,72,80,0,127]

def binary (op : Bool) (a b : Sig) := if op then a ||| b else a &&& b

def moves (b : List Sig) : List Sig :=
  ((b.flatMap fun u => b.flatMap fun v => [u &&& v, u ||| v]).eraseDups).filter
    (fun u => decide (u ∉ b))

def meets (b : List Sig) : Bool :=
  decide ((31 : Sig)∈b ∨ ((63 : Sig)∈b ∧ (95 : Sig)∈b))

def cert : ℕ → List Sig → Bool
  | 0,b => !meets b
  | k+1,b => cert k b && (moves b).all fun u => cert k (u::b)

theorem mem_moves {a b : Sig} {B : List Sig} (ha : a∈B) (hb : b∈B)
    (op : Bool) (new : binary op a b ∉ B) : binary op a b ∈ moves B := by
  simp only [moves,List.mem_filter,List.mem_eraseDups,decide_eq_true_eq]
  refine ⟨List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩,new⟩
  cases op <;> simp [binary]

theorem meet_cases : ∀ u v : Sig, u &&& v = 31 →
    u=31 ∨ v=31 ∨ (u=63 ∧ v=95) ∨ (v=63 ∧ u=95) := by
  decide +kernel

theorem no_meet {B : List Sig} (h : meets B=false) {a b : Sig} (ha:a∈B) (hb:b∈B) :
    a &&& b ≠ 31 := by
  intro eq
  have no := meet_cases a b eq
  simp only [meets,decide_eq_false_iff_not] at h
  rcases no with e|e|⟨e,f⟩|⟨e,f⟩ <;> subst_vars <;> tauto

inductive builds : ℕ → List Sig → Prop
  | done {B a b} (ha : a∈B) (hb : b∈B) (value : a &&& b = 31) : builds 0 B
  | skip {k B} : builds k B → builds (k+1) B
  | gate {k B a b} (op : Bool) (ha : a∈B) (hb : b∈B) :
    builds k ((binary op a b)::B) → builds (k+1) B

theorem sound {k B} (h : cert k B=true) :
    ∀ A, (∀ u∈A, u∈B) → ¬ builds k A := by
  intro A sub run
  induction run generalizing B with
  | done ha hb eq =>
    exact no_meet (by simpa [cert] using h) (sub _ ha) (sub _ hb) eq
  | skip r ih =>
    exact ih (Bool.and_eq_true_iff.mp h).1 sub
  | @gate k A a b op ha hb r ih =>
    obtain ⟨old,step⟩ := Bool.and_eq_true_iff.mp h
    by_cases seen : binary op a b∈B
    · apply ih old
      intro u hu
      rcases List.mem_cons.mp hu with e|hu
      · simpa only [e] using seen
      · exact sub _ hu
    · have next := List.all_eq_true.mp step (binary op a b) (mem_moves (sub _ ha) (sub _ hb) op seen)
      apply ih next
      intro u hu
      rcases List.mem_cons.mp hu with e|hu
      · exact List.mem_cons.mpr (Or.inl e)
      · exact List.mem_cons.mpr (Or.inr (sub _ hu))

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem first2 : cert 3 (2::roots) = true := by decide +kernel
theorem first4 : cert 3 (4::roots) = true := by decide +kernel
theorem first8 : cert 3 (8::roots) = true := by decide +kernel
theorem first16 : cert 3 (16::roots) = true := by decide +kernel
theorem first63 : cert 3 (63::roots) = true := by decide +kernel
theorem first64 : cert 3 (64::roots) = true := by decide +kernel
theorem first67 : cert 3 (67::roots) = true := by decide +kernel
theorem first69 : cert 3 (69::roots) = true := by decide +kernel
theorem first70 : cert 3 (70::roots) = true := by decide +kernel
theorem first73 : cert 3 (73::roots) = true := by decide +kernel
theorem first74 : cert 3 (74::roots) = true := by decide +kernel
theorem first76 : cert 3 (76::roots) = true := by decide +kernel
theorem first81 : cert 3 (81::roots) = true := by decide +kernel
theorem first82 : cert 3 (82::roots) = true := by decide +kernel
theorem first84 : cert 3 (84::roots) = true := by decide +kernel
theorem first88 : cert 3 (88::roots) = true := by decide +kernel
theorem first126 : cert 3 (126::roots) = true := by decide +kernel
theorem old : cert 3 roots=true := by decide +kernel
theorem table : cert 4 roots=true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨old,List.all_eq_true.mpr ?_⟩
  intro u hu
  have casesU : u=2 ∨ u=4 ∨ u=8 ∨ u=16 ∨ u=63 ∨ u=64 ∨ u=67 ∨ u=69 ∨ u=70 ∨ u=73 ∨ u=74 ∨ u=76 ∨ u=81 ∨ u=82 ∨ u=84 ∨ u=88 ∨ u=126 := by
    have closed : ∀ u : Sig, u ∈ moves roots → u=2 ∨ u=4 ∨ u=8 ∨ u=16 ∨ u=63 ∨ u=64 ∨ u=67 ∨ u=69 ∨ u=70 ∨ u=73 ∨ u=74 ∨ u=76 ∨ u=81 ∨ u=82 ∨ u=84 ∨ u=88 ∨ u=126 := by decide +kernel
    exact closed u hu
  rcases casesU with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact first2 | exact first4 | exact first8 | exact first16 | exact first63 | exact first64 | exact first67 | exact first69 | exact first70 | exact first73 | exact first74 | exact first76 | exact first81 | exact first82 | exact first84 | exact first88 | exact first126

theorem five_gates_excluded : ¬ builds 4 roots := sound table roots (fun _ h => h)

end Residual2620
