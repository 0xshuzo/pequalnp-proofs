import PEqualNP.Defs
namespace PEqualNP.Outside.Pcx9792Cylinders

abbrev V := Fin 24
def edges : List (V × V) := [(0, 15), (0, 21), (0, 23), (1, 16), (1, 22), (2, 13), (2, 17), (2, 23), (3, 13), (3, 14), (3, 18), (4, 14), (4, 15), (4, 19), (5, 13), (5, 15), (5, 16), (5, 20), (6, 14), (6, 16), (6, 17), (6, 21), (7, 15), (7, 17), (7, 18), (7, 22), (8, 16), (8, 18), (8, 19), (8, 23), (9, 17), (9, 19), (9, 20), (10, 18), (10, 20), (10, 21), (11, 13), (11, 19), (11, 21), (11, 22), (12, 14), (12, 20), (12, 22), (12, 23)]
def graph (s : Finset V) : Prop := ∃ e ∈ edges, e.1 ∈ s ∧ e.2 ∈ s
instance (s : Finset V) : Decidable (graph s) :=
  inferInstanceAs (Decidable (∃ e ∈ edges, e.1∈s ∧ e.2∈s))
def witnesses : List Nat := [112128, 1703947, 6439200, 9701458, 4980837, 607365, 2110354, 334357, 4204369]
def bits (m : Nat) : Finset V := Finset.univ.filter (fun i : V => m.testBit i.val)
def special (i j k : V) : Bool := decide (({i,j,k} : Finset V) = {1,16,22})

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem supports : witnesses.all (fun m => decide (¬graph (bits m)) &&
    (List.finRange 24).all (fun i => m.testBit i.val || decide (graph (insert i (bits m)))))=true := by
  decide +kernel

theorem outside : ∀ i j k : V, (special i j k || witnesses.any
  (fun m => !m.testBit i.val && !m.testBit j.val && !m.testBit k.val))=true := by
  decide +kernel

theorem one (m : Nat) (hm : m ∈ witnesses) : ¬graph (bits m) ∧
    ∀ i : V, m.testBit i.val=false → graph (insert i (bits m)) := by
  have a := List.all_eq_true.mp supports m hm
  simp only [Bool.and_eq_true,decide_eq_true_eq] at a
  refine ⟨a.1,?_⟩
  intro i off
  have b := List.all_eq_true.mp a.2 i (List.mem_finRange i)
  simpa [off] using b

def loses (f : Finset V → Prop) (i : V) : Prop := ∀ s, f (insert i s) → f s

theorem triple {f g h : Finset V → Prop} (correct : ∀ s, graph s ↔ f s ∧ g s ∧ h s)
    {i j k : V} (li : loses f i) (lj : loses g j) (lk : loses h k) :
    ({i,j,k} : Finset V) = {1,16,22} := by
  have cover := outside i j k
  rcases Bool.or_eq_true.mp cover with yes|other
  · exact of_decide_eq_true yes
  · obtain ⟨m,hm,test⟩ := List.any_eq_true.mp other
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at test
    have r := one m hm
    have fa := li _ ((correct _).mp (r.2 i test.1.1)).1
    have gb := lj _ ((correct _).mp (r.2 j test.1.2)).2.1
    have hc := lk _ ((correct _).mp (r.2 k test.2)).2.2
    exact False.elim (r.1 ((correct _).mpr ⟨fa,gb,hc⟩))

theorem repeatFalse : ∀ a b : V, ({a,b,b} : Finset V) ≠ {1,16,22} := by decide +kernel

/-- A two-way AND factorization has an operand responsive to every input. -/
theorem fullParent {f g : Finset V → Prop} (correct : ∀ s, graph s ↔ f s ∧ g s) :
    (∀ i, ¬loses f i) ∨ (∀ j, ¬loses g j) := by
  classical
  by_contra n
  obtain ⟨i,hi⟩ : ∃ i, loses f i := by
    by_contra! fail
    exact n (Or.inl fail)
  obtain ⟨j,hj⟩ : ∃ j, loses g j := by
    by_contra! fail
    exact n (Or.inr fail)
  have combined : ∀ s, graph s ↔ f s ∧ g s ∧ g s := by
    intro s
    simpa only [and_self] using correct s
  exact repeatFalse i j (triple combined hi hj hj)

end PEqualNP.Outside.Pcx9792Cylinders
