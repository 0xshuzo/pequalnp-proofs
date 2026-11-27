import PEqualNP.Defs
namespace Obstruction468
open MvPolynomial PEqualNP.ProofComplexity
abbrev K := ZMod 2
abbrev Poly (V : Type) := MvPolynomial V K
def agree {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (p : Poly V) (c : T → K) :=
  ∀ x∈Q, eval x p = ∑ i, c i * eval x (f i)
def separated {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (d : ℕ) :=
  ∀ (p : Poly V) (c : T → K), p.totalDegree<d → agree Q f p c → ∀ i, c i=0

theorem lines {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (A : Set (Poly V))
    (d : ℕ) (van : ∀ a∈A, ∀ x∈Q, eval x a=0) (sep : separated Q f d)
    {p : Poly V} (h : PCDerivable (A ∪ Set.range f) d p) : ∃ c, agree Q f p c := by
  classical
  induction h with
  | ax hp _ =>
    rcases hp with a|⟨i,rfl⟩
    · exact ⟨0,fun x hx => by simpa using van _ a x hx⟩
    · refine ⟨fun j => if i=j then 1 else 0,?_⟩
      intro x hx
      simp
  | zero => exact ⟨0,fun x _ => by simp⟩
  | add _ _ il ir =>
    obtain ⟨a,ha⟩ := il
    obtain ⟨b,hb⟩ := ir
    refine ⟨a+b,?_⟩
    intro x hx
    simp only [map_add,ha x hx,hb x hx,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  | @mulX v p hp hd ih =>
    refine ⟨0,?_⟩
    intro x hx
    by_cases hn : p=0
    · simp [hn]
    · rw [totalDegree_mul_of_isDomain (X_ne_zero v) hn,totalDegree_X] at hd
      obtain ⟨c,hc⟩ := ih
      have z := sep p c (by omega) hc
      have hz : eval x p=0 := by simpa [z] using hc x hx
      simp [hz]

theorem notRefutable {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (A : Set (Poly V))
    (d : ℕ) (hd : 0<d) (wit : Q.Nonempty) (van : ∀ a∈A, ∀ x∈Q, eval x a=0)
    (sep : separated Q f d) : ¬PCRefutable (A ∪ Set.range f) d := by
  intro contra
  obtain ⟨c,hc⟩ := lines Q f A d van sep contra
  have val := sep 1 c (by simpa using hd) hc
  obtain ⟨x,hx⟩ := wit
  have bad := hc x hx
  simpa [val] using bad

theorem cube_separates {V T B Z : Type} [Fintype T] [Fintype Z]
    (Q : Set (V → K)) (f : T → Poly V) (d : ℕ)
    (probe : B → Z → (V → K)) (inside : ∀ b z, probe b z∈Q)
    (low : ∀ p : Poly V, p.totalDegree < d → ∀ b, ∑ z, eval (probe b z) p=0)
    (profiles : LinearIndependent K (fun i : T => fun b : B => ∑ z, eval (probe b z) (f i))) :
    separated Q f d := by
  classical
  intro p c dp agree
  apply Fintype.linearIndependent_iff.mp profiles c
  funext b
  change (∑ i, c i • (fun b : B => ∑ z, eval (probe b z) (f i))) b = 0
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ z, eval (probe b z) p := Finset.sum_congr rfl (fun z _ => (agree _ (inside b z)).symm)
    _ = 0 := low p dp b
end Obstruction468
