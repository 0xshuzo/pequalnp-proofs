import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9348.Affine
abbrev V := Fin 21
abbrev Rect := Finset V × Finset V
abbrev Pat := Bool × Bool × Bool
def ink (r c : V) : Bool := (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List Nat).getD r.val 0).testBit c.val
def chain : Pat → Fin 3
  | (false,false,false) | (true,false,false) | (true,true,false) | (true,true,true) => 0
  | (false,true,false) | (false,true,true) => 1
  | _ => 2
def inc (p q : Pat) : Prop := (p.1 = true → q.1 = true) ∧
  (p.2.1 = true → q.2.1 = true) ∧ (p.2.2 = true → q.2.2 = true)
instance (p q : Pat) : Decidable (inc p q) := by unfold inc; infer_instance
theorem comparable : ∀ p q : Pat, chain p = chain q → inc p q ∨ inc q p := by decide +kernel
def marks (R : Fin 3 → Rect) (r : V) : Pat :=
  (decide (r∈(R 0).1),decide (r∈(R 1).1),decide (r∈(R 2).1))
theorem carry {R : Fin 3 → Rect} {a b : V} (h : inc (marks R a) (marks R b))
    (t : Fin 3) (ha : a ∈ (R t).1) : b ∈ (R t).1 := by
  simp only [inc,marks,decide_eq_true_eq] at h
  fin_cases t
  · exact h.1 ha
  · exact h.2.1 ha
  · exact h.2.2 ha
theorem distinguishes : ∀ a b : V, a ≠ b → ∃ c : V, ink a c = false ∧ ink b c = true := by
  decide +kernel
theorem fourRows (v : Fin 4 → V) (inj : Function.Injective v) (R : Fin 3 → Rect)
    (law : ∀ t a, a ∈ (R t).1 → ∀ c ∈ (R t).2, ink a c = false)
    (cov : ∀ i c, ink (v i) c = false → ∃ t : Fin 3, v i ∈ (R t).1 ∧ c ∈ (R t).2) :
    False := by
  have reflect {i j : Fin 4} (h : inc (marks R (v i)) (marks R (v j))) : i = j := by
    by_contra ne
    obtain ⟨c,good,bad⟩ := distinguishes (v i) (v j) (fun eq => ne (inj eq))
    obtain ⟨t,hm,hc⟩ := cov i c good
    have no := law t (v j) (carry h t hm) c hc
    simp_all
  have small : Function.Injective (fun i : Fin 4 => chain (marks R (v i))) := by
    intro i j he
    rcases comparable _ _ he with h | h
    · exact reflect h
    · exact (reflect h).symm
  have h := Fintype.card_le_of_injective _ small
  norm_num at h
def rows (i : Fin 4) : V := ([1, 16, 4, 14] : List V).getD i.val 0
def bank : List (Nat × Nat) := [(266048,1576971),(1180940,284705),(537672,82067),(175232,524597),(1048768,427779),(1087008,270477),(557312,202309),(2088,713281),(397312,1083105),(787620,1124609),(8708,167001)]
theorem rows_injective : Function.Injective rows := by decide +kernel
theorem untouched : ∀ i : Fin 4, ∀ b ∈ bank, b.1.testBit (rows i).val = false := by decide +kernel
theorem affineExtra (R : Fin 3 → Rect)
    (law : ∀ t a, a ∈ (R t).1 → ∀ c ∈ (R t).2, ink a c = false)
    (cov : ∀ a c, ink a c = false →
      (∃ b ∈ bank, b.1.testBit a.val = true ∧ b.2.testBit c.val = true) ∨
      ∃ t : Fin 3, a ∈ (R t).1 ∧ c ∈ (R t).2) : False := by
  apply fourRows rows rows_injective R law
  intro i c good
  rcases cov (rows i) c good with ⟨b,hb,h,_⟩ | found
  · rw [untouched i b hb] at h
    contradiction
  · exact found
end PEqualNP.Outside.L_meta_9348.Affine
