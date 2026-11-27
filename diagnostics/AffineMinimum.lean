import PEqualNP.Outside.L_meta_10036
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
def localInk (i : Fin 16) (j : Fin 20) : Bool :=
  (([69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528] : List Nat).getD i.val 0).testBit j.val
def chartRows (i : Fin 16) : V := ([2, 7, 8, 11, 5, 6, 9, 19, 15, 20, 3, 13, 17, 10, 12, 18] : List V).getD i.val 0
def chartColumns (j : Fin 20) : V := ([1, 6, 8, 18, 2, 12, 15, 16, 9, 3, 4, 11, 19, 14, 13, 10, 7, 5, 20, 17] : List V).getD j.val 0
theorem chartChecked : ∀ i j, ink (chartRows i) (chartColumns j) = localInk i j := by decide +kernel

abbrev SmallRect := Finset (Fin 16) × Finset (Fin 20)
def pull (R : Fin 16 → V) (C : Fin 20 → V) (b : Rect) : SmallRect :=
  (Finset.univ.filter (fun i => R i ∈ b.1), Finset.univ.filter (fun j => C j ∈ b.2))
def active (R : Fin 16 → V) (C : Fin 20 → V) (b : Rect) :=
  decide ((pull R C b).1.Nonempty ∧ (pull R C b).2.Nonempty)

theorem elevenInChart (R : Fin 16 → V) (C : Fin 20 → V)
    (eq : ∀ i j, ink (R i) (C j) = localInk i j) (L : List Rect)
    (law : ∀ b ∈ L, ∀ a ∈ b.1, ∀ c ∈ b.2, ink a c = false)
    (cov : ∀ a c, ink a c = false → ∃ b ∈ L, a ∈ b.1 ∧ c ∈ b.2) :
    11 ≤ (L.filter (active R C)).length := by
  by_contra! few
  apply PEqualNP.Outside.L_meta_10036
  refine ⟨(L.filter (active R C)).map (pull R C),?_,?_,?_⟩
  · rw [List.length_map]
    omega
  · intro box hbox i hi j hj
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hbox
    have bi : R i ∈ b.1 := by simpa [pull] using hi
    have bj : C j ∈ b.2 := by simpa [pull] using hj
    exact (eq i j).symm.trans (law b (List.mem_filter.mp hb).1 (R i) bi (C j) bj)
  · intro i j hz
    obtain ⟨b,hb,hi,hj⟩ := cov (R i) (C j) ((eq i j).trans hz)
    have ri : i ∈ (pull R C b).1 := by simpa [pull] using hi
    have cj : j ∈ (pull R C b).2 := by simpa [pull] using hj
    have ok : active R C b = true := by
      apply decide_eq_true
      exact ⟨⟨i,ri⟩,⟨j,cj⟩⟩
    exact ⟨pull R C b,List.mem_map_of_mem (List.mem_filter.mpr ⟨hb,ok⟩),ri,cj⟩

theorem postedChart (L : List Rect)
    (law : ∀ b ∈ L, ∀ a ∈ b.1, ∀ c ∈ b.2, ink a c = false)
    (cov : ∀ a c, ink a c = false → ∃ b ∈ L, a ∈ b.1 ∧ c ∈ b.2) :
    11 ≤ (L.filter (active chartRows chartColumns)).length :=
  elevenInChart chartRows chartColumns chartChecked L law cov

end PEqualNP.Outside.L_meta_9348.Affine
