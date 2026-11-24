import Mathlib
import PEqualNP.Defs

-- The sparse-output equivalence follows R_meta_3252_417 by danyalutsevich.
set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_4289_1
    (sizeBound : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (2 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) → (3 : ℕ) * x2 ≤ x9 + (1 : ℕ))
    (hard : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      300 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p : Fin n // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool))),
      let m := n+n
      let one (p i : Fin n) := decide (i=p)
      let A (w : ℕ) := {p : Fin n | (one p, fun _ => false) ∈ W w}
      o < m+s → (∀ p : Fin n, W p.val = {z | z.1 p = true} ∧ W (n+p.val) = {z | z.2 p = true}) →
      (∀ g < s, ∃ a b, max a b < m+g ∧ W (m+g) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
      (∀ z : (Fin n → Bool) × (Fin n → Bool), Fintype.card {l : Fin n // z.2 l = true} ≤ q →
        (z ∈ W o ↔ ∃ p l, I p l ∧ z.1 p = true ∧ z.2 l = true)) →
      (∃ g < s, ∃ a < m+g, ∃ b < m+g,
        W (m+g) = W a ∩ W b ∧
        (∃ p r t : Fin n, p ≠ r ∧ t ≠ p ∧ t ≠ r ∧ p ∈ A (m+g) ∧ r ∈ A (m+g) ∧ t ∈ A (m+g)) ∧
        (∃ u : Fin n, u ∈ A a ∧ u ∉ A b) ∧ (∃ v : Fin n, v ∈ A b ∧ v ∉ A a) ∧
        (¬∃ u < m+g, ∃ v < m+g, A (m+g) = A u ∪ A v) ∧
        ∀ j < g, ∀ p r : Fin n, p ≠ r → p ∈ A (m+j) → r ∈ A (m+j) →
          ∃ u < m+j, ∃ v < m+j, A (m+j) = A u ∪ A v) →
      n*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (x22 : Fin x2) => Bool.false) else (fun (x22 : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Fin x2) (x22 : Fin x2), x21 ≠ x22 ∧ x21 ∈ x19 Bool.true (x12 + x20) ∧ x22 ∈ x19 Bool.true (x12 + x20) ∧ ¬∃ x23 < x12 + x20, ∃ x24 < x12 + x20, x19 Bool.true (x12 + x20) = x19 Bool.true x23 ∪ x19 Bool.true x24) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  dsimp only
  intro q n I inst large order degrees unique s o W out inputs steps positive negative witness
  by_cases big : 300 ≤ q
  · apply hard q n I big order degrees unique s o W out inputs steps
    · let below (a b : (Fin n → Bool) × (Fin n → Bool)) :=
        (∀ i, a.1 i = true → b.1 i = true) ∧ (∀ i, a.2 i = true → b.2 i = true)
      have monotone : ∀ w < n+n+s, ∀ a b, below a b → a ∈ W w → b ∈ W w := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw a b le ha
          by_cases left : w < n
          · let p : Fin n := ⟨w,left⟩
            have eq : W w = {z | z.1 p = true} := (inputs p).1
            rw [eq] at ha ⊢
            exact le.1 p ha
          · by_cases right : w < n+n
            · let p : Fin n := ⟨w-n, by omega⟩
              have eq : w = n+p.val := by dsimp [p]; omega
              rw [eq,(inputs p).2] at ha ⊢
              exact le.2 p ha
            · let g := w-(n+n)
              have eq : w = n+n+g := by dsimp [g]; omega
              obtain ⟨u,v,lower,law⟩ := steps g (by omega)
              have mx : max u v < w := by rwa [eq]
              have hu : u < w := lt_of_le_of_lt (le_max_left _ _) mx
              have hv : v < w := lt_of_le_of_lt (le_max_right _ _) mx
              have um := ih u hu (by omega) a b le
              have vm := ih v hv (by omega) a b le
              rw [eq] at ha ⊢
              simp only [List.mem_cons,List.not_mem_nil,or_false] at law
              rcases law with union | copy | zero | inter
              · rw [union] at ha ⊢
                exact ha.elim (fun h => Or.inl (um h)) (fun h => Or.inr (vm h))
              · rw [copy] at ha ⊢
                exact um ha
              · rw [zero] at ha
                exact False.elim ha
              · rw [inter] at ha ⊢
                exact ⟨um ha.1,vm ha.2⟩
      intro z sparse
      constructor
      · intro accepted
        by_contra forbidden
        let a : Fin n → Bool := fun p => decide (¬ ∃ l, I p l ∧ z.2 l = true)
        apply negative z.2 sparse
        apply monotone o out z (a,z.2) ?_ accepted
        refine ⟨?_,fun i h => h⟩
        intro p hp
        change decide (¬ ∃ l, I p l ∧ z.2 l = true) = true
        apply decide_eq_true
        rintro ⟨l,inc,line⟩
        exact forbidden ⟨p,l,inc,hp,line⟩
      · rintro ⟨p,l,inc,hp,hl⟩
        apply monotone o out _ z ?_ (positive p l inc)
        refine ⟨?_,?_⟩
        · intro i hi
          change decide (i=p) = true at hi
          rw [of_decide_eq_true hi]
          exact hp
        · intro i hi
          change decide (i=l) = true at hi
          rw [of_decide_eq_true hi]
          exact hl
    · let m := n+n
      let one (p i : Fin n) := decide (i=p)
      let X (D : Set ((Fin n → Bool) × (Fin n → Bool))) : Set (Fin n) := {p | (one p, fun _ => false) ∈ D}
      let A (w : ℕ) := X (W w)
      let bad (i : ℕ) := i < s ∧ ∃ p r : Fin n, p ≠ r ∧ p ∈ A (m+i) ∧ r ∈ A (m+i) ∧
        ¬∃ u < m+i, ∃ v < m+i, A (m+i) = A u ∪ A v
      have ex : ∃ i, bad i := by simpa only [bad, A, X, one, m, if_true] using witness
      let i := Nat.find ex
      obtain ⟨hi, p, r, hpr, hp, hr, hn⟩ := Nat.find_spec ex
      obtain ⟨a,b,lower,law⟩ := steps i hi
      have ha : a < m+i := lt_of_le_of_lt (le_max_left _ _) lower
      have hb : b < m+i := lt_of_le_of_lt (le_max_right _ _) lower
      simp only [List.mem_cons,List.not_mem_nil,or_false] at law
      have meet : W (m+i) = W a ∩ W b := by
        rcases law with h | h | h | h
        · exact (hn ⟨a,ha,b,hb,congrArg X h⟩).elim
        · have eq : A (m+i) = A a := congrArg X h
          exact (hn ⟨a,ha,a,ha,by simpa only [Set.union_self] using eq⟩).elim
        · change (one p, fun _ => false) ∈ W (m+i) at hp
          rw [h] at hp
          exact hp.elim
        · exact h
      have ix : A (m+i) = A a ∩ A b := congrArg X meet
      have raw (v : Fin n) : A v.val = {v} := by
        ext u
        change (one u, fun _ => false) ∈ W v.val ↔ u = v
        rw [(inputs v).1]
        change decide (v = u) = true ↔ u = v
        exact ⟨fun h => (of_decide_eq_true h).symm, fun h => decide_eq_true h.symm⟩
      have third : ∃ t : Fin n, t ∈ A (m+i) ∧ t ≠ p ∧ t ≠ r := by
        by_contra none
        apply hn
        refine ⟨p.val, by dsimp [m]; omega, r.val, by dsimp [m]; omega, ?_⟩
        rw [raw p, raw r]
        ext z
        constructor
        · intro hz
          by_cases ep : z = p
          · exact Or.inl ep
          by_cases er : z = r
          · exact Or.inr er
          exact (none ⟨z,hz,ep,er⟩).elim
        · rintro (ep | er)
          · exact (show z = p from ep).symm ▸ hp
          · exact (show z = r from er).symm ▸ hr
      have leftOnly : ∃ u : Fin n, u ∈ A a ∧ u ∉ A b := by
        by_contra! all
        apply hn
        refine ⟨a,ha,a,ha,?_⟩
        rw [ix, Set.union_self]
        ext v
        exact ⟨fun h => h.1, fun h => ⟨h,all v h⟩⟩
      have rightOnly : ∃ v : Fin n, v ∈ A b ∧ v ∉ A a := by
        by_contra! all
        apply hn
        refine ⟨b,hb,b,hb,?_⟩
        rw [ix, Set.union_self]
        ext v
        exact ⟨fun h => h.2, fun h => ⟨all v h,h⟩⟩
      obtain ⟨t,hit,np,nr⟩ := third
      refine ⟨i,hi,a,ha,b,hb,meet,⟨p,r,t,hpr,np,nr,hp,hr,hit⟩,leftOnly,rightOnly,hn,?_⟩
      intro j hj u v ne hu hv
      by_contra no
      have earlier : bad j := ⟨hj.trans hi, u,v,ne,hu,hv,no⟩
      exact Nat.find_min ex hj earlier
  · have h3 := sizeBound q n I (by omega) order degrees unique s o W out inputs steps positive negative
    have hq : q ≤ 299 := by omega
    have scaled := Nat.mul_le_mul_left n hq
    have room : 100 ≤ n := by omega
    omega
