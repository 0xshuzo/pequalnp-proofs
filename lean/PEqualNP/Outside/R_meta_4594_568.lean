import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CrossAnd PEqualNP.GenericRejection

set_option maxHeartbeats 700000 in
theorem PEqualNP.Outside.R_meta_4594_568
    (kill : ∀ (n : ℕ) (M : Finset (Fin n)) (C : Circuit) (j : ℕ),
      Monotone2 C → j < C.size → IsCrossAnd n M C j →
      let D : Circuit := ⟨C.gates.set j ⟨GateOp.or,[]⟩,C.output⟩
      Monotone2 D ∧ D.size = C.size ∧ crossCount n M D < crossCount n M C ∧
      ∀ x : List Bool, x.length = n → D.eval x = true → C.eval x = true)
    (repair : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (D : Circuit)
      (F : Finset (Fin n × Fin n)) (P L : Finset (Fin n)),
      let count := crossCount (n+n) (Finset.map (Fin.natAddEmb n) Finset.univ)
      Monotone2 D →
      (∀ X Y : Finset (Fin n), D.eval (incidenceInput X Y) = true → incidenceFun S X Y = true) →
      (∀ l (p : Fin n), p ∈ S l → D.eval (incidenceInput {p} {l}) = true ∨ (p,l) ∈ F) →
      (∀ e ∈ F, e.1 ∈ S e.2) →
      (∀ e ∈ F, e.1 ∈ P ∨ e.2 ∈ L) →
      ∃ B : Circuit, Monotone2 B ∧ ComputesIncidence S B ∧ count B ≤ count D ∧
        B.size ≤ D.size + F.card + P.card + L.card)
    (costly : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      let M := Finset.map (Fin.natAddEmb n) Finset.univ
      let count := crossCount (n+n) M
      let lost := fun j : ℕ => (Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
        e.1 ∈ S e.2 ∧ (Circuit.mk (C.gates.set j ⟨GateOp.or,[]⟩) C.output).eval
          (incidenceInput {e.1} {e.2}) = false)
      199 ≤ q → n = q^2+q+1 → (∀ l, (S l).card=q+1) →
      (∀ l k, l ≠ k → (S l ∩ S k).card ≤ 1) →
      Monotone2 C → ComputesIncidence S C → 2*C.size < n*q → 0 < count C →
      (∀ j < C.size, IsCrossAnd (n+n) M C j → ∀ P L : Finset (Fin n),
        (∀ e ∈ lost j, e.1 ∈ P ∨ e.2 ∈ L) → 50 ≤ (lost j).card + P.card + L.card) →
      ∃ B : Circuit, Monotone2 B ∧ ComputesIncidence S B ∧ count B < count C ∧ B.size ≤ C.size+49) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (199 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → (x3 x8 ∩ x3 x9).card ≤ (1 : ℕ)) →           PEqualNP.MetaComplexity.Monotone2 x4 →             PEqualNP.GenericRejection.ComputesIncidence x3 x4 →               have x11 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := PEqualNP.CrossAnd.crossCount (x2 + x2) (Finset.map (Fin.natAddEmb x2) Finset.univ);               (2 : ℕ) * x4.size < x2 * x1 → (0 : ℕ) < x11 x4 → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ PEqualNP.GenericRejection.ComputesIncidence x3 x14 ∧ x11 x14 < x11 x4 ∧ x14.size ≤ x4.size + (49 : ℕ) := by
  classical
  intro q n S C hq hn hl hmeet hm hfun
  dsimp only
  intro short pos
  by_contra none
  apply none
  apply costly q n S C hq hn hl hmeet hm hfun short pos
  intro j hj cross P L cover
  by_contra! cheap
  let D : Circuit := ⟨C.gates.set j ⟨GateOp.or,[]⟩,C.output⟩
  let F := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
    e.1 ∈ S e.2 ∧ D.eval (incidenceInput {e.1} {e.2}) = false)
  obtain ⟨dm,sz,cc,safe⟩ := kill (n+n) _ C j hm hj cross
  have under (X Y : Finset (Fin n)) (h : D.eval (incidenceInput X Y) = true) : incidenceFun S X Y = true := by
    rw [← hfun X Y]
    apply safe _ _ h
    change ((List.ofFn (fun p : Fin n => decide (p ∈ X))) ++
      (List.ofFn (fun l : Fin n => decide (l ∈ Y)))).length = n+n
    rw [List.length_append,List.length_ofFn,List.length_ofFn]
  have captured (l p : Fin n) (hp : p ∈ S l) :
      D.eval (incidenceInput {p} {l}) = true ∨ (p,l) ∈ F := by
    cases read : D.eval (incidenceInput {p} {l}) with
    | true => exact Or.inl rfl
    | false => exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,read⟩)
  have incident (e : Fin n × Fin n) (he : e ∈ F) : e.1 ∈ S e.2 := (Finset.mem_filter.mp he).2.1
  obtain ⟨B,bm,bf,count,size⟩ := repair n S D F P L dm under captured incident cover
  change D.size = C.size at sz
  change F.card + P.card + L.card < 50 at cheap
  exact none ⟨B,bm,bf,lt_of_le_of_lt count cc,by omega⟩
