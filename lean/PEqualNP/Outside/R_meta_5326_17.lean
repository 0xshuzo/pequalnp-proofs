import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 14000 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_5326_17
    (orient : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → 5 ≤ p.length) → IsLeastAO G C →
      let A := fun w : ℕ => Finset.univ.filter (fun u : Fin n => wireVal n C w (pairInput u u)=true)
      NoFourCycle G ∧ ∀ j∈tops G C,
        (∀ u∈A (opnd C j 0), ∀ v∈A (opnd C j 1), G.Adj u v) ∧ ((A (opnd C j 0)).card ≤ 1 ∨ (A (opnd C j 1)).card ≤ 1))
    (trace : ∀ (n : ℕ) (C : Circuit), IsAO2 n C →
      let A := fun w : ℕ => Finset.univ.filter (fun u : Fin n => wireVal n C w (pairInput u u)=true)
      ∀ (w : ℕ) (v : Fin n), v∈A w → A w={v} ∨
        (∃ j<C.size, ∃ b : Fin 2, 2≤(A (n+j)).card ∧ A (n+j)⊆A w ∧ A (opnd C j b)={v}) ∨
        ∃ j<C.size, (gateAt C j).op=GateOp.and ∧ OrReaches n C w j ∧ 2≤(A (n+j)).card ∧ v∈A (n+j))
    (price : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      ∀ (A : ℕ → Finset (Fin n)) (E : Finset (Sym2 (Fin n))), NoFourCycle G →
      (∀ e∈E, (∃ j<C.size, ∃ u v : Fin n, e=s(u,v) ∧ A (opnd C j 0)={u} ∧ A (opnd C j 1)={v}) ∨ (∃ j<C.size, ∃ b : Fin 2, ∃ c v : Fin n, e=s(c,v) ∧ 2≤(A (n+j)).card ∧
            (∀ z∈A (n+j), G.Adj c z) ∧ A (opnd C j b)={v})) → E.card ≤ 3*C.size)
    (hard : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → 5 ≤ p.length) → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      let A := fun w : ℕ => Finset.univ.filter (fun u : Fin n => wireVal n C w (pairInput u u)=true)
      ((Ustar G C).filter (fun e : Sym2 (Fin n) => ∃ c v : Fin n, e=s(c,v) ∧
        ∃ a∈tops G C, ∃ b : Fin 2, A (opnd C a (1-b))={c} ∧
        ∃ j∈junk G C, OrReaches n C (opnd C a b) j ∧ 2≤(A (n+j)).card ∧ v∈A (n+j))).card ≤ k*(C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, PEqualNP.CleanedNonEdge.wireVal x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.true ∧ PEqualNP.CleanedNonEdge.wireVal x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  letI := gateOpDecEq
  obtain ⟨k,hk⟩ := hard
  refine ⟨k+3,?_⟩
  intro n G inst C hg hm ht
  let A := fun w : ℕ => Finset.univ.filter (fun u : Fin n => wireVal n C w (pairInput u u)=true)
  let good := fun e : Sym2 (Fin n) => ∃ u v : Fin n, e=s(u,v) ∧ ∃a∈tops G C, u∈A (opnd C a 0) ∧ v∈A (opnd C a 1)
  let bad := fun e : Sym2 (Fin n) => ∃ c v : Fin n, e=s(c,v) ∧
        ∃ a∈tops G C, ∃ b : Fin 2, A (opnd C a (1-b))={c} ∧
        ∃ j∈junk G C, OrReaches n C (opnd C a b) j ∧ 2≤(A (n+j)).card ∧ v∈A (n+j)
  let T := (Ustar G C).filter good
  let D := (Ustar G C).filter bad
  have hD : D.card ≤ k*(C.size+1) := hk n G C hg hm ht
  have no_self_graphFun : ∀ u : Fin n, graphFun G ∅ (pairInput u u) = false := by
    intro u
    rw [Bool.eq_false_iff]
    intro h
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), pairInput u u a = true) ||
      decide (∃ a b : Fin n, G.Adj a b ∧ pairInput u u a = true ∧ pairInput u u b = true)) = true at h
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    rcases h with ⟨a, ha, _⟩ | ⟨a, b, hab, ha, hb⟩
    · exact (Finset.notMem_empty a ha).elim
    · change decide (a = u ∨ a = u) = true at ha
      change decide (b = u ∨ b = u) = true at hb
      rw [decide_eq_true_eq] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact G.irrefl hab
  obtain ⟨free,stars⟩ := orient n G C hg hm
  have hsmall : (T \ D).card ≤ 3*C.size := by
    apply price n G C A _ free
    intro e he
    obtain ⟨hT,out⟩ := Finset.mem_sdiff.mp he
    obtain ⟨hu, u,v,eq,a,ha,uv,vv⟩ := Finset.mem_filter.mp hT
    have small (w : ℕ) (x : Fin n) (hx : x∈A w) (lo : (A w).card ≤ 1) : A w={x} := by
      apply Finset.Subset.antisymm
      · intro y hy
        exact Finset.mem_singleton.mpr (Finset.card_le_one.mp lo y hy x hx)
      · exact Finset.singleton_subset_iff.mpr hx
    have bounded : a<C.size := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    obtain ⟨adj,casesA⟩ := stars a ha
    have handle (b : Fin 2) (c z : Fin n) (eqE : e=s(c,z)) (cent : A (opnd C a (1-b))={c})
        (hit : z∈A (opnd C a b)) (neigh : ∀ t∈A (opnd C a b), G.Adj c t) :
        A (opnd C a b)={z} ∨ (∃ j<C.size, ∃ b : Fin 2, ∃ c v : Fin n, e=s(c,v) ∧ 2≤(A (n+j)).card ∧
            (∀ z∈A (n+j), G.Adj c z) ∧ A (opnd C j b)={v}) := by
      rcases trace n C hm.1 (opnd C a b) z hit with one|⟨j,hj,p,many,sub,single⟩|⟨j,hj,op,path,many,active⟩
      · exact Or.inl one
      · exact Or.inr ⟨j,hj,p,c,z,eqE,many,fun t h => neigh t (sub h),single⟩
      · have marks : gateVal n C j (pairInput z z)=true := (Finset.mem_filter.mp active).2
        have dirty : j∈junk G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,op,hj,pairInput z z,marks,no_self_graphFun z⟩
        exact False.elim (out (Finset.mem_filter.mpr ⟨hu,c,z,eqE,a,ha,b,cent,j,dirty,path,many,active⟩))
    rcases casesA with left|right
    · have cent := small _ _ uv left
      rcases handle 1 u v eq cent vv (fun t th => adj u uv t th) with one|h
      · exact Or.inl ⟨a,bounded,u,v,eq,cent,one⟩
      · exact Or.inr h
    · have cent := small _ _ vv right
      have sw : e=s(v,u) := eq.trans Sym2.eq_swap
      rcases handle 0 v u sw cent uv (fun t th => (adj t th v vv).symm) with one|h
      · exact Or.inl ⟨a,bounded,u,v,eq,one,cent⟩
      · exact Or.inr h
  have split : T.card ≤ (T \ D).card + D.card := by
    have part := Finset.card_sdiff_add_card_inter T D
    have le : (T ∩ D).card ≤ D.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have bound : T.card ≤ (k+3)*(C.size+1) := by
    rw [Nat.add_mul]
    omega
  have same : ((Ustar G C).filter (fun e => ∃ u v : Fin n, e=s(u,v) ∧ ∃ a∈tops G C,
        wireVal n C (opnd C a 0) (pairInput u u)=true ∧ wireVal n C (opnd C a 1) (pairInput v v)=true)) = T := by
    apply Finset.ext
    intro e
    constructor
    · intro he
      obtain ⟨hu,u,v,eq,a,ha,left,right⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨hu,u,v,eq,a,ha,Finset.mem_filter.mpr ⟨Finset.mem_univ _,left⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,right⟩⟩
    · intro he
      obtain ⟨hu,u,v,eq,a,ha,left,right⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨hu,u,v,eq,a,ha,(Finset.mem_filter.mp left).2,(Finset.mem_filter.mp right).2⟩
  rw [same]
  exact bound
