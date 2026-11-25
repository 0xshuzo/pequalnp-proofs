import Mathlib
import PEqualNP.Defs

namespace Exchange1593

def Indep {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

theorem no3 {n : ℕ} (G : SimpleGraph (Fin n)) (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (a b c : Fin n) (e0 : G.Adj a b) (e1 : G.Adj b c) (e2 : G.Adj c a) (n01 : a ≠ b) (n02 : a ≠ c) (n12 : b ≠ c) : False := by
  let W : G.Walk a a := SimpleGraph.Walk.cons e0 (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2 SimpleGraph.Walk.nil))
  have valid : W.IsCycle := by
    change (SimpleGraph.Walk.cons e0 _).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff,n01,n01.symm,n02,n02.symm,n12,n12.symm]
    · simp [Sym2.eq_iff,n01,n01.symm,n02,n02.symm,n12,n12.symm]
  have h := girth a W valid
  simp [W] at h

theorem no4 {n : ℕ} (G : SimpleGraph (Fin n)) (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (a b c d : Fin n) (e0 : G.Adj a b) (e1 : G.Adj b c) (e2 : G.Adj c d) (e3 : G.Adj d a) (n01 : a ≠ b) (n02 : a ≠ c) (n03 : a ≠ d) (n12 : b ≠ c) (n13 : b ≠ d) (n23 : c ≠ d) : False := by
  let W : G.Walk a a := SimpleGraph.Walk.cons e0 (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2 (SimpleGraph.Walk.cons e3 SimpleGraph.Walk.nil)))
  have valid : W.IsCycle := by
    change (SimpleGraph.Walk.cons e0 _).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n12,n12.symm,n13,n13.symm,n23,n23.symm]
    · simp [Sym2.eq_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n12,n12.symm,n13,n13.symm,n23,n23.symm]
  have h := girth a W valid
  simp [W] at h

theorem no5 {n : ℕ} (G : SimpleGraph (Fin n)) (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (a b c d e : Fin n) (e0 : G.Adj a b) (e1 : G.Adj b c) (e2 : G.Adj c d) (e3 : G.Adj d e) (e4 : G.Adj e a) (n01 : a ≠ b) (n02 : a ≠ c) (n03 : a ≠ d) (n04 : a ≠ e) (n12 : b ≠ c) (n13 : b ≠ d) (n14 : b ≠ e) (n23 : c ≠ d) (n24 : c ≠ e) (n34 : d ≠ e) : False := by
  let W : G.Walk a a := SimpleGraph.Walk.cons e0 (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2 (SimpleGraph.Walk.cons e3 (SimpleGraph.Walk.cons e4 SimpleGraph.Walk.nil))))
  have valid : W.IsCycle := by
    change (SimpleGraph.Walk.cons e0 _).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n04,n04.symm,n12,n12.symm,n13,n13.symm,n14,n14.symm,n23,n23.symm,n24,n24.symm,n34,n34.symm]
    · simp [Sym2.eq_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n04,n04.symm,n12,n12.symm,n13,n13.symm,n14,n14.symm,n23,n23.symm,n24,n24.symm,n34,n34.symm]
  have h := girth a W valid
  simp [W] at h

theorem badPair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : ∀ u (w : G.Walk u u), w.IsCycle → 7 ≤ w.length)
    (A B : Finset (Fin n) → Bool) (ma : Monotone A) (mb : Monotone B)
    (faithful : ∀ S : Finset (Fin n), S.card ≤ 3 →
       ((A S && B S) = true ↔ ∃ i∈S, ∃ j∈S,G.Adj i j))
    (u p q : Fin n) (degree : 3≤G.degree u) (blind : ∀ S,B (S.erase u) = B S)
    (wrong : A {p,q}=true) (non : ¬G.Adj p q) : u=p ∨ u=q := by
  classical
  by_contra! miss
  let N := G.neighborFinset u
  have forward (b : Fin n) (hb:b∈N) : G.Adj p b ∨ G.Adj q b := by
    have ub := (G.mem_neighborFinset u b).mp hb
    have sz : ({u,b}:Finset (Fin n)).card≤3 := by
      have h:=Finset.card_insert_le u ({b}:Finset (Fin n))
      simp only [Finset.card_singleton] at h
      omega
    have hot := (faithful {u,b} sz).mpr ⟨u,by simp,b,by simp,ub⟩
    have take := (blind {u,b}).trans (Bool.and_eq_true_iff.mp hot).2
    have b1 : B {b}=true := by simpa [ub.ne,ub.ne.symm] using take
    let T : Finset (Fin n) := insert b {p,q}
    have bas : {p,q} ⊆ T := Finset.subset_insert _ _
    have sin : {b} ⊆ T := Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
    have three : T.card≤3 := by
      have h1 := Finset.card_insert_le b ({p,q}:Finset (Fin n))
      have h2 := Finset.card_insert_le p ({q}:Finset (Fin n))
      simp only [Finset.card_singleton] at h2
      change (insert b {p,q}).card≤3
      omega
    obtain ⟨i,hi,j,hj,edge⟩ := (faithful T three).mp (Bool.and_eq_true_iff.mpr
      ⟨Bool.le_iff_imp.mp (ma bas) wrong,Bool.le_iff_imp.mp (mb sin) b1⟩)
    have ei : i=b ∨ i=p ∨ i=q := by simpa [T] using hi
    have ej : j=b ∨ j=p ∨ j=q := by simpa [T] using hj
    rcases ei with ei|ei|ei <;> rcases ej with ej|ej|ej <;> rw [ei,ej] at edge <;>
      first | exact False.elim (G.loopless.irrefl _ edge) | exact False.elim (non edge) |
        exact False.elim (non edge.symm) | exact Or.inl edge | exact Or.inr edge |
        exact Or.inl edge.symm | exact Or.inr edge.symm
  let K (v : Fin n) := N.filter (G.Adj v)
  have narrow (v : Fin n) (uv : u≠v) : (K v).card≤1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra ne
    obtain ⟨au,va⟩ := Finset.mem_filter.mp ha
    obtain ⟨bu,vb⟩ := Finset.mem_filter.mp hb
    have ua := (G.mem_neighborFinset u a).mp au
    have ub := (G.mem_neighborFinset u b).mp bu
    exact no4 G girth u a v b ua va.symm vb ub.symm ua.ne uv ub.ne va.ne.symm ne vb.ne
  have part : N⊆K p ∪ K q := by
    intro b hb
    rcases forward b hb with h|h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb,h⟩)
  have lim := (Finset.card_le_card part).trans (Finset.card_union_le (K p) (K q))
  have s1:=narrow p miss.1
  have s2:=narrow q miss.2
  have du : N.card=G.degree u := G.card_neighborFinset_eq_degree _
  omega

end Exchange1593
