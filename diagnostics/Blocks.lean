import Mathlib
import PEqualNP.Defs

namespace BlockRamsey5192

theorem fiber {α β : Type} [DecidableEq β] [Fintype β] (S : Finset α) (f : α → β)
    (t : ℕ) (large : Fintype.card β * t < S.card) :
    ∃ c, t < (S.filter fun x => f x = c).card := by
  classical
  by_contra contra
  push_neg at contra
  have count := Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ) (f := f)
    (fun x _ => Finset.mem_univ (f x))
  have bound := Finset.sum_le_sum (s := (Finset.univ : Finset β)) (g := fun _ => t)
    (fun i _ => contra i)
  rw [count] at large
  have eq : ∑ _i : β, t = Fintype.card β * t := by simp
  rw [eq] at bound
  omega

theorem endHomogeneous (β : Type) [DecidableEq β] [Fintype β] (k : ℕ) :
    ∃ N : ℕ, ∀ (α : Type) [DecidableEq α] (F : Finset α) (color : α → α → β), N ≤ F.card →
    ∃ (f : Fin k → α) (c : Fin k → β), Function.Injective f ∧ (∀ i, f i ∈ F) ∧
      ∀ i j : Fin k, i < j → color (f i) (f j) = c i := by
  induction k with
  | zero =>
    refine ⟨0,?_⟩
    intro α inst S color h
    exact ⟨Fin.elim0,Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨N,prev⟩ := ih
    refine ⟨Fintype.card β*N+2,?_⟩
    intro α inst F color enough
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < F.card by omega)
    have count := Finset.card_erase_of_mem ha
    obtain ⟨b,hb⟩ := fiber (F.erase a) (color a) N (by omega)
    let T := (F.erase a).filter (fun s => color a s = b)
    obtain ⟨f,c,inj,on,regular⟩ := prev α T color (by exact Nat.le_of_lt hb)
    have apart (i : Fin k) : f i ≠ a := (Finset.mem_erase.mp (Finset.mem_filter.mp (on i)).1).1
    have old (i : Fin k) : f i ∈ F := (Finset.mem_erase.mp (Finset.mem_filter.mp (on i)).1).2
    have link (i : Fin k) : color a (f i) = b := (Finset.mem_filter.mp (on i)).2
    refine ⟨Fin.cons a f,Fin.cons b c,?_,?_,?_⟩
    · intro i j he
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j => exact False.elim (apart j (show a=f j from he).symm)
      | succ i =>
        cases j using Fin.cases with
        | zero => exact False.elim (apart i he)
        | succ j => exact congrArg Fin.succ (inj he)
    · intro i
      cases i using Fin.cases with
      | zero => exact ha
      | succ i => exact old i
    · intro i j h
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact False.elim (lt_irrefl _ h)
        | succ j => exact link j
      | succ i =>
        cases j using Fin.cases with
        | zero => have no : ¬i.succ < 0 := Fin.not_lt_zero i.succ; contradiction
        | succ j => exact regular i j (Fin.succ_lt_succ_iff.mp h)

theorem homogeneous (β : Type) [DecidableEq β] [Fintype β] (k : ℕ) :
    ∃ N : ℕ, ∀ (α : Type) [DecidableEq α] (F : Finset α) (color : α → α → β), N ≤ F.card →
    ∃ (f : Fin k → α) (b : β), Function.Injective f ∧ (∀ i, f i ∈ F) ∧
      ∀ i j : Fin k, i < j → color (f i) (f j) = b := by
  let d := Fintype.card β*k+1
  obtain ⟨N,first⟩ := endHomogeneous β d
  refine ⟨N,?_⟩
  intro α inst F color enough
  obtain ⟨f,c,inj,mem,links⟩ := first α F color enough
  have large : Fintype.card β*k < (Finset.univ : Finset (Fin d)).card := by simp [d]
  obtain ⟨b,card⟩ := fiber Finset.univ c k large
  obtain ⟨U,sub,sz⟩ := Finset.exists_subset_card_eq (le_of_lt card)
  let idx := U.orderEmbOfFin sz
  refine ⟨fun i => f (idx i),b,inj.comp idx.injective,fun i => mem _,?_⟩
  intro i j lt
  exact (links _ _ (idx.strictMono lt)).trans
    (Finset.mem_filter.mp (sub (Finset.orderEmbOfFin_mem _ _ i))).2

lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
  have h5 := hg a _ hcyc
  simp at h5


theorem blocks : ∀ k : ℕ, ∃ r : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ t (w : G.Walk t t), w.IsCycle → 5 ≤ w.length) →
      ∀ (u v : Fin n) (F : Finset (Fin n × Fin n)), G.Adj u v → r ≤ F.card →
      (∀ p ∈ F, ¬ G.Adj p.1 p.2) →
      (let E := fun p : Fin n × Fin n => ({p.1,p.2} : Finset (Fin n)) \ {u,v}
       ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (E p) (E q)) →
      ∃ (b : Finset (Fin n)) (B : Fin k → Finset (Fin n)), b ⊆ {u,v} ∧ b.card ≤ 1 ∧
      (∀ i, (B i).Nonempty ∧ (B i).card ≤ 2 ∧ Disjoint (B i) {u,v}) ∧
      Pairwise (fun i h => Disjoint (B i) (B h)) ∧
      (∀ i, ∃ p ∈ F, p.1 ∈ b ∪ B i ∧ p.2 ∈ b ∪ B i) ∧ (∀ p ∈ b ∪ Finset.univ.biUnion B, ∀ q ∈ b ∪ Finset.univ.biUnion B, ¬ G.Adj p q) := by
  intro k
  let palette := (Bool → Bool) × (Bool → Bool → Bool)
  let d := k+5
  obtain ⟨N,ramsey⟩ := homogeneous palette d
  refine ⟨N+4,?_⟩
  intro n G girth u v F uv large ok disj
  classical
  let A : Finset (Fin n) := {u,v}
  let occ (p : Fin n × Fin n) : Finset (Fin n) := {p.1,p.2}
  let rem (p : Fin n × Fin n) := occ p \ A
  let good := F \ (A ×ˢ A)
  have a2 : A.card ≤ 2 := by
    have hh := Finset.card_insert_le u ({v} : Finset (Fin n))
    simpa [A] using hh
  have prod4 : (A ×ˢ A).card ≤ 4 := by
    rw [Finset.card_product]
    exact Nat.mul_le_mul a2 a2
  have comp : F ⊆ good ∪ (A ×ˢ A) := by
    intro p hp
    by_cases h : p ∈ A ×ˢ A
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp,h⟩)
  have ngood : N ≤ good.card := by
    have hs := (Finset.card_le_card comp).trans (Finset.card_union_le good (A ×ˢ A))
    omega
  let co (p : Fin n × Fin n) (t : Bool) :=
    if p.1 ∈ A then p.2 else if p.2 ∈ A then p.1 else if t then p.1 else p.2
  have free {p : Fin n × Fin n} (hp : p ∈ good) : ¬ (p.1 ∈ A ∧ p.2 ∈ A) :=
    fun h => (Finset.mem_sdiff.mp hp).2 (Finset.mem_product.mpr h)
  have cmem {p : Fin n × Fin n} (hp : p ∈ good) (t : Bool) : co p t ∈ rem p := by
    have h := free hp
    by_cases a : p.1 ∈ A <;> by_cases b : p.2 ∈ A <;> cases t <;>
      simp [co,rem,occ,a,b] at h ⊢
  have exhausted {p : Fin n × Fin n} {w : Fin n} (hw : w ∈ rem p) :
      ∃ t, w = co p t := by
    obtain ⟨mem,off⟩ := Finset.mem_sdiff.mp hw
    rcases (by simpa [occ] using mem : w = p.1 ∨ w = p.2) with rfl | rfl
    · exact ⟨true,by simp [co,off]⟩
    · exact ⟨false,by by_cases h : p.1 ∈ A <;> simp [co,h,off]⟩
  let tag (p : Fin n × Fin n) (t : Bool) := decide ((if t then u else v) ∈ occ p)
  let col (p q : Fin n × Fin n) : palette :=
    (tag p,fun x y => decide (G.Adj (co p x) (co q y)))
  obtain ⟨f,hue,inj,sel,hmono⟩ := ramsey _ good col ngood
  have old (i : Fin d) : f i ∈ F := (Finset.mem_sdiff.mp (sel i)).1
  have unequal {i j : Fin d} (ne : i ≠ j) (x y : Bool) : co (f i) x ≠ co (f j) y := by
    intro h
    exact Finset.disjoint_left.mp (disj _ (old i) _ (old j) (fun he => ne (inj he)))
      (cmem (sel i) x) (h.symm ▸ cmem (sel j) y)
  have matrix {i j : Fin d} (lt : i < j) (x y : Bool) :
      decide (G.Adj (co (f i) x) (co (f j) y)) = hue.2 x y :=
    congrArg (fun z : palette => z.2 x y) (hmono i j lt)
  have dark (x y : Bool) : hue.2 x y = false := by
    cases h : hue.2 x y with
    | false => rfl
    | true =>
      let z0 : Fin d := ⟨0,by dsimp [d]; omega⟩
      let z1 : Fin d := ⟨1,by dsimp [d]; omega⟩
      let z2 : Fin d := ⟨2,by dsimp [d]; omega⟩
      let z3 : Fin d := ⟨3,by dsimp [d]; omega⟩
      have edge {i j : Fin d} (lt : i < j) : G.Adj (co (f i) x) (co (f j) y) :=
        of_decide_eq_true ((matrix lt x y).trans h)
      have e02 := edge (show z0 < z2 by change 0 < 2; decide)
      have e12 := edge (show z1 < z2 by change 1 < 2; decide)
      have e13 := edge (show z1 < z3 by change 1 < 3; decide)
      have e03 := edge (show z0 < z3 by change 0 < 3; decide)
      exact False.elim (no4 G girth _ _ _ _ e02 e12.symm e13 e03.symm
        (unequal (show z0 ≠ z1 by intro hh; have := congrArg Fin.val hh; change 0=1 at this; omega) x x)
        (unequal (show z2 ≠ z3 by intro hh; have := congrArg Fin.val hh; change 2=3 at this; omega) y y))
  have crossed {i j : Fin d} (ne : i ≠ j) {a c : Fin n}
      (ha : a ∈ rem (f i)) (hc : c ∈ rem (f j)) : ¬ G.Adj a c := by
    obtain ⟨x,rfl⟩ := exhausted ha
    obtain ⟨y,rfl⟩ := exhausted hc
    rcases lt_or_gt_of_ne ne with h|h
    · exact of_decide_eq_false ((matrix h x y).trans (dark x y))
    · exact fun e => (of_decide_eq_false ((matrix h y x).trans (dark y x))) e.symm
  let last : Fin d := ⟨k+4,by dsimp [d]; omega⟩
  let start : Fin d := ⟨0,by dsimp [d]; omega⟩
  let atI (i : Fin k) : Fin d := ⟨i.val,by have := i.isLt; dsimp [d]; omega⟩
  have pre (i : Fin k) : atI i < last := by change i.val < k+4; have := i.isLt; omega
  have initial : start < last := by change 0 < k+4; omega
  have tags {i : Fin d} (lt : i<last) (t : Bool) : tag (f i) t = tag (f start) t :=
    (congrArg (fun z : palette => z.1 t) (hmono i last lt)).trans
      (congrArg (fun z : palette => z.1 t) (hmono start last initial)).symm
  have independent (i : Fin d) {p q : Fin n} (hp : p ∈ occ (f i)) (hq : q ∈ occ (f i)) :
      ¬ G.Adj p q := by
    have h := ok _ (old i)
    rcases (by simpa [occ] using hp : p=(f i).1 ∨ p=(f i).2) with rfl|rfl <;>
      rcases (by simpa [occ] using hq : q=(f i).1 ∨ q=(f i).2) with rfl|rfl
    · exact G.loopless.irrefl _
    · exact h
    · exact fun e => h e.symm
    · exact G.loopless.irrefl _
  let b := (occ (f start)) ∩ A
  let B (i : Fin k) := rem (f (atI i))
  have bp : b ⊆ A := Finset.inter_subset_right
  have bo : b ⊆ occ (f start) := Finset.inter_subset_left
  have small : b.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    rcases (by simpa [A] using bp hp : p=u ∨ p=v) with rfl|rfl <;>
      rcases (by simpa [A] using bp hq : q=u ∨ q=v) with rfl|rfl
    · rfl
    · exact False.elim (independent start (bo hp) (bo hq) uv)
    · exact False.elim (independent start (bo hq) (bo hp) uv)
    · rfl
  have agree (i : Fin k) {x : Fin n} (h : x ∈ A) : x ∈ occ (f (atI i)) ↔ x ∈ occ (f start) := by
    rcases (by simpa [A] using h : x=u ∨ x=v) with rfl|rfl
    · have := tags (pre i) true
      simpa [tag] using (Bool.eq_iff_iff.mp this)
    · have := tags (pre i) false
      simpa [tag] using (Bool.eq_iff_iff.mp this)
  have union (i : Fin k) : b ∪ B i = occ (f (atI i)) := by
    ext x
    by_cases h : x ∈ A
    · simp [b,B,rem,h,agree i h]
    · simp [b,B,rem,h]
  refine ⟨b,B,bp,small,?_,?_,?_,?_⟩
  · intro i
    have lim : (occ (f (atI i))).card ≤ 2 := by
      have hh := Finset.card_insert_le (f (atI i)).1 ({(f (atI i)).2} : Finset (Fin n))
      simpa only [Finset.card_singleton] using hh
    exact ⟨⟨_,cmem (sel (atI i)) true⟩,(Finset.card_le_card Finset.sdiff_subset).trans lim,
      Finset.disjoint_left.mpr (fun x hx => (Finset.mem_sdiff.mp hx).2)⟩
  · intro i j neq
    apply disj _ (old (atI i)) _ (old (atI j))
    intro hh
    exact neq (Fin.ext (congrArg (fun v : Fin d => v.val) (inj hh)))
  · intro i
    refine ⟨f (atI i),old _,?_,?_⟩ <;> rw [union] <;> simp [occ]
  · intro p hp q hq
    have one {i : Fin k} {p q : Fin n} (hp : p ∈ b ∪ B i) (hq : q ∈ b ∪ B i) : ¬ G.Adj p q :=
      independent (atI i) (union i ▸ hp) (union i ▸ hq)
    rcases Finset.mem_union.mp hp with pbase | pvar
    · rcases Finset.mem_union.mp hq with qbase | qvar
      · exact independent start (bo pbase) (bo qbase)
      · obtain ⟨i,_,hq⟩ := Finset.mem_biUnion.mp qvar
        exact one (Finset.mem_union_left _ pbase) (Finset.mem_union_right _ hq)
    · obtain ⟨i,_,hp⟩ := Finset.mem_biUnion.mp pvar
      rcases Finset.mem_union.mp hq with qbase | qvar
      · exact one (Finset.mem_union_right _ hp) (Finset.mem_union_left _ qbase)
      · obtain ⟨j,_,hq⟩ := Finset.mem_biUnion.mp qvar
        by_cases eq : i=j
        · subst j; exact one (Finset.mem_union_right _ hp) (Finset.mem_union_right _ hq)
        · exact crossed (fun e => eq (Fin.ext (congrArg (fun x : Fin d => x.val) e))) hp hq

end BlockRamsey5192
