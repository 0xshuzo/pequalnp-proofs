import Mathlib
import PEqualNP.Defs

namespace Pilot4765

-- Bound the number of geometrically distinct lines seen by an OR of two rectangle covers.
theorem rectangleCount (n u v : ℕ) (I : Fin n → Fin n → Prop)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (good : Set (Fin n)) (A B : Fin u → Set (Fin n)) (C D : Fin v → Set (Fin n))
    (active : ∀ l ∈ good, ∃ i j, l∈B i ∧ l∈D j ∧
      ∃ p∈A i, ∃ r∈C j, p≠r)
    (soundA : ∀ l∈good, ∀ i, l∈B i → ∀ p∈A i, I p l)
    (soundC : ∀ l∈good, ∀ j, l∈D j → ∀ r∈C j, I r l) :
    good.ncard ≤ u*v := by
  classical
  have tags (l : good) : ∃ t : Fin u × Fin v, l.val∈B t.1 ∧ l.val∈D t.2 ∧
      ∃ p∈A t.1, ∃ r∈C t.2, p≠r := by
    obtain ⟨i,j,h⟩ := active l.val l.property
    exact ⟨(i,j),h⟩
  choose tag cert using tags
  have inj : Function.Injective tag := by
    intro l k eq
    obtain ⟨lb,ld,p,pa,r,rc,diff⟩ := cert l
    have kb := (cert k).1
    have kd := (cert k).2.1
    rw [←eq] at kb kd
    exact Subtype.ext ((join p r diff).unique
      ⟨soundA l.val l.property _ lb p pa,soundC l.val l.property _ ld r rc⟩
      ⟨soundA k.val k.property _ kb p pa,soundC k.val k.property _ kd r rc⟩)
  have bound := Fintype.card_le_of_injective tag inj
  simpa only [Set.fintypeCard_eq_ncard,Fintype.card_prod,Fintype.card_fin] using bound

theorem paidUnion (n u v a b w : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I]
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool))) (ha : a < w) (hb : b < w)
    (law : W w = W a ∪ W b)
    (A B : Fin u → Set (Fin n)) (C D : Fin v → Set (Fin n)) :
    let one (p i : Fin n) := decide (i=p)
    let anti (l : Fin n) := fun p => decide (¬I p l)
    let F (l : Fin n) (k : ℕ) := {p : Fin n | I p l ∧
      (one p,one l)∈W k ∧ (anti l,one l)∉W k}
    (∀ p l, ¬I p l → (one p,one l)∈W w → (anti l,one l)∈W w) →
    (∀ p l, (one p,one l)∈W a ↔ ∃ i, p∈A i ∧ l∈B i) →
    (∀ p l, (one p,one l)∈W b ↔ ∃ j, p∈C j ∧ l∈D j) →
    {l : Fin n | ∀ k < w, ¬F l w ⊆ F l k}.ncard ≤ u*v := by
  classical
  intro one anti F mono left right
  let good : Set (Fin n) := {l | ∀ k < w, ¬F l w ⊆ F l k}
  have split (l : Fin n) (hl : l∈good) :
      (anti l,one l)∉W w ∧ ∃ p r, p≠r ∧ (one p,one l)∈W a ∧ (one r,one l)∈W b := by
    have miss (k : ℕ) (hk : k < w) : ∃ p, p∈F l w ∧ p∉F l k := by
      by_contra! sub
      exact hl k hk sub
    obtain ⟨p,hp,np⟩ := miss b hb
    obtain ⟨r,hr,nr⟩ := miss a ha
    obtain ⟨ip,yp,safe⟩ := hp
    obtain ⟨ir,yr,_⟩ := hr
    refine ⟨safe,?_⟩
    rw [law] at yp yr safe
    have pb : (one p,one l)∉W b := fun h => np ⟨ip,h,fun t => safe (Or.inr t)⟩
    have ra : (one r,one l)∉W a := fun h => nr ⟨ir,h,fun t => safe (Or.inl t)⟩
    have pa := yp.resolve_right pb
    have rb := yr.resolve_left ra
    exact ⟨p,r,fun h => pb (by simpa only [h] using rb),pa,rb⟩
  apply rectangleCount n u v I join good A B C D
  · intro l hl
    obtain ⟨_,p,r,ne,pa,rb⟩ := split l hl
    obtain ⟨i,hp,hl₁⟩ := (left p l).mp pa
    obtain ⟨j,hr,hl₂⟩ := (right r l).mp rb
    exact ⟨i,j,hl₁,hl₂,p,hp,r,hr,ne⟩
  · intro l hl i lb p pa
    by_contra h
    apply (split l hl).1 (mono p l h ?_)
    rw [law]
    exact Or.inl ((left p l).mpr ⟨i,pa,lb⟩)
  · intro l hl j ld r rc
    by_contra h
    apply (split l hl).1 (mono r l h ?_)
    rw [law]
    exact Or.inr ((right r l).mpr ⟨j,rc,ld⟩)



theorem forceOR {X P L : Type*}
    (I : P → L → Prop) (pos : P → L → X) (neg : L → X)
    (W : ℕ → Set X) (w a b : ℕ) (ha : a < w) (hb : b < w)
    (rule : W w ∈ [W a ∪ W b,W a,∅,W a ∩ W b]) :
    let F (l : L) (k : ℕ) := {p : P | I p l ∧ pos p l ∈ W k ∧ neg l ∉ W k}
    ∀ l, (∀ k < w, ¬F l w ⊆ F l k) → W w = W a ∪ W b := by
  classical
  intro F l novel
  simp only [List.mem_cons,List.not_mem_nil,or_false] at rule
  rcases rule with union | copy | zero | inter
  · exact union
  · exfalso
    apply novel a ha
    intro p hp
    obtain ⟨inc,yes,no⟩ := hp
    rw [copy] at yes no
    exact ⟨inc,yes,no⟩
  · exfalso
    apply novel a ha
    intro p hp
    have yes := hp.2.1
    rw [zero] at yes
    exact False.elim yes
  · exfalso
    by_cases safe : neg l ∉ W a
    · apply novel a ha
      intro p hp
      have yes := hp.2.1
      rw [inter] at yes
      exact ⟨hp.1,yes.1,safe⟩
    · apply novel b hb
      intro p hp
      obtain ⟨inc,yes,no⟩ := hp
      rw [inter] at yes no
      exact ⟨inc,yes.2,fun h => no ⟨not_not.mp safe,h⟩⟩

theorem sectionSound (n s : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I]
    (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool)))
    (raw : ∀ p : Fin n, W p.val = {z | z.1 p = true} ∧ W (n+p.val) = {z | z.2 p = true})
    (steps : ∀ j < s, ∃ a b, max a b < n+n+j ∧ W (n+n+j) ∈ [W a ∪ W b,W a,∅,W a ∩ W b]) :
    let one (p i : Fin n) := decide (i=p)
    ∀ w < n+n+s, ∀ p l, ¬I p l → (one p,one l)∈W w →
      ((fun i => decide (¬I i l)),one l)∈W w := by
  classical
  intro one w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw p l noninc yes
    by_cases h₁ : w < n
    · let i : Fin n := ⟨w,h₁⟩
      have eq : W w = {z | z.1 i = true} := (raw i).1
      rw [eq] at yes ⊢
      change decide (i=p) = true at yes
      change decide (¬I i l) = true
      rw [of_decide_eq_true yes]
      exact decide_eq_true noninc
    · by_cases h₂ : w < n+n
      · let i : Fin n := ⟨w-n,by omega⟩
        have eq : w=n+i.val := by dsimp [i]; omega
        rw [eq,(raw i).2] at yes ⊢
        exact yes
      · let j := w-(n+n)
        have eq : n+n+j=w := by dsimp [j]; omega
        obtain ⟨a,b,lower,law⟩ := steps j (by omega)
        rw [eq] at lower law
        have ha := lt_of_le_of_lt (le_max_left a b) lower
        have hb := lt_of_le_of_lt (le_max_right a b) lower
        have ma := ih a ha (by omega) p l noninc
        have mb := ih b hb (by omega) p l noninc
        simp only [List.mem_cons,List.not_mem_nil,or_false] at law
        rcases law with u | c | e | both
        · rw [u] at yes ⊢
          exact yes.elim (fun h => Or.inl (ma h)) (fun h => Or.inr (mb h))
        · rw [c] at yes ⊢
          exact ma yes
        · rw [e] at yes
          exact False.elim yes
        · rw [both] at yes ⊢
          exact ⟨ma yes.1,mb yes.2⟩


theorem boundedWidth (n s : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I]
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool)))
    (raw : ∀ p : Fin n, W p.val = {z | z.1 p = true} ∧ W (n+p.val) = {z | z.2 p = true})
    (steps : ∀ j < s, ∃ a b, max a b < n+n+j ∧ W (n+n+j) ∈ [W a ∪ W b,W a,∅,W a ∩ W b]) :
    let one (p i : Fin n) := decide (i=p)
    let anti (l : Fin n) := fun p => decide (¬I p l)
    let F (l : Fin n) (k : ℕ) := {p : Fin n | I p l ∧
      (one p,one l)∈W k ∧ (anti l,one l)∉W k}
    (∀ j < s, ∀ a b, max a b < n+n+j → W (n+n+j) = W a ∪ W b →
      ∃ u v, u*v≤100 ∧ ∃ (A B : Fin u → Set (Fin n)) (C D : Fin v → Set (Fin n)),
        (∀ p l, (one p,one l)∈W a ↔ ∃ i, p∈A i ∧ l∈B i) ∧
        (∀ p l, (one p,one l)∈W b ↔ ∃ i, p∈C i ∧ l∈D i)) →
    ∀ j < s, {l : Fin n | ∀ k < n+n+j, ¬F l (n+n+j) ⊆ F l k}.ncard ≤ 100 := by
  classical
  intro one anti F width j hj
  let w := n+n+j
  obtain ⟨a,b,lower,rule⟩ := steps j hj
  have ha : a < w := lt_of_le_of_lt (le_max_left _ _) lower
  have hb : b < w := lt_of_le_of_lt (le_max_right _ _) lower
  by_cases union : W w = W a ∪ W b
  · obtain ⟨u,v,price,A,B,C,D,left,right⟩ := width j hj a b lower union
    have mono := sectionSound n s I W raw steps w (by dsimp [w]; omega)
    apply (paidUnion n u v a b w I join W ha hb union A B C D mono left right).trans price
  · have empty : {l : Fin n | ∀ k < w, ¬F l w ⊆ F l k} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro l hl
      exact union (forceOR I (fun p l => (one p,one l)) (fun l => (anti l,one l))
        W w a b ha hb rule l hl)
    change ({l : Fin n | ∀ k < w, ¬F l w ⊆ F l k} : Set (Fin n)).ncard ≤ 100
    simp [empty]

end Pilot4765
