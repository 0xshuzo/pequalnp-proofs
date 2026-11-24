import Mathlib
import PEqualNP.Defs

namespace Pilot4765

theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

theorem matrix : ∀ (n m s o q : ℕ) (F : Fin n → ℕ → Set (Fin n)), o < m+s →
      (∀ l k, k<m → (F l k).ncard ≤ 1) →
      (∀ l j, j<s → ∃ a b, max a b<m+j ∧ F l (m+j) ⊆ F l a ∪ F l b) →
      (∀ l, q+1 ≤ (F l o).ncard) →
      n*q ≤ 100*s ∨ ∃ j<s, 100 < {l : Fin n | ∀ k<m+j, ¬ F l (m+j) ⊆ F l k}.ncard := by
  classical
  intro n m s o q F out leaves cover roots
  let gates := Finset.Ico m (m+s)
  let B (l : Fin n) := gates.filter fun w => ∀ k<w, ¬ F l w ⊆ F l k
  have need (l : Fin n) : q ≤ (B l).card := by
    let f (k : ℕ) : Finset (Fin n) := (F l k).toFinset
    have wire (w : ℕ) (hw : w < m+s) (two : 1 < (f w).card) :
        ∃ cs : Finset ℕ, cs ⊆ Finset.range w ∧ f w ⊆ cs.biUnion f ∧
          cs.card ≤ 1+(if w∈B l then 1 else 0) := by
      have notleaf : m≤w := by
        by_contra! hw'
        have h := leaves l w hw'
        rw [Set.ncard_eq_toFinset_card'] at h
        exact (Nat.not_lt_of_ge h) two
      by_cases old : ∃ k<w, F l w ⊆ F l k
      · obtain ⟨k,hk,sub⟩ := old
        refine ⟨{k},by simpa using hk,?_,by simp⟩
        simpa [f] using sub
      · have mem : w ∈ B l := Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨notleaf,hw⟩,fun k hk hk' => old ⟨k,hk,hk'⟩⟩
        have eq : m+(w-m)=w := by omega
        obtain ⟨a,b,lower,sub⟩ := cover l (w-m) (by omega)
        rw [eq] at lower sub
        refine ⟨{a,b},?_,?_,?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.mem_range.mpr (lt_of_le_of_lt (le_max_left _ _) lower)
          · rw [Finset.mem_singleton.mp hi]
            exact Finset.mem_range.mpr (lt_of_le_of_lt (le_max_right _ _) lower)
        · intro p hp
          have h := sub (Set.mem_toFinset.mp hp)
          rcases h with ha | hb
          · exact Finset.mem_biUnion.mpr ⟨a,by simp,Set.mem_toFinset.mpr ha⟩
          · exact Finset.mem_biUnion.mpr ⟨b,by simp,Set.mem_toFinset.mpr hb⟩
        · simp only [mem,ite_true]
          exact Finset.card_le_two
    have h := countUnion f (B l) (m+s) wire {o} (by simpa using out)
    have h' : (f o).card ≤ 1+((Finset.range (m+s)) ∩ B l).card := by simpa using h
    have cut := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range (m+s)) (s₂ := B l))
    have r := roots l
    rw [Set.ncard_eq_toFinset_card'] at r
    change q+1 ≤ (f o).card at r
    omega
  have sum : ∑ l : Fin n, (B l).card =
        ∑ w ∈ gates, (Finset.univ.filter (fun l : Fin n => w ∈ B l)).card := by
    have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset (Fin n))) (t := gates) (r := fun l w => w ∈ B l)
    simp only [Finset.bipartiteAbove,Finset.bipartiteBelow] at key
    rw [←key]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    ext w
    exact ⟨fun h => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1,h⟩,
      fun h => (Finset.mem_filter.mp h).2⟩
  by_cases good : ∀ w∈gates, (Finset.univ.filter (fun l : Fin n => w ∈ B l)).card ≤ 100
  · left
    calc
      n*q = ∑ _l : Fin n, q := by simp
      _ ≤ ∑ l : Fin n, (B l).card := Finset.sum_le_sum fun l _ => need l
      _ = _ := sum
      _ ≤ ∑ _w ∈ gates, 100 := Finset.sum_le_sum good
      _ = 100*s := by simp [gates,Nat.mul_comm]
  · right
    push_neg at good
    obtain ⟨w,hw,many⟩ := good
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hw
    have eq : m+(w-m)=w := by omega
    refine ⟨w-m,by omega,?_⟩
    rw [eq,Set.ncard_eq_toFinset_card']
    have same : ({l : Fin n | ∀ k<w, ¬ F l w ⊆ F l k} : Set (Fin n)).toFinset =
        Finset.univ.filter (fun l : Fin n => w∈B l) := by
      ext l
      simp [B,hw]
    rwa [same]

end Pilot4765
