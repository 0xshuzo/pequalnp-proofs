import Mathlib

namespace UnionBank2262
variable {α : Type*} [DecidableEq α]

-- A bank contains all wires available so far. A single operation adjoins a union.
inductive Program (B : Finset (Finset α)) : ℕ → Finset (Finset α) → Prop where
  | initial : Program B 0 B
  | add {r S x y} : Program B r S → x∈S → y∈S → Program B (r+1) (insert (x∪y) S)

def Covers (T : Finset α) (F : Finset (Finset α)) : Prop := ∀ x∈T, ∃ s∈F, x∈s

theorem frontier {B S : Finset (Finset α)} {r : ℕ} (pr : Program B r S)
    (T : Finset α) (F : Finset (Finset α)) (sub : F⊆S) (hc : Covers T F) :
    ∃ P⊆B, P.card≤F.card+r ∧ Covers T P := by
  classical
  induction pr generalizing F with
  | initial => exact ⟨F,sub,by omega,hc⟩
  | @add r S a b _ ha hb ih =>
    by_cases present : a∪b∈F
    · let F' := insert a (insert b (F.erase (a∪b)))
      have fs : F' ⊆ S := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | tail
        · exact ha
        rcases Finset.mem_insert.mp tail with rfl | old
        · exact hb
        have old' := Finset.mem_erase.mp old
        exact (Finset.mem_insert.mp (sub old'.2)).resolve_left old'.1
      have cv : Covers T F' := by
        intro x hx
        obtain ⟨q,mem,xq⟩ := hc x hx
        by_cases eq : q=a∪b
        · rw [eq] at xq
          rcases Finset.mem_union.mp xq with xa | xb
          · exact ⟨a,Finset.mem_insert_self _ _,xa⟩
          · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),xb⟩
        · exact ⟨q,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨eq,mem⟩)),xq⟩
      have fc : F'.card≤F.card+1 := by
        have ad := Finset.card_insert_le a (insert b (F.erase (a∪b)))
        have bd := Finset.card_insert_le b (F.erase (a∪b))
        have er := Finset.card_erase_add_one present
        dsimp only [F']
        omega
      obtain ⟨P,ps,pc,pv⟩ := ih F' fs cv
      exact ⟨P,ps,by omega,pv⟩
    · have fs : F⊆S := by
        intro q hq
        rcases Finset.mem_insert.mp (sub hq) with eq | old
        · exact (present (eq ▸ hq)).elim
        · exact old
      obtain ⟨P,ps,pc,pv⟩ := ih F fs hc
      exact ⟨P,ps,by omega,pv⟩

-- Even if every subset of each old target is available for free, k+1 initial pieces
-- are required to reach a target with k newly counted gates.
theorem single_target {B S : Finset (Finset α)} {r : ℕ} (pr : Program B r S)
    {A T : Finset α} (goal : T∈S) (need : A⊆T)
    {k : ℕ} (price : ∀ P⊆B, Covers A P → k+1≤P.card) : k≤r := by
  classical
  have within : ({T} : Finset (Finset α)) ⊆ S := Finset.singleton_subset_iff.mpr goal
  have cov : Covers A {T} := fun x hx => ⟨T,Finset.mem_singleton_self _,need hx⟩
  obtain ⟨P,sub,size,covered⟩ := frontier pr A {T} within cov
  have units := price P sub covered
  rw [Finset.card_singleton] at size
  omega

end UnionBank2262
