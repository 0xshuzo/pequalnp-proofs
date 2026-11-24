import Mathlib
import PEqualNP.Defs

namespace Plane4919

theorem footprint {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (N : α → Finset β) (degree : ∀ p, (N p).card=5)
    (one : ∀ p r, p≠r → ((N p)∩(N r)).card≤1) :
    5*A.card ≤ (A.biUnion N).card+A.card.choose 2 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert p A hp ih =>
    classical
    have sub : N p ∩ A.biUnion N ⊆ A.biUnion (fun r => N p ∩ N r) := by
      intro x hx
      obtain ⟨hpx,ax⟩ := Finset.mem_inter.mp hx
      obtain ⟨r,hr,rx⟩ := Finset.mem_biUnion.mp ax
      exact Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_inter.mpr ⟨hpx,rx⟩⟩
    have overlap : (N p ∩ A.biUnion N).card ≤ A.card := by
      calc
        _ ≤ _ := Finset.card_le_card sub
        _ ≤ ∑ r∈A, (N p ∩ N r).card := Finset.card_biUnion_le
        _ ≤ ∑ _r∈A, 1 := Finset.sum_le_sum fun r hr => one p r (fun e => hp (e ▸ hr))
        _ = _ := by simp
    have split := Finset.card_union_add_card_inter (N p) (A.biUnion N)
    rw [degree] at split
    rw [Finset.card_insert_of_notMem hp,Finset.biUnion_insert]
    have ch : (A.card+1).choose 2=A.card+A.card.choose 2 := by
      rw [Nat.choose_succ_succ,Nat.choose_one_right]
    rw [ch,Nat.mul_succ]
    omega

theorem six (N : Fin 21 → Finset (Fin 21)) (degree : ∀ p, (N p).card=5)
    (one : ∀ p r, p≠r → ((N p)∩(N r)).card≤1)
    (P L : Finset (Fin 21)) (indep : ∀ p∈P, ∀ l∈L, l∉N p) (many : 6≤P.card) :
    L.card≤6 := by
  classical
  obtain ⟨A,sub,sz⟩ := Finset.exists_subset_card_eq many
  have count := footprint A N degree one
  rw [sz] at count
  have disj : Disjoint L (A.biUnion N) := by
    refine Finset.disjoint_left.mpr ?_
    intro l hl assigned
    obtain ⟨p,hp,pl⟩ := Finset.mem_biUnion.mp assigned
    exact indep p (sub hp) l hl pl
  have cap := Finset.card_le_univ (L ∪ A.biUnion N)
  rw [Finset.card_union_of_disjoint disj,Fintype.card_fin] at cap
  norm_num [Nat.choose] at count
  omega

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem classification (P L : Finset (Fin 21)) :
    let I (p l : Fin 21) := (l.val+42-p.val)%21 ∈ ([0,5,7,17,20] : List ℕ)
    (∀ p∈P, ∀ l∈L, ¬ I p l) →
    P.card≤5 ∨ L.card≤5 ∨ (P.card=6 ∧ L.card=6) := by
  intro I neg
  let N (p : Fin 21) := Finset.univ.filter fun l => I p l
  let M (l : Fin 21) := Finset.univ.filter fun p => I p l
  have row : ∀ p, (N p).card=5 := by dsimp only [N,I]; decide +kernel
  have col : ∀ l, (M l).card=5 := by dsimp only [M,I]; decide +kernel
  have pr : ∀ p r, p≠r → ((N p)∩(N r)).card≤1 := by dsimp only [N,I]; decide +kernel
  have pl : ∀ p r, p≠r → ((M p)∩(M r)).card≤1 := by dsimp only [M,I]; decide +kernel
  by_cases hp : P.card≤5
  · exact Or.inl hp
  by_cases hl : L.card≤5
  · exact Or.inr (Or.inl hl)
  have a := six N row pr P L (fun p h l k h' => neg p h l k (Finset.mem_filter.mp h').2) (by omega)
  have b := six M col pl L P (fun l h p k h' => neg p k l h (Finset.mem_filter.mp h').2) (by omega)
  exact Or.inr (Or.inr ⟨by omega,by omega⟩)
theorem validate : ∀ F : Finset (Fin 21) → Finset (Fin 21) → Bool,
      let I (p l : Fin 21) := (l.val+42-p.val)%21 ∈ ([0,5,7,17,20] : List ℕ)
      (∀ P Q L M, P⊆Q → L⊆M → F P L=true → F Q M=true) →
      (∀ p l, I p l → F {p} {l} = true) →
      (∀ P L, (∀ p, p∈P ↔ ∀ l∈L, ¬I p l) → (∀ l, l∈L ↔ ∀ p∈P, ¬I p l) →
        (P.card≤5 ∨ L.card≤5 ∨ P.card=6 ∧ L.card=6) → F P L = false) →
      ∀ P L, F P L = true ↔ ∃ p∈P, ∃ l∈L, I p l := by
  intro F I mono flags rejected P L
  constructor
  · intro yes
    by_contra bad
    let M := Finset.univ.filter fun l : Fin 21 => ∀ p∈P, ¬I p l
    let Q := Finset.univ.filter fun p : Fin 21 => ∀ l∈M, ¬I p l
    have lm : L⊆M := by
      intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp hit => bad ⟨p,hp,l,hl,hit⟩⟩
    have pq : P⊆Q := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl => (Finset.mem_filter.mp hl).2 p hp⟩
    have qm (p : Fin 21) : p∈Q ↔ ∀ l∈M, ¬I p l := by simp [Q]
    have mq (l : Fin 21) : l∈M ↔ ∀ p∈Q, ¬I p l := by
      constructor
      · intro hl p hp
        exact (qm p).mp hp l hl
      · intro all
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => all p (pq hp)⟩
    have small := classification Q M (fun p hp => (qm p).mp hp)
    have no := rejected Q M qm mq small
    exact Bool.noConfusion ((mono P Q L M pq lm yes).symm.trans no)
  · rintro ⟨p,hp,l,hl,hit⟩
    exact mono {p} P {l} L (Finset.singleton_subset_iff.mpr hp)
      (Finset.singleton_subset_iff.mpr hl) (flags p l hit)

end Plane4919
