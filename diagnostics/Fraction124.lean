import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9743_Allocation
open Finset
abbrev P := Fin 21
abbrev F := Fin 104
def row : F → P := ![0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20]
def col : F → P := ![5, 7, 17, 20, 0, 1, 6, 8, 18, 1, 2, 7, 9, 19, 2, 3, 8, 10, 20, 0, 3, 4, 9, 11, 1, 4, 5, 10, 12, 2, 5, 6, 11, 13, 3, 6, 7, 12, 14, 4, 7, 8, 13, 15, 5, 8, 9, 14, 16, 6, 9, 10, 15, 17, 7, 10, 11, 16, 18, 8, 11, 12, 17, 19, 9, 12, 13, 18, 20, 0, 10, 13, 14, 19, 1, 11, 14, 15, 20, 0, 2, 12, 15, 16, 1, 3, 13, 16, 17, 2, 4, 14, 17, 18, 3, 5, 15, 18, 19, 4, 6, 16, 19, 20]
def matched : P → F := ![0, 6, 11, 16, 22, 27, 32, 37, 42, 47, 52, 57, 62, 67, 73, 78, 79, 84, 89, 94, 99]
def mcol (p : P) : P := ⟨(p.val+5)%21,by omega⟩
theorem on_matching : ∀ p : P, row (matched p)=p ∧ col (matched p)=mcol p := by decide +kernel
theorem mcol_inj : Function.Injective mcol := by
  intro a b h
  have z := congrArg Fin.val h
  apply Fin.ext
  dsimp [mcol] at z
  omega

abbrev Vertex := Sum P P
def bucket {n k : Nat} (f : Fin n → Fin k) (j : Fin k) : Finset (Fin n) :=
  univ.filter (fun i => f i=j)
theorem bucket_sum {n k : Nat} (f : Fin n → Fin k) :
    ∑ j : Fin k,(bucket f j).card=n := by
  have eqn := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n)))
    (t := (univ : Finset (Fin k))) (f := f) (fun i _ => mem_univ (f i))
  simpa [bucket] using eqn.symm

def endpoint (cover : Finset Vertex) (p : P) : Vertex :=
  if Sum.inl p∈cover then Sum.inl p else Sum.inr (mcol p)

theorem ep_inj (cover : Finset Vertex) : Function.Injective (endpoint cover) := by
  intro a b h
  by_cases ha : Sum.inl a∈cover <;> by_cases hb : Sum.inl b∈cover
  · simpa [endpoint,ha,hb] using h
  · simp [endpoint,ha,hb] at h
  · simp [endpoint,ha,hb] at h
  · exact mcol_inj (by simpa [endpoint,ha,hb] using h)

theorem bucket_matching {k} (assign : F → Fin k) (j : Fin k) (cover : Finset Vertex)
    (hits : ∀ e : F, assign e=j → Sum.inl (row e)∈cover ∨ Sum.inr (col e)∈cover) :
    (bucket (assign ∘ matched) j).card≤cover.card := by
  have sub : (bucket (assign ∘ matched) j).image (endpoint cover) ⊆ cover := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have h : assign (matched i)=j := (mem_filter.mp hi).2
    have t := hits (matched i) h
    rw [(on_matching i).1,(on_matching i).2] at t
    unfold endpoint
    split <;> tauto
  have done := card_le_card sub
  rwa [card_image_of_injective _ (ep_inj cover)] at done

-- Costs refer to the independent paid gates of each terminal. Their raw inputs
-- and the edges they accept may overlap. Each true edge has one chosen owner.
theorem allocated124 {k : Nat} (assign : F → Fin k) (cost : Fin k → Nat)
    (cover : Fin k → Finset Vertex)
    (tops : ∀ j e, assign e=j → Sum.inl (row e)∈cover j ∨ Sum.inr (col e)∈cover j)
    (charge : ∀ j, (bucket assign j).card+(cover j).card≤cost j+1) :
    124≤(∑ j,cost j)+(k-1) := by
  have h (j : Fin k) :
      (bucket assign j).card+(bucket (assign ∘ matched) j).card≤cost j+1 :=
    (Nat.add_le_add_left (bucket_matching assign j (cover j) (tops j)) _).trans (charge j)
  have total := Finset.sum_le_sum (s := (univ : Finset (Fin k))) (fun j _ => h j)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
    bucket_sum assign,bucket_sum (assign ∘ matched)] at total
  simp at total
  have pos : 0<k := by have z := (assign (0:F)).isLt; omega
  omega

def marks : Fin 84 → F := ![0, 6, 11, 16, 22, 27, 32, 37, 42, 47, 52, 57, 62, 67, 73, 78, 79, 84, 89, 94, 99, 1, 7, 12, 17, 23, 28, 33, 38, 43, 48, 53, 58, 63, 68, 69, 74, 80, 85, 90, 95, 100, 2, 8, 13, 18, 19, 24, 29, 34, 39, 44, 49, 54, 59, 64, 70, 75, 81, 86, 91, 96, 101, 3, 4, 9, 14, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 71, 76, 82, 87, 92, 97, 102]
def shiftID (i : Fin 84) : Fin 4 := ⟨i.val/21,by omega⟩
set_option maxRecDepth 10000 in
theorem ids_distinct : ∀ i j : Fin 84, marks i=marks j → i=j := by decide +kernel
set_option maxRecDepth 10000 in
theorem disjoint_left : ∀ i j : Fin 84, shiftID i=shiftID j →
    row (marks i)=row (marks j) → i=j := by decide +kernel
set_option maxRecDepth 10000 in
theorem disjoint_right : ∀ i j : Fin 84, shiftID i=shiftID j →
    col (marks i)=col (marks j) → i=j := by decide +kernel

def colored (h : Finset Vertex) (i : Fin 84) : Fin 4 × Vertex :=
  (shiftID i,if Sum.inl (row (marks i))∈h then Sum.inl (row (marks i)) else Sum.inr (col (marks i)))
theorem colored_inj (cover : Finset Vertex) : Function.Injective (colored cover) := by
  intro a b h
  have tagEq : shiftID a=shiftID b := congrArg Prod.fst h
  have epEq := congrArg Prod.snd h
  by_cases ha : Sum.inl (row (marks a))∈cover <;> by_cases hb : Sum.inl (row (marks b))∈cover
  · exact disjoint_left a b tagEq (by simpa [colored,ha,hb] using epEq)
  · simp [colored,ha,hb] at epEq
  · simp [colored,ha,hb] at epEq
  · exact disjoint_right a b tagEq (by simpa [colored,ha,hb] using epEq)

theorem weight_cap {k} (assign : F → Fin k) (j : Fin k) (cover : Finset Vertex)
    (tops : ∀ e : F, assign e=j → Sum.inl (row e)∈cover ∨ Sum.inr (col e)∈cover) :
    (bucket (assign ∘ marks) j).card≤min (bucket assign j).card (4*cover.card) := by
  apply Nat.le_min.mpr
  constructor
  · have sub : (bucket (assign ∘ marks) j).image marks ⊆ bucket assign j := by
      intro t ht
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
    have le := card_le_card sub
    rwa [card_image_of_injective _ (fun a b h => ids_distinct a b h)] at le
  · have sub : (bucket (assign ∘ marks) j).image (colored cover) ⊆
        (univ : Finset (Fin 4)) ×ˢ cover := by
      intro t ht
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
      have hit := tops (marks i) (mem_filter.mp hi).2
      apply mem_product.mpr
      refine ⟨mem_univ _,?_⟩
      change (if Sum.inl (row (marks i))∈cover then _ else _) ∈ cover
      split <;> tauto
    have le := card_le_card sub
    simpa only [card_image_of_injective _ (colored_inj cover),card_product,card_univ,Fintype.card_fin] using le

theorem fractional124 {k : Nat} (assign : F → Fin k) (cost : Fin k → Nat)
    (cover : Fin k → Finset Vertex)
    (tops : ∀ j e, assign e=j → Sum.inl (row e)∈cover j ∨ Sum.inr (col e)∈cover j)
    (charge : ∀ j, 4*(bucket assign j).card+min (bucket assign j).card (4*(cover j).card)≤4*(cost j+1)) :
    124≤(∑ j,cost j)+(k-1) := by
  have h (j : Fin k) :
      4*(bucket assign j).card+(bucket (assign ∘ marks) j).card≤4*(cost j+1) :=
    (Nat.add_le_add_left (weight_cap assign j (cover j) (tops j)) _).trans (charge j)
  have total := Finset.sum_le_sum (s := (univ : Finset (Fin k))) (fun j _ => h j)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    bucket_sum assign,bucket_sum (assign ∘ marks),Finset.sum_add_distrib] at total
  simp at total
  omega

end PEqualNP.Outside.L_meta_9743_Allocation
