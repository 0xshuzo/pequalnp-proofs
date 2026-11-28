import PEqualNP.Defs
open Finset
namespace PEqualNP.Outside.L_meta_9341_Baer
abbrev V := Fin 21
abbrev J := Fin 7
abbrev Box := Finset V × Finset V
def black (r c : V) := (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List Nat).getD r.val 0).testBit c.val
def p : J → V := ![0, 3, 6, 9, 12, 15, 18]
def l : J → V := ![2, 5, 8, 11, 14, 17, 20]
def board (r c : J) := black (p r) (l c)
def right (A : Finset J) : Finset J := Finset.univ.filter (fun c => ∀r∈A,board r c=false)
theorem cap : ∀ A : Finset J, A.card*(right A).card≤4 := by decide +kernel
def pr (b : Box) := Finset.univ.filter (fun i : J => p i∈b.1)
def lc (b : Box) := Finset.univ.filter (fun j : J => l j∈b.2)
def area (b : Box) := (pr b).card*(lc b).card
theorem bounded (b : Box) (ok : ∀r∈b.1,∀c∈b.2,black r c=false) : area b≤4 := by
  have sub : lc b⊆right (pr b) := by
    intro c m
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    intro r rr
    exact ok _ (Finset.mem_filter.mp rr).2 _ (Finset.mem_filter.mp m).2
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card sub)).trans (cap _)
def tile (b : Box) := (pr b) ×ˢ (lc b)
def goals := Finset.univ.filter (fun z : J×J => board z.1 z.2=false)
theorem size : goals.card=28 := by decide +kernel
def active (B : List Box) := Finset.univ.filter (fun i : Fin B.length => (tile (B.get i)).Nonempty)
theorem pencil (B : List Box) (ok : ∀b∈B,∀r∈b.1,∀c∈b.2,black r c=false)
    (cover : ∀r c,black r c=false → ∃b∈B,r∈b.1 ∧ c∈b.2) :
    7≤(active B).card ∧ ((active B).card≤7 → ∀i∈active B,area (B.get i)=4) := by
  classical
  let I := active B
  have sub : goals⊆I.biUnion (fun i => tile (B.get i)) := by
    intro x mem
    obtain ⟨b,inb,rr,cc⟩ := cover (p x.1) (l x.2) (Finset.mem_filter.mp mem).2
    obtain ⟨i,eq⟩ := List.mem_iff_get.mp inb
    have has : x ∈ tile (B.get i) := by
      rw [eq]
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,rr⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,cc⟩⟩
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨x,has⟩⟩,has⟩
  have mass : 28≤∑i∈I,area (B.get i) := by
    have hh := (Finset.card_le_card sub).trans (Finset.card_biUnion_le)
    simpa only [size,tile,Finset.card_product,area] using hh
  have localCap (i : Fin B.length) : area (B.get i)≤4 := bounded _ (ok _ (List.get_mem B i))
  have mx := Finset.sum_le_sum (s:=I) (fun i _ => localCap i)
  simp only [Finset.sum_const,nsmul_eq_mul] at mx
  change 7≤I.card ∧ (I.card≤7 → ∀i∈I,area (B.get i)=4)
  constructor
  · omega
  · intro hi i mi
    have split := Finset.add_sum_erase I (fun j => area (B.get j)) mi
    have bound := Finset.sum_le_sum (s:=I.erase i) (fun j _ => localCap j)
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_erase_of_mem mi] at bound
    have here := localCap i
    omega
end PEqualNP.Outside.L_meta_9341_Baer
