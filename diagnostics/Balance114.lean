import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9804_Balance
open Finset
abbrev P := Fin 20
abbrev F := Fin 95
def row : F → P := ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19]
def col : F → P := ![0, 5, 7, 17, 1, 6, 8, 18, 1, 2, 7, 9, 19, 0, 2, 3, 8, 10, 3, 4, 9, 11, 1, 4, 5, 10, 12, 2, 5, 6, 11, 13, 3, 6, 7, 12, 14, 4, 7, 8, 13, 15, 5, 8, 9, 14, 16, 6, 9, 10, 15, 17, 7, 10, 11, 16, 18, 8, 11, 12, 17, 19, 0, 9, 12, 13, 18, 10, 13, 14, 19, 0, 1, 11, 14, 15, 2, 12, 15, 16, 1, 3, 13, 16, 17, 2, 4, 14, 17, 18, 3, 5, 15, 18, 19]
def weight : F → Nat := ![4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 4, 4, 3, 3, 3, 3, 4, 4, 4, 4, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 4, 3, 3, 3, 4, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 3, 3, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 4, 3, 3, 3, 3, 4, 4, 4, 4, 4, 3, 3, 3, 3, 4, 4, 4, 4, 3, 3, 3, 4, 3, 3, 4, 3, 3, 3, 3, 3, 3, 3, 4]
abbrev Vertex := Sum P P
def bucket {n k : Nat} (f : Fin n → Fin k) (j : Fin k) : Finset (Fin n) :=
  univ.filter (fun i => f i=j)
theorem bucket_sum {n k : Nat} (f : Fin n → Fin k) :
    ∑ j : Fin k,(bucket f j).card=n := by
  have eqn := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n)))
    (t := (univ : Finset (Fin k))) (f := f) (fun i _ => mem_univ (f i))
  simpa [bucket] using eqn.symm

def atVertex (v : Vertex) (e : F) : Prop :=
  Sum.inl (row e)=v ∨ Sum.inr (col e)=v
instance (v : Vertex) (e : F) : Decidable (atVertex v e) := by unfold atVertex; infer_instance
theorem all_mass : (∑ e : F, weight e)=320 := by decide +kernel
set_option maxRecDepth 10000 in
theorem unit_mass : ∀ v : Vertex, (∑ e : F, if atVertex v e then weight e else 0)=16 := by decide +kernel

def mass {k : Nat} (f : F → Fin k) (j : Fin k) := ∑ e∈bucket f j,weight e
theorem mass_sum {k : Nat} (f : F → Fin k) : (∑ j,mass f j)=320 := by
  have h := Finset.sum_fiberwise_of_maps_to (s := (univ : Finset F))
    (t := (univ : Finset (Fin k))) (g := f) (fun e _ => mem_univ (f e)) weight
  exact h.trans all_mass

theorem mass_cover {k : Nat} (f : F → Fin k) (j : Fin k) (cover : Finset Vertex)
    (hit : ∀ e, f e=j → Sum.inl (row e)∈cover ∨ Sum.inr (col e)∈cover) :
    mass f j≤16*cover.card := by
  classical
  have one (e : F) (he : e∈bucket f j) :
      weight e≤∑ v∈cover, if atVertex v e then weight e else 0 := by
    rcases hit e (mem_filter.mp he).2 with a|b
    · have z := Finset.single_le_sum (f := fun v : Vertex => if atVertex v e then weight e else 0)
        (fun v _ => Nat.zero_le _) a
      simpa [atVertex] using z
    · have z := Finset.single_le_sum (f := fun v : Vertex => if atVertex v e then weight e else 0)
        (fun v _ => Nat.zero_le _) b
      simpa [atVertex] using z
  have local_sum (v : Vertex) : (∑ e∈bucket f j, if atVertex v e then weight e else 0)≤16 := by
    rw [← unit_mass v]
    exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  calc
    mass f j≤∑ e∈bucket f j,∑ v∈cover,if atVertex v e then weight e else 0 := sum_le_sum one
    _ = ∑ v∈cover,∑ e∈bucket f j,if atVertex v e then weight e else 0 := Finset.sum_comm
    _ ≤ ∑ _v∈cover,16 := Finset.sum_le_sum (fun v _ => local_sum v)
    _ = 16*cover.card := by simp [Nat.mul_comm]

theorem weighted114 {k : Nat} (f : F → Fin k) (cost : Fin k → Nat)
    (charge : ∀ j,16*(bucket f j).card+mass f j≤16*(cost j+1)) :
    114≤(∑ j,cost j)+(k-1) := by
  have total := Finset.sum_le_sum (s := (univ : Finset (Fin k))) (fun j _ => charge j)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,bucket_sum,mass_sum,
    Finset.sum_add_distrib] at total
  simp at total
  omega


-- All residual dyads have one endpoint in K. U records all exceptions.
theorem interdiction (U : Finset F) (K : Finset Vertex)
    (hit : ∀ e, e ∉ U → Sum.inl (row e) ∈ K ∨ Sum.inr (col e) ∈ K) :
    320 ≤ 16*K.card + ∑ e∈U, weight e := by
  classical
  let pick (e : F) : Fin 2 := if e∈U then 1 else 0
  have hp (e : F) : pick e=0 ↔ e∉U := by by_cases he : e∈U <;> simp [pick,he]
  have hq : bucket pick 1=U := by
    ext e
    by_cases he : e∈U <;> simp [bucket,pick,he]
  have h0 := mass_cover pick 0 K (fun e he => hit e ((hp e).mp he))
  have h1 : mass pick 1=∑ e∈U,weight e := by simp [mass,hq]
  have ha := mass_sum pick
  rw [Fin.sum_univ_two, h1] at ha
  omega

-- Applicable when a least DAG has already supplied the exposed cover account.
theorem charged_interdiction (U : Finset F) (K : Finset Vertex) (paid : Nat)
    (hit : ∀ e, e ∉ U → Sum.inl (row e) ∈ K ∨ Sum.inr (col e) ∈ K)
    (price : K.card + paid ≤ 19 + U.card) :
    16*(paid+1) ≤ 16*U.card + ∑ e∈U, weight e := by
  have h := interdiction U K hit
  omega
end PEqualNP.Outside.L_meta_9804_Balance
