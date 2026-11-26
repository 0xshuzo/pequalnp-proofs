import PEqualNP.Outside.L_meta_9672

namespace PEqualNP.Outside.L_meta_9682_aux.Trace
open PEqualNP.Search PEqualNP.ProofComplexity
open PEqualNP.Outside.L_meta_9672_aux.CPGraphScratch PEqualNP.Outside.L_meta_9672_aux.CPHalfScratch
open PEqualNP.Outside.L_meta_9672_aux.CPIntegrationScratch PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch
theorem cap51 (source : ParitySource) {read : ℕ → CPLine Vars}
    {rule : ℕ → Rule Vars} {live : Finset ℕ} {root : ℕ}
    (hroot : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (hsize : live.card ≤ 51) (hr : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j)) :
    (live.filter (fun i => (parents (rule i)).length = 0)).card ≤ 23 ∧
      4 ≤ (live.filter (fun i => isDivision (rule i) = true)).card ∧
      (live.filter (fun i => isDivision (rule i) = true)).card +
      (live.filter (fun i => isMultiply (rule i) = true)).card +
      ∑ i ∈ live.erase root, (uses (fun n => parents (rule n)) live i - 1) + 2 * (live.filter (fun i => (parents (rule i)).length = 0)).card ≤ 52 := by
  have hL := at_least_22_leaves hroot hr hl hc
  have hD := at_least_four_divisions source hroot hr hl hc
  have hcount := count_budget hroot hsub hc hused horder (fun i _ => parent_count (rule i))
  have hdis : Disjoint (live.filter (fun i => isDivision (rule i) = true))
      (live.filter (fun i => isMultiply (rule i) = true)) := by
    refine Finset.disjoint_left.mpr fun i hi hj => ?_
    exact unary_kinds_disjoint (rule i) ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩
  have hunion : live.filter (fun i => (parents (rule i)).length = 1) =
      (live.filter (fun i => isDivision (rule i) = true)) ∪
      (live.filter (fun i => isMultiply (rule i) = true)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, unary_kind]
    tauto
  rw [hunion, Finset.card_union_of_disjoint hdis] at hcount
  let leaves := (live.filter (fun i => (parents (rule i)).length = 0)).card
  have drop : leaves≤23 := by
    by_contra bad
    have hd4 : (divs rule live).card=4 := by
      change (live.filter (fun i=>isDivision (rule i)=true)).card=4
      dsimp only [leaves] at bad
      omega
    have nonempty : (divs rule live).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨first,mem⟩ := nonempty
    obtain ⟨j,hj,_⟩ := four_divisions_reach_obstruction hroot hsub hd4 mem hr hl hc horder hused
    have gt : 0<(obstructions rule live root).card := Finset.card_pos.mpr ⟨_,hj⟩
    have bound := obstructions_card_le rule live root
    change (obstructions rule live root).card ≤
      (live.filter (fun i => isMultiply (rule i)=true)).card +
        ∑ i ∈ live.erase root, (uses (fun j=>parents (rule j)) live i - 1) at bound
    dsimp only [leaves] at bad
    omega
  exact ⟨drop,hD,by omega⟩

def Trace (π : List (CPLine Vars)) (read : ℕ → CPLine Vars) (rule : ℕ → Rule Vars)
    (live : Finset ℕ) (root : ℕ) : Prop :=
  root∈live ∧ live ⊆ Finset.range (root+1) ∧ live.card≤π.length ∧ read root=(0,1) ∧
  (∀ i∈live,legalRule (PHP (3+1) 3) i read (read i) (rule i)) ∧
  closedUnder (fun j=>parents (rule j)) live ∧
  (∀ i j,j∈parents (rule i) → j<i) ∧
  ∀ i∈live,i≠root → ∃ j∈live,i∈parents (rule j)

theorem postedTrace (π : List (CPLine Vars)) (r : IsCPRefutation (PHP (3+1) 3) π) (length : π.length≤51) :
   ∃ read rule live root, Trace π read rule live root ∧
     let leaves := (live.filter (fun i => (parents (rule i)).length=0)).card
     let excess := ∑ i ∈ live.erase root, (uses (fun j=>parents (rule j)) live i-1)
     (leaves=22 ∨ leaves=23) ∧ 4≤(divs rule live).card ∧
       2*leaves+(divs rule live).card+(mults rule live).card+excess≤52 := by
  classical
  obtain ⟨read,rule,live,root,mem,sub,size,goal,h,closed,order,used⟩ := exists_live_trace r
  refine ⟨read,rule,live,root,⟨mem,sub,size,goal,h,closed,order,used⟩,?_⟩
  dsimp only
  obtain ⟨upper,minDiv,budget⟩ := cap51 PEqualNP.Outside.L_meta_9672_aux.Sol9668HalfBridge.half_point
    mem sub (size.trans length) goal h closed order used
  have lower := at_least_22_leaves mem goal h closed
  simp only [divs,mults]
  exact ⟨by omega,minDiv,by omega⟩
end PEqualNP.Outside.L_meta_9682_aux.Trace
