import Mathlib

namespace Frontier4675
variable {N : Nat}
abbrev Index (N : Nat) := Fin N

noncomputable def visited (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun v=>∃r∈roots,Relation.ReflTransGen (fun i j=>j∈child i) r v)
theorem mem_visit (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N)) (v : Fin N) :
    v∈visited roots child ↔ ∃r∈roots,Relation.ReflTransGen (fun i j=>j∈child i) r v := by
  classical
  simp [visited]

theorem rootVisit (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N)) :
    roots⊆visited roots child := by
  intro i hi
  exact (mem_visit _ _ _).mpr ⟨i,hi,.refl⟩

theorem childVisit {roots : Finset (Fin N)} {child : Fin N → Finset (Fin N)} {i j}
    (hi : i∈visited roots child) (hj : j∈child i) : j∈visited roots child := by
  obtain ⟨r,hr,tr⟩ := (mem_visit _ _ _).mp hi
  exact (mem_visit _ _ _).mpr ⟨r,hr,tr.tail hj⟩

noncomputable def tips (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N)) :=
  (visited roots child).filter (fun i=>child i=∅)

noncomputable def forks (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N)) :=
  (visited roots child).filter (fun i=>2≤(child i).card)

theorem budget (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N))
    (two : ∀i,(child i).card≤2) :
    (tips roots child).card≤roots.card+(forks roots child).card := by
  classical
  let V := visited roots child
  let U := V.filter (fun i=>(child i).Nonempty)
  let B := forks roots child
  have support : V ⊆ roots ∪ U.biUnion child := by
    intro i hi
    obtain ⟨r,hr,reach⟩ := (mem_visit _ _ _).mp hi
    cases reach with
    | refl => exact Finset.mem_union_left _ hr
    | tail prev step =>
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_filter.mpr
        ⟨(mem_visit _ _ _).mpr ⟨r,hr,prev⟩,⟨_,step⟩⟩,step⟩
  have ucnt : ∑ i∈U,(child i).card ≤ U.card+B.card := by
    have h := Finset.sum_le_sum (s:=U) (fun i (hi : i∈U) =>
      (show (child i).card ≤ 1+(if 2≤(child i).card then 1 else 0) by have := two i;split <;> omega))
    have d : U.filter (fun i=>2≤(child i).card)=B := by
      ext i
      simp only [U,B,forks,V,Finset.mem_filter,Finset.card_pos.symm]
      omega
    rw [Finset.sum_add_distrib,←Finset.card_filter,d] at h
    simpa using h
  have splitV : (tips roots child).card+U.card=V.card := by
    have d : V.filter (fun i=>¬child i=∅)=U := by ext i;simp [U,Finset.nonempty_iff_ne_empty]
    have h := Finset.card_filter_add_card_filter_not (s:=V) (fun i=>child i=∅)
    rw [d] at h
    exact h
  have c := (Finset.card_le_card support).trans (Finset.card_union_le _ _)
  have d : (U.biUnion child).card ≤ ∑i∈U,(child i).card := Finset.card_biUnion_le
  change _≤roots.card+B.card
  omega

theorem cover {α : Type} [DecidableEq α] (roots : Finset (Fin N)) (child : Fin N→Finset (Fin N))
    (earlier : ∀i j,j∈child i→j<i) (alive direct : Fin N→Finset α)
    (transfer : ∀i∈visited roots child, ∀e∈alive i,
      (∃j∈child i,e∈alive j) ∨ (child i=∅ ∧ e∈direct i) ∨ (∃r∈roots,r<i ∧ e∈alive r)) :
    roots.biUnion alive ⊆ (tips roots child).biUnion direct := by
  classical
  intro e he
  obtain ⟨r,hr,er⟩ := Finset.mem_biUnion.mp he
  let W := (visited roots child).filter (fun i=>e∈alive i)
  have wn : W.Nonempty := ⟨r,Finset.mem_filter.mpr ⟨rootVisit roots child hr,er⟩⟩
  let i := W.min' wn
  have mi : i∈W := Finset.min'_mem W wn
  have least (j : Fin N) (h : j∈W) : i≤j := Finset.min'_le W j h
  obtain ⟨hv,ee⟩ := Finset.mem_filter.mp mi
  rcases transfer i hv e ee with ⟨j,hj,ej⟩|⟨empty,ed⟩|⟨s,hs,lt,es⟩
  · exact False.elim (not_lt_of_ge (least j (Finset.mem_filter.mpr ⟨childVisit hv hj,ej⟩)) (earlier i j hj))
  · exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨hv,empty⟩,ed⟩
  · exact False.elim (not_lt_of_ge (least s (Finset.mem_filter.mpr ⟨rootVisit roots child hs,es⟩)) lt)
end Frontier4675
namespace Builder4675
open Frontier4675

theorem stars {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    {N : Nat} (K H : Finset (Fin N)) (center : Fin N→V) (head : Fin N→Fin N)
    (relation : V→Finset V) (pair : V→V→E) (S : Fin N→Finset V) (child : Fin N→Finset (Fin N))
    (two : ∀i,(child i).card≤2) (back : ∀i j,j∈child i→j<i)
    (sound : ∀i j,j∈child i→S j⊆S i)
    (complete : ∀i,(child i).Nonempty→S i⊆(child i).biUnion S)
    (tipsmall : ∀i,child i=∅→(S i).card≤1)
    (branch : ∀i,2≤(child i).card→i∈K ∧ 2≤(S i).card)
    (valid : ∀h∈H,S (head h)⊆relation (center h))
    (c4 : ∀u v,u≠v→((relation u)∩(relation v)).card≤1) :
    (H.biUnion (fun h=>(S (head h)).image (pair (center h)))).card≤H.card+K.card := by
  classical
  let part (c : V) := H.filter (fun h=>center h=c)
  let starts (c : V) := (part c).image head
  let leaves (c : V) := (starts c).biUnion S
  let fork (c : V) := forks (starts c) child
  have inRel {c : V} {j : Fin N} (hj : j∈visited (starts c) child) : S j⊆relation c := by
    obtain ⟨r,hr,reach⟩ := (mem_visit _ _ _).mp hj
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hm,eq⟩ := Finset.mem_filter.mp hh
    induction reach with
    | refl => simpa only [←eq] using valid h hm
    | tail t e ih => exact (sound _ _ e).trans ih
  have dis : (Finset.univ : Finset V).toSet.PairwiseDisjoint fork := by
    intro c _ d _ cd
    apply Finset.disjoint_left.mpr
    intro i hc hd
    obtain ⟨uc,ic⟩ := Finset.mem_filter.mp hc
    obtain ⟨ud,_⟩ := Finset.mem_filter.mp hd
    have sub : S i⊆relation c∩relation d := fun e he=>Finset.mem_inter.mpr ⟨inRel uc he,inRel ud he⟩
    have b := (branch i ic).2
    have x := (Finset.card_le_card sub).trans (c4 c d cd)
    omega
  have bound (c : V) : (leaves c).card≤(part c).card+(fork c).card := by
    have support : leaves c ⊆ (tips (starts c) child).biUnion S := by
      apply cover _ _ back
      intro i _ e he
      rcases (child i).eq_empty_or_nonempty with emp|non
      · exact Or.inr (Or.inl ⟨emp,he⟩)
      · exact Or.inl (Finset.mem_biUnion.mp (complete i non he))
    have tip : ((tips (starts c) child).biUnion S).card≤(tips (starts c) child).card := by
      calc
        _ ≤ ∑i∈tips (starts c) child,(S i).card := Finset.card_biUnion_le
        _ ≤ ∑_i∈tips (starts c) child,1 := Finset.sum_le_sum (fun i hi=>tipsmall i (Finset.mem_filter.mp hi).2)
        _ = _ := by simp
    have q := (Finset.card_le_card support).trans (tip.trans (budget (starts c) child two))
    exact q.trans (Nat.add_le_add_right Finset.card_image_le _)
  have distinct : ∑c,(fork c).card ≤ K.card := by
    rw [←Finset.card_biUnion dis]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨c,_,hc⟩ := Finset.mem_biUnion.mp hi
    exact (branch i (Finset.mem_filter.mp hc).2).1
  have parts : ∑c,(part c).card=H.card := by
    symm
    exact Finset.card_eq_sum_card_fiberwise (fun _ _=>Finset.mem_univ _)
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun c _=>bound c)
  rw [Finset.sum_add_distrib,parts] at total
  have edges : H.biUnion (fun h=>(S (head h)).image (pair (center h))) ⊆
      Finset.univ.biUnion (fun c=>(leaves c).image (pair c)) := by
    intro e he
    obtain ⟨h,hh,he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_biUnion.mpr ⟨center h,Finset.mem_univ _,Finset.mem_image_of_mem _
      (Finset.mem_biUnion.mpr ⟨head h,Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hh,rfl⟩),hi⟩)⟩
  calc
    _ ≤ _ := Finset.card_le_card edges
    _ ≤ ∑c,((leaves c).image (pair c)).card := Finset.card_biUnion_le
    _ ≤ ∑c,(leaves c).card := Finset.sum_le_sum (fun _ _=>Finset.card_image_le)
    _ ≤ _ := total.trans (Nat.add_le_add_left distinct _)
end Builder4675
