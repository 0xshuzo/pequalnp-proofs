import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_921
variable {m : ℕ}
private abbrev V (m : ℕ) := Fin m
private def fam (q : ℕ) (P : Finset (V m)) := (Finset.univ.powersetCard q).filter (P ⊆ ·)
private theorem inFam {q : ℕ} {P S : Finset (V m)} : S∈fam q P ↔ P⊆S ∧ S.card=q := by
  simp [fam,Finset.mem_powersetCard,and_comm]
private theorem famSize (q : ℕ) (P : Finset (V m)) (hp : P.card≤q) :
    (fam q P).card=Nat.choose (m-P.card) (q-P.card) := by
  classical
  let U := (Finset.univ : Finset (V m)) \ P
  have e : (fam q P).card=(U.powersetCard (q-P.card)).card := by
    apply Finset.card_bij (fun S _ => S \ P)
    · intro S hs
      obtain ⟨inc,cc⟩ := inFam.mp hs
      apply Finset.mem_powersetCard.mpr
      refine ⟨fun z hz => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hz).2⟩,?_⟩
      rw [Finset.card_sdiff_of_subset inc,cc]
    · intro S hs T ht eq
      have si := (inFam.mp hs).1
      have ti := (inFam.mp ht).1
      simp only [Finset.ext_iff,Finset.subset_iff,Finset.mem_sdiff] at *
      grind
    · intro T ht
      obtain ⟨sub,sz⟩ := Finset.mem_powersetCard.mp ht
      have dis : Disjoint P T := Finset.disjoint_left.mpr (by
        intro v hv h; exact (Finset.mem_sdiff.mp (sub h)).2 hv)
      refine ⟨P∪T,inFam.mpr ⟨Finset.subset_union_left,?_⟩,?_⟩
      · rw [Finset.card_union_of_disjoint dis,sz]; omega
      · ext v
        have h := Finset.disjoint_left.mp dis (a:=v)
        simp only [Finset.mem_union,Finset.mem_sdiff]
        tauto
  rw [e,Finset.card_powersetCard]
  congr 1
  simp [U,Finset.card_sdiff_of_subset]
variable {m : ℕ}
private def deg (q : ℕ) (P : Finset (Fin m)) : ℚ := (Nat.choose (m-P.card) (q-P.card) : ℕ)
private def children (P : Finset (Fin m)) := (Finset.univ : Finset (Fin m)) \ P
private theorem childCard (P : Finset (Fin m)) : (children P).card=m-P.card := by
  simp [children,Finset.card_sdiff_of_subset]
private theorem famOne (q : ℕ) (P : Finset (Fin m)) (hp : P.card=q) : fam q P={P} := by
  ext S
  simp only [inFam,Finset.mem_singleton]
  exact ⟨fun h => (Finset.eq_of_subset_of_card_le h.1 (by omega)).symm,fun h => h ▸ ⟨Finset.Subset.rfl,hp⟩⟩
private theorem degPos {q : ℕ} {P : Finset (Fin m)} (hm : q≤m) (hp : P.card≤q) : 0<deg q P := by
  unfold deg
  exact_mod_cast Nat.choose_pos (show q-P.card≤m-P.card by omega)
private theorem countChildren {q : ℕ} (P : Finset (Fin m)) (f : Finset (Fin m) → ℚ) :
    (∑ j∈children P,∑ S∈fam q (insert j P),f S)=((q-P.card : ℕ) : ℚ)*∑ S∈fam q P,f S := by
  classical
  have famIns (j : Fin m) : fam q (insert j P)=(fam q P).filter (j∈·) := by
    ext S; simp only [inFam,Finset.mem_filter,Finset.insert_subset_iff]; tauto
  simp_rw [famIns,Finset.sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hs
  have e : (children P).filter (·∈S)=S\P := by ext j; simp [children,and_comm]
  have c : (S\P).card=q-P.card := by
    obtain ⟨sub,cc⟩ := inFam.mp hs
    rw [Finset.card_sdiff_of_subset sub,cc]
  rw [←Finset.sum_filter,e,Finset.sum_const,c,nsmul_eq_mul]
private theorem avgFixed {q : ℕ} (hm : q≤m) (P : Finset (Fin m)) (hp : P.card<q)
    (f : Finset (Fin m) → ℚ) :
    ((m-P.card : ℕ) : ℚ)*((∑S∈fam q P,f S)/deg q P)=
      ∑j∈children P,(∑S∈fam q (insert j P),f S)/deg q (insert j P) := by
  classical
  let k : ℚ := (Nat.choose (m-(P.card+1)) (q-(P.card+1)) : ℕ)
  have hk : 0<k := by
    dsimp [k]; exact_mod_cast Nat.choose_pos (show q-(P.card+1)≤m-(P.card+1) by omega)
  have hd (j : Fin m) (hj : j∈children P) : deg q (insert j P)=k := by
    have ne := (Finset.mem_sdiff.mp hj).2
    simp [deg,k,Finset.card_insert_of_notMem ne]
  have hc (j : Fin m) (hj : j∈children P) : ((fam q (insert j P)).card : ℚ)=k := by
    rw [←hd j hj]
    unfold deg
    rw [famSize]
    have ne := (Finset.mem_sdiff.mp hj).2
    rw [Finset.card_insert_of_notMem ne]; omega
  have hn := countChildren (q:=q) P (fun _ => (1:ℚ))
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hn
  rw [Finset.sum_congr rfl hc,Finset.sum_const,nsmul_eq_mul,childCard,famSize q P (by omega)] at hn
  change ((m-P.card : ℕ) : ℚ)*k=((q-P.card : ℕ) : ℚ)*deg q P at hn
  calc
    _ = (((q-P.card : ℕ) : ℚ)*(∑S∈fam q P,f S))/k := by
      have hd0 := (degPos hm (le_of_lt hp)).ne'
      field_simp [hd0,hk.ne']
      linear_combination (∑S∈fam q P,f S)*hn
    _ = (∑j∈children P,(∑S∈fam q (insert j P),f S))/k := by rw [countChildren]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj; rw [hd j hj]
private theorem descend {q : ℕ} (hm : q≤m) (val tr : Finset (Fin m) → ℚ)
    (terminal : ∀ P, P.card=q → val P=tr P)
    (step : ∀ P, P.card<q → ((m-P.card : ℕ) : ℚ)*val P≤∑j∈children P,val (insert j P))
    (P : Finset (Fin m)) (hp : P.card≤q) :
    ∃S,P⊆S ∧ S.card=q ∧ val P≤tr S := by
  classical
  generalize h : q-P.card=k
  induction k using Nat.strong_induction_on generalizing P with
  | h k ih =>
    by_cases eq : P.card=q
    · exact ⟨P,Finset.Subset.rfl,eq,(terminal P eq).le⟩
    have lt : P.card<q := by omega
    have nn : (children P).Nonempty := by rw [←Finset.card_pos,childCard]; omega
    obtain ⟨j,hj,maxj⟩ := Finset.exists_max_image (children P) (fun j => val (insert j P)) nn
    have b := (step P lt).trans (Finset.sum_le_sum (s:=children P) (fun i hi => maxj i hi))
    rw [Finset.sum_const,nsmul_eq_mul,childCard] at b
    have pos : (0:ℚ)<((m-P.card : ℕ) : ℚ) := by exact_mod_cast (show 0<m-P.card by omega)
    have up := le_of_mul_le_mul_left b pos
    have ne := (Finset.mem_sdiff.mp hj).2
    have sz := Finset.card_insert_of_notMem ne
    obtain ⟨S,sub,cost,yes⟩ := ih (q-(insert j P).card) (by omega) (insert j P) (by omega) rfl
    exact ⟨S,(Finset.subset_insert _ _).trans sub,cost,up.trans yes⟩
end PEqualNP.Outside.L_lib_921
