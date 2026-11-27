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
private def xx (P A S : Finset (V m)) := (A∩S) \ P
private def yy (P A B S : Finset (V m)) := S \ (P∪A∪B)
private def both (P A B : Finset (V m)) := (A∩B) \ P
private def neither (P A B : Finset (V m)) := (Finset.univ : Finset (V m)) \ (P∪A∪B)
private theorem splitSets (P A B S : Finset (V m)) (sub : P⊆S) (hs : A∩S=B∩S) :
    let X := xx P A S
    let Y := yy P A B S
    X⊆both P A B ∧ Y⊆neither P A B ∧ P∪X∪Y=S ∧
    (A∩P)∪X=A∩S ∧ (A∩P)=(B∩P) := by
  dsimp [xx,yy,both,neither]
  simp only [Finset.ext_iff,Finset.subset_iff,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_univ,true_and] at *
  grind
private theorem joinSets (P A B X Y : Finset (V m)) (hx : X⊆both P A B) (hy : Y⊆neither P A B) :
    let S := P∪X∪Y
    P⊆S ∧ A∩S=(A∩P)∪X ∧ B∩S=(B∩P)∪X ∧
    xx P A S=X ∧ yy P A B S=Y ∧ Disjoint P X ∧ Disjoint (P∪X) Y ∧ Disjoint (A∩P) X := by
  dsimp [xx,yy,both,neither] at *
  simp only [Finset.ext_iff,Finset.subset_iff,Finset.disjoint_left,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_univ,true_and] at *
  grind
private def good (q t : ℕ) (P A B : Finset (V m)) := (fam q P).filter fun S => A∩S=B∩S ∧ (A∩S).card=t
private def formula (q t : ℕ) (P A B : Finset (V m)) :=
  let locked := A∩P
  let e := t-locked.card
  let l := q-P.card
  if locked=B∩P ∧ locked.card≤t ∧ e≤l then ((both P A B).card.choose e)*((neither P A B).card.choose (l-e)) else 0
private theorem goodSize (q t : ℕ) (P A B : Finset (V m)) (hp : P.card≤q) :
    (good q t P A B).card=formula q t P A B := by
  classical
  let e := t-(A∩P).card
  let l := q-P.card
  have enc (S : Finset (V m)) (hs : S∈good q t P A B) :
      let X := xx P A S
      let Y := yy P A B S
      X∈(both P A B).powersetCard e ∧ Y∈(neither P A B).powersetCard (l-e) ∧
      P∪X∪Y=S ∧ A∩P=B∩P ∧ (A∩P).card≤t ∧ e≤l := by
    have ⟨f,se,tc⟩ := Finset.mem_filter.mp hs
    obtain ⟨inc,sc⟩ := inFam.mp f
    obtain ⟨hx,hy,j,k,lock⟩ := splitSets P A B S inc se
    obtain ⟨_,_,_,_,_,dx,dy,dh⟩ := joinSets P A B _ _ hx hy
    have a := congrArg Finset.card j
    have b := congrArg Finset.card k
    rw [Finset.card_union_of_disjoint dy,Finset.card_union_of_disjoint dx,sc] at a
    rw [Finset.card_union_of_disjoint dh,tc] at b
    dsimp [e,l]
    exact ⟨Finset.mem_powersetCard.mpr ⟨hx,by omega⟩,Finset.mem_powersetCard.mpr ⟨hy,by omega⟩,j,lock,by omega,by omega⟩
  by_cases h : A∩P=B∩P ∧ (A∩P).card≤t ∧ e≤l
  · rw [formula,if_pos h]
    change (good q t P A B).card=(both P A B).card.choose e*(neither P A B).card.choose (l-e)
    rw [←Finset.card_powersetCard,←Finset.card_powersetCard,←Finset.card_product]
    apply Finset.card_bij (fun S _ => (xx P A S,yy P A B S))
    · intro S hs
      exact Finset.mem_product.mpr ⟨(enc S hs).1,(enc S hs).2.1⟩
    · intro S hs T ht eq
      obtain ⟨a,b⟩ := Prod.mk.inj eq
      rw [←(enc S hs).2.2.1,a,b,(enc T ht).2.2.1]
    · rintro ⟨X,Y⟩ xy
      obtain ⟨xm,ym⟩ := Finset.mem_product.mp xy
      obtain ⟨xs,xc⟩ := Finset.mem_powersetCard.mp xm
      obtain ⟨ys,yc⟩ := Finset.mem_powersetCard.mp ym
      obtain ⟨inc,a,b,x,y,dx,dy,dh⟩ := joinSets P A B X Y xs ys
      refine ⟨P∪X∪Y,Finset.mem_filter.mpr ⟨inFam.mpr ⟨inc,?_⟩,?_,?_⟩,Prod.ext x y⟩
      · rw [Finset.card_union_of_disjoint dy,Finset.card_union_of_disjoint dx,xc,yc]
        dsimp [e,l] at *; omega
      · rw [a,b,h.1]
      · rw [a,Finset.card_union_of_disjoint dh,xc]; dsimp [e]; omega
  · rw [formula,if_neg h,Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hs
    exact h (enc S hs).2.2.2
end PEqualNP.Outside.L_lib_921
