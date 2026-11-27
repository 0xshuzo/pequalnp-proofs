import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8009.Count
abbrev Pt := Fin 13
def Inc (p l : Pt) : Prop := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
instance (p l : Pt) : Decidable (Inc p l) := by unfold Inc; infer_instance
theorem squareFree : ∀ a b p q : Pt, a≠b → p≠q →
    ¬(Inc a p ∧ Inc a q ∧ Inc b p ∧ Inc b q) := by decide +kernel

abbrev Board := Finset (Pt×Pt)
def rel (d : Bool) (p l : Pt) : Prop := if d then Inc l p else Inc p l
instance (d : Bool) (p l : Pt) : Decidable (rel d p l) := by unfold rel; infer_instance
def tr (E : Board) := E.image Prod.swap
theorem memTr {p l : Pt} {E : Board} : (l,p)∈tr E ↔ (p,l)∈E := by
  constructor
  · rintro h
    obtain ⟨⟨a,b⟩,e,eq⟩ := Finset.mem_image.mp h
    cases eq
    exact e
  · exact fun h => Finset.mem_image.mpr ⟨(p,l),h,rfl⟩
theorem cardTr (E : Board) : (tr E).card=E.card :=
  Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.swap h)

def fibre (E : Board) (p : Pt) := Finset.univ.filter fun l : Pt => (p,l)∈E
def fat (E : Board) := ∃ p, 4≤(fibre E p).card
def wrong (d : Bool) (E : Board) := ∀ e∈E, ¬rel d e.1 e.2
def compatible (d : Bool) (E F : Board) := ∀ e∈E, ∀ f∈F, rel d e.1 f.2 ∨ rel d f.1 e.2
theorem wrongTr {d E} (h : wrong d E) : wrong (!d) (tr E) := by
  rintro ⟨l,p⟩ mem
  have no := h (p,l) (memTr.mp mem)
  cases d <;> simpa [rel] using no
theorem compatSwap {d E F} (h : compatible d E F) : compatible d F E :=
  fun f hf e he => (h e he f hf).symm
theorem compatTr {d E F} (h : compatible d E F) : compatible (!d) (tr E) (tr F) := by
  rintro ⟨l,p⟩ e ⟨m,q⟩ f
  have z := (h (p,l) (memTr.mp e) (q,m) (memTr.mp f)).symm
  cases d <;> simpa [rel] using z

def cylinders (E : Board) (P : Finset Pt) : Board := P.biUnion fun p => (fibre E p).image (fun l => (p,l))
theorem inCyl {p l : Pt} {E : Board} {P : Finset Pt} (h : (p,l)∈E) (hp : p∈P) :
    (p,l)∈cylinders E P := Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_image.mpr
      ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩⟩
theorem cylCost (E : Board) (P : Finset Pt) (no : ¬fat E) : (cylinders E P).card≤3*P.card := by
  calc
    _ ≤ ∑ p∈P, ((fibre E p).image fun l => (p,l)).card := Finset.card_biUnion_le
    _ ≤ ∑ _p∈P, 3 := Finset.sum_le_sum (fun p _ => Finset.card_image_le.trans (by
      have h : ¬4≤(fibre E p).card := fun z => no ⟨p,z⟩
      omega))
    _ = _ := by simp [Nat.mul_comm]

theorem coverFat {E : Board} (big : 13≤E.card) {P L : Finset Pt}
    (cov : ∀ e∈E, e.1∈P ∨ e.2∈L) (sz : P.card+L.card≤4) : fat E ∨ fat (tr E) := by
  by_contra! absent
  have sub : E ⊆ cylinders E P ∪ tr (cylinders (tr E) L) := by
    rintro ⟨p,l⟩ h
    rcases cov (p,l) h with hp|hl
    · exact Finset.mem_union_left _ (inCyl h hp)
    · exact Finset.mem_union_right _ (memTr.mpr (inCyl (memTr.mpr h) hl))
  have cap := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  rw [cardTr] at cap
  have x := cylCost E P absent.1
  have y := cylCost (tr E) L absent.2
  omega

theorem fourAxes : ∀ d : Bool, ∀ p : Pt, (Finset.univ.filter (fun l : Pt => rel d p l)).card=4 ∧
    (Finset.univ.filter (fun l : Pt => ¬rel d p l)).card=9 := by decide +kernel
theorem missCommon : ∀ d : Bool, ∀ p q : Pt,
    (Finset.univ.filter (fun l : Pt => ¬rel d p l ∧ rel d q l)).card≤3 := by decide +kernel
theorem squareDir (d : Bool) (p q l m : Pt) (pq : p≠q) (lm : l≠m) :
    ¬(rel d p l ∧ rel d p m ∧ rel d q l ∧ rel d q m) := by
  cases d
  · exact squareFree p q l m pq lm
  · rintro ⟨a,b,c,e⟩
    exact squareFree l m p q lm pq ⟨a,c,b,e⟩
theorem forcesPencil {d : Bool} {E F : Board} (error : wrong d E) (cross : compatible d E F)
    (p : Pt) (large : 4≤(fibre E p).card) : ∀ f∈F, rel d p f.2 := by
  intro f mem
  by_contra no
  have sub : fibre E p ⊆ Finset.univ.filter (fun l : Pt => ¬rel d p l ∧ rel d f.1 l) := by
    intro l hl
    have e := (Finset.mem_filter.mp hl).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,error (p,l) e,(cross (p,l) e f mem).resolve_left no⟩
  have cost := (Finset.card_le_card sub).trans (missCommon d p f.1)
  omega

def extras (E : Board) (p : Pt) := (E.filter fun e => e.1≠p).image Prod.snd

theorem extraTwo {d : Bool} {E : Board} {p l : Pt} (error : wrong d E) (inc : rel d p l)
    (pencil : ∀ e∈E, rel d e.1 l) (big : 13≤E.card) : 2≤(extras E p).card := by
  let X := (Finset.univ : Finset Pt).filter (fun n => ¬rel d p n)
  let Y := (Finset.univ : Finset Pt).filter (fun r => rel d r l ∧ r≠p)
  have cn : X.card=9 := (fourAxes d p).2
  have yn : Y.card≤3 := by
    have ff : ∀ d : Bool, ∀ p l : Pt, rel d p l →
        (Finset.univ.filter (fun r : Pt => rel d r l ∧ r≠p)).card=3 := by decide +kernel
    exact (ff d p l inc).le
  have sub : E ⊆ ({p}:Finset Pt) ×ˢ X ∪ Y ×ˢ (extras E p) := by
    rintro ⟨r,n⟩ en
    by_cases rEq : r=p
    · subst r
      exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨by simp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,error _ en⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,pencil _ en,rEq⟩,
         Finset.mem_image.mpr ⟨(r,n),Finset.mem_filter.mpr ⟨en,rEq⟩,rfl⟩⟩)
  have cost := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  simp only [Finset.card_product,Finset.card_singleton,one_mul,cn] at cost
  by_contra! tiny
  have small := Nat.mul_le_mul yn (show (extras E p).card≤1 by omega)
  omega

theorem rowImpossible {d : Bool} {E F : Board} (e : wrong d E) (f : wrong d F) (cross : compatible d E F)
    (e13 : 13≤E.card) (f13 : 13≤F.card) (heavy : fat E) : False := by
  obtain ⟨p,hp⟩ := heavy
  have allF := forcesPencil e cross p hp
  let P := Finset.univ.filter (fun m : Pt => rel d p m)
  have sz : P.card=4 := (fourAxes d p).1
  have fHeavy : fat (tr F) := by
    by_contra nf
    have sub : tr F ⊆ cylinders (tr F) P := by
      rintro ⟨m,q⟩ h
      exact inCyl h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,allF (q,m) (memTr.mp h)⟩)
    have cost := (Finset.card_le_card sub).trans (cylCost (tr F) P nf)
    rw [cardTr,sz] at cost
    omega
  obtain ⟨l,hl⟩ := fHeavy
  have el (r n : Pt) (h : (r,n)∈E) : rel d r l := by
    have z := forcesPencil (wrongTr f) (compatTr (compatSwap cross)) l hl (n,r) (memTr.mpr h)
    cases d <;> simpa [rel] using z
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (show 0<(fibre (tr F) l).card by omega)
  have pl := allF (q,l) (memTr.mp (Finset.mem_filter.mp hq).2)
  have exA := extraTwo e pl (fun a ha => el a.1 a.2 ha) e13
  have lp : rel (!d) l p := by cases d <;> simpa [rel] using pl
  have ff : ∀ a∈tr F, rel (!d) a.1 p := by
    rintro ⟨m,v⟩ hm
    have z := allF (v,m) (memTr.mp hm)
    cases d <;> simpa [rel] using z
  have exB := extraTwo (wrongTr f) lp ff (by rwa [cardTr])
  have rectangle (v : Pt) (hv : v∈extras (tr F) l) (n : Pt) (hn : n∈extras E p) : rel d v n := by
    obtain ⟨⟨m,z⟩,hz,zz⟩ := Finset.mem_image.mp hv
    change z=v at zz
    subst z
    obtain ⟨⟨r,k⟩,hk,kk⟩ := Finset.mem_image.mp hn
    change k=n at kk
    subst k
    obtain ⟨hm,ml⟩ := Finset.mem_filter.mp hz
    obtain ⟨hr,rp⟩ := Finset.mem_filter.mp hk
    have vf := memTr.mp hm
    have possible := cross (r,n) hr (v,m) vf
    apply possible.resolve_left
    intro rm
    exact squareDir d r p m l rp ml ⟨rm,el r n hr,allF _ vf,pl⟩
  obtain ⟨v,hv,w,hw,vw⟩ := Finset.one_lt_card.mp exB
  obtain ⟨n,hn,m,hm,nm⟩ := Finset.one_lt_card.mp exA
  exact squareDir d v w n m vw nm ⟨rectangle v hv n hn,rectangle v hv m hm,
    rectangle w hw n hn,rectangle w hw m hm⟩

theorem atMostTwelve {E F : Board} (e : wrong false E) (f : wrong false F)
    (cross : compatible false E F) {P L : Finset Pt} (cov : ∀ z∈E, z.1∈P ∨ z.2∈L)
    (sz : P.card+L.card≤4) : E.card≤12 ∨ F.card≤12 := by
  by_contra! both
  obtain fe|fe := coverFat both.1 cov sz
  · exact rowImpossible e f cross both.1 both.2 fe
  · exact rowImpossible (wrongTr e) (wrongTr f) (compatTr cross) (by rwa [cardTr]) (by rwa [cardTr]) fe


end PEqualNP.Outside.L_meta_8009.Count
