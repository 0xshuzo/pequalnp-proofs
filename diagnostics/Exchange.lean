import Mathlib
import PEqualNP.Defs

namespace Exchange1593

def Indep {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

theorem no3 {n : ℕ} (G : SimpleGraph (Fin n)) (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (a b c : Fin n) (e0 : G.Adj a b) (e1 : G.Adj b c) (e2 : G.Adj c a) (n01 : a ≠ b) (n02 : a ≠ c) (n12 : b ≠ c) : False := by
  let W : G.Walk a a := SimpleGraph.Walk.cons e0 (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2 SimpleGraph.Walk.nil))
  have valid : W.IsCycle := by
    change (SimpleGraph.Walk.cons e0 _).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff,n01,n01.symm,n02,n02.symm,n12,n12.symm]
    · simp [Sym2.eq_iff,n01,n01.symm,n02,n02.symm,n12,n12.symm]
  have h := girth a W valid
  simp [W] at h

theorem no4 {n : ℕ} (G : SimpleGraph (Fin n)) (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (a b c d : Fin n) (e0 : G.Adj a b) (e1 : G.Adj b c) (e2 : G.Adj c d) (e3 : G.Adj d a) (n01 : a ≠ b) (n02 : a ≠ c) (n03 : a ≠ d) (n12 : b ≠ c) (n13 : b ≠ d) (n23 : c ≠ d) : False := by
  let W : G.Walk a a := SimpleGraph.Walk.cons e0 (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2 (SimpleGraph.Walk.cons e3 SimpleGraph.Walk.nil)))
  have valid : W.IsCycle := by
    change (SimpleGraph.Walk.cons e0 _).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n12,n12.symm,n13,n13.symm,n23,n23.symm]
    · simp [Sym2.eq_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n12,n12.symm,n13,n13.symm,n23,n23.symm]
  have h := girth a W valid
  simp [W] at h

theorem no5 {n : ℕ} (G : SimpleGraph (Fin n)) (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (a b c d e : Fin n) (e0 : G.Adj a b) (e1 : G.Adj b c) (e2 : G.Adj c d) (e3 : G.Adj d e) (e4 : G.Adj e a) (n01 : a ≠ b) (n02 : a ≠ c) (n03 : a ≠ d) (n04 : a ≠ e) (n12 : b ≠ c) (n13 : b ≠ d) (n14 : b ≠ e) (n23 : c ≠ d) (n24 : c ≠ e) (n34 : d ≠ e) : False := by
  let W : G.Walk a a := SimpleGraph.Walk.cons e0 (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2 (SimpleGraph.Walk.cons e3 (SimpleGraph.Walk.cons e4 SimpleGraph.Walk.nil))))
  have valid : W.IsCycle := by
    change (SimpleGraph.Walk.cons e0 _).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n04,n04.symm,n12,n12.symm,n13,n13.symm,n14,n14.symm,n23,n23.symm,n24,n24.symm,n34,n34.symm]
    · simp [Sym2.eq_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n04,n04.symm,n12,n12.symm,n13,n13.symm,n14,n14.symm,n23,n23.symm,n24,n24.symm,n34,n34.symm]
  have h := girth a W valid
  simp [W] at h

theorem swap {n : ℕ} (G : SimpleGraph (Fin n)) (D I : Finset (Fin n)) (Iin : I⊆D)
    (free : Indep G I) (best : ∀ S⊆D, Indep G S → S.card ≤ I.card)
    (B Y : Finset (Fin n)) (Bin : B⊆D \ I) (Yin : Y⊆I) (ok : Indep G B)
    (hit : ∀ b∈B, ∀ i∈I, G.Adj b i → i∈Y) : B.card ≤ Y.card := by
  classical
  let J := I \ Y
  have old : J⊆I := Finset.sdiff_subset
  have fresh : B⊆D := Bin.trans Finset.sdiff_subset
  have apart : Disjoint J B := Finset.disjoint_left.mpr (fun ha hb => (Finset.mem_sdiff.mp (Bin hb)).2 (old ha))
  have no {x y} (hx : x∈J) (hy : y∈B) : ¬G.Adj x y := fun e =>
    (Finset.mem_sdiff.mp hx).2 (hit y hy x (old hx) e.symm)
  have mix : Indep G (J ∪ B) := by
    intro x hx y hy
    rcases Finset.mem_union.mp hx with xj|xb <;> rcases Finset.mem_union.mp hy with yj|yb
    · exact free x (old xj) y (old yj)
    · exact no xj yb
    · exact fun e => no yj xb e.symm
    · exact ok x xb y yb
  have h := best (J ∪ B) (Finset.union_subset (old.trans Iin) fresh) mix
  rw [Finset.card_union_of_disjoint apart] at h
  have rem : J.card = I.card-Y.card := Finset.card_sdiff_of_subset Yin
  have := Finset.card_le_card Yin
  omega

theorem cheap_pair {n : ℕ} (G : SimpleGraph (Fin n)) (D I : Finset (Fin n))
    (sub : I⊆D) (free : Indep G I) (best : ∀ S⊆D, Indep G S → S.card ≤ I.card)
    (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (u a b x y p q : Fin n) (ui : u∈I) (ai : a∈I) (bi : b∈I)
    (xt : x∈D \ I) (yt : y∈D \ I) (pt : p∈D \ I) (qt : q∈D \ I)
    (ua : u≠a) (ub : u≠b) (ab : a≠b) (xy : x≠y)
    (xu : G.Adj x u) (xa : G.Adj x a) (yu : G.Adj y u) (yb : G.Adj y b)
    (pa : G.Adj p a) (qb : G.Adj q b)
    (oneP : ∀ i∈I, G.Adj p i → i=a) (oneQ : ∀ i∈I, G.Adj q i → i=b)
    (twoX : ∀ i∈I, G.Adj x i → i=u ∨ i=a)
    (twoY : ∀ i∈I, G.Adj y i → i=u ∨ i=b) : G.Adj p q := by
  classical
  have cross {z w} (zz : z∈D \ I) (ww : w∈I) : z≠w := fun eq => (Finset.mem_sdiff.mp zz).2 (eq.symm ▸ ww)
  have xp : x≠p := fun eq => ua (oneP u ui (eq ▸ xu))
  have xq : x≠q := fun eq => ub (oneQ u ui (eq ▸ xu))
  have yp : y≠p := fun eq => ua (oneP u ui (eq ▸ yu))
  have yq : y≠q := fun eq => ub (oneQ u ui (eq ▸ yu))
  have pq : p≠q := fun eq => ab (oneQ a ai (eq ▸ pa))
  have noXY : ¬G.Adj x y := fun e => no3 G girth x y u e yu xu.symm xy xu.ne yu.ne
  have noXP : ¬G.Adj x p := fun e => no3 G girth x p a e pa xa.symm xp xa.ne pa.ne
  have noYQ : ¬G.Adj y q := fun e => no3 G girth y q b e qb yb.symm yq yb.ne qb.ne
  have noXQ : ¬G.Adj x q := fun e => no5 G girth x u y b q xu yu.symm yb qb.symm e.symm
      xu.ne xy (cross xt bi) xq yu.ne.symm ub (cross qt ui).symm yb.ne yq qb.ne.symm
  have noYP : ¬G.Adj y p := fun e => no5 G girth y u x a p yu xu.symm xa pa.symm e.symm
      yu.ne xy.symm (cross yt ai) yp xu.ne.symm ua (cross pt ui).symm xa.ne xp pa.ne.symm
  by_contra noPQ
  let B : Finset (Fin n) := {x,y,p,q}
  let Y : Finset (Fin n) := {u,a,b}
  have Bin : B⊆D \ I := by intro z hz; rcases (by simpa [B] using hz : z=x ∨ z=y ∨ z=p ∨ z=q) with rfl|rfl|rfl|rfl <;> assumption
  have Yin : Y⊆I := by intro z hz; rcases (by simpa [Y] using hz : z=u ∨ z=a ∨ z=b) with rfl|rfl|rfl <;> assumption
  have ok : Indep G B := by
    intro z hz w hw
    rcases (by simpa [B] using hz : z=x ∨ z=y ∨ z=p ∨ z=q) with rfl|rfl|rfl|rfl <;>
      rcases (by simpa [B] using hw : w=x ∨ w=y ∨ w=p ∨ w=q) with rfl|rfl|rfl|rfl <;>
      first | exact G.loopless.irrefl _ | assumption | exact fun e => noXY e.symm |
        exact fun e => noXP e.symm | exact fun e => noXQ e.symm | exact fun e => noYP e.symm |
        exact fun e => noYQ e.symm | exact fun e => noPQ e.symm
  have cover : ∀ z∈B, ∀ i∈I, G.Adj z i → i∈Y := by
    intro z hz i hi edge
    rcases (by simpa [B] using hz : z=x ∨ z=y ∨ z=p ∨ z=q) with rfl|rfl|rfl|rfl
    · rcases twoX i hi edge with h|h <;> simp [Y,h]
    · rcases twoY i hi edge with h|h <;> simp [Y,h]
    · simp [Y,oneP i hi edge]
    · simp [Y,oneQ i hi edge]
  have lim := swap G D I sub free best B Y Bin Yin ok cover
  simp [B,Y,xy,xp,xq,yp,yq,pq,ua,ub,ab] at lim

end Exchange1593
