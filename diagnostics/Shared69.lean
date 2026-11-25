import Mathlib
import PEqualNP.Outside.L_meta_971

namespace Shared9798
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_971_aux

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
def TwoAt (G : Fin n → Fin n → Prop) (I : Finset (Fin n)) (u : Fin n) : Prop :=
  ∃ a∈I, ∃ b∈I, ∃ c, a≠b ∧ a≠c ∧ b≠c ∧ G u a ∧ G u b ∧ G u c

def exits (D : Dag) (u : Fin n) := exitArcs n D (carrierT n D {u})

theorem saturated (hg : sem_Gr G) (live : StrictLive n D) (hc : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {pos : Fin n → ℕ × Bool} (hp : k4_Pos n G D pos)
    (budget : Bplus n D ≤ (eligSet n D).card+1) {u : Fin n}
    (h : TwoAt G (ineligSet n D) u) :
    (exits D u).card=3 ∧ merges n D (carrierT n D {u})=∅ ∧
      ∃ ρ∈residualUnits n D b, u ∈ supp n D ρ.1 := by
  classical
  obtain ⟨a,ha,v,hv,c,av,ac,vc,ua,uv,uc⟩ := h
  have lo := k4_three_cons hg live hc hp ha hv av ac vc ua uv uc
  have hi := k4_budget hg live hc b hb {u}
  have flow := carrier_flow_union live ({u} : Finset (Fin n))
    (by rw [sem_supp_out hg hc, Finset.empty_inter])
  rw [Finset.card_singleton] at hi flow
  have eq := surplus_carrierT_eq live.1 b hb ({u} : Finset (Fin n))
  have cap : (({u} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  unfold exits
  refine ⟨by omega,Finset.card_eq_zero.mp (by omega),?_⟩
  obtain ⟨ρ,hr⟩ := Finset.card_pos.mp (by omega :
    0 < ((residualUnits n D b).filter (fun z => (supp n D z.1 ∩ {u}).Nonempty)).card)
  obtain ⟨inside,ww⟩ := Finset.mem_filter.mp hr
  obtain ⟨v,hv⟩ := ww
  obtain ⟨support,eqv⟩ := Finset.mem_inter.mp hv
  exact ⟨ρ,inside,(Finset.mem_singleton.mp eqv) ▸ support⟩

theorem overlapping (hg : sem_Gr G) (live : StrictLive n D) (hc : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {pos : Fin n → ℕ × Bool} (hp : k4_Pos n G D pos)
    (budget : Bplus n D ≤ (eligSet n D).card+1) {u v : Fin n}
    (hu : TwoAt G (ineligSet n D) u) (hv : TwoAt G (ineligSet n D) v) :
    (exits D u).card = 3 ∧ (exits D v \ exits D u).card ≤ 1 := by
  classical
  obtain ⟨size,mu,r,hr,cu⟩ := saturated hg live hc b hb hp budget hu
  obtain ⟨szv,mv,t,ht,cv⟩ := saturated hg live hc b hb hp budget hv
  have residual := card_residual live.1 b hb
  have eq : r=t := Finset.card_le_one.mp (by omega) r hr t ht
  rw [←eq] at cv
  have fan : 2 ≤ fanout D r.1 := by
    unfold residualUnits unitsPlus at hr
    have := (mem_units.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1).1).2
    omega
  obtain ⟨a,c,ne,au,av,cu',cv'⟩ := k4_joint_exits hg live hc mu mv cu cv fan
  have common : 2≤(exits D v ∩ exits D u).card := Finset.one_lt_card.mpr
    ⟨a,Finset.mem_inter.mpr ⟨av,au⟩,c,Finset.mem_inter.mpr ⟨cv',cu'⟩,ne⟩
  have split := Finset.card_sdiff_add_card_inter (exits D v) (exits D u)
  exact ⟨size,by omega⟩

def Pack (G : Fin n → Fin n → Prop) (I : Finset (Fin n)) : Prop :=
 ∃ u v w : Fin n, TwoAt G I u ∧ TwoAt G I v ∧ TwoAt G I w ∧
  6 ≤ (I.filter (fun i => by classical exact (decide (G i u ∨ G i v ∨ G i w) = true))).card

theorem packed (hg : sem_Gr G) (live : StrictLive n D) (hc : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {pos : Fin n → ℕ × Bool} (hp : k4_Pos n G D pos)
    (pack : Pack G (ineligSet n D)) : (eligSet n D).card+2 ≤ Bplus n D := by
  classical
  by_contra h
  have budget : Bplus n D≤(eligSet n D).card+1 := by omega
  obtain ⟨u,v,w,hu,hv,hw,six⟩ := pack
  let J := (ineligSet n D).filter (fun i => by classical exact (decide (G i u ∨ G i v ∨ G i w) = true))
  change 6≤J.card at six
  have inj : Set.InjOn pos (↑J) := fun x hx y hy eq =>
    hp.2 x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 eq
  have push := Finset.card_image_of_injOn inj
  let X := exits D u
  let Y := exits D v \ X
  let Z := exits D w \ X
  have sub : J.image pos ⊆ (X∪Y)∪Z := by
    intro p hp'
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp'
    obtain ⟨hi,hg'⟩ := Finset.mem_filter.mp hi
    have hhit : G i u ∨ G i v ∨ G i w := of_decide_eq_true hg'
    by_cases hx : pos i ∈ X
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    rcases hhit with g|g|g
    · exact False.elim (hx (k4_pos_exit hp hi g (Finset.mem_singleton_self u)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨k4_pos_exit hp hi g (Finset.mem_singleton_self v),hx⟩))
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨k4_pos_exit hp hi g (Finset.mem_singleton_self w),hx⟩)
  obtain ⟨xs,ys⟩ := overlapping hg live hc b hb hp budget hu hv
  obtain ⟨_,zs⟩ := overlapping hg live hc b hb hp budget hu hw
  change X.card=3 at xs
  change Y.card≤1 at ys
  change Z.card≤1 at zs
  have sur := Finset.card_le_card sub
  have c1 := Finset.card_union_le X Y
  have c2 := Finset.card_union_le (X∪Y) Z
  omega

end Shared9798
