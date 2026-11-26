import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_4087.Rails

abbrev Pt := Fin 13
def D : Finset Pt := {0,1,3,9}
def core : Finset Pt := {0,2,3,7}
def ctr : Fin 9 → Pt := ![1,4,5,6,8,9,10,11,12]
def rotation : Fin 9 → Fin 3 := ![0,2,0,0,2,2,2,2,0]
def delta (j:Fin 9) : Pt := if rotation j=0 then 1 else if rotation j=1 then 3 else 9
def first (j:Fin 9) : Finset Pt := {ctr j,ctr j+delta j}
def second (j:Fin 9) : Finset Pt := {ctr j+3*delta j,ctr j+9*delta j}
def rail (i:Fin 18) : Finset Pt := if i.val % 2=0 then first (Fin.ofNat 9 (i.val/2)) else second (Fin.ofNat 9 (i.val/2))
def incident (p l:Pt) : Prop := p-l∈D
instance (p l:Pt) : Decidable (incident p l) := by unfold incident; infer_instance
def Arc (P:Finset Pt) : Prop := ∀l:Pt,(P.filter (fun p=>incident p l)).card≤2
def onRail (P:Finset Pt) (i:Fin 18) : Prop := ∃p∈rail i,p∈P
def hits (p:Pt) : Fin 3→Fin 18 := ![![2,13,16],![0,5,15],![0,7,17],![0,0,0],![1,2,8],![3,4,10],![4,6,12],![3,6,14],![5,8,17],![7,9,10],![1,11,12],![9,13,14],![11,15,16]] p
def mates (p:Pt) : Finset Pt := ![{4,11,12},{2,8,12},{1,8,9},∅,{0,8,10},{6,7,9},{5,7,10},{5,6,11},{1,2,4},{2,5,11},{4,6,12},{0,7,9},{0,1,10}] p
def carrier (p:Pt) : Pt := ![0,12,0,0,0,6,0,0,1,2,3,0,0] p

theorem rows : ∀ (p:Pt),p≠3 →
    (mates p).card = 3 := by decide +kernel
theorem line : ∀ (p:Pt),p≠3 → ∀q∈mates p,incident q (carrier p) := by decide +kernel
theorem direct : ∀ (p:Pt),p≠3 → ∀k:Fin 3,p∈rail (hits p k) := by decide +kernel
theorem partners : ∀ (p:Pt),p≠3 → ∀q∈mates p,∃k:Fin 3,∀ t∈rail (hits p k),t=p ∨ t=q := by decide +kernel

/-- The twelve noncentral raw point bits are reconstructed on every point arc by the
three pair signals selected in this nine-line configuration. -/
theorem recovered (P:Finset Pt) (ha:Arc P) (p:Pt) (hp:p≠3) :
    p∈P ↔ ∀k:Fin 3,onRail P (hits p k) := by
  constructor
  · exact fun h k=>⟨p,direct p hp k,h⟩
  · intro all
    by_contra hn
    have sub : mates p ⊆ P.filter (fun t=>incident t (carrier p)) := by
      intro q hq
      obtain ⟨k,hk⟩:=partners p hp q hq
      obtain ⟨u,hu,hm⟩:=all k
      rcases hk u hu with rfl|rfl
      · exact False.elim (hn hm)
      · exact Finset.mem_filter.mpr ⟨hm,line p hp _ hq⟩
    have count:=Finset.card_le_card sub
    rw [rows p hp] at count
    have small:=ha (carrier p)
    omega

theorem uncovered : ∀ l:Pt,l∈core ↔ ¬∃j:Fin 9,ctr j=l := by decide +kernel
theorem common : ∀ l∈core,incident 3 l := by decide +kernel
end PEqualNP.Outside.L_meta_4087.Rails
