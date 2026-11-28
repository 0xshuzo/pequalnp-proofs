import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8869.Matching
open Finset
variable {α β : Type} [DecidableEq α] [DecidableEq β]

def Induced (R : α → β → Prop) (E : Finset (α × β)) (d : Nat) : Prop :=
  ∃ a : Fin d → α, ∃ b : Fin d → β,(∀ i,(a i,b i)∈E) ∧ ∀ i j,R (a i) (b j) → i=j

def Linear (R : α → β → Prop) : Prop := ∀ a a' b b',a≠a' → R a b → R a b' → R a' b → R a' b' → b=b'

theorem other {γ : Type} [DecidableEq γ] (S : Finset γ) (h : 2≤S.card) (g : γ) :
    ∃ x∈S,x≠g := by
  classical
  by_contra! all
  have sub : S⊆{g} := fun x hx => mem_singleton.mpr (all x hx)
  have bound := card_le_card sub
  simp only [card_singleton] at bound
  omega

theorem induced_min (R : α → β → Prop) [DecidableRel R] (E : Finset (α × β))
    (lin : Linear R) (inc : ∀ e∈E,R e.1 e.2) (d : Nat) (P : Finset α) (L : Finset β)
    (alive : 0<d → P.Nonempty)
    (rows : ∀ a∈P,d≤(L.filter (fun b => (a,b)∈E)).card)
    (cols : ∀ b∈L,d≤(P.filter (fun a => (a,b)∈E)).card) :
    ∃ a : Fin d → α, ∃ b : Fin d → β,
      (∀ i,a i∈P ∧ b i∈L ∧ (a i,b i)∈E) ∧ ∀ i j,R (a i) (b j) → i=j := by
  classical
  induction d generalizing P L with
  | zero => exact ⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0⟩
  | succ d ih =>
    obtain ⟨u,up⟩ := alive (by omega)
    have rowU := rows u up
    obtain ⟨v,hv⟩ := card_pos.mp (show 0<(L.filter (fun b => (u,b)∈E)).card by omega)
    obtain ⟨vl,uv⟩ := mem_filter.mp hv
    have ur := inc (u,v) uv
    let P' := P.filter (fun p => ¬R p v)
    let L' := L.filter (fun b => ¬R u b)
    have alive' (pos : 0<d) : P'.Nonempty := by
      obtain ⟨t,ht,vt⟩ := other _ (show 2≤(L.filter (fun b => (u,b)∈E)).card by omega) v
      obtain ⟨tl,ut⟩ := mem_filter.mp ht
      have colT := cols t tl
      obtain ⟨p,hp,pu⟩ := other _ (show 2≤(P.filter (fun a => (a,t)∈E)).card by omega) u
      obtain ⟨pp,pt⟩ := mem_filter.mp hp
      exact ⟨p,mem_filter.mpr ⟨pp,fun pv => vt (lin p u t v pu (inc (p,t) pt) pv (inc (u,t) ut) ur)⟩⟩
    have row' (p : α) (hp : p∈P') : d≤(L'.filter (fun b => (p,b)∈E)).card := by
      obtain ⟨pp,pv⟩ := mem_filter.mp hp
      have pu : p≠u := fun eq => pv (eq ▸ ur)
      let A := L.filter (fun b => (p,b)∈E)
      let B := L'.filter (fun b => (p,b)∈E)
      have sub : B⊆A := fun b hb => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hb).1).1,(mem_filter.mp hb).2⟩
      have lose (b : β) (hb : b∈A\B) : R p b ∧ R u b := by
        obtain ⟨ha,hno⟩ := mem_sdiff.mp hb
        obtain ⟨bl,eb⟩ := mem_filter.mp ha
        exact ⟨inc (p,b) eb,by by_contra no; exact hno (mem_filter.mpr ⟨mem_filter.mpr ⟨bl,no⟩,eb⟩)⟩
      have one : (A\B).card≤1 := card_le_one.mpr (fun b hb c hc => lin p u b c pu
        (lose b hb).1 (lose c hc).1 (lose b hb).2 (lose c hc).2)
      have eq := card_sdiff_add_card_eq_card sub
      have low : d+1≤A.card := rows p pp
      change d≤B.card
      omega
    have col' (b : β) (hb : b∈L') : d≤(P'.filter (fun p => (p,b)∈E)).card := by
      obtain ⟨bl,ub⟩ := mem_filter.mp hb
      have bv : b≠v := fun e => ub (e ▸ ur)
      let A := P.filter (fun p => (p,b)∈E)
      let B := P'.filter (fun p => (p,b)∈E)
      have sub : B⊆A := fun p hp => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
      have lose (p : α) (hp : p∈A\B) : R p b ∧ R p v := by
        obtain ⟨ha,hno⟩ := mem_sdiff.mp hp
        obtain ⟨pp,eb⟩ := mem_filter.mp ha
        exact ⟨inc (p,b) eb,by by_contra no; exact hno (mem_filter.mpr ⟨mem_filter.mpr ⟨pp,no⟩,eb⟩)⟩
      have one : (A\B).card≤1 := card_le_one.mpr (fun p hp r hr => by
        by_contra ne
        exact bv (lin p r b v ne (lose p hp).1 (lose p hp).2 (lose r hr).1 (lose r hr).2))
      have eq := card_sdiff_add_card_eq_card sub
      have low : d+1≤A.card := cols b bl
      change d≤B.card
      omega
    obtain ⟨a,b,good,ind⟩ := ih P' L' alive' row' col'
    refine ⟨Fin.cases u a,Fin.cases v b,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨up,vl,uv⟩
      · exact ⟨(mem_filter.mp (good j).1).1,(mem_filter.mp (good j).2.1).1,(good j).2.2⟩
    · intro i j
      refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
      · exact fun _ => rfl
      · exact fun h => False.elim ((mem_filter.mp (good l).2.1).2 h)
      · exact fun h => False.elim ((mem_filter.mp (good k).1).2 h)
      · exact fun h => congrArg Fin.succ (ind k l h)

end PEqualNP.Outside.L_meta_8869.Matching
