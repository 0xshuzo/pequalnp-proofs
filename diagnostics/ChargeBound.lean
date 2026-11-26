import PEqualNP.Outside.L_meta_1491
import PEqualNP.Outside.L_meta_6838
import PEqualNP.Outside.L_meta_18800
import PEqualNP.Outside.L_meta_1527
import PEqualNP.Outside.L_meta_8567
import PEqualNP.Outside.L_meta_8725
import PEqualNP.Outside.L_meta_8933
import PEqualNP.Outside.L_meta_6369
namespace PEqualNP.Outside.L_meta_9738_read
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
set_option maxRecDepth 32768
set_option maxHeartbeats 0
abbrev V := Fin 25
def edges : List (Nat × Nat) := [(0, 16), (0, 22), (0, 24), (1, 13), (1, 17), (1, 23), (2, 13), (2, 14), (2, 18), (2, 24), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 17), (8, 19), (8, 20), (8, 24), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23), (12, 15), (12, 21), (12, 23), (12, 24)]
def rel (a b : V) := (a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges
instance (a b : V) : Decidable (rel a b) := by unfold rel; infer_instance
def G : SimpleGraph V where
  Adj := rel
  symm := ⟨fun a b h => Or.symm h⟩
  loopless := by
    have h : ∀ a : V, ¬rel a a := by decide +kernel
    exact ⟨h⟩
instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (rel a b))
theorem c4 : NoFourCycle G := by decide +kernel
theorem edgeCount : G.edgeFinset.card = 48 := by decide +kernel
def leftPoint (i : Fin 12) : V :=
  ([1,2,3,4,5,6,8,11,9,10,7,0] : List V).getD i.val 0

def rightLine (i : Fin 12) : V := ⟨13+i.val,by omega⟩

private theorem matched : ∀ i : Fin 12, G.Adj (leftPoint i) (rightLine i) := by decide +kernel

private theorem apart : ∀ i j : Fin 12, i ≠ j →
    leftPoint i ≠ leftPoint j ∧ leftPoint i ≠ rightLine j ∧
    rightLine i ≠ leftPoint j ∧ rightLine i ≠ rightLine j := by decide +kernel

theorem coverCount (S : Finset V) (covers : ∀ a b : V, G.Adj a b → a ∈ S ∨ b ∈ S) :
    12 ≤ S.card := by
  let pick (i : Fin 12) : V := if leftPoint i ∈ S then leftPoint i else rightLine i
  have chosen (i : Fin 12) : pick i ∈ S := by
    by_cases h : leftPoint i ∈ S
    · simpa [pick,h] using h
    · simpa [pick,h] using (covers _ _ (matched i)).resolve_left h
  have injective : Function.Injective pick := by
    intro i j eq
    by_contra ne
    obtain ⟨hll,hlr,hrl,hrr⟩ := apart i j ne
    by_cases hi : leftPoint i ∈ S <;> by_cases hj : leftPoint j ∈ S <;>
      simp only [pick,hi,hj,ite_true,ite_false] at eq
    · exact hll eq
    · exact hlr eq
    · exact hrl eq
    · exact hrr eq
  let f (i : Fin 12) : {v // v ∈ S} := ⟨pick i,chosen i⟩
  have bound := Fintype.card_le_of_injective f (fun i j eq =>
    injective (congrArg Subtype.val eq))
  simpa using bound

theorem lower (C : Circuit) (ao : IsAO2 25 C) (r : IsReadK 25 C 1)
    (ok : ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔ ∃ a b : V,(a.val,b.val)∈edges ∧ x a=true ∧ x b=true) : 59 ≤ C.size := by
  have h (x : V → Bool) : circuitFun 25 C x = decide (∃ a b : V, G.Adj a b ∧ x a=true ∧ x b=true) := by
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x)=true ↔ _
    rw [decide_eq_true_eq,ok]
    constructor
    · rintro ⟨a,b,ab,ha,hb⟩
      exact ⟨a,b,Or.inl ab,ha,hb⟩
    · rintro ⟨a,b,ab,ha,hb⟩
      rcases ab with ab | ba
      · exact ⟨a,b,ab,ha,hb⟩
      · exact ⟨b,a,ba,hb,ha⟩
  obtain ⟨S,hS,hcost⟩ := PEqualNP.Outside.L_meta_6369 25 G C c4 ao h r
  have hs := coverCount S hS
  rw [edgeCount] at hcost
  omega

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def repeatedPair (C : Circuit) : Prop :=
  ∃ j < C.size, (gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j ∧
    ∃ a b c d : V, G.Adj a b ∧ G.Adj c d ∧ s(a,b) ≠ s(c,d) ∧
      readsAtMost C 25 [a.val,b.val] 1 = false ∧
      readsAtMost C 25 [c.val,d.val] 1 = false ∧
      gateVal 25 C j (pairInput a b) = true ∧ gateVal 25 C j (pairInput c d) = true

theorem normalizeCounterexample (C : Circuit) (m : Monotone2 C) (small : C.size ≤ 58)
    (ok : ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔
      ∃ a b : V,(a.val,b.val)∈edges ∧ x a=true ∧ x b=true) :
    ∃ T : Circuit, IsLeastAO G T ∧ TopForm G T ∧ T.size ≤ 58 ∧
      2 ≤ (junk G T).card ∧ repeatedPair T := by
  have computed (x : V → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ a b : V, G.Adj a b ∧ x a=true ∧ x b=true := by
    rw [ok]
    constructor
    · rintro ⟨a,b,ab,ha,hb⟩
      exact ⟨a,b,Or.inl ab,ha,hb⟩
    · rintro ⟨a,b,ab,ha,hb⟩
      rcases ab with ab | ba
      · exact ⟨a,b,ab,ha,hb⟩
      · exact ⟨b,a,ba,hb,ha⟩
  have nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [edgeCount]; decide)
  obtain ⟨D,ao,agree,sz⟩ := PEqualNP.Outside.L_meta_1527 25 G C m computed
  obtain ⟨T,least,top,szT⟩ := PEqualNP.Outside.L_meta_8567 25 G D nonempty ao agree
  have sz' : T.size ≤ 58 := by omega
  have pair : repeatedPair T := by
    by_contra none
    obtain ⟨S,covers,hcost⟩ := PEqualNP.Outside.L_meta_8933 25 G T c4 nonempty
      least.1 least.2.1 none
    have atLeast := coverCount S covers
    rw [edgeCount] at hcost
    omega
  have large : 2 ≤ (junk G T).card := by
    have bip : ∀ a b : V, G.Adj a b → decide (13 ≤ a.val) ≠ decide (13 ≤ b.val) := by
      decide +kernel
    have nonunit := PEqualNP.Outside.L_meta_8725 25 G T (fun a => decide (13 ≤ a.val)) bip c4 least
    obtain ⟨j,hj,hop,notBelow,_⟩ := pair
    unfold BelowF at notBelow
    push_neg at notBelow
    obtain ⟨x,hx,hf⟩ := notBelow
    have hfalse : graphFun G ∅ x = false := by
      cases e : graphFun G ∅ x <;> simp_all
    have member : j ∈ junk G T := by
      change j ∈ (Finset.range T.gates.length).filter _
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hj,hop,hj,x,hx,hfalse⟩
    have positive := Finset.card_pos.mpr (show (junk G T).Nonempty from ⟨j,member⟩)
    omega
  exact ⟨T,least,top,sz',large,pair⟩


private def incident (v : V) : Finset (Sym2 V) := G.edgeFinset.filter fun e => v ∈ e

private theorem degreeLimit : ∀ v : V, (incident v).card ≤ 4 := by decide +kernel

theorem coverAfterDeleting (U : Finset (Sym2 V)) (K : Finset V)
    (cover : ∀ u v : V, G.Adj u v → s(u,v) ∉ U → u ∈ K ∨ v ∈ K) :
    48 ≤ 4*K.card + U.card := by
  classical
  have included : G.edgeFinset ⊆ U ∪ K.biUnion incident := by
    intro e he
    by_cases eu : e ∈ U
    · exact Finset.mem_union_left _ eu
    · apply Finset.mem_union_right
      induction e using Sym2.ind with
      | _ u v =>
        rcases cover u v (SimpleGraph.mem_edgeFinset.mp he) eu with hu | hv
        · exact Finset.mem_biUnion.mpr ⟨u,hu,Finset.mem_filter.mpr ⟨he,by simp⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_filter.mpr ⟨he,by simp⟩⟩
  have a := Finset.card_le_card included
  have b := Finset.card_union_le U (K.biUnion incident)
  have c := Finset.card_biUnion_le_card_mul K incident 4 (fun v _ => degreeLimit v)
  rw [edgeCount] at a
  omega

theorem necessaryCharge (T : Circuit) (least : IsLeastAO G T) (top : TopForm G T)
    (small : T.size ≤ 58) (two : 2 ≤ (junk G T).card) :
    4 ≤ (Ustar G T).card ∧
    4 * (2 * (centreless G T).card + (junk G T).card + (orN G T \ lam G T).card) + 4
      ≤ 5 * (Ustar G T).card := by
  have nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [edgeCount]; decide)
  obtain ⟨K,covers,count⟩ := PEqualNP.Outside.L_meta_18800 25 G T c4 least top
  have geom := coverAfterDeleting (Ustar G T) K covers
  have sum := (PEqualNP.Outside.L_meta_1491 25 G T c4 nonempty least top).1
  rw [edgeCount] at sum
  have budget : 4 * (2 * (centreless G T).card + (junk G T).card + (orN G T \ lam G T).card) + 4
      ≤ 5 * (Ustar G T).card := by omega
  have positive : 0 < (Ustar G T).card := by omega
  obtain ⟨e,he⟩ := Finset.card_pos.mp positive
  have extra : 1 ≤ 2 * (centreless G T).card + (orN G T \ lam G T).card := by
    induction e using Sym2.ind with
    | _ u v => exact PEqualNP.Outside.L_meta_6838 25 G T c4 nonempty least top u v he
  exact ⟨by omega,budget⟩

end PEqualNP.Outside.L_meta_9738_read
