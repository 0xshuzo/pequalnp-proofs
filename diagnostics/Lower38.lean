import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_4510
import PEqualNP.Outside.L_meta_2880
namespace Lower2626
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4510_aux
set_option maxRecDepth 16384
set_option maxHeartbeats 0
abbrev I := Fin 13
abbrev V := Fin (13+13)
def D : Finset I := {0,1,3,9}
def seeds : List (Nat × Nat) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
def mult : List I := [1,3,9]
def row (x : Nat × Nat) (m t : I) (sw : Bool) : V → Bool :=
  let get := fun (a b : Nat) (i : I) => if sw=true then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
  Fin.append (get x.1 x.2) (get x.2 x.1)
def pair (p l : I) (i : V) := decide (i=p.castAdd 13 ∨ i=Fin.natAdd 13 l)
def Positive (C : Circuit) := ∀ p l : I, (∃ v∈D,p=l+v) → circuitFun 26 C (pair p l)=true
def Negative (C : Circuit) := ∀ s∈seeds,∀ m∈mult, ∀ (t : I) (w : Bool), circuitFun 26 C (row s m t w)=false

def near (p l : I) := (p-l)∈D
instance (p l : I) : Decidable (near p l) := inferInstanceAs (Decidable ((p-l)∈D))
def side (i : V) := i.val<13
def name (i : V) := Fin.ofNat 13 i.val
def edge (u v : V) := if u.val<13 then decide (13≤v.val ∧ (name u-name v)∈D)
  else decide (v.val<13 ∧ (name v-name u)∈D)
def G : SimpleGraph V where
  Adj u v := edge u v=true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (edge u v=true))
def spec (j : Nat) : (Nat × Nat) × I × I × Bool :=
  (seeds[j/78]?.getD (0,0),mult[(j/26)%3]?.getD 0,Fin.ofNat 13 (j/2),decide (j%2=1))
def code : Array Nat := #[0,0,0,47,13,11,9,21,21,21,39,4,2,0,4,2,0,0,4,2,0,0,0,0,26,0,0,0,0,7,41,11,9,7,19,19,19,33,2,0,0,2,0,19,0,2,0,0,0,7,0,29,0,0,0,5,5,35,9,7,5,17,17,17,27,27,0,0,0,17,17,0,0,0,0,5,5,0,47,7,5,3,3,3,29,7,5,3,15,15,15,0,34,0,0,15,15,15,0,7,5,3,3,3,13,41,5,3,1,1,1,49,5,3,1,13,13,1,0,28,0,0,13,13,13,0,5,3,1,1,11,11,35,3,1,1,1,16,43,3,1,25,11,1,16,0,26,0,0,11,11,11,0,3,1,1,9,9,9,29,1,1,1,14,14,37,1,25,23,1,14,14,0,27,0,0,9,9,9,0,1,1,21,7,7,7,49,16,14,7,12,12,31,25,23,14,12,12,12,0,36,0,0,7,7,7,0,16,21,19,5,5,5,43,14,12,5,10,10,51,23,14,12,10,10,10,0,30,0,0,5,5,5,0,21,19,17,3,3,3,37,12,10,3,8,8,45,0,12,10,8,8,8,0,26,0,0,3,3,3,39,19,17,15,1,1,1,31,10,8,1,6,6,1,0,10,8,6,6,6,0,27,0,0,1,1,4,33,17,15,13,25,25,25,51,8,6,4,4,6,4,0,8,6,4,4,4,0,38,0,0,8,2,2,27,15,13,11,23,23,23,45,6,4,2,6,4,2,0,6,4,2,2,2,0,32,0,0,0,0,27,0,1,1,1,14,14,0,1,6,6,1,14,14,40,6,6,6,18,16,14,32,1,1,4,0,0,34,0,16,14,12,12,12,0,4,4,14,4,12,12,34,4,4,4,16,14,12,26,16,2,2,0,0,28,0,14,12,10,10,10,0,2,14,12,2,10,10,28,2,2,2,14,12,10,46,0,0,0,0,0,26,0,12,10,8,8,8,0,40,12,10,0,8,8,48,0,0,0,12,10,8,0,19,17,15,0,0,27,0,10,8,6,6,6,6,34,10,8,6,6,6,42,24,24,24,10,8,4,0,17,15,13,0,0,36,0,8,6,4,4,6,4,28,8,6,4,4,4,36,22,22,22,8,2,2,0,15,13,11,0,0,30,0,6,4,2,6,4,2,48,6,4,2,2,2,30,20,20,20,0,0,0,0,13,11,9,0,0,26,0,4,2,18,4,2,0,42,4,2,0,0,0,50,18,18,0,0,0,7,0,11,9,7,0,0,27,0,2,16,16,2,0,24,36,2,0,0,0,7,44,16,0,0,0,5,5,0,9,7,5,0,0,38,0,14,14,14,0,24,22,30,0,0,0,5,5,38,0,7,5,3,3,3,0,7,5,3,0,0,32,32,12,12,12,24,22,20,50,7,5,3,3,3,26,0,5,3,1,1,1,0,5,3,1,0,0,1,26,10,10,10,22,20,18,44,5,3,1,1,0,29,0,3,1,1,1,16,0,3,1,8,0,1,16,46,8,8,8,20,18,16,38,3,1,1]
def certify (u v : V) := code[(26*u.val+v.val)]?.getD 0

theorem box : ∀ u v : V, edge u v=false →
  let z := spec (certify u v)
  z.1∈seeds ∧ z.2.1∈mult ∧ row z.1 z.2.1 z.2.2.1 z.2.2.2 u=true ∧
    row z.1 z.2.1 z.2.2.1 z.2.2.2 v=true := by decide +kernel
theorem flags : ∀ u v : V,edge u v=true → ∃ p l : I, (∃ j∈D,p=l+j) ∧
    ((u=p.castAdd 13 ∧ v=Fin.natAdd 13 l) ∨ (v=p.castAdd 13 ∧ u=Fin.natAdd 13 l)) := by decide +kernel
theorem tests (C : Circuit) (hm : Monotone2 C) (pos : Positive C) (neg : Negative C) : GraphEval C G := by
  intro u v
  change circuitFun 26 C (point {u,v})=true ↔ edge u v=true
  constructor
  · intro h
    cases h' : edge u v with
    | true => rfl
    | false =>
      let z := spec (certify u v)
      obtain ⟨hs,hmul,hu,hv⟩ := box u v h'
      have le : point {u,v} ≤ row z.1 z.2.1 z.2.2.1 z.2.2.2 := by
        intro k
        apply Bool.le_iff_imp.mpr
        intro hk
        have loc : k=u ∨ k=v := by simpa [point] using hk
        rcases loc with rfl|rfl
        · exact hu
        · exact hv
      have no := neg z.1 hs z.2.1 hmul z.2.2.1 z.2.2.2
      have yes := PEqualNP.Outside.L_meta_2880.cmono C hm 26 _ _ le h
      exact no.symm.trans yes
  · intro adj
    obtain ⟨p,l,incident,loc⟩ := flags u v adj
    have eqp : point {u,v} = pair p l := by
      funext k
      rcases loc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [point,pair,or_comm]
    rw [eqp]
    exact pos p l incident

theorem unrestricted (C : Circuit) (hm : Monotone2 C) (pos : Positive C) (neg : Negative C) : 38 ≤ C.size := by
  have noSq : NoSq G := by
    have distinctN : ∀ u v : V, u≠v → (Finset.univ.filter (fun t : V => edge u t=true ∧ edge v t=true)).card ≤ 1 := by decide +kernel
    rintro a b c d ac bd ⟨ab,bc,cd,da⟩
    exact bd (Finset.card_le_one.mp (distinctN a c ac) b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,G.adj_symm bc⟩)
      d (Finset.mem_filter.mpr ⟨Finset.mem_univ _,G.adj_symm da,cd⟩))
  have degree (i : V) : 2 ≤ (G.neighborSet i).ncard := by
    have existsTwo : ∀ i : V, ∃ a b, edge i a=true ∧ edge i b=true ∧ a≠b := by decide +kernel
    obtain ⟨a,b,ha,hb,ne⟩ := existsTwo i
    exact (Set.one_lt_ncard_iff (s:=G.neighborSet i)).mpr ⟨a,b,ha,hb,ne⟩
  have coverMin (S : Finset V) (coverS : CoverPromise.IsVertexCover G S) : 13≤S.card := by
    let P (i : Fin 13) := i.castAdd 13
    let Q (i : Fin 13) := Fin.natAdd 13 i
    have flags : ∀ i : Fin 13, edge (P i) (Q i)=true := by decide +kernel
    let pick (i : Fin 13) := if P i∈S then P i else Q i
    have inside (i : Fin 13) : pick i∈S := by
      by_cases hi : P i∈S
      · simpa [pick,hi] using hi
      · simpa [pick,hi] using (coverS (P i) (Q i) (flags i)).resolve_left hi
    let back (x : V) : Fin 13 := if x.val<13 then Fin.ofNat 13 x.val else Fin.ofNat 13 x.val
    have inv : ∀ i : Fin 13, back (P i)=i ∧ back (Q i)=i := by decide +kernel
    have ret (i : Fin 13) : back (pick i)=i := by dsimp only [pick]; split <;> first | exact (inv i).1 | exact (inv i).2
    have inj : Function.Injective pick := fun a b e => (ret a).symm.trans ((congrArg back e).trans (ret b))
    have h := Finset.card_le_card_of_injOn (s:=Finset.univ) (t:=S) pick (fun i _ => inside i) inj.injOn
    simpa only [Finset.card_univ,Fintype.card_fin] using h
  have h := min_two_bound noSq degree coverMin hm (tests C hm pos neg)
  omega
end Lower2626
