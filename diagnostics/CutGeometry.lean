import Mathlib
import PEqualNP.Outside.L_meta_1485
import PEqualNP.Outside.L_meta_5242

namespace Forced3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1485

abbrev V (n : Nat) := Fin n → Bool
def W {n : Nat} (C : Circuit) (w : Nat) (z : V n) : Prop :=
  val C (List.ofFn z) w = true

theorem read_raw {n : Nat} (C : Circuit) (x : V n) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := PEqualNP.Outside.L_meta_5242.Base.val_ofFn C x u

theorem ops {C : Circuit} (hm : Monotone2 C) {j : Nat} (hj : j < C.gates.length) :
    ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧ (gateAt C j).inputs.length ≤ 2 := by
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm _ (gateAt_mem hj)

theorem monotone {n : Nat} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (x y : V n) (inc : ∀ i, x i = true → y i = true) :
    ∀ w, W C w x → W C w y := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases raw : w<n
    · let i : Fin n := ⟨w,raw⟩
      change val C (List.ofFn x) i.val = true → val C (List.ofFn y) i.val = true
      rw [read_raw C x i,read_raw C y i]
      exact inc i
    · by_cases out : n+C.gates.length ≤ w
      · intro hx
        change val C (List.ofFn x) w = true at hx
        rw [val_ge (n := n) (by simp) out] at hx
        contradiction
      · let j := w-n
        have wj : w=n+j := by dsimp [j]; omega
        have hj : j<C.gates.length := by omega
        rcases (ops hm hj).1 with hand | hor
        · intro h
          rw [wj] at h ⊢
          apply (val_and (n := n) (C := C) (x := List.ofFn y) (by simp) hj hand).mpr
          intro a ha
          obtain ⟨lt,up⟩ := (val_and (n := n) (C := C) (x := List.ofFn x) (by simp) hj hand).mp
            h a ha
          exact ⟨lt,ih a (by omega) up⟩
        · intro h
          rw [wj] at h ⊢
          obtain ⟨a,ha,lt,up⟩ := (val_or (n := n) (by simp) hj hor).mp h
          exact (val_or (by simp) hj hor).mpr ⟨a,ha,lt,ih a (by omega) up⟩


theorem transfer {n : Nat} (C A B : Circuit) (x : V n) (S : Finset Nat)
    (hm : Monotone2 C) (lenA : A.gates.length=C.gates.length) (lenB : B.gates.length=C.gates.length)
    (keep : ∀ j<C.gates.length, j∉S → gateAt A j = gateAt C j ∧ gateAt B j = gateAt C j)
    (new : ∀ j<C.gates.length, j∈S → W A (n+j) x → W B (n+j) x) :
    ∀ w, W A w x → W B w x := by
  let xs := List.ofFn x
  have hx : xs.length=n := List.length_ofFn
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro ht
    change val A xs w = true at ht
    change val B xs w = true
    by_cases hi : w < n
    · rwa [val_input hx hi, ← val_input (C := A) hx hi]
    by_cases hj : w < n+C.gates.length
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
      have h : j<C.gates.length := by omega
      by_cases change' : j∈S
      · exact new j h change' ht
      obtain ⟨ha,hb⟩ := keep j h change'
      have ha' : j<A.gates.length := by omega
      have hb' : j<B.gates.length := by omega
      rcases (ops hm h).1 with opt | opt
      · rw [val_and hx ha' (by rwa [ha]),ha] at ht
        rw [val_and hx hb' (by rwa [hb]),hb]
        exact fun i hi => ⟨(ht i hi).1, ih i (ht i hi).1 (ht i hi).2⟩
      · rw [val_or hx ha' (by rwa [ha]),ha] at ht
        rw [val_or hx hb' (by rwa [hb]),hb]
        obtain ⟨i,hi,lt,hv⟩ := ht
        exact ⟨i,hi,lt,ih i lt hv⟩
    · rw [val_ge hx (by omega)] at ht
      contradiction


def constGate (t : Bool) : Gate := ⟨if t then .and else .or,[]⟩

def splice (C : Circuit) (cut A : Finset Nat) : Circuit :=
  ⟨(List.range C.gates.length).map (fun j =>
    if j∈cut then constGate (decide (j∈A)) else gateAt C j),C.output⟩

theorem length_splice (C : Circuit) (S A : Finset Nat) :
    (splice C S A).gates.length=C.gates.length := by simp [splice]

theorem gate_splice (C : Circuit) (S A : Finset Nat) {j : Nat} (h : j<C.gates.length) :
    gateAt (splice C S A) j=if j∈S then constGate (decide (j∈A)) else gateAt C j := by
  have lt : j<(splice C S A).gates.length := by rwa [length_splice]
  rw [gateAt_eq lt]
  simp [splice]

theorem forced {n : Nat} (C : Circuit) (S A : Finset Nat) {j : Nat} (hj : j<C.gates.length)
    (changed : j∈S) (x : V n) : W (splice C S A) (n+j) x ↔ j∈A := by
  have legal : j<(splice C S A).gates.length := by rwa [length_splice]
  rw [W,val_gate (by simp) legal,gate_splice C S A hj,if_pos changed]
  by_cases hp : j∈A <;> simp [hp,constGate,GateOp.eval]

theorem valid {n : Nat} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C) (S A : Finset Nat) :
    Monotone2 (splice C S A) ∧ ReadsBack n (splice C S A) := by
  let D := splice C S A
  have l : D.gates.length=C.gates.length := length_splice _ _ _
  have decomp (j) (hj : j<D.gates.length) :
      ((gateAt D j).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ (gateAt D j).inputs.length ≤ 2) ∧
      ∀ w∈(gateAt D j).inputs, w<n+j := by
    have hc : j<C.gates.length := by omega
    dsimp only [D]
    rw [gate_splice C S A hc]
    by_cases mark : j∈S
    · by_cases hot : j∈A <;> simp [mark,hot,constGate]
    · rw [if_neg mark]
      exact ⟨hm _ (gateAt_mem hc),rb j hc⟩
  constructor
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq hj]
    exact (decomp _ hj).1
  · exact fun j hj => (decomp _ hj).2

def input {n : Nat} (X : Finset (Fin n)) : V n := fun i => decide (i∈X)

noncomputable def old {n : Nat} (C : Circuit) (S : Finset Nat) (X : Finset (Fin n)) : Finset Nat := by
  classical
  exact S.filter fun j => W C (n+j) (input X)

theorem old_iff {n : Nat} (C : Circuit) (S : Finset Nat) (X : Finset (Fin n)) (j : Nat) :
    j∈old C S X ↔ j∈S ∧ W C (n+j) (input X) := by classical simp [old]

def K {n : Nat} (C : Circuit) (S : Finset Nat) (X : Finset (Fin n)) (A : Finset Nat) :=
  W (splice C S A) C.output (input X)

theorem ports {n : Nat} {C : Circuit} (hm : Monotone2 C) (S : Finset Nat)
    (x : V n) {A B : Finset Nat} (sub : A ⊆ B) :
    ∀ w, W (splice C S A) w x → W (splice C S B) w x :=
  transfer C _ _ x S hm (length_splice _ _ _) (length_splice _ _ _)
    (fun j hj no => ⟨(gate_splice _ _ _ hj).trans (if_neg no),(gate_splice _ _ _ hj).trans (if_neg no)⟩)
    (fun j hj yes on => (forced C S B hj yes x).mpr (sub ((forced C S A hj yes x).mp on)))

theorem joint {n : Nat} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C) (S : Finset Nat)
    {X Y : Finset (Fin n)} {A B : Finset Nat} (xy : X ⊆ Y) (ab : A ⊆ B) :
    K C S X A → K C S Y B := by
  intro h
  have v := valid hm rb S B
  exact monotone v.1 v.2 _ _ (fun _ on => decide_eq_true (xy (of_decide_eq_true on))) _
    (ports hm S (input X) ab _ h)

theorem matches_old {n : Nat} {C : Circuit} (hm : Monotone2 C) (S : Finset Nat) (X : Finset (Fin n)) :
    K C S X (old C S X) ↔ W C C.output (input X) := by
  let A := old C S X
  have same (j) (hj : j<C.gates.length) (no : j∉S) :
      gateAt (splice C S A) j=gateAt C j := (gate_splice _ _ _ hj).trans (if_neg no)
  have on (j) (hj : j<C.gates.length) (yes : j∈S) :
      W (splice C S A) (n+j) (input X) ↔ W C (n+j) (input X) := by
    rw [forced C S A hj yes,show A=old C S X from rfl,old_iff]
    exact and_iff_right yes
  exact ⟨transfer C _ _ _ S hm (length_splice _ _ _) rfl (fun j hj no => ⟨same j hj no,rfl⟩)
      (fun j hj yes => (on j hj yes).mp) C.output,
    transfer C _ _ _ S hm rfl (length_splice _ _ _) (fun j hj no => ⟨rfl,same j hj no⟩)
      (fun j hj yes => (on j hj yes).mpr) C.output⟩

end Forced3321

namespace Forced3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n : Nat} {C : Circuit} (G : SimpleGraph (Fin n))

def Pos (X : Finset (Fin n)) := ∃ u∈X, ∃ v∈X, G.Adj u v

theorem collision (hm : Monotone2 C) (rb : ReadsBack n C)
    (exact' : ∀ X, W C C.output (input X) ↔ Pos G X)
    (S A : Finset Nat) {X Y : Finset (Fin n)} (active : A ⊆ old C S X) (accept : K C S Y A) :
    Pos G (X∪Y) := by
  have expand : A ⊆ old C S (X∪Y) := by
    intro j hj
    obtain ⟨sel,hit⟩ := (old_iff _ _ _ _).mp (active hj)
    refine (old_iff _ _ _ _).mpr ⟨sel,?_⟩
    exact monotone hm rb _ _ (fun _ h => decide_eq_true (Finset.mem_union_left _ (of_decide_eq_true h))) _ hit
  have real := joint hm rb S (show Y ⊆ X∪Y from fun _ hy => Finset.mem_union_right _ hy) expand accept
  exact (exact' _).mp ((matches_old hm S _).mp real)

theorem cross_edges (hm : Monotone2 C) (rb : ReadsBack n C)
    (exact' : ∀ X, W C C.output (input X) ↔ Pos G X)
    (S A : Finset Nat) {X Y : Finset (Fin n)} (active : A ⊆ old C S X) (accept : K C S Y A)
    (nx : ¬ Pos G X) (ny : ¬ Pos G Y) : ∃ u∈X, ∃ v∈Y, G.Adj u v := by
  obtain ⟨u,hu,v,hv,adj⟩ := collision G hm rb exact' S A active accept
  rcases Finset.mem_union.mp hu with ux | uy <;> rcases Finset.mem_union.mp hv with vx | vy
  · exact (nx ⟨u,ux,v,vx,adj⟩).elim
  · exact ⟨u,ux,v,vy,adj⟩
  · exact ⟨v,vx,u,uy,adj.symm⟩
  · exact (ny ⟨u,uy,v,vy,adj⟩).elim

theorem strong_on_complement (hm : Monotone2 C) (rb : ReadsBack n C)
    (exact' : ∀ Z, W C C.output (input Z) ↔ Pos G Z)
    (S : Finset Nat) {X Y : Finset (Fin n)}
    (active : S ⊆ old C S X) (indep : ¬ Pos G X)
    (away : ∀ u∈X, ∀ v∈Y, ¬ G.Adj u v) :
    K C S Y S ↔ Pos G Y := by
  constructor
  · intro h
    by_contra no
    obtain ⟨u,ux,v,vy,adj⟩ := cross_edges G hm rb exact' S S active h indep no
    exact away u ux v vy adj
  · intro h
    have oldBound : old C S Y ⊆ S := by
      intro j hj
      exact ((old_iff _ _ _ _).mp hj).1
    exact joint hm rb S (Finset.Subset.refl _) oldBound ((matches_old hm S Y).mpr ((exact' _).mpr h))

theorem neighbours (hm : Monotone2 C) (rb : ReadsBack n C)
    (exact' : ∀ Z, W C C.output (input Z) ↔ Pos G Z) (S : Finset Nat)
    {p : Fin n} {X : Finset (Fin n)} (fires : S ⊆ old C S {p})
    (no : ¬ Pos G X) (outside : K C S X S) : ∃ v∈X, G.Adj p v := by
  have single : ¬ Pos G {p} := by
    rintro ⟨u,hu,v,hv,adj⟩
    exact adj.ne ((Finset.mem_singleton.mp hu).trans (Finset.mem_singleton.mp hv).symm)
  obtain ⟨u,hu,v,hv,adj⟩ := cross_edges G hm rb exact' S S fires outside single no
  exact ⟨v,hv,Finset.mem_singleton.mp hu ▸ adj⟩

end Forced3321
