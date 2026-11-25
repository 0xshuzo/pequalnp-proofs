import Mathlib
import PEqualNP.Outside.L_meta_1485
import PEqualNP.Outside.L_meta_5242

namespace Patch3321
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


def rebuild (C : Circuit) (S : Finset Nat) (a b : Nat → Nat) : Circuit :=
  ⟨(List.range C.gates.length).map (fun j =>
      if j ∈ S then ⟨.and,[a j,b j]⟩ else gateAt C j),C.output⟩

theorem size_rebuild (C : Circuit) (S : Finset Nat) (a b : Nat → Nat) :
    (rebuild C S a b).gates.length = C.gates.length := by simp [rebuild]

theorem step_rebuild {C : Circuit} (S : Finset Nat) (a b : Nat → Nat)
    {j : Nat} (hj : j<C.gates.length) : gateAt (rebuild C S a b) j =
      if j∈S then ⟨.and,[a j,b j]⟩ else gateAt C j := by
  have hj' : j < (rebuild C S a b).gates.length := by rwa [size_rebuild]
  rw [gateAt_eq hj']
  simp [rebuild]

theorem valid {n : Nat} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (S : Finset Nat) (a b : Nat → Nat)
    (back : ∀ j < C.gates.length, j∈S → a j < n+j ∧ b j < n+j) :
    Monotone2 (rebuild C S a b) ∧ ReadsBack n (rebuild C S a b) := by
  let D := rebuild C S a b
  have h (j) (hj : j<D.gates.length) :
      ((gateAt D j).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ (gateAt D j).inputs.length ≤ 2) ∧
      ∀ w∈(gateAt D j).inputs, w<n+j := by
    have hc : j < C.gates.length := by simpa only [D,size_rebuild] using hj
    dsimp only [D]
    rw [step_rebuild S a b hc]
    by_cases hs : j∈S
    · rw [if_pos hs]
      refine ⟨by simp,?_⟩
      intro w hw
      rcases (show w=a j ∨ w=b j by simpa using hw) with rfl | rfl
      · exact (back j hc hs).1
      · exact (back j hc hs).2
    · rw [if_neg hs]
      exact ⟨hm _ (gateAt_mem hc),rb j hc⟩
  constructor
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq hj]
    exact (h j hj).1
  · exact fun j hj => (h j hj).2

theorem frozen {n : Nat} {C : Circuit} (S : Finset Nat) (a b : Nat → Nat)
    (Z : Nat → Prop) (close : ∀ j < C.gates.length, Z (n+j) →
      j∉S ∧ ∀ u∈(gateAt C j).inputs, Z u) (x : V n) :
    ∀ w, Z w → val (rebuild C S a b) (List.ofFn x) w = val C (List.ofFn x) w := by
  let D := rebuild C S a b
  have hl : D.gates.length = C.gates.length := size_rebuild _ _ _ _
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hz
    by_cases raw : w<n
    · rw [val_input (by simp) raw,val_input (by simp) raw]
    by_cases lim : w<n+C.gates.length
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt raw)
      have hj : j<C.gates.length := by omega
      have hD : j<D.gates.length := by omega
      obtain ⟨keep,closed⟩ := close j hj hz
      rw [val_gate (by simp) hD,val_gate (by simp) hj,show gateAt D j=gateAt C j from
        (step_rebuild S a b hj).trans (if_neg keep)]
      congr 1
      apply List.map_congr_left
      intro u hu
      by_cases lt : u<n+j
      · simp only [if_pos lt]
        exact ih u lt (closed u hu)
      · simp only [if_neg lt]
    · have outD : n+D.gates.length ≤ w := by omega
      rw [val_ge (by simp) outD,val_ge (by simp) (Nat.le_of_not_gt lim)]

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

theorem stars {n : Nat} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (F Samples : V n → Prop) (exact' : ∀ x, W C C.output x ↔ F x)
    (gen : ∀ x, F x → ∃ y, Samples y ∧ F y ∧ ∀ i, y i=true → x i=true)
    (S : Finset Nat) (a b : Nat → Nat) (Z : Nat → Prop)
    (close : ∀ j<C.gates.length, Z (n+j) → j∉S ∧ ∀ u ∈ (gateAt C j).inputs, Z u)
    (ports : ∀ j<C.gates.length, j∈S → a j < n+j ∧ b j < n+j ∧ Z (a j) ∧ Z (b j))
    (safe : ∀ j<C.gates.length, j∈S → ∀ x, W C (a j) x → W C (b j) x → F x)
    (hits : ∀ j<C.gates.length, j∈S → ∀ x, Samples x → W C (n+j) x →
      W C (a j) x ∧ W C (b j) x)
    (retained : ∀ j<C.gates.length, j∉S → (gateAt C j).op=.and → ∀ x, W C (n+j) x → F x) :
    let D := rebuild C S a b
    Monotone2 D ∧ ReadsBack n D ∧ D.size=C.size ∧ (∀ x, W D D.output x ↔ F x) ∧
      ∀ j<D.gates.length, (gateAt D j).op=.and → ∀ x, W D (n+j) x → F x := by
  intro D
  have hl : D.gates.length=C.gates.length := size_rebuild _ _ _ _
  have legal := valid hm rb S a b (fun j hj hs => ⟨(ports j hj hs).1,(ports j hj hs).2.1⟩)
  have unchanged (j) (hj : j<C.gates.length) (hs : j∉S) : gateAt D j=gateAt C j :=
    (step_rebuild S a b hj).trans (if_neg hs)
  have paired (j) (hj : j<C.gates.length) (hs : j∈S) (x : V n) :
      W D (n+j) x ↔ W C (a j) x ∧ W C (b j) x := by
    have hDj : j<D.gates.length := by omega
    have eg : gateAt D j=⟨.and,[a j,b j]⟩ := (step_rebuild S a b hj).trans (if_pos hs)
    obtain ⟨la,lb,za,zb⟩ := ports j hj hs
    change val D (List.ofFn x) (n+j) = true ↔ _
    rw [val_and (by simp) hDj (by rw [eg]),eg]
    have ea : val D (List.ofFn x) (a j)=val C (List.ofFn x) (a j) := frozen S a b Z close x _ za
    have eb : val D (List.ofFn x) (b j)=val C (List.ofFn x) (b j) := frozen S a b Z close x _ zb
    simp [W,ea,eb,la,lb]
  have down (x : V n) (bad : ¬F x) : ∀ w, W D w x → W C w x :=
    transfer C D C x S hm hl rfl (fun j hj hs => ⟨unchanged j hj hs,rfl⟩) (by
      intro j hj hs h
      obtain ⟨u,v⟩ := (paired j hj hs x).mp h
      exact (bad (safe j hj hs x u v)).elim)
  have up (x : V n) (good : Samples x) : ∀ w, W C w x → W D w x :=
    transfer C C D x S hm rfl hl (fun j hj hs => ⟨rfl,unchanged j hj hs⟩) (by
      intro j hj hs h
      exact (paired j hj hs x).mpr (hits j hj hs x good h))
  refine ⟨legal.1,legal.2,hl,?_,?_⟩
  · intro x
    constructor
    · intro on
      by_contra bad
      exact bad ((exact' x).mp (down x bad C.output on))
    · intro good
      obtain ⟨y,hy,fy,inc⟩ := gen x good
      exact monotone legal.1 legal.2 y x inc C.output (up y hy C.output ((exact' y).mpr fy))
  · intro j hj op x on
    have hc : j<C.gates.length := by omega
    by_cases hs : j∈S
    · obtain ⟨aa,bb⟩ := (paired j hc hs x).mp on
      exact safe j hc hs x aa bb
    · by_contra bad
      exact bad (retained j hc hs (unchanged j hc hs ▸ op) x (down x bad _ on))

end Patch3321
