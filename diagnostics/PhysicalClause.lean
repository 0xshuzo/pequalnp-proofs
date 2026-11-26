import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4077.Research

abbrev V := Fin 10
abbrev X := V → Bool

def edges : List (V × V) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
   (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def pet (x : X) := edges.any fun e => x e.1 && x e.2
def two (a b : V) : X := fun i => decide (i=a ∨ i=b)
def three (a b c : V) : X := fun i => decide (i=a ∨ i=b ∨ i=c)
def four (a b c d : V) : X := fun i => decide (i=a ∨ i=b ∨ i=c ∨ i=d)

theorem pet_mono {x y : X} (on : ∀ i, x i = true → y i = true) (h : pet x = true) :
    pet y = true := by
  obtain ⟨e,he,yes⟩ := List.any_eq_true.mp h
  apply List.any_eq_true.mpr
  simp only [Bool.and_eq_true] at yes
  exact ⟨e,he,by simp [on _ yes.1, on _ yes.2]⟩

def ignores (A : X → Bool) (v : V) :=
  ∀ x y : X, (∀ i, i ≠ v → x i = y i) → A x = A y

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem pair_rows : ∀ i j : V, ∃ a b : V, pet (two a b) = false ∧
    pet (three i a b) = true ∧ pet (three j a b) = true := by decide +kernel

theorem full_factor (A B : X → Bool) (exactPair : ∀ x, (A x && B x) = pet x) :
    (∀ i, ¬ ignores A i) ∨ (∀ i, ¬ ignores B i) := by
  classical
  by_cases all : ∀ i, ¬ ignores A i
  · exact Or.inl all
  push_neg at all
  obtain ⟨i,hi⟩ := all
  refine Or.inr (fun j hj => ?_)
  obtain ⟨a,b,base,l,r⟩ := pair_rows i j
  have posA := (exactPair (three i a b)).trans l
  have posB := (exactPair (three j a b)).trans r
  simp only [Bool.and_eq_true] at posA posB
  have ea := hi (three i a b) (two a b) (fun w hw => by simp [three,two,hw])
  have eb := hj (three j a b) (two a b) (fun w hw => by simp [three,two,hw])
  rw [ea] at posA
  rw [eb] at posB
  have neg := (exactPair (two a b)).trans base
  simp [posA.1,posB.2] at neg

def close (a b c : V) (x : X) : X := fun i =>
  if i=a ∨ i=b ∨ i=c then true else x i

def outside (a b c z : V) (x : X) : Bool :=
  (List.finRange 10).any fun i => decide (i≠a ∧ i≠b ∧ i≠c ∧ i≠z) && x i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem near_maximal : ∀ a b c : V, a < b → b < c → ∃ z : V, ∀ w : V,
    w≠a → w≠b → w≠c → w≠z → pet (four a b c w) = true := by decide +kernel

/-- A factor accepting the whole positive set and ignoring three coordinates is
the OR of the remaining six or seven coordinates with a unary Boolean function. -/
theorem clause_of_three (A : X → Bool) (positive : ∀ x, pet x = true → A x = true)
    (a b c : V) (ab : a<b) (bc : b<c)
    (indep : ∀ x y : X, (∀ i, i≠a → i≠b → i≠c → x i=y i) → A x=A y) :
    ∃ (z : V) (f : Bool → Bool), ∀ x, A x = (outside a b c z x || f (x z)) := by
  obtain ⟨z,hz⟩ := near_maximal a b c ab bc
  let only (t : Bool) : X := fun i => if i=z then t else false
  refine ⟨z,fun t => A (only t), fun x => ?_⟩
  cases ho : outside a b c z x with
  | true =>
    simp only [Bool.true_or]
    obtain ⟨w,_,hw⟩ := List.any_eq_true.mp ho
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hw
    have hleft := hz w hw.1.1 hw.1.2.1 hw.1.2.2.1 hw.1.2.2.2
    have has : pet (close a b c x) = true := by
      apply pet_mono _ hleft
      intro i hi
      change decide (i=a ∨ i=b ∨ i=c ∨ i=w) = true at hi
      rw [decide_eq_true_eq] at hi
      rcases hi with h|h|h|h
      · simp [close,h]
      · simp [close,h]
      · simp [close,h]
      · subst i
        simpa [close,hw.1.1,hw.1.2.1,hw.1.2.2.1] using hw.2
    exact (indep x (close a b c x) (fun i ha hb hc => by simp [close,ha,hb,hc])).trans
      (positive _ has)
  | false =>
    simp only [Bool.false_or]
    apply indep
    intro i ha hb hc
    by_cases iz : i=z
    · simp [only,iz]
    · have hi : x i = false := by
        cases h : x i with
        | false => rfl
        | true =>
          have out : outside a b c z x = true :=
            List.any_eq_true.mpr ⟨i,by simp,by simp [ha,hb,hc,iz,h]⟩
          simp [ho] at out
      simpa [only,iz] using hi

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The backward support count follows the argument in L_meta_1942.
private def supportRun (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

private lemma supportRun_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    supportRun (gs ++ [g]) x = supportRun gs x ++
      [g.op.eval (g.inputs.map fun i => (supportRun gs x).getD i false)] := by
  simp [supportRun, Circuit.wires, List.foldl_append]

private lemma supportRun_length (gs : List Gate) (x : List Bool) :
    (supportRun gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [supportRun, Circuit.wires]
  | append_singleton gs g ih => simp [supportRun_snoc, ih, Nat.add_assoc]

private lemma gateSupports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (supportRun gs x).getD i false = (supportRun gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (supportRun gs x).length = j := by simp [supportRun_length, hx, j]
    have ey : (supportRun gs y).length = j := by simp [supportRun_length, hy, j]
    rw [supportRun_snoc, supportRun_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma outputSupport {n : ℕ} (C : Circuit) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ S : Finset (Fin n), S.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → circuitFun n C x = circuitFun n C y := by
  obtain ⟨S, hcard, hs⟩ := gateSupports n C.gates fan {C.output}
  let T := S.preimage (Fin.val : Fin n → ℕ) Fin.val_injective.injOn
  have bound : T.card ≤ S.card :=
    Finset.card_le_card_of_injOn Fin.val (fun _ h => Finset.mem_preimage.mp h) Fin.val_injective.injOn
  refine ⟨T, bound.trans (by simpa [Circuit.size, Nat.add_comm] using hcard), ?_⟩
  intro x y hxy
  apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro i hi
  by_cases hn : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hn), List.getD_eq_getElem _ _ (by simpa using hn)]
    simpa only [List.getElem_ofFn] using hxy ⟨i, hn⟩ (Finset.mem_preimage.mpr hi)
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def put (b : Bool) (x : X) : List Bool :=
  List.ofFn x ++ [x 0 || if b=true then x 1 else x 2]

def val (b : Bool) (C : Circuit) (r : Nat) (x : X) := (C.wires (put b x)).getD r false

private def firstGate (b : Bool) : Gate := ⟨.or,[0,if b=true then 1 else 2]⟩

private theorem rawRead (i : V) (x : X) : (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private theorem firstValue (b : Bool) (x : X) :
    supportRun [firstGate b] (List.ofFn x) = put b x := by
  have z := rawRead (0:V) x
  have o := rawRead (1:V) x
  have t := rawRead (2:V) x
  change (List.ofFn x).getD 0 false = x 0 at z
  change (List.ofFn x).getD 1 false = x 1 at o
  change (List.ofFn x).getD 2 false = x 2 at t
  cases b <;> simp [supportRun, Circuit.wires, firstGate, GateOp.eval, put, z,o,t]

private theorem retained (gs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (supportRun gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [supportRun_snoc, List.getD_append _ _ _ _ (by rw [supportRun_length]; omega), ih]

private theorem keeps (C : Circuit) (m : Nat) (x : List Bool) (r : Nat)
    (hm : m ≤ C.size) (hr : r < x.length+m) :
    (supportRun (C.gates.take m) x).getD r false = (C.wires x).getD r false := by
  have len : (supportRun (C.gates.take m) x).length = x.length + m := by
    simp [supportRun_length, Nat.min_eq_left (show m ≤ C.gates.length from hm)]
  have ret := retained (C.gates.drop m) (supportRun (C.gates.take m) x) r (by omega)
  have app : supportRun (C.gates.drop m) (supportRun (C.gates.take m) x) = C.wires x := by
    simp only [supportRun,Circuit.wires,← List.foldl_append,List.take_append_drop]
  rw [app] at ret
  exact ret.symm

theorem physical_support (b : Bool) (C : Circuit) (r : Nat) (fan : FanInTwo C) :
    ∃ S : Finset V, S.card ≤ max 2 (r-8) ∧
      ∀ x y : X, (∀ i ∈ S, x i=y i) → val b C r x=val b C r y := by
  by_cases valid : r < 11+C.size
  · let k := r-10
    have le : k ≤ C.size := by dsimp [k]; omega
    let D : Circuit := ⟨[firstGate b] ++ C.gates.take k,r⟩
    have dfan : FanInTwo D := by
      intro g hg
      change g ∈ [firstGate b] ++ C.gates.take k at hg
      rcases List.mem_append.mp hg with h|h
      · obtain rfl := List.mem_singleton.mp h
        simp [firstGate]
      · exact fan g (List.mem_of_mem_take h)
    have eval (x : X) : circuitFun 10 D x = val b C r x := by
      have head : supportRun ([firstGate b] ++ C.gates.take k) (List.ofFn x) =
          supportRun (C.gates.take k) (supportRun [firstGate b] (List.ofFn x)) := by
        simp only [supportRun,Circuit.wires,List.foldl_append]
      change (supportRun ([firstGate b] ++ C.gates.take k) (List.ofFn x)).getD r false = _
      rw [head,firstValue]
      apply keeps C k (put b x) r le
      simp only [put,List.length_append,List.length_ofFn,List.length_singleton]
      dsimp [k]; omega
    obtain ⟨S,sc,hs⟩ := outputSupport (n:=10) D dfan
    refine ⟨S,?_,fun x y eq => (eval x).symm.trans ((hs x y eq).trans (eval y))⟩
    have sizeD : D.size = 1+k := by simp [D,Circuit.size,Nat.min_eq_left (show k ≤ C.gates.length from le)]
    rw [sizeD] at sc
    dsimp [k] at sc
    omega
  · refine ⟨∅,by simp,fun x y _ => ?_⟩
    have defaultV (z : X) : val b C r z = false := by
      apply List.getD_eq_default
      change (supportRun C.gates (put b z)).length ≤ r
      simp only [supportRun_length, put,List.length_append,List.length_ofFn,List.length_singleton]
      change ¬ r < 11+C.gates.length at valid
      omega
    exact (defaultV x).trans (defaultV y).symm

def coverClause (S : Finset V) (x : X) := decide (∃ i ∈ S, x i=true)

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem coverData :
    (∀ S : Finset V, S.card < 6 → pet (fun i => decide (i∉S)) = true) ∧
    (∀ S : Finset V, S.card ≤ 6 → ∀ w∈S, pet (fun i => decide (i∉S ∨ i=w)) = true) := by
  decide +kernel

theorem small_terminal (b : Bool) (C : Circuit) (r : Nat) (fan : FanInTwo C) (hr : r≤14)
    (pos : ∀ x, pet x=true → val b C r x=true) (off : ∃ x, val b C r x=false) :
    ∃ S : Finset V, S.card=6 ∧ pet (fun i => decide (i∉S))=false ∧
      ∀ x, val b C r x = coverClause S x := by
  obtain ⟨S,sc,sup⟩ := physical_support b C r fan
  have six : S.card ≤ 6 := by omega
  have yes (x : X) (hc : coverClause S x = true) : val b C r x=true := by
    obtain ⟨w,hw,on⟩ := of_decide_eq_true hc
    let y : X := fun i => if i∈S then x i else true
    have hp : pet y = true := by
      apply pet_mono _ (coverData.2 S six w hw)
      intro i hi
      obtain hl|hl := of_decide_eq_true hi
      · simp [y,hl]
      · subst i
        simp [y,hw,on]
    exact (sup x y (fun i hi => by simp [y,hi])).trans (pos y hp)
  obtain ⟨z,hz⟩ := off
  have zoff : coverClause S z = false := by
    cases e : coverClause S z with
    | false => rfl
    | true => have bad := yes z e; simp [hz] at bad
  have blank (x : X) (hc : coverClause S x=false) (i : V) (hi : i∈S) : x i=false := by
    cases ex : x i with
    | false => rfl
    | true =>
      have bad : coverClause S x=true := decide_eq_true ⟨i,hi,ex⟩
      simp [hc] at bad
  have result (x : X) : val b C r x = coverClause S x := by
    cases h : coverClause S x with
    | true => exact yes x h
    | false =>
      exact (sup x z (fun i hi => (blank x h i hi).trans (blank z zoff i hi).symm)).trans hz
  let u : X := fun i => decide (i∉S)
  have uc : coverClause S u=false := by simp [coverClause,u]
  have ui : pet u=false := by
    cases hp : pet u with
    | false => rfl
    | true => have ht := pos u hp; rw [result,uc] at ht; contradiction
  have eq : S.card=6 := by
    by_contra he
    have hc := coverData.1 S (by omega)
    rw [show pet (fun i => decide (i∉S)) = false from ui] at hc
    contradiction
  exact ⟨S,eq,ui,result⟩

end PEqualNP.Outside.L_meta_4077.Research
