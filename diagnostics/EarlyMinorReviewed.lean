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
def put (b : Bool) (x : X) : List Bool :=
  List.ofFn x ++ [x 0 || if b=true then x 1 else x 2]

def val (b : Bool) (C : Circuit) (r : Nat) (x : X) := (C.wires (put b x)).getD r false


namespace Minor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

private theorem stepVal (ws : List Bool) (g : Gate) (i : Nat) :
    (step ws g).getD i false = if i=ws.length then g.op.eval (g.inputs.map fun j => ws.getD j false)
        else ws.getD i false := by
  by_cases he : i=ws.length
  · subst i; simp [step]
  · by_cases hi : i < ws.length
    · simpa only [step,ite_eq_right he] using List.getD_append ws [_] false i hi
    · rw [ite_eq_right he,List.getD_eq_default (step ws g) false (by simp [step]; omega),
          List.getD_eq_default ws false (by omega)]

def rename (r : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩

private theorem runMap (r : Nat → Nat) (L : Nat)
    (fresh : ∀ k < L, ∀ j, r j = 9+k ↔ j=11+k)
    (gs : List Gate) (k : Nat) (n o : List Bool) (sz : k+gs.length ≤ L)
    (hn : n.length = 9+k) (ho : o.length = 11+k)
    (same : ∀ j, n.getD (r j) false = o.getD j false) :
    ∀ j, ((gs.map (rename r)).foldl step n).getD (r j) false =
      (gs.foldl step o).getD j false := by
  induction gs generalizing k n o with
  | nil => exact same
  | cons g gs ih =>
    have h0 : k < L := by simp only [List.length_cons] at sz; omega
    have vals : (rename r g).op.eval ((rename r g).inputs.map fun i => n.getD i false) =
        g.op.eval (g.inputs.map fun i => o.getD i false) := by
      simp [rename,List.map_map,Function.comp_def,same]
    apply ih (k+1) (step n (rename r g)) (step o g)
    · simp only [List.length_cons] at sz; omega
    · simp [step,hn]; omega
    · simp [step,ho]; omega
    · intro j
      rw [stepVal,stepVal,hn,ho]
      by_cases hj : j=11+k
      · rw [if_pos ((fresh k h0 j).2 hj),if_pos hj]; exact vals
      · rw [if_neg (fun hr => hj ((fresh k h0 j).1 hr)),if_neg hj]; exact same j

def p9 (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
  (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def lift (y : Fin 9 → Bool) : X := fun j =>
  [false,y 6,y 8,y 5,y 7,y 4,y 1,y 3,y 0,y 2].getD j.val false

def rewire (b : Bool) (L i : Nat) := if i<11 then
  ([9+L,6,8,5,7,4,1,3,0,2,if b=true then 6 else 8] : List Nat).getD i 0 else i-2

private theorem freshMap (b : Bool) (L k : Nat) (hk : k<L) (j : Nat) :
    rewire b L j=9+k ↔ j=11+k := by
  by_cases h : j<11
  · interval_cases j <;> cases b <;> simp [rewire] <;> omega
  · simp [rewire,h]; omega

private theorem startMap (b : Bool) (L : Nat) (y : Fin 9 → Bool) (j : Nat) :
    (List.ofFn y).getD (rewire b L j) false = (put b (lift y)).getD j false := by
  by_cases h : j<11
  · have big : (List.ofFn y).getD (9+L) false=false := List.getD_eq_default _ _ (by simp)
    interval_cases j <;> cases b <;> simp [rewire,put,lift,List.ofFn_succ] <;>
      first | exact big | simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by simp [rewire,h]; omega),
        List.getD_eq_default _ _ (by simp [put]; omega)]

private theorem liftPet (y : Fin 9 → Bool) : pet (lift y) = p9 y := by
  have h : ∀ a b c d e f g h i : Bool, pet (fun j : V =>
      [false,g,i,f,h,e,b,d,a,c].getD j.val false) =
      ((a&&b)||(b&&c)||(c&&d)||(d&&e)||(e&&a)||(a&&f)||(b&&g)||(c&&h)||(d&&i)||
        (f&&h)||(g&&i)||(i&&f)) := by decide
  exact h (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

/-- On the zero slice of pin 0 the additional seed duplicates one raw variable.
No common wire available after just fifteen prefix gates can equal that entire minor. -/
theorem early_zero (lower : ¬ HasCircuitSize 9 p9 15) (b : Bool) (C : Circuit)
    (fan : FanInTwo C) (low : C.size ≤ 15) (r : Nat) :
    ¬∀ x : X, x 0=false → val b C r x=pet x := by
  intro computes
  let L := C.size
  let rup := rewire b L
  let D : Circuit := ⟨C.gates.map (rename rup),rup r⟩
  apply lower
  refine ⟨D,?_,?_,?_⟩
  · intro g hg
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hg
    exact ⟨(fan s hs).1,by simpa [rename] using (fan s hs).2⟩
  · simpa [D,Circuit.size] using low
  · intro y
    have e := runMap rup L (freshMap b L) C.gates 0 (List.ofFn y) (put b (lift y))
       (by simp [L,Circuit.size]) (by simp) (by simp [put]) (startMap b L y) r
    exact e.trans ((computes (lift y) (by rfl)).trans (liftPet y))

end Minor

end PEqualNP.Outside.L_meta_4077.Research
