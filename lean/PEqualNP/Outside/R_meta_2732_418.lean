import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Positive rows are the edges. Negative rows are the maximal independent sets.
-- Each raw input is one column of this table, with the positive rows in the low bits.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem PEqualNP.Outside.R_meta_2732_418
    (h_symm : ∀ (F : (Fin 14 → Bool) → Bool) (C : Circuit),
      IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      2 ≤ C.size → C.size ≤ 26 → (∀ x, C.eval (List.ofFn x) = F x) →
      have x3 : ℕ → ℕ → ℕ → ℕ → ℕ := fun u v p q =>
        ((15 * min u v + max u v) * 225) + (15 * min p q + max p q);
      have x4 : Equiv.Perm (Fin 14) → Fin 15 → ℕ := fun σ i =>
        if ↑i < 14 then ↑(σ (Fin.ofNat 14 ↑i)) else 14;
      ∃ (a b : Fin 14) (c d : Fin 15) (op1 op2 : GateOp) (D : Circuit),
        a < b ∧ c < d ∧ (op1 = GateOp.and ∨ op1 = GateOp.or) ∧ (op2 = GateOp.and ∨ op2 = GateOp.or) ∧
        (∀ σ : Equiv.Perm (Fin 14), (∀ x, F (x ∘ ⇑σ) = F x) →
          x3 ↑a ↑b ↑c ↑d ≤ x3 ↑(σ a) ↑(σ b) (x4 σ c) (x4 σ d)) ∧
        Monotone2 D ∧ D.size ≤ 24 ∧
        ∀ x : Fin 14 → Bool,
          have w : List Bool := List.ofFn x ++ [op1.eval [x a, x b]];
          D.eval (w ++ [op2.eval [w.getD (↑c) false, w.getD (↑d) false]]) = F x)
    (packed :
      ∃ (a b : Fin 26 → ℕ) (join : Fin 26 → Bool) (o : ℕ),
        (∀ j, a j < b j ∧ b j < 14 + j.val) ∧
        ((List.ofFn (fun j : Fin 26 => j)).foldl
          (fun (w : List ℕ) j => w ++ [if join j then w.getD (a j) 0 ||| w.getD (b j) 0
              else w.getD (a j) 0 &&& w.getD (b j) 0]) [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]).getD o 0 = 2097151) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); have x3 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x3 x4 x5 x6 : ℕ) => ((15 : ℕ) * Min.min x3 x4 + Max.max x3 x4) * (225 : ℕ) + ((15 : ℕ) * Min.min x5 x6 + Max.max x5 x6); have x4 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x4 : Equiv.Perm (Fin (14 : ℕ))) (x5 : Fin (15 : ℕ)) => if ↑x5 < (14 : ℕ) then ↑(x4 (Fin.ofNat (14 : ℕ) ↑x5)) else (14 : ℕ); ∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)) (x7 : Fin (15 : ℕ)) (x8 : Fin (15 : ℕ)) (x9 : PEqualNP.CircuitLowerBounds.GateOp) (x10 : PEqualNP.CircuitLowerBounds.GateOp) (x11 : PEqualNP.CircuitLowerBounds.Circuit),   x5 < x6 ∧     x7 < x8 ∧       (x9 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x9 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧         (x10 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧           (∀ (x12 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x13 : Fin (14 : ℕ) → Bool), x2 (x13 ∘ ⇑x12) = x2 x13) → x3 ↑x5 ↑x6 ↑x7 ↑x8 ≤ x3 (↑(x12 x5)) (↑(x12 x6)) (x4 x12 x7) (x4 x12 x8)) ∧             PEqualNP.MetaComplexity.Monotone2 x11 ∧               x11.size ≤ (24 : ℕ) ∧                 ∀ (x12 : Fin (14 : ℕ) → Bool),                   have x13 : List Bool := List.ofFn x12 ++ [x9.eval [x12 x5, x12 x6]];                   x11.eval (x13 ++ [x10.eval [x13.getD (↑x7) Bool.false, x13.getD (↑x8) Bool.false]]) = x2 x12 := by
  obtain ⟨a,b,join,o,range,witness⟩ := packed
  let cols : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let edges : List (ℕ × ℕ) := [(0,7), (0,8), (0,10), (1,7), (1,9), (1,13), (2,8), (2,12), (2,13), (3,7), (3,11), (3,12), (4,10), (4,11), (4,13), (5,9), (5,10), (5,12), (6,8), (6,9), (6,11)]
  let F (x : Fin 14 → Bool) := decide (∃ u v : Fin 14,
    (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true)
  let indices := List.ofFn (fun j : Fin 26 => j)
  let mkGate (j : Fin 26) : Gate := ⟨if join j then .or else .and,[a j,b j]⟩
  let C : Circuit := ⟨indices.map mkGate,o⟩
  let wstep (w : List ℕ) (j : Fin 26) :=
    w ++ [if join j then w.getD (a j) 0 ||| w.getD (b j) 0 else w.getD (a j) 0 &&& w.getD (b j) 0]
  let bstep (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun t => w.getD t false)]
  have gates : C.gates = List.ofFn mkGate := by simp [C,indices,List.map_ofFn,Function.comp_def]
  have count : C.size = 26 := by change C.gates.length = 26; rw [gates,List.length_ofFn]
  have member (g : Gate) (hg : g ∈ C.gates) : ∃ j, g=mkGate j := by
    change g ∈ indices.map mkGate at hg
    obtain ⟨j,_,eq⟩ := List.mem_map.mp hg
    exact ⟨j,eq.symm⟩
  have model : IsAO2 14 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,rfl⟩ := member g hg
      cases h : join j <;> simp [mkGate,h]
    · intro j hj i hi
      have small : j<26 := by simpa only [gates,List.length_ofFn] using hj
      let k : Fin 26 := ⟨j,small⟩
      have same : NestedCover.gateAt C j = mkGate k := by
        unfold NestedCover.gateAt
        rw [gates,List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using small),List.getElem_ofFn]
      rw [same] at hi
      change i ∈ [a k,b k] at hi
      have bounds := range k
      change a k < b k ∧ b k < 14+j at bounds
      simp only [List.mem_cons,List.mem_singleton] at hi
      rcases hi with h|h <;> omega
    · intro g hg
      obtain ⟨j,rfl⟩ := member g hg
      rfl
  have distinct (g : Gate) (hg : g ∈ C.gates) : g.inputs.Nodup := by
    obtain ⟨j,rfl⟩ := member g hg
    simp [mkGate,ne_of_lt (range j).1]
  let sample (r : ℕ) (j : Fin 14) := (cols.getD j.val 0).testBit r
  have extracted (r : ℕ) : C.eval (List.ofFn (sample r)) = (2097151 : ℕ).testBit r := by
    let bit (t : ℕ) := t.testBit r
    have readbit (w : List ℕ) (i : ℕ) :
        (w.map bit).getD i false = bit (w.getD i 0) := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
      cases w[i]? with
      | none => simp [bit]
      | some n => rfl
    have run (js : List (Fin 26)) (w : List ℕ) :
        (js.foldl wstep w).map bit = (js.map mkGate).foldl bstep (w.map bit) := by
      induction js generalizing w with
      | nil => rfl
      | cons j js ih =>
        simp only [List.foldl_cons,List.map_cons]
        rw [ih]
        congr 1
        cases h : join j <;>
          simp [wstep,bstep,mkGate,h,bit,GateOp.eval,List.map_append,readbit,
            Nat.testBit_and,Nat.testBit_or]
    have raw : List.ofFn (sample r) = cols.map bit := by
      have rawCols : List.ofFn (fun j : Fin 14 => cols.getD j.val 0) = cols := by rfl
      rw [←rawCols,List.map_ofFn]
      rfl
    change ((indices.map mkGate).foldl bstep (List.ofFn (sample r))).getD o false = _
    rw [raw,←run,readbit]
    change (indices.foldl wstep cols).getD o 0 = 2097151 at witness
    rw [witness]
  let pt (i : Fin 7) : Fin 14 := ⟨i.val,by omega⟩
  let ln (i : Fin 7) : Fin 14 := ⟨7+i.val,by omega⟩
  have posRows : ∀ u v : Fin 14, (u.val,v.val) ∈ edges →
      ∃ r : Fin 21, ∀ j : Fin 14, sample r.val j = true → j=u ∨ j=v := by decide +kernel
  have negRows : ∀ p : Fin 7 → Bool, ∃ r : Fin 37,
      (∀ i : Fin 7, p i=true → sample (21+r.val) (pt i)=true) ∧
      (∀ j : Fin 7, (∀ i : Fin 7, p i=true → (i.val,7+j.val) ∉ edges) →
        sample (21+r.val) (ln j)=true) := by decide +kernel
  have posbit : ∀ r : Fin 21, (2097151 : ℕ).testBit r.val = true := by decide
  have negbit : ∀ r : Fin 37, (2097151 : ℕ).testBit (21+r.val) = false := by decide
  have lift (js : List (Fin 26)) (U V : List Bool) (hl : U.length=V.length)
      (h : ∀ i, U.getD i false=true → V.getD i false=true) :
      ∀ i, ((js.map mkGate).foldl bstep U).getD i false=true →
          ((js.map mkGate).foldl bstep V).getD i false=true := by
    induction js generalizing U V with
    | nil => exact h
    | cons j js ih =>
      simp only [List.map_cons,List.foldl_cons]
      apply ih
      · simp [bstep,hl]
      · intro t
        rcases lt_trichotomy t U.length with ht|ht|ht
        · unfold bstep
          rw [List.getD_append _ _ _ _ ht,List.getD_append _ _ _ _ (by omega)]
          exact h t
        · subst t
          unfold bstep
          rw [List.getD_append_right _ _ _ _ le_rfl,
            List.getD_append_right _ _ _ _ (by omega)]
          simp only [hl,Nat.sub_self,List.getD_cons_zero]
          cases hop : join j <;> simp [mkGate,hop,GateOp.eval] <;> grind
        · have hz : (bstep U (mkGate j)).getD t false=false :=
            List.getD_eq_default _ _ (by simp [bstep]; omega)
          simp [hz]
  have mono (x y : Fin 14 → Bool) (h : ∀ i, x i=true → y i=true) :
      C.eval (List.ofFn x)=true → C.eval (List.ofFn y)=true := by
    apply lift indices (List.ofFn x) (List.ofFn y) (by simp) _ o
    intro w
    by_cases hw : w < 14
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hw,dite_true,Option.getD_some]
      exact h ⟨w,hw⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp
  apply h_symm F C model distinct (by omega) (by omega)
  intro x
  by_cases yes : ∃ u v : Fin 14, (u.val,v.val) ∈ edges ∧ x u=true ∧ x v=true
  · have ft : F x=true := decide_eq_true yes
    rw [ft]
    obtain ⟨u,v,he,hu,hv⟩ := yes
    obtain ⟨r,hr⟩ := posRows u v he
    apply mono (sample r.val) x (fun j hj => ?_) ((extracted r.val).trans (posbit r))
    rcases hr j hj with rfl|rfl
    · exact hu
    · exact hv
  · have ff : F x=false := decide_eq_false yes
    rw [ff]
    obtain ⟨r,hp,hl⟩ := negRows (fun i => x (pt i))
    have below (k : Fin 14) (hk : x k=true) : sample (21+r.val) k=true := by
      by_cases lo : k.val<7
      · let i : Fin 7 := ⟨k.val,lo⟩
        have eq : pt i=k := Fin.ext rfl
        exact eq ▸ hp i (eq.symm ▸ hk)
      · let j : Fin 7 := ⟨k.val-7,by omega⟩
        have eq : ln j=k := Fin.ext (by dsimp [ln,j]; omega)
        rw [←eq] at hk ⊢
        apply hl j
        intro i hi edge
        exact yes ⟨pt i,ln j,edge,hi,hk⟩
    cases hx : C.eval (List.ofFn x)
    · rfl
    · have bad := mono x (sample (21+r.val)) below hx
      rw [extracted,negbit r] at bad
      contradiction
