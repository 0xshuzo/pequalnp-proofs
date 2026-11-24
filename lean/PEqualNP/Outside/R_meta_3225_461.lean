import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Remove the sole extra OR reader. Its output is a copy on the low cofactor and true on the high cofactor.
-- The three sensitive rows rule out five input wires as that copy and constrain every computed wire used as the copy.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_3225_461
    (raw : let rows := ([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ)
      let lo := fun (x : Fin 8 → Bool) => let k := tableIndex x
        (rows.getD (k / 64) 0).testBit (k % 64)
      let w := fun (b : Bool) (x : Fin 8 → Bool) =>
        [x 1, x 0, x 4, x 7, x 5, x 2, false, x 6, x 3, x 1 || b]
      ∀ (P Q : Circuit), FanInTwo P → FanInTwo Q → P.size + Q.size = 13 →
      P.output ∈ ([1,3,4,5,6] : List ℕ) →
      (∀ x : Fin 8 → Bool, Q.eval (P.wires (w false x) ++ [P.eval (w false x)]) = lo x) →
      ∃ x : Fin 8 → Bool, Q.eval (P.wires (w true x) ++ [true]) ≠ (lo x || x 0 || x 3))
    (computed : let rows := ([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ)
      let lo := fun (x : Fin 8 → Bool) => let k := tableIndex x
        (rows.getD (k / 64) 0).testBit (k % 64)
      let w := fun (b : Bool) (x : Fin 8 → Bool) =>
        [x 1, x 0, x 4, x 7, x 5, x 2, false, x 6, x 3, x 1 || b]
      ∀ (P Q : Circuit), FanInTwo P → FanInTwo Q → P.size + Q.size = 13 →
      (10 ≤ P.output ∧ P.output < 10 + P.size) →
      (∀ a : Fin 3, P.eval (w false (fun i => (([10,26,74] : List ℕ).getD a.val 0).testBit i.val)) = false) →
      (∀ x : Fin 8 → Bool, Q.eval (P.wires (w false x) ++ [P.eval (w false x)]) = lo x) →
      ∃ x : Fin 8 → Bool, Q.eval (P.wires (w true x) ++ [true]) ≠ (lo x || x 0 || x 3)) :
have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x8 ∈ x4.gates, x8.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x8.inputs) → (∀ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x9) = x3 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x10) ≠ (x3 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  intro read input z D fan size count existsOr correct
  let packed : (Fin 8 → Bool) → Bool := fun x =>
        let k := tableIndex x
        (([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (k / 64) 0).testBit (k % 64)
  have unpack : ∀ x, packed x = z x := by
    dsimp only [packed,z]
    decide +kernel
  have noReadGate (g : Gate) (basis : g.op = .and ∨ g.op = .or ∨ g.op = .not)
      (skip : read g = false) (w w' : List Bool)
      (agree : ∀ i, i ≠ 6 → w.getD i false = w'.getD i false) :
      g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
    obtain ⟨op,pins⟩ := g
    rcases basis with h|h|h <;> change op = _ at h <;> subst op
    · apply congrArg GateOp.and.eval
      apply List.map_congr_left
      intro i hi
      apply agree
      rintro rfl
      change (pins.any (fun j => decide (j = 6))) = false at skip
      have exclude : ∀ x ∈ pins, x ≠ 6 := by simpa using skip
      exact exclude 6 hi rfl
    · apply congrArg GateOp.or.eval
      apply List.map_congr_left
      intro i hi
      apply agree
      rintro rfl
      change (pins.any (fun j => decide (j = 6))) = false at skip
      have exclude : ∀ x ∈ pins, x ≠ 6 := by simpa using skip
      exact exclude 6 hi rfl
    · cases pins with
      | nil => rfl
      | cons i rest =>
        change (decide (i = 6) || false) = false at skip
        have ne : i ≠ 6 := by simpa using skip
        exact congrArg Bool.not (agree i ne)
  let stepSix (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have noReadSuffix (gs : List Gate)
      (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ read g = false)
      (w w' : List Bool) (len : w.length = w'.length)
      (agree : ∀ i, i ≠ 6 → w.getD i false = w'.getD i false) :
      ∀ i, i ≠ 6 → (gs.foldl stepSix w).getD i false = (gs.foldl stepSix w').getD i false := by
    induction gs generalizing w w' with
    | nil => exact agree
    | cons g gs ih =>
      obtain ⟨basis,skip⟩ := ok g (by simp)
      apply ih (fun h hh => ok h (List.mem_cons_of_mem g hh)) (stepSix w g) (stepSix w' g)
      · simp [stepSix,len]
      · intro i ne
        by_cases h : i < w.length
        · simpa only [stepSix,List.getD_append _ _ false i h,List.getD_append _ _ false i (len ▸ h)] using agree i ne
        · have he := noReadGate g basis skip w w' agree
          simp only [stepSix,List.getD_append_right _ _ _ _ (by omega : w.length ≤ i),
            List.getD_append_right _ _ _ _ (by omega : w'.length ≤ i),len,he]
  have split (gs : List Gate) (one : gs.countP read = 1) :
      ∃ pre g post, gs = pre ++ g :: post ∧ read g = true ∧
        ∀ h ∈ pre ++ post, read h = false := by
    induction gs with
    | nil => simp at one
    | cons g gs ih =>
      cases r : read g with
      | true =>
        have empty : gs.countP read = 0 := by simpa [List.countP_cons,r] using one
        exact ⟨[],g,gs,rfl,r,by simpa using List.countP_eq_zero.mp empty⟩
      | false =>
        obtain ⟨pre,k,post,eqn,rk,rest⟩ := ih (by simpa [List.countP_cons,r] using one)
        refine ⟨g::pre,k,post,by simp [eqn],rk,?_⟩
        intro h mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact r
        · exact rest h mem
  have preserved (gs : List Gate) (w : List Bool) (hw : 6 < w.length) :
      (gs.foldl stepSix w).getD 6 false = w.getD 6 false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (stepSix w g) (by simp [stepSix]; omega)]
      exact List.getD_append _ _ false 6 hw
  have lengthRun (gs : List Gate) (v : List Bool) :
      (gs.foldl stepSix v).length = v.length + gs.length := by
    induction gs generalizing v with
    | nil => simp
    | cons h gs ih =>
      rw [List.foldl_cons,ih]
      simp only [stepSix,List.length_append,List.length_cons,List.length_nil]
      omega
  obtain ⟨reader,mem,rop,reads⟩ := existsOr
  have rr : read reader = true := by
    change (if reader.op.eval [false,false] then reader.inputs.take 1 else reader.inputs).any (fun i => decide (i = 6)) = true
    rw [rop]
    change reader.inputs.any (fun i => decide (i=6)) = true
    exact List.any_eq_true.mpr ⟨6,reads,by decide⟩
  have positive : 0 < D.gates.countP read := List.countP_pos_iff.mpr ⟨reader,mem,rr⟩
  have one : D.gates.countP read = 1 := by omega
  by_cases outSix : D.output = 6
  · refine ⟨fun _ => false, ?_⟩
    change (D.gates.foldl stepSix (input true (fun _ => false))).getD D.output false ≠ _
    rw [outSix,preserved _ _ (by decide)]
    decide
  by_contra! high
  obtain ⟨pre,g,post,splitG,rg,rest⟩ := split D.gates one
  have which : reader = g := by
    rw [splitG] at mem
    rcases List.mem_append.mp mem with hm|hm
    · exact False.elim (by simpa [rr] using rest reader (List.mem_append_left _ hm))
    · rcases List.mem_cons.mp hm with h|hm
      · exact h
      · exact False.elim (by simpa [rr] using rest reader (List.mem_append_right _ hm))
  subst reader
  have total : pre.length + post.length = 13 := by
    change D.gates.length = 14 at size
    rw [splitG,List.length_append,List.length_cons] at size
    omega
  have inclP (t : Gate) (mt : t ∈ pre) : t ∈ D.gates := by rw [splitG]; simp [mt]
  have inclQ (t : Gate) (mt : t ∈ post) : t ∈ D.gates := by rw [splitG]; simp [mt]
  have inclG : g ∈ D.gates := by rw [splitG]; simp
  have base (t : Gate) (mt : t ∈ D.gates) : t.op = .and ∨ t.op = .or ∨ t.op = .not := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (fan t mt).1
  have okP (t : Gate) (mt : t ∈ pre) := And.intro (base t (inclP t mt)) (rest t (List.mem_append_left _ mt))
  have okQ (t : Gate) (mt : t ∈ post) := And.intro (base t (inclQ t mt)) (rest t (List.mem_append_right _ mt))
  have findTap (ps : List ℕ) (small : ps.length ≤ 2) (hit : 6 ∈ ps) :
      ∃ t : ℕ, ∀ W : List Bool, GateOp.or.eval (ps.map fun i => W.getD i false) =
        (W.getD 6 false || W.getD t false) := by
    rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
    · simp at hit
    · have qa : a = 6 := by simpa [eq_comm] using hit
      subst a
      exact ⟨6,fun w => by change (w.getD 6 false || false) = _; simp⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hit
      rcases hit with rfl | rfl
      · exact ⟨b,fun w => by change (_ || (_ || false)) = _; simp⟩
      · exact ⟨a,fun w => by change (_ || (_ || false)) = _; simp [Bool.or_comm]⟩
    · simp at small
  obtain ⟨t,ht⟩ := findTap g.inputs (fan g inclG).2 reads
  let w := fun (b : Bool) (x : Fin 8 → Bool) =>
    [x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3,x 1 || b]
  let p := if t < 10 + pre.length then t else 6
  let P : Circuit := ⟨pre,p⟩
  let Q : Circuit := ⟨post,D.output⟩
  have pf : FanInTwo P := fun t mt => fan t (inclP t mt)
  have qf : FanInTwo Q := fun t mt => fan t (inclQ t mt)
  let orig := fun b x => pre.foldl stepSix (input b x)
  let alt := fun b x => pre.foldl stepSix (w b x)
  have eqLen (b : Bool) (x : Fin 8 → Bool) : (orig b x).length = 10 + pre.length := by
    change (pre.foldl stepSix _).length = _
    rw [lengthRun]; rfl
  have altLen (b : Bool) (x : Fin 8 → Bool) : (alt b x).length = 10 + pre.length := by
    change (pre.foldl stepSix _).length = _
    rw [lengthRun]; rfl
  have agree (b : Bool) (x : Fin 8 → Bool) (i : ℕ) (hi : i ≠ 6) :
      (orig b x).getD i false = (alt b x).getD i false := by
    refine noReadSuffix pre okP (input b x) (w b x) rfl ?_ i hi
    intro j hj
    by_cases hj' : j < 10
    · interval_cases j <;> first | rfl | contradiction
    · rw [List.getD_eq_default _ false (by change 10 ≤ j; omega),
          List.getD_eq_default _ false (by change 10 ≤ j; omega)]
  have val6 (b : Bool) (x : Fin 8 → Bool) : (orig b x).getD 6 false = b :=
    preserved pre (input b x) (by change 6 < 10; decide)
  have alt6 (b : Bool) (x : Fin 8 → Bool) : (alt b x).getD 6 false = false :=
    preserved pre (w b x) (by change 6 < 10; decide)
  have tap (x : Fin 8 → Bool) : (orig false x).getD t false = P.eval (w false x) := by
    change _ = (alt false x).getD p false
    by_cases live : t < 10 + pre.length
    · simp only [p,live,↓reduceIte]
      by_cases ht6 : t = 6
      · rw [ht6] <;> exact (val6 false x).trans (alt6 false x).symm
      · exact agree false x t ht6
    · rw [show p = 6 by simp [p,live],alt6,List.getD_eq_default _ _ (by rw [eqLen]; omega)]
  have sim (b : Bool) (x : Fin 8 → Bool) :
      D.eval (input b x) = Q.eval (P.wires (w b x) ++ [if b then true else P.eval (w b x)]) := by
    change (D.gates.foldl stepSix _).getD D.output false =
        (post.foldl stepSix (alt b x ++ [_])).getD D.output false
    rw [splitG,List.foldl_append,List.foldl_cons]
    apply noReadSuffix post okQ _ _ _ _ _ outSix
    · change (orig b x ++ [_]).length = (alt b x ++ [_]).length
      simp only [List.length_append,List.length_cons,List.length_nil,eqLen,altLen]
    · intro i hi
      change (orig b x ++ [g.op.eval (g.inputs.map fun j => (orig b x).getD j false)]).getD i false = _
      have v : g.op.eval (g.inputs.map fun j => (orig b x).getD j false) =
          (if b then true else P.eval (w b x)) := by
        rw [rop,ht,val6]
        cases b
        · simpa using tap x
        · simp
      by_cases below : i < (orig b x).length
      · rw [List.getD_append _ _ _ _ below,List.getD_append _ _ _ _ (by rw [altLen]; simpa only [eqLen] using below)]
        exact agree b x i hi
      · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by rw [altLen]; rw [eqLen] at below; omega),eqLen,altLen,v]
  have low (x : Fin 8 → Bool) : Q.eval (P.wires (w false x) ++ [P.eval (w false x)]) = packed x :=
    (sim false x).symm.trans ((correct x).trans (unpack x).symm)
  have upper (x : Fin 8 → Bool) : Q.eval (P.wires (w true x) ++ [true]) = (packed x || x 0 || x 3) := by
    have hx := high x
    rw [← unpack x] at hx
    exact (sim true x).symm.trans hx
  let probe := fun (j : Fin 3) (i : Fin 8) => (([10,26,74] : List ℕ).getD j.val 0).testBit i.val
  have critical : ∀ j : Fin 3, w true (probe j) = w false (probe j) ∧ packed (probe j) = false ∧ probe j 3 = true := by decide +kernel
  have cold (j : Fin 3) : P.eval (w false (probe j)) = false := by
    cases hh : P.eval (w false (probe j)) with
    | false => rfl
    | true =>
      have l := low (probe j)
      have h := upper (probe j)
      rw [(critical j).1,(critical j).2.2,Bool.or_true] at h
      rw [hh,(critical j).2.1] at l
      exact h.symm.trans l
  by_cases rawTap : p < 10
  · have rawAt (j : Fin 3) : (w false (probe j)).getD p false = false := by
      have prekeep (ls : List Gate) (v : List Bool) (i : ℕ) (hv : i < v.length) :
          (ls.foldl stepSix v).getD i false = v.getD i false := by
        induction ls generalizing v with
        | nil => rfl
        | cons g gs ih =>
          rw [List.foldl_cons,ih (stepSix v g) (by simp [stepSix]; omega)]
          exact List.getD_append _ _ false i hv
      have h := cold j
      change (pre.foldl stepSix _).getD p false = false at h
      rwa [prekeep _ _ p (by exact rawTap)] at h
    have classify : ∀ i : Fin 10, (∀ j : Fin 3, (w false (probe j)).getD i.val false = false) →
        i.val ∈ ([1,3,4,5,6] : List ℕ) := by decide +kernel
    obtain ⟨x,hx⟩ := raw P Q pf qf total (classify ⟨p,rawTap⟩ rawAt) low
    exact hx (upper x)
  · have lim : p < 10 + pre.length := by unfold p; split <;> omega
    obtain ⟨x,hx⟩ := computed P Q pf qf total ⟨by change 10 ≤ p; omega,lim⟩ cold low
    exact hx (upper x)
