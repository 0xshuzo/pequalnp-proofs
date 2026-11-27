import PEqualNP.Defs
namespace PencilArithmetic3471

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

end PencilArithmetic3471
namespace Bank8811
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PencilArithmetic3471

abbrev SubBank (α : Type*) := ℕ → Set α

def Steps {α : Type*} (W : SubBank α) (n s : ℕ) :=
  ∀ j < s, ∃ a < n+j, ∃ b < n+j,
    W (n+j) = W a ∪ W b ∨ W (n+j)=W a ∨ W (n+j)=∅ ∨ W (n+j)=W a ∩ W b

theorem compile {α : Type*} (n s o : ℕ) (W : SubBank α) (raw : α → Fin n → Bool)
    (hr : ∀ z (i : Fin n), raw z i = true ↔ z ∈ W i.val)
    (hs : Steps W n s) (ho : o < n+s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size=s ∧
      ∀ z, circuitFun n C (raw z)=true ↔ z ∈ W o := by
  classical
  have pick (j : Fin s) : ∃ g : Gate,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 ∧
      (∀ a ∈ g.inputs, a < n+j.val) ∧
      ∀ z : α, g.op.eval (g.inputs.map (fun i => decide (z ∈ W i))) = true ↔ z ∈ W (n+j.val) := by
    obtain ⟨a,ha,b,hb,e|e|e|e⟩ := hs j j.isLt
    · refine ⟨⟨.or,[a,b]⟩,Or.inr rfl,by decide,?_,?_⟩
      · simp [ha,hb]
      · intro z; simp [GateOp.eval,e]
    · refine ⟨⟨.or,[a]⟩,Or.inr rfl,by decide,?_,?_⟩
      · simp [ha]
      · intro z; simp [GateOp.eval,e]
    · refine ⟨⟨.or,[]⟩,Or.inr rfl,by decide,by simp,?_⟩
      intro z; simp [GateOp.eval,e]
    · refine ⟨⟨.and,[a,b]⟩,Or.inl rfl,by decide,?_,?_⟩
      · simp [ha,hb]
      · intro z; simp [GateOp.eval,e]
  choose gs spec using pick
  let C : Circuit := ⟨List.ofFn gs,o⟩
  have sz : C.size=s := by simp [C,Circuit.size]
  refine ⟨C,?_,sz,?_⟩
  · intro g hg
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hg
    exact ⟨(spec j).1,(spec j).2.1⟩
  intro z
  have allWire (k : ℕ) (hk : k < n+s) : val C (raw z) k=true ↔ z ∈ W k := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      by_cases h : k < n
      · rw [show val C (raw z) k = raw z ⟨k,h⟩ from val_input C (raw z) ⟨k,h⟩]; exact hr z ⟨k,h⟩
      let j : Fin s := ⟨k-n,by omega⟩
      have eq : n+j.val=k := by dsimp [j]; omega
      have atj : C.gates[j.val]? = some (gs j) := by simp [C]
      have gv := val_gate C (raw z) atj
      rw [eq] at gv
      have reads (a : ℕ) (ha : a ∈ (gs j).inputs) :
          operand C (raw z) k a = decide (z ∈ W a) := by
        have hprior := (spec j).2.2.1 a ha
        rw [eq] at hprior
        rw [operand,if_pos hprior]
        have hsem := ih a hprior (hprior.trans hk)
        by_cases hm : z ∈ W a
        · simp [hm,hsem.mpr hm]
        · have hn : val C (raw z) a=false := by cases e : val C (raw z) a <;> simp_all
          simp [hm,hn]
      rw [gv,List.map_congr_left reads]
      rw [← eq]
      exact (spec j).2.2.2 z
  exact allWire o ho

theorem upward {α : Type*} (n s : ℕ) (W : SubBank α) (hs : Steps W n s)
    {z t : α} (h : ∀ i < n, z ∈ W i → t ∈ W i) :
    ∀ k < n+s, z ∈ W k → t ∈ W k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hz
    by_cases raw : k<n
    · exact h k raw hz
    let j := k-n
    have he : n+j=k := by dsimp [j]; omega
    obtain ⟨a,ha,b,hb,e|e|e|e⟩ := hs j (by dsimp [j]; omega) <;> rw [he] at ha hb e <;> rw [e] at hz ⊢
    · rcases hz with h | h
      exact Or.inl (ih a ha (ha.trans hk) h)
      exact Or.inr (ih b hb (hb.trans hk) h)
    · exact ih a ha (ha.trans hk) hz
    · exact hz
    · exact ⟨ih a ha (ha.trans hk) hz.1, ih b hb (hb.trans hk) hz.2⟩

end Bank8811
