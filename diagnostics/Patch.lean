import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
namespace Repair5284
def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]

theorem keepW (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (W gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g t ih =>
    change (W t (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := {C with gates := C.gates.set j g}
def off : Gate := ⟨.or,[]⟩
def literal {n : ℕ} (p r : Fin n) : Gate := ⟨.and,[p.val,r.val]⟩

theorem take_set' {α : Type} (L : List α) (k : ℕ) (h : k<L.length) (g : α) :
    L.set k g = L.take k ++ g :: L.drop (k+1) := by
  induction L generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change a :: t.set k g = a :: (t.take k ++ g :: t.drop (k+1))
      exact congrArg (List.cons a) (ih k (by simpa using h))

theorem psize (C : Circuit) (j : ℕ) (g : Gate) : (patch C j g).size = C.size := by
  change (C.gates.set j g).length = C.gates.length
  simp

theorem pop (C : Circuit) (j i : ℕ) (g : Gate) (hj : j<C.size) :
    gateAt (patch C j g) i = if i=j then g else gateAt C i := by
  change (C.gates.set j g).getD i _ = _
  rw [List.getD_eq_getElem?_getD]
  by_cases eq : i=j
  · subst i
    simp [List.getElem?_set,hj]
  · rw [if_neg eq,List.getElem?_set_ne (Ne.symm eq)]
    exact (List.getD_eq_getElem?_getD ..).symm

theorem pmono {C : Circuit} (m : Monotone2 C) {j : ℕ} (hj : j<C.size) {g : Gate}
    (good : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    Monotone2 (patch C j g) := by
  intro x hx
  change x∈C.gates.set j g at hx
  rw [take_set' C.gates j hj] at hx
  rcases List.mem_append.mp hx with hp | ht
  · exact m _ (List.mem_of_mem_take hp)
  · rcases List.mem_cons.mp ht with rfl | h
    · exact good
    · exact m _ (List.mem_of_mem_drop h)

def value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem pairValue {n : ℕ} (pre : List Gate) (x : Fin n → Bool) (u v : Fin n) :
    value (literal u v) (W pre (List.ofFn x)) = (x u && x v) := by
  have atRaw (w : Fin n) : (W pre (List.ofFn x)).getD w.val false = x w := by
    rw [keepW _ _ _ (by simp)]
    simp [ofFn_getD]
  simp [literal,value,GateOp.eval,atRaw]

theorem offValue (w : List Bool) : value off w=false := rfl

theorem ppLe {n : ℕ} (C : Circuit) (m : Monotone2 C) {j : ℕ} (hj : j<C.size)
    (g f : Gate) (x : Fin n → Bool)
    (rise : value g (W (C.gates.take j) (List.ofFn x)) = true →
      value f (W (C.gates.take j) (List.ofFn x)) = true) :
    Le ((patch C j g).wires (List.ofFn x)) ((patch C j f).wires (List.ofFn x)) := by
  let w := W (C.gates.take j) (List.ofFn x)
  have op (a : Gate) (ha : a ∈ C.gates.drop (j+1)) : a.op=.and ∨ a.op=.or := by
    simpa using (m _ (List.mem_of_mem_drop ha)).1
  have step (h : Gate) : (patch C j h).wires (List.ofFn x) =
      W (C.gates.drop (j+1)) (w++[value h w]) := by
    change W (C.gates.set j h) _ = _
    rw [take_set' _ _ hj]
    simp [W,w,value,List.foldl_append]
  rw [step,step]
  apply W_mono _ op _ _ (by simp)
  intro i h
  rw [getD_snoc] at h ⊢
  by_cases lt : i<w.length
  · simpa [lt] using h
  by_cases eq : i=w.length
  · simpa [lt,eq] using rise (by simpa [lt,eq] using h)
  · simpa [lt,eq] using h

theorem orig (C : Circuit) {j : ℕ} (hj : j<C.size) : patch C j (gateAt C j) = C := by
  have eq : gateAt C j = C.gates[j] := by
    change C.gates.getD j _ = _
    exact List.getD_eq_getElem _ _ hj
  cases C with
  | mk gs out =>
    change (⟨gs.set j (gateAt ⟨gs,out⟩ j),out⟩ : Circuit) = _
    rw [eq]
    simp

theorem selfWire {n : ℕ} (C : Circuit) {j : ℕ} (hj : j<C.size)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = value g (W (C.gates.take j) (List.ofFn x)) := by
  let w := W (C.gates.take j) (List.ofFn x)
  have len : w.length=n+j := by simp [w,W_length,List.length_take,Nat.min_eq_left hj.le]
  change (W (C.gates.set j g) (List.ofFn x)).getD (n+j) false = _
  rw [take_set' _ _ hj]
  have rs : W (C.gates.take j ++ g :: C.gates.drop (j+1)) (List.ofFn x) =
      W (C.gates.drop (j+1)) (w++[value g w]) := by simp [W,w,value,List.foldl_append]
  rw [rs,keepW _ _ _ (by simp [len]),←len]
  simp [w]

end Repair5284
