import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17744
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section Reindex
variable {m n : Nat}

def liftIn (r : Fin n → Option (Fin m)) (x : Fin m → Bool) (w : Fin n) :=
  (r w).elim false x

def ref (r : Fin n → Option (Fin m)) (bound v : Nat) : Nat :=
  if h : v < n then (r ⟨v,h⟩).elim (m+bound+1) Fin.val else m+(v-n)

def rewriteGate (rr : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map rr⟩

def reindex (r : Fin n → Option (Fin m)) (C : Circuit) : Circuit :=
  let rr := ref r C.size
  ⟨C.gates.map (rewriteGate rr),rr C.output⟩

theorem ref_next (r : Fin n → Option (Fin m)) (cap k : Nat) (hk : k ≤ cap) (i : Nat) :
    ref r cap i = m+k ↔ i=n+k := by
  by_cases h : i<n
  · simp only [ref,dif_pos h]
    cases e : r ⟨i,h⟩ with
    | none => simp only [Option.elim_none]; omega
    | some j => simp only [Option.elim_some]; have := j.isLt; omega
  · simp only [ref,dif_neg h]; omega

theorem snoc_off (w : List Bool) (b : Bool) (i : Nat) (hn : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases lt : i<w.length
  · exact getD_snoc_lt w b i lt
  · rw [getD_snoc_gt w b i (by omega), List.getD_eq_default _ _ (by omega)]

theorem fold_ref (r : Fin n → Option (Fin m)) (cap : Nat) (gs : List Gate) (A B : List Bool)
    (k : Nat) (ha : A.length=n+k) (hb : B.length=m+k)
    (hlen : k+gs.length≤cap) (eq : ∀ i,A.getD i false = B.getD (ref r cap i) false) :
    ∀ i,(wf gs A).getD i false =
      (wf (gs.map (rewriteGate (ref r cap))) B).getD (ref r cap i) false := by
  induction gs generalizing k A B with
  | nil => exact eq
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i => A.getD i false))
    have hg : (rewriteGate (ref r cap) g).op.eval ((rewriteGate (ref r cap) g).inputs.map
        (fun i => B.getD i false)) = v := by
      simp only [rewriteGate,List.map_map,Function.comp_def,v,eq]
    simp only [List.map_cons,wf,List.foldl_cons] at ⊢
    change ∀ i, (wf gs (A++[v])).getD i false = (wf (gs.map (rewriteGate (ref r cap)))
      (B++[(rewriteGate (ref r cap) g).op.eval ((rewriteGate (ref r cap) g).inputs.map
        fun j => B.getD j false)])).getD (ref r cap i) false
    rw [hg]
    apply ih (A++[v]) (B++[v]) (k+1) (by simp [ha]; omega) (by simp [hb]; omega)
      (by simp at hlen; omega)
    intro i
    have hit := ref_next r cap k (by simp at hlen; omega) i
    by_cases hi : i=n+k
    · have hi' : i=A.length := hi.trans ha.symm
      have hj : ref r cap i=B.length := (hit.mpr hi).trans hb.symm
      rw [hi',getD_snoc_eq]
      rw [← hi',hj,getD_snoc_eq]
    · rw [snoc_off _ _ _ (by omega),snoc_off _ _ _ (fun e => hi (hit.mp (e.trans hb))),eq]

theorem reindex_eval (r : Fin n → Option (Fin m)) (C : Circuit) (x : Fin m → Bool) :
    (reindex r C).eval (List.ofFn x) = C.eval (List.ofFn (liftIn r x)) := by
  symm
  apply fold_ref r C.size C.gates _ _ 0 (by simp) (by simp) (by simp [Circuit.size])
  intro i
  by_cases hi : i<n
  · simp only [ref,dif_pos hi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos hi,Option.getD_some,liftIn]
    cases h : r ⟨i,hi⟩ with
    | some j => simp [j.isLt]
    | none => simp; omega
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp [ref,hi])]
theorem reindex_mono (r : Fin n → Option (Fin m)) (C : Circuit) (mc : Monotone2 C) :
    Monotone2 (reindex r C) := by
  intro g hg
  obtain ⟨h,hm,rfl⟩ := List.mem_map.mp hg
  simpa [rewriteGate] using mc h hm
end Reindex

end PEqualNP.Outside.L_meta_17744
