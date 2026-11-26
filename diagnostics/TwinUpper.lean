import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21872.Merge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev BFn (n : Nat) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def MonSize (n : ℕ) (f : BFn n) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : MonSize n h s) : MonSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this


theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

def bank {r c : Nat} (u : Fin r) (bits : Fin c → Bool) : Fin (r+c) → Bool :=
  Fin.append (fun i => decide (i = u)) bits

def hot {c : Nat} (v : Fin c) : Fin c → Bool := fun i => decide (i = v)

theorem bank_list {r c : Nat} (u : Fin r) (v : Fin c) :
    List.ofFn (bank u (hot v)) = oneEach u v := by
  rw [bank, List.ofFn_fin_append]
  rfl

theorem hot_cast {c : Nat} (v : Fin c) :
    hot v.castSucc = Fin.snoc (hot v) false := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hot]

theorem hot_last (c : Nat) :
    hot (Fin.last c) = Fin.snoc (fun _ : Fin c => false) true := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hot]

theorem withLast {r c : Nat} (u : Fin r) (x : Fin c → Bool) (b : Bool) :
    List.ofFn (Fin.snoc (bank u x) b) = List.ofFn (bank u (Fin.snoc x b)) := by
  rw [ofFn_snoc, bank, List.ofFn_fin_append, bank, List.ofFn_fin_append, ofFn_snoc, List.append_assoc]

theorem castRow {r c : Nat} (u : Fin r) (v : Fin c) :
    List.ofFn (Fin.snoc (bank u (hot v)) false) = oneEach u v.castSucc := by
  rw [withLast, ← hot_cast, bank_list]

theorem lastRow {r c : Nat} (u : Fin r) :
    List.ofFn (Fin.snoc (bank u (fun _ : Fin c => false)) true) = oneEach u (Fin.last c) := by
  rw [withLast, ← hot_last, bank_list]


def joinMap {n : Nat} (p i : Fin n) : Fin (n+2) :=
  if i = p then Fin.last (n+1) else i.castSucc.castSucc

def meld {n : Nat} (p : Fin n) (x : Fin (n+1) → Bool) (i : Fin n) : Bool :=
  if i = p then x p.castSucc || x (Fin.last n) else x i.castSucc

def extraBit {n : Nat} (p : Fin n) (x : Fin (n+1) → Bool) : Fin (n+2) → Bool :=
  Fin.snoc x (x p.castSucc || x (Fin.last n))

def joinGate {n : Nat} (p : Fin n) : Gate := ⟨.or,[p.val,n]⟩

theorem joinRead {n : Nat} (p : Fin n) (x : Fin (n+1) → Bool) :
    extraBit p x ∘ joinMap p = meld p x := by
  funext i
  by_cases h : i = p <;> simp [extraBit,joinMap,meld,h]

theorem arrayGet {k : Nat} (x : Fin k → Bool) (i : Fin k) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

theorem joinStep {n : Nat} (p : Fin n) (x : Fin (n+1) → Bool) :
    step (List.ofFn x) (joinGate p) = List.ofFn (extraBit p x) := by
  have hp := arrayGet x p.castSucc
  have hn := arrayGet x (Fin.last n)
  simp only [Fin.val_castSucc,Fin.val_last] at hp hn
  rw [extraBit,ofFn_snoc]
  simp [step,joinGate,GateOp.eval,hp,hn]

theorem mergePhysical {n s : Nat} (p : Fin n) (f : BFn n) (h : MonSize n f s) :
    MonSize (n+1) (fun x => f (meld p x)) (s+1) := by
  obtain ⟨D,hm,hs,ev⟩ := relabel_size (joinMap p) f s h
  let E : Circuit := ⟨joinGate p :: D.gates,D.output⟩
  refine ⟨E,?_,?_,?_⟩
  · intro g hg
    change g ∈ joinGate p :: D.gates at hg
    rcases List.mem_cons.mp hg with h | h
    · subst g
      simp [joinGate]
    · exact hm _ h
  · change (joinGate p :: D.gates).length ≤ s+1
    change D.gates.length ≤ s at hs
    simpa using Nat.succ_le_succ hs
  · intro x
    change D.eval (step (List.ofFn x) (joinGate p)) = _
    rw [joinStep,ev,joinRead]

theorem meldFalse {n : Nat} (p : Fin n) (x : Fin n → Bool) :
    meld p (Fin.snoc x false) = x := by
  funext i
  by_cases h : i = p <;> simp [meld,h]

theorem meldTrue {r c : Nat} (u : Fin r) (t : Fin c) :
    meld (Fin.natAdd r t) (Fin.snoc (bank u (fun _ : Fin c => false)) true) = bank u (hot t) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have ne : Fin.castAdd c a ≠ Fin.natAdd r t := by
      intro eq
      have hh := congrArg Fin.val eq
      simp at hh
      omega
    simp [meld,ne,bank]
  · by_cases h : b = t
    · subst b
      simp [meld,bank,hot]
    · have ne : Fin.natAdd r b ≠ Fin.natAdd r t := by
        intro eq
        apply h
        apply Fin.ext
        have hh := congrArg Fin.val eq
        simpa using hh
      simp [meld,ne,bank,hot,h]

def duplicate {r c : Nat} (A : Fin r → Fin c → Bool) (t : Fin c) (u : Fin r) (v : Fin (c+1)) : Bool :=
  A u (Fin.lastCases t (fun j => j) v)

theorem duplicate_upper {r c s : Nat} (A : Fin r → Fin c → Bool) (t : Fin c) (h : RepSizeAtMost A s) :
    RepSizeAtMost (duplicate A t) (s+1) := by
  obtain ⟨C,hm,hs,rep⟩ := h
  let f : BFn (r+c) := fun x => C.eval (List.ofFn x)
  obtain ⟨D,hd,hk,ev⟩ := mergePhysical (Fin.natAdd r t) f ⟨C,hm,hs,fun _ => rfl⟩
  refine ⟨D,hd,hk,?_⟩
  intro u v
  refine Fin.lastCases ?_ (fun i => ?_) v
  · rw [← lastRow,ev]
    change f (meld (Fin.natAdd r t) (Fin.snoc (bank u (fun _ : Fin c => false)) true)) = _
    rw [meldTrue]
    change C.eval (List.ofFn (bank u (hot t))) = _
    rw [bank_list]
    simpa [duplicate] using rep u t
  · rw [← castRow,ev]
    change f (meld (Fin.natAdd r t) (Fin.snoc (bank u (hot i)) false)) = _
    rw [meldFalse]
    change C.eval (List.ofFn (bank u (hot i))) = _
    rw [bank_list]
    simpa [duplicate] using rep u i
end PEqualNP.Outside.L_meta_21872.Merge

open PEqualNP.Represents PEqualNP.Outside.L_meta_21872.Merge in
theorem PEqualNP.Outside.L_meta_21872 {r c s : Nat} (A : Fin r → Fin c → Bool) (t : Fin c) (h : RepSizeAtMost A s) : RepSizeAtMost (duplicate A t) (s+1) := duplicate_upper A t h
