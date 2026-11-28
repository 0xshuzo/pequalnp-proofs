import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9829.SignedRelocation
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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
def original (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat) : Circuit :=
  ⟨pre++(g::post),out⟩
def value (pre : List Gate) (g : Gate) (x : List Bool) :=
  g.op.eval (g.inputs.map fun i => (W pre x).getD i false)
def after (pre post : List Gate) (out : Nat) (x : List Bool) (v : Bool) :=
  (W post (W pre x++[v])).getD out false

theorem origSplit (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat) (x : List Bool) :
    (original pre g post out).eval x=after pre post out x (value pre g x) := by
  simp only [original,Circuit.eval,Circuit.wires,after,W,value,List.foldl_append,List.foldl_cons]

theorem protectedWire (gs : List Gate) (w : List Bool) (i : Nat) (small : i<w.length) :
    (W gs w).getD i false=w.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g h =>
    rw [W_snoc,getD_snoc,if_pos (by rw [W_length]; omega),h]

def mutedLow (pre post : List Gate) (out : Nat) : Circuit := ⟨pre ++ (⟨.or,[]⟩ :: post),out⟩
def rewireLow (n : Nat) (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat) : Circuit :=
  let k := n+pre.length+1+post.length
  mutedLow pre (post++[g,⟨.or,[out,k]⟩]) (k+1)

theorem rewireLowEval {n : Nat} (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat)
    (ordered : ∀i∈g.inputs,i<n+pre.length) (output : out<n+pre.length+1+post.length)
    (x : Fin n → Bool) :
    (rewireLow n pre g post out).eval (List.ofFn x) =
      (after pre post out (List.ofFn x) false || value pre g (List.ofFn x)) := by
  let w := W pre (List.ofFn x)
  let z := W post (w++[false])
  let k := n+pre.length+1+post.length
  have wlen : w.length=n+pre.length := by simp [w,W_length]
  have zlen : z.length=k := by simp [z,k,W_length,wlen,Nat.add_assoc]
  have atRead (i) (hi : i∈g.inputs) : z.getD i false=w.getD i false := by
    have sm : i<w.length := wlen.symm ▸ ordered i hi
    rw [show z=W post (w++[false]) from rfl,protectedWire _ _ _ (by simp;omega),getD_snoc,if_pos sm]
  have same : g.inputs.map (fun i => z.getD i false)=g.inputs.map (fun i => w.getD i false) :=
    List.map_congr_left atRead
  have folded : (rewireLow n pre g post out).eval (List.ofFn x)=
      (W [g,⟨.or,[out,k]⟩] z).getD (k+1) false := by
    simp [rewireLow,mutedLow,Circuit.eval,Circuit.wires,W,z,w,k,List.foldl_append,GateOp.eval]
  rw [folded]
  let v := g.op.eval (g.inputs.map fun i => z.getD i false)
  change (((z++[v])++[GateOp.or.eval ([out,k].map fun i => (z++[v]).getD i false)])).getD (k+1) false = _
  have small : out<z.length := by simpa [zlen,k] using output
  rw [getD_snoc,if_neg (by simp [zlen]),if_pos (by simp [zlen])]
  simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false]
  rw [getD_snoc,if_pos small,getD_snoc,if_neg (by omega),if_pos (by omega)]
  change (z.getD out false || g.op.eval (g.inputs.map fun i => z.getD i false))=_
  rw [same]
  rfl
theorem relocationLow {n : Nat} (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat)
    (ordered : ∀ i ∈ g.inputs, i < n+pre.length) (output : out<n+pre.length+1+post.length)
    (safe : ∀ x : Fin n → Bool, value pre g (List.ofFn x)=true →
       (original pre g post out).eval (List.ofFn x)=true)
    (x : Fin n → Bool) :
      (rewireLow n pre g post out).eval (List.ofFn x) =
        (original pre g post out).eval (List.ofFn x) := by
  rw [rewireLowEval pre g post out ordered output x]
  cases h : value pre g (List.ofFn x) with
  | false => simp [origSplit,h]
  | true => simp [safe x h]
def mutedHigh (pre post : List Gate) (out : Nat) : Circuit := ⟨pre ++ (⟨.and,[]⟩ :: post),out⟩
def rewireHigh (n : Nat) (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat) : Circuit :=
  let k := n+pre.length+1+post.length
  mutedHigh pre (post++[g,⟨.and,[out,k]⟩]) (k+1)

theorem rewireHighEval {n : Nat} (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat)
    (ordered : ∀i∈g.inputs,i<n+pre.length) (output : out<n+pre.length+1+post.length)
    (x : Fin n → Bool) :
    (rewireHigh n pre g post out).eval (List.ofFn x) =
      (after pre post out (List.ofFn x) true && value pre g (List.ofFn x)) := by
  let w := W pre (List.ofFn x)
  let z := W post (w++[true])
  let k := n+pre.length+1+post.length
  have wlen : w.length=n+pre.length := by simp [w,W_length]
  have zlen : z.length=k := by simp [z,k,W_length,wlen,Nat.add_assoc]
  have atRead (i) (hi : i∈g.inputs) : z.getD i false=w.getD i false := by
    have sm : i<w.length := wlen.symm ▸ ordered i hi
    rw [show z=W post (w++[true]) from rfl,protectedWire _ _ _ (by simp;omega),getD_snoc,if_pos sm]
  have same : g.inputs.map (fun i => z.getD i false)=g.inputs.map (fun i => w.getD i false) :=
    List.map_congr_left atRead
  have folded : (rewireHigh n pre g post out).eval (List.ofFn x)=
      (W [g,⟨.and,[out,k]⟩] z).getD (k+1) false := by
    simp [rewireHigh,mutedHigh,Circuit.eval,Circuit.wires,W,z,w,k,List.foldl_append,GateOp.eval]
  rw [folded]
  let v := g.op.eval (g.inputs.map fun i => z.getD i false)
  change (((z++[v])++[GateOp.and.eval ([out,k].map fun i => (z++[v]).getD i false)])).getD (k+1) false = _
  have small : out<z.length := by simpa [zlen,k] using output
  rw [getD_snoc,if_neg (by simp [zlen]),if_pos (by simp [zlen])]
  simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true]
  rw [getD_snoc,if_pos small,getD_snoc,if_neg (by omega),if_pos (by omega)]
  change (z.getD out false && g.op.eval (g.inputs.map fun i => z.getD i false))=_
  rw [same]
  rfl
theorem relocationHigh {n : Nat} (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat)
    (ordered : ∀ i ∈ g.inputs, i < n+pre.length) (output : out<n+pre.length+1+post.length)
    (safe : ∀ x : Fin n → Bool, value pre g (List.ofFn x)=false →
       (original pre g post out).eval (List.ofFn x)=false)
    (x : Fin n → Bool) :
      (rewireHigh n pre g post out).eval (List.ofFn x) =
        (original pre g post out).eval (List.ofFn x) := by
  rw [rewireHighEval pre g post out ordered output x]
  cases h : value pre g (List.ofFn x) with
  | false => simp [safe x h]
  | true => simp [origSplit,h]
end PEqualNP.Outside.L_meta_9829.SignedRelocation
