import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1972.Ports
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
theorem m1892_eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl step x).getD C.output false := rfl

theorem m1892_getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

def shift (cut replacement i : Nat) : Nat :=
  if i < cut then i else if i=cut then replacement else i-1

def change (cut replacement : Nat) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (shift cut replacement)⟩

def bypass (n : Nat) (pre post : List Gate) (o replacement : Nat) : Circuit :=
  ⟨pre ++ post.map (change (n+pre.length) replacement),shift (n+pre.length) replacement o⟩

def value (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem foldLength (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,step] <;> omega

theorem extendRead (old fresh : List Bool) (cut replacement : Nat)
    (size : old.length = fresh.length+1) (room : cut ≤ fresh.length)
    (valid : replacement < cut ∨ fresh.length < replacement)
    (agree : ∀ i, old.getD i false = fresh.getD (shift cut replacement i) false)
    (v : Bool) (i : Nat) :
    (old++[v]).getD i false = (fresh++[v]).getD (shift cut replacement i) false := by
  rw [m1892_getD_snoc,m1892_getD_snoc,agree]
  by_cases ie : i=old.length
  · have se : shift cut replacement i = fresh.length := by
      have gt : cut < i := by omega
      simp [shift,show ¬i < cut by omega,show i≠cut by omega] <;> omega
    rw [if_pos ie,if_pos se]
  · have se : shift cut replacement i ≠ fresh.length := by
      simp only [shift]
      split_ifs <;> omega
    rw [if_neg ie,if_neg se]

theorem foldAgree (cut replacement : Nat) (post : List Gate) (old fresh : List Bool)
    (size : old.length=fresh.length+1) (room : cut ≤ fresh.length)
    (valid : replacement < cut ∨ fresh.length+post.length ≤ replacement)
    (agree : ∀ i, old.getD i false = fresh.getD (shift cut replacement i) false) :
    ∀ i, (post.foldl step old).getD i false =
      ((post.map (change cut replacement)).foldl step fresh).getD (shift cut replacement i) false := by
  induction post generalizing old fresh with
  | nil => exact agree
  | cons g post ih =>
    have v : value old g = value fresh (change cut replacement g) := by
      unfold value change
      simp only [List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => agree i)
    simp only [List.map_cons,List.foldl_cons]
    apply ih
    · simp [step,size]
    · simp [step] <;> omega
    · simp [step,List.length_cons] at * <;> omega
    · intro i
      change (old ++ [value old g]).getD i false =
        (fresh ++ [value fresh (change cut replacement g)]).getD _ false
      rw [←v]
      apply extendRead old fresh cut replacement size room _ agree
      simp only [List.length_cons] at valid
      omega

theorem evalBypass (n : Nat) (pre post : List Gate) (o replacement : Nat)
    (valid : replacement < n+pre.length ∨ n+pre.length+post.length ≤ replacement)
    (x : Fin n → Bool) :
    (bypass n pre post o replacement).eval (List.ofFn x) =
      (let w := pre.foldl step (List.ofFn x);
       post.foldl step (w ++ [w.getD replacement false])).getD o false := by
  let w := pre.foldl step (List.ofFn x)
  have len : w.length = n+pre.length := by simp [w,foldLength]
  rw [m1892_eval_eq]
  change ((pre ++ post.map (change (n+pre.length) replacement)).foldl step _).getD _ false = _
  rw [List.foldl_append]
  change ((post.map (change (n+pre.length) replacement)).foldl step w).getD _ false = _
  symm
  apply foldAgree (n+pre.length) replacement post (w++[w.getD replacement false]) w
  · simp
  · omega
  · omega
  · intro i
    rw [m1892_getD_snoc]
    by_cases lt : i < w.length
    · simp [shift,←len,lt,show i≠w.length by omega]
    by_cases eq : i=w.length
    · simp [shift,←len,lt,eq]
    · have h1 : w.length ≤ i := by omega
      have h2 : w.length ≤ i-1 := by omega
      simp [shift,←len,lt,eq,List.getD_eq_getElem?_getD,List.getElem?_eq_none h1,
        List.getElem?_eq_none h2]

theorem short (n : Nat) (pre post : List Gate) (o r : Nat) (g : Gate) :
    (bypass n pre post o r).size+1=(Circuit.mk (pre++g::post) o).size := by
  simp [bypass,Circuit.size] <;> omega


def source (pre post : List Gate) (a b o : Nat) : Circuit :=
  ⟨pre ++ ⟨.or,[a,b]⟩ :: post,o⟩

def tailOr (n : Nat) (C : Circuit) (w : Nat) : Circuit :=
  ⟨C.gates++[⟨.or,[C.output,w]⟩],n+C.size⟩

theorem prefix_read (gs : List Gate) (w : List Bool) (j : Nat) (room : j<w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ room

theorem tail_eval (n : Nat) (C : Circuit) (w : Nat) (x : Fin n → Bool) :
    (tailOr n C w).eval (List.ofFn x) =
      (C.eval (List.ofFn x) || (C.gates.foldl step (List.ofFn x)).getD w false) := by
  let W := C.gates.foldl step (List.ofFn x)
  have len : W.length = n+C.size := by simp [W,foldLength,Circuit.size]
  change ((C.gates++[⟨.or,[C.output,w]⟩]).foldl step (List.ofFn x)).getD (n+C.size) false = _
  rw [List.foldl_append]
  change (W++[_]).getD (n+C.size) false = (W.getD C.output false || W.getD w false)
  rw [m1892_getD_snoc,if_pos len.symm]
  simp [GateOp.eval]

theorem source_eval (n : Nat) (pre post : List Gate) (a b o : Nat) (x : Fin n → Bool) :
    (source pre post a b o).eval (List.ofFn x) =
      (let w := pre.foldl step (List.ofFn x);
        (post.foldl step (w++[w.getD a false || w.getD b false])).getD o false) := by
  rw [m1892_eval_eq]
  simp [source,List.foldl_append,step,GateOp.eval]

theorem move_or (n : Nat) (pre post : List Gate) (a b o : Nat) (ab : a<n+pre.length)
    (bb : b<n+pre.length) (fan : FanInTwo (source pre post a b o))
    (absorb : ∀ x : Fin n → Bool, (source pre post a b o).eval (List.ofFn x)=false →
      (pre.foldl step (List.ofFn x)).getD b false=false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = (source pre post a b o).size ∧
      D.gates.getLast? = some ⟨.or,[(bypass n pre post o a).output,b]⟩ ∧
      circuitFun n D = circuitFun n (source pre post a b o) := by
  let B := bypass n pre post o a
  let D := tailOr n B b
  refine ⟨D,?_,?_,?_,?_⟩
  · intro h hh
    change h ∈ (pre++post.map (change (n+pre.length) a))++[⟨.or,[B.output,b]⟩] at hh
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hh
    rcases hh with (hp|⟨g,hg,rfl⟩)|rfl
    · exact fan h (List.mem_append_left _ hp)
    · obtain ⟨op,ar⟩ := fan g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))
      exact ⟨op,by simpa [change] using ar⟩
    · simp
  · simp [D,B,tailOr,source,bypass,Circuit.size]
  · simp [D,tailOr,B]
  · funext x
    change (tailOr n B b).eval (List.ofFn x) = (source pre post a b o).eval (List.ofFn x)
    rw [tail_eval]
    let w := pre.foldl step (List.ofFn x)
    have bw : b < w.length := by simpa [w,foldLength] using bb
    have back : (B.gates.foldl step (List.ofFn x)).getD b false = w.getD b false := by
      change ((pre++_).foldl step (List.ofFn x)).getD b false = _
      rw [List.foldl_append]
      exact prefix_read _ _ _ bw
    rw [back]
    cases hb : w.getD b false with
    | false =>
      rw [Bool.or_false,source_eval,evalBypass n pre post o a (Or.inl ab)]
      change (post.foldl step (w++[w.getD a false])).getD o false =
        (post.foldl step (w++[w.getD a false || w.getD b false])).getD o false
      rw [hb,Bool.or_false]
    | true =>
      rw [Bool.or_true]
      cases eq : (source pre post a b o).eval (List.ofFn x) with
      | true => rfl
      | false => exact False.elim (Bool.noConfusion (hb.symm.trans (absorb x eq)))

end PEqualNP.Outside.L_meta_1972.Ports
