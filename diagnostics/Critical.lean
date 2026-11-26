import PEqualNP.Defs

namespace Bypass9739
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 10000
def m1892_stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem m1892_eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl m1892_stp x).getD C.output false := rfl

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

theorem m1892_ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem m1892_ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem m1892_mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl m1892_stp W1).getD i false = true → (gs.foldl m1892_stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (m1892_stp W1 g) (m1892_stp W2 g) (by simp [m1892_stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [m1892_stp, m1892_getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [m1892_ev_and g _ ha, m1892_ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [m1892_ev_or g _ ho, m1892_ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem m1892_all_idx (n : ℕ) (x y : List Bool) (hx : x.length = n)
    (H : ∀ i < n, x.getD i false = true → y.getD i false = true) :
    ∀ i, x.getD i false = true → y.getD i false = true := by
  intro i hi
  by_cases h : i < n
  · exact H i h hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
    exact Bool.noConfusion hi

theorem evalMono1892 {N : ℕ} (gs : List Gate) (u : ℕ)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin N → Bool) (hle : ∀ p, x p = true → y p = true) :
    (Circuit.mk gs u).eval (List.ofFn x) = true →
      (Circuit.mk gs u).eval (List.ofFn y) = true := by
  rw [m1892_eval_eq, m1892_eval_eq]
  apply m1892_mono gs _ _ (by simp) hop _ u
  apply m1892_all_idx N _ _ (by simp)
  intro i hi
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
    List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
  simpa only [List.getElem_ofFn] using hle ⟨i, hi⟩



def shift (cut replacement i : Nat) : Nat :=
  if i < cut then i else if i=cut then replacement else i-1

def change (cut replacement : Nat) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (shift cut replacement)⟩

def bypass (n : Nat) (pre post : List Gate) (o replacement : Nat) : Circuit :=
  ⟨pre ++ post.map (change (n+pre.length) replacement),shift (n+pre.length) replacement o⟩

def value (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem foldLength (gs : List Gate) (xs : List Bool) :
    (gs.foldl m1892_stp xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,m1892_stp] <;> omega

theorem extendRead (old fresh : List Bool) (cut replacement : Nat)
    (size : old.length = fresh.length+1) (room : cut ≤ fresh.length)
    (valid : replacement < cut ∨ fresh.length < replacement)
    (agree : ∀ i, old.getD i false = fresh.getD (shift cut replacement i) false)
    (v : Bool) (i : Nat) :
    (old++[v]).getD i false = (fresh++[v]).getD (shift cut replacement i) false := by
  rw [m1892_getD_snoc,m1892_getD_snoc,agree]
  by_cases ie : i=old.length
  · have se : shift cut replacement i = fresh.length := by
      have gt : cut<i := by omega
      simp [shift,show ¬i<cut by omega,show i≠cut by omega] <;> omega
    rw [if_pos ie,if_pos se]
  · have se : shift cut replacement i ≠ fresh.length := by
      simp only [shift]
      split_ifs <;> omega
    rw [if_neg ie,if_neg se]

theorem foldAgree (cut replacement : Nat) (post : List Gate) (old fresh : List Bool)
    (size : old.length=fresh.length+1) (room : cut ≤ fresh.length)
    (valid : replacement<cut ∨ fresh.length+post.length ≤ replacement)
    (agree : ∀ i, old.getD i false = fresh.getD (shift cut replacement i) false) :
    ∀ i, (post.foldl m1892_stp old).getD i false =
      ((post.map (change cut replacement)).foldl m1892_stp fresh).getD (shift cut replacement i) false := by
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
    · simp [m1892_stp,size]
    · simp [m1892_stp] <;> omega
    · simp [m1892_stp,List.length_cons] at * <;> omega
    · intro i
      change (old ++ [value old g]).getD i false =
        (fresh ++ [value fresh (change cut replacement g)]).getD _ false
      rw [←v]
      apply extendRead old fresh cut replacement size room _ agree
      simp only [List.length_cons] at valid
      omega

theorem evalBypass (n : Nat) (pre post : List Gate) (o replacement : Nat)
    (valid : replacement<n+pre.length ∨ n+pre.length+post.length ≤ replacement)
    (x : Fin n → Bool) :
    (bypass n pre post o replacement).eval (List.ofFn x) =
      (let w := pre.foldl m1892_stp (List.ofFn x);
       post.foldl m1892_stp (w ++ [w.getD replacement false])).getD o false := by
  let w := pre.foldl m1892_stp (List.ofFn x)
  have len : w.length = n+pre.length := by simp [w,foldLength]
  rw [m1892_eval_eq]
  change ((pre ++ post.map (change (n+pre.length) replacement)).foldl m1892_stp _).getD _ false = _
  rw [List.foldl_append]
  change ((post.map (change (n+pre.length) replacement)).foldl m1892_stp w).getD _ false = _
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
    · have h1 : w.length≤i := by omega
      have h2 : w.length≤i-1 := by omega
      simp [shift,←len,lt,eq,List.getD_eq_getElem?_getD,List.getElem?_eq_none h1,
        List.getElem?_eq_none h2]

theorem short (n : Nat) (pre post : List Gate) (o r : Nat) (g : Gate) :
    (bypass n pre post o r).size+1=(Circuit.mk (pre++g::post) o).size := by
  simp [bypass,Circuit.size] <;> omega

theorem legal (n : Nat) (pre post : List Gate) (o r : Nat) (g : Gate)
    (h : Monotone2 (Circuit.mk (pre++g::post) o)) : Monotone2 (bypass n pre post o r) := by
  intro z hz
  change z ∈ pre++post.map _ at hz
  rcases List.mem_append.mp hz with left|right
  · exact h z (List.mem_append_left _ left)
  · obtain ⟨old,mem,rfl⟩ := List.mem_map.mp right
    have hh := h old (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
    simpa [change] using hh

def edgeGoal {n : Nat} (E : List (Nat × Nat)) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, (u.val,v.val)∈E ∧ x u=true ∧ x v=true
def exactOn (n : Nat) (E : List (Nat × Nat)) (C : Circuit) :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x)=true ↔ edgeGoal E x
def minimal (n : Nat) (E : List (Nat × Nat)) (C : Circuit) :=
  ∀ D : Circuit, Monotone2 D → exactOn n E D → C.size ≤ D.size
def two {n : Nat} (u v i : Fin n) := decide (i=u ∨ i=v)
def prefix {n : Nat} (pre : List Gate) (x : Fin n → Bool) := pre.foldl m1892_stp (List.ofFn x)
def afterG (post : List Gate) (o : Nat) (w : List Bool) (b : Bool) :=
  (post.foldl m1892_stp (w++[b])).getD o false

theorem bestExists {n E C} (ops : Monotone2 C) (exact : exactOn n E C) :
    ∃ D : Circuit, D.size≤ C.size ∧ Monotone2 D ∧ exactOn n E D ∧ minimal n E D := by
  classical
  let pred (k : Nat) := ∃ D : Circuit, D.size=k ∧ Monotone2 D ∧ exactOn n E D
  have someSize : ∃ k, pred k := ⟨C.size,C,rfl,ops,exact⟩
  obtain ⟨D,sz,dm,dx⟩ := Nat.find_spec someSize
  refine ⟨D,?_,dm,dx,?_⟩
  · rw [sz]
    exact Nat.find_min' someSize ⟨C,rfl,ops,exact⟩
  · intro W wm wx
    rw [sz]
    exact Nat.find_min' someSize ⟨W,rfl,wm,wx⟩

theorem splitEval {n} (pre post : List Gate) (g : Gate) (o : Nat) (x : Fin n → Bool) :
    (Circuit.mk (pre++g::post) o).eval (List.ofFn x) =
    afterG post o (prefix pre x) (value (prefix pre x) g) := by
  rw [m1892_eval_eq,List.foldl_append]
  rfl

theorem afterMono (post : List Gate) (ops : ∀ g ∈ post, g.op=.and ∨ g.op=.or)
    (o : Nat) (w : List Bool) (a b : Bool) (le : a=true → b=true) :
    afterG post o w a=true → afterG post o w b=true := by
  apply m1892_mono post _ _ (by simp) ops _ o
  intro i
  rw [m1892_getD_snoc,m1892_getD_snoc]
  by_cases h : i=w.length <;> simp only [h,if_true,if_false]
  · exact le
  · exact id

theorem forceNeeded {n E} (pre post : List Gate) (g : Gate) (o : Nat)
    (ops : Monotone2 (Circuit.mk (pre++g::post) o))
    (ex : exactOn n E (Circuit.mk (pre++g::post) o))
    (opt : minimal n E (Circuit.mk (pre++g::post) o)) :
    ∃ u v : Fin n, (u.val,v.val)∈E ∧
      value (prefix pre (two u v)) g=true ∧ afterG post o (prefix pre (two u v)) false=false := by
  classical
  let r := n+pre.length+post.length
  let D := bypass n pre post o r
  have dm : Monotone2 D := legal n pre post o r g ops
  have dp : ∀ g ∈ post, g.op=.and ∨ g.op=.or := fun h hh => by
    simpa using (ops h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))).1
  have de (x : Fin n → Bool) : D.eval (List.ofFn x)=afterG post o (prefix pre x) false := by
    rw [show D=bypass n pre post o r by rfl,evalBypass n pre post o r (Or.inr (Nat.le_refl _))]
    change afterG post o (prefix pre x) ((prefix pre x).getD r false) = _
    have tail : (prefix pre x).length≤r := by simp [prefix,foldLength,r]
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none tail]
  have sound (x : Fin n → Bool) (d : D.eval (List.ofFn x)=true) : edgeGoal E x := by
    apply (ex x).mp
    rw [splitEval]
    exact afterMono post dp o _ false _ (by simp) ((de x) ▸ d)
  by_contra! none
  have correct : exactOn n E D := by
    intro x
    refine ⟨sound x,?_⟩
    rintro ⟨u,v,e,hu,hv⟩
    have good : edgeGoal E (two u v) := ⟨u,v,e,by simp [two],by simp [two]⟩
    have acc := (ex (two u v)).mpr good
    rw [splitEval] at acc
    have hit : afterG post o (prefix pre (two u v)) false=true := by
      cases h : value (prefix pre (two u v)) g with
      | false => simpa only [h] using acc
      | true => cases off : afterG post o (prefix pre (two u v)) false with
                | true => rfl
                | false => exact False.elim (by have := none u v e h; simp_all)
    have run : D.eval (List.ofFn (two u v))=true := (de _).trans hit
    apply evalMono1892 D.gates D.output (fun a ha => by simpa using (dm a ha).1) (two u v) x _ run
    intro i hi
    rcases of_decide_eq_true hi with rfl|rfl
    · exact hu
    · exact hv
  have shortD := short n pre post o r g
  have low := opt D dm correct
  change D.size+1=_ at shortD
  omega

def replacement (bound fallback a : Nat) := if a<bound then a else fallback

theorem andBypass {n E} (pre post : List Gate) (a b o : Nat)
    (ops : Monotone2 (Circuit.mk (pre++⟨.and,[a,b]⟩::post) o))
    (ex : exactOn n E (Circuit.mk (pre++⟨.and,[a,b]⟩::post) o))
    (opt : minimal n E (Circuit.mk (pre++⟨.and,[a,b]⟩::post) o))
    (c d : Nat) (sel : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) :
    ∃ x : Fin n → Bool, ¬edgeGoal E x ∧
      (prefix pre x).getD c false=true ∧ (prefix pre x).getD d false=false ∧
      afterG post o (prefix pre x) true=true ∧ afterG post o (prefix pre x) false=false := by
  classical
  let gate : Gate := ⟨.and,[a,b]⟩
  let bound := n+pre.length
  let r := replacement bound (bound+post.length) c
  let D := bypass n pre post o r
  have dm : Monotone2 D := legal n pre post o r gate ops
  have vr : r<bound ∨ bound+post.length≤r := by
    dsimp [r,replacement]
    split <;> omega
  have de (x : Fin n → Bool) : D.eval (List.ofFn x) =
      afterG post o (prefix pre x) ((prefix pre x).getD c false) := by
    rw [show D=bypass n pre post o r by rfl,evalBypass n pre post o r vr]
    change afterG post o (prefix pre x) ((prefix pre x).getD r false) = _
    by_cases h : c<bound
    · simp [r,replacement,h]
    · have l : (prefix pre x).length=bound := by simp [prefix,bound,foldLength]
      have c1 : (prefix pre x).length≤c := by omega
      have c2 : (prefix pre x).length≤bound+post.length := by omega
      simp [r,replacement,h,List.getD_eq_getElem?_getD,List.getElem?_eq_none c1,List.getElem?_eq_none c2]
  have dp : ∀ g ∈ post, g.op=.and ∨ g.op=.or := fun g h => by
    simpa using (ops g (List.mem_append_right _ (List.mem_cons_of_mem _ h))).1
  have gateVal (w : List Bool) : value w gate = (w.getD c false && w.getD d false) := by
    rcases sel with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [gate,value,GateOp.eval,Bool.and_comm]
  have att (x : Fin n → Bool) := ex x
  have run (x : Fin n → Bool) : afterG post o (prefix pre x)
      ((prefix pre x).getD c false && (prefix pre x).getD d false)=true ↔ edgeGoal E x := by
    rw [←gateVal,←splitEval]
    exact att x
  have leak : ∃ x : Fin n → Bool, D.eval (List.ofFn x)=true ∧ ¬edgeGoal E x := by
    by_contra! no
    have good : exactOn n E D := by
      intro x
      refine ⟨no x,?_⟩
      intro positive
      rw [de]
      apply afterMono post dp o _ _ _ _ ((run x).mpr positive)
      simp
    have lo := opt D dm good
    have sh := short n pre post o r gate
    change D.size+1=(Circuit.mk (pre++gate::post) o).size at sh
    change (Circuit.mk (pre++gate::post) o).size≤D.size at lo
    omega
  obtain ⟨x,on,np⟩ := leak
  rw [de] at on
  have off := mt (run x).mp np
  refine ⟨x,np,?_⟩
  cases hc : (prefix pre x).getD c false <;> cases hd : (prefix pre x).getD d false <;>
    simp_all

end Bypass9739
