import Mathlib
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

def pins (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
def reads (v : Nat) (g : Gate) := (pins g).contains v
def mark {n : Nat} (S : Finset (Fin n)) (v : Fin n) := decide (v ∈ S)
def atBank (g : Gate) (z : List Bool) := g.op.eval (g.inputs.map fun k => z.getD k false)

lemma eval_from_pins (g : Gate) (z w : List Bool)
    (fan : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (agree : ∀ i ∈ pins g, z.getD i false = w.getD i false) : atBank g z = atBank g w := by
  obtain ⟨op,ins⟩ := g
  rcases fan with ⟨opok,arity⟩
  change op = .and ∨ op = .or ∨ op = .not at opok
  change ins.length ≤ 2 at arity
  rcases opok with rfl|rfl|rfl <;> cases ins with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | nil =>
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢ <;> simp [ha]
    | cons b t =>
      have empty : t=[] := by simpa using arity
      subst t
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢
      rw [ha]
      all_goals
        have hb := agree b (by simp [pins,GateOp.eval])
        simp only [List.getD_eq_getElem?_getD] at hb
        rw [hb]

theorem kept_eq (j : Fin n) (x : Fin n → Bool) (gs : List Gate) :
    (gs.foldl step (List.ofFn x)).getD j.val false=x j := by
  rw [prefix_read _ _ _ (by simp)]
  simp

def quiet (v : Fin n) (gs : List Gate) : Prop := ∀ g∈gs, v.val∉pins g
def near (v : Nat) (a b : List Bool) : Prop :=
  a.length=b.length ∧ ∀ j, j ≠ v → a.getD j false = b.getD j false

theorem snocNear {v : Nat} {a b : List Bool} (ab : near v a b) (val : Bool) :
    near v (a++[val]) (b++[val]) := by
  refine ⟨by simp [ab.1],?_⟩
  intro i ne
  rw [m1892_getD_snoc,m1892_getD_snoc,ab.1,ab.2 i ne]

theorem foldQuiet {v : Fin n} {gs : List Gate} (q : quiet v gs)
    (fan : ∀ g∈gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    {w z : List Bool} (e : near v.val w z) : near v.val (gs.foldl step w) (gs.foldl step z) := by
  induction gs generalizing w z with
  | nil => exact e
  | cons g gs ih =>
    have val := eval_from_pins g w z (fan g (by simp)) (fun i hi =>
      e.2 i (fun eq => q g (by simp) (eq ▸ hi)))
    simp only [List.foldl_cons]
    apply ih (fun i hi => q i (List.mem_cons_of_mem _ hi)) (fun i hi => fan i (List.mem_cons_of_mem _ hi))
    change near v.val (w++[atBank g w]) (z++[atBank g z])
    rw [val]
    exact snocNear e _

theorem rawNear (v : Fin n) (x : Fin n → Bool) : near v.val (List.ofFn x) (List.ofFn (Function.update x v true)) := by
  refine ⟨by simp,?_⟩
  intro i ne
  by_cases hi : i<n
  · let j : Fin n := ⟨i,hi⟩
    have different : j≠v := fun e => ne (congrArg Fin.val e)
    change (List.ofFn x).getD j.val false = (List.ofFn (Function.update x v true)).getD j.val false
    simp [Function.update_of_ne different]
  · simp [List.getD_eq_getElem?_getD,hi]

open PEqualNP.MetaComplexity.NestedCover

def andSource (pre post : List Gate) (a b o : Nat) : Circuit :=
  ⟨pre ++ Gate.mk .and [a,b] :: post,o⟩

theorem and_eval (n : Nat) (pre post : List Gate) (a b o : Nat) (x : Fin n → Bool) :
    (andSource pre post a b o).eval (List.ofFn x) =
      (let w := pre.foldl step (List.ofFn x);
        (post.foldl step (w++[w.getD a false && w.getD b false])).getD o false) := by
  rw [m1892_eval_eq]
  simp [andSource,List.foldl_append,step,GateOp.eval]

theorem andNeedsHigh (v : Fin n) (pre post : List Gate) (j o : Nat) (jo : j≠v.val) (oo : o≠v.val)
    (fan : FanInTwo (andSource pre post v.val j o)) (qp : quiet v pre) (qs : quiet v post)
    (x : Fin n → Bool)
    (flips : (andSource pre post v.val j o).eval (List.ofFn x) ≠
      (andSource pre post v.val j o).eval (List.ofFn (Function.update x v true))) :
    (pre.foldl step (List.ofFn x)).getD j false=true := by
  let y := Function.update x v true
  let a := pre.foldl step (List.ofFn x)
  let b := pre.foldl step (List.ofFn y)
  have relation : near v.val a b := foldQuiet qp (fun g hg => fan g (List.mem_append_left _ hg)) (rawNear v x)
  cases hj : a.getD j false with
  | true => rfl
  | false =>
    have bj : b.getD j false=false := (relation.2 j jo).symm.trans hj
    have tail := foldQuiet qs (fun g hg => fan g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))) (snocNear relation false)
    apply False.elim
    apply flips
    rw [and_eval,and_eval]
    change (post.foldl step (a++[a.getD v.val false && a.getD j false])).getD o false =
      (post.foldl step (b++[b.getD v.val false && b.getD j false])).getD o false
    simp only [hj,bj,Bool.and_false]
    exact tail.2 o oo

theorem essential_neighbors (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (v : Fin n) (pre post : List Gate) (j o : Nat) (jv : j≠v.val) (oo : o≠v.val)
    (iso : ∀ s t, G.Adj s t → s∉A)
    (fan : FanInTwo (andSource pre post v.val j o)) (qp : quiet v pre) (qs : quiet v post)
    (rep : ∀ x, (andSource pre post v.val j o).eval (List.ofFn x)=graphFun G A x)
    (least : ∀ D : Circuit, FanInTwo D → circuitFun n D=circuitFun n (andSource pre post v.val j o) →
      (andSource pre post v.val j o).size≤D.size)
    (mono : ∀ x : Fin n → Bool, (pre.foldl step (List.ofFn (fun _ : Fin n => false))).getD j false=true →
      (pre.foldl step (List.ofFn x)).getD j false=true) :
    (pre.foldl step (List.ofFn (fun _ : Fin n => false))).getD j false=false ∧
    ∀ t, G.Adj v t → (pre.foldl step (List.ofFn (fun i : Fin n => decide (i=t)))).getD j false=true := by
  classical
  let C := andSource pre post v.val j o
  refine ⟨?_,?_⟩
  · cases hz : (pre.foldl step (List.ofFn (fun _ : Fin n => false))).getD j false with
    | false => rfl
    | true =>
      let D := bypass n pre post o v.val
      have fd : FanInTwo D := by
        intro h hh
        change h∈pre++post.map (change (n+pre.length) v.val) at hh
        rcases List.mem_append.mp hh with hp|hp
        · exact fan h (List.mem_append_left _ hp)
        · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hp
          obtain ⟨op,ar⟩ := fan g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))
          exact ⟨op,by simpa [change] using ar⟩
      have eq : circuitFun n D=circuitFun n C := by
        funext x
        change (bypass n pre post o v.val).eval (List.ofFn x) = (andSource pre post v.val j o).eval (List.ofFn x)
        rw [evalBypass n pre post o v.val (Or.inl (by have := v.isLt; omega)),and_eval]
        simp only [mono x hz,Bool.and_true]
      have lower := least D fd eq
      have upper := short n pre post o v.val (Gate.mk .and [v.val,j])
      change D.size + 1 = C.size at upper
      change C.size ≤ D.size at lower
      omega
  · intro t vt
    let X : Fin n → Bool := fun i => decide (i=t)
    apply andNeedsHigh v pre post j o jv oo fan qp qs X
    rw [rep,rep]
    have off : graphFun G A X=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have h' : (∃ a∈A, X a=true) ∨ ∃ a b, G.Adj a b ∧ X a=true ∧ X b=true := by
        simpa only [graphFun,Bool.or_eq_true,decide_eq_true_eq] using (show graphFun G A X=true from h)
      rcases h' with ⟨a,ha,at'⟩|⟨a,b,ab,at',bt⟩
      · have eq : a=t := by simpa [X] using at'
        exact iso _ _ vt.symm (eq ▸ ha)
      · have ea : a=t := by simpa [X] using at'
        have eb : b=t := by simpa [X] using bt
        exact ab.ne (ea.trans eb.symm)
    have on : graphFun G A (Function.update X v true)=true := by
      simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
      exact Or.inr ⟨v,t,vt,by simp,by simp [Function.update_of_ne vt.ne.symm,X]⟩
    rw [off,on]
    decide

end PEqualNP.Outside.L_meta_1972.Ports
