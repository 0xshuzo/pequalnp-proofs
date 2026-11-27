import Mathlib
import PEqualNP.Defs

-- From the published L_meta_5355.
namespace PEqualNP.Outside.L_meta_8181.Stars

open PEqualNP.CircuitLowerBounds

-- A vertex cover circuit: for each cover vertex c (in increasing order) an OR chain of the
-- neighbours of c not already handled, ANDed with c; the AND gates are ORed together.

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def V {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ fs.map (fun f => f x)

def Sem {n : ℕ} (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  ∀ x : Fin n → Bool, wf gs (List.ofFn x) = V fs x

def Val {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (i : ℕ) (F : (Fin n → Bool) → Bool) : Prop :=
  i < n + fs.length ∧ ∀ x, (V fs x).getD i false = F x

def Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def St {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) (gs : List Gate)
    (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  Sem gs fs ∧ fs.length = gs.length ∧ Mono gs ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ l, P l ∧ ∀ x, fs.getD j (fun _ => false) x = true → x l = true) ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ c v : Fin n, G.Adj c v ∧
      fs.getD j (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = true ∧
      ∀ i < j, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false)

def N {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => G.Adj c w ∧ ¬ (w ∈ C ∧ w < c))

def gad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n)
    (x : Fin n → Bool) : Bool :=
  x c && decide (∃ w ∈ N G C c, x w = true)

end PEqualNP.Outside.L_meta_8181.Stars

-- From the published L_meta_1527.
namespace PEqualNP.Outside.L_meta_8181.Normalize

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

end PEqualNP.Outside.L_meta_8181.Normalize

namespace PEqualNP.Outside.L_meta_8181.Budget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open PEqualNP.MetaComplexity.CoverPromise

variable {n : Nat}

def Conclusion (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (z : Fin n) : Prop :=
  ∃ D : Circuit, IsAO2 n D ∧
    circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
      (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a=true ∧ y b=true)
      (Classical.propDecidable _)) ∧
    D.size + G.degree z ≤ C.size ∧ ((∃ p q : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj p q) →
      (∃ S : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), IsVertexCover G T → S.card < T.card) →
      D.size + G.degree z + 1 ≤ C.size)

end PEqualNP.Outside.L_meta_8181.Budget

-- Finite core classification from the published L_meta_17265.
namespace PEqualNP.Outside.L_meta_8181.Ten

namespace ThetaAnd3241

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.ReadK

def thetaAdj (i j : Fin 4) : Bool := (13726 : Nat).testBit (4*i.val+j.val)

def theta (x : Fin 8 → Bool) : Bool :=
  decide (∃ i j : Fin 4, thetaAdj i j = true ∧
    x (Fin.castAdd 4 i) = true ∧ x (Fin.natAdd 4 j) = true)

def nine : Fin 9 → Finset (Fin 8) :=
  ![{0,1,2,3}, {0,4}, {1,2,5}, {1,3,6}, {1,5,6}, {2,3,7}, {2,5,7}, {3,6,7}, {4,5,6,7}]

def andGate (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

theorem subtract_or_eq_and {n : Nat} (C : Circuit) (ao : IsAO2 n C) :
    C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) =
      C.gates.countP andGate := by
  have total (gs : List Gate) (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      gs.countP andGate + gs.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have tail := ih (fun a ha => ok a (List.mem_cons_of_mem _ ha))
      rcases ok g List.mem_cons_self with h | h
      · have a : andGate g = true := by simp [andGate,h]
        have o : PEqualNP.SharedBlockCost.isOrOp g.op = false := by rw [h]; rfl
        simp [a,o]
        omega
      · have a : andGate g = false := by simp [andGate,h]
        have o : PEqualNP.SharedBlockCost.isOrOp g.op = true := by rw [h]; rfl
        simp [a,o]
        omega
  have count := total C.gates ao.1
  unfold Circuit.size
  omega

end ThetaAnd3241

namespace ThetaPin3241

abbrev Signal (α : Type) := α → Bool
abbrev Gate (α : Type) := Signal α × Signal α

def join {α : Type} (a b : Signal α) : Signal α := fun x => a x || b x
def meet {α : Type} (a b : Signal α) : Signal α := fun x => a x && b x

def Free {α : Type} (B : Set (Signal α)) (a : Signal α) : Prop :=
  ∀ S : Set (Signal α), B ⊆ S → (fun _ => false) ∈ S → (fun _ => true) ∈ S →
    (∀ u ∈ S, ∀ v ∈ S, meet u v ∈ S) → a ∈ S

theorem atom {α : Type} {B : Set (Signal α)} {a : Signal α} (ha : a ∈ B) : Free B a :=
  fun _ h _ _ _ => h ha

theorem free_zero {α : Type} {B : Set (Signal α)} : Free B (fun _ => false) :=
  fun _ _ h _ _ => h

theorem free_one {α : Type} {B : Set (Signal α)} : Free B (fun _ => true) :=
  fun _ _ _ h _ => h

theorem free_meet {α : Type} {B : Set (Signal α)} {u v : Signal α} (hu : Free B u)
    (hv : Free B v) : Free B (meet u v) :=
  fun S incl h0 h1 hc => hc _ (hu S incl h0 h1 hc) _ (hv S incl h0 h1 hc)

theorem widen {α : Type} {B D : Set (Signal α)} {a : Signal α}
    (incl : B ⊆ D) (h : Free B a) : Free D a :=
  fun S incl' => h S (incl.trans incl')

theorem transport {α β : Type} (p : β → α) {B : Set (Signal α)} {D : Set (Signal β)}
    (base : ∀ a ∈ B, Free D (a ∘ p)) {a : Signal α} (ha : Free B a) : Free D (a ∘ p) := by
  apply ha {a | Free D (a ∘ p)}
  · exact base
  · exact free_zero
  · exact free_one
  · intro u hu v hv
    exact free_meet hu hv

theorem factors {α : Type} {B : Set (Signal α)} {f : Signal α} (ok : Free B f) :
    f = (fun _ => false) ∨ ∃ xs : List (Signal α), (∀ a ∈ xs, a ∈ B) ∧
      f = (fun x => xs.all (fun a => a x)) := by
  let S : Set (Signal α) := {f | f = (fun _ => false) ∨
    ∃ xs : List (Signal α), (∀ a ∈ xs, a ∈ B) ∧ f = (fun x => xs.all (fun a => a x))}
  apply ok S
  · intro a ha
    exact Or.inr ⟨[a],by simpa using ha,funext (fun x => by simp)⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨[],by simp,rfl⟩
  · intro a ha b hb
    rcases ha with rfl | ⟨xs,hh,rfl⟩
    · exact Or.inl rfl
    rcases hb with rfl | ⟨ys,ii,rfl⟩
    · exact Or.inl (funext (fun x => by simp [meet]))
    · refine Or.inr ⟨xs++ys,?_,?_⟩
      · intro u hu
        exact (List.mem_append.mp hu).elim (hh u) (ii u)
      · exact funext (fun x => by simp [meet])

def Valid {α : Type} (B : Set (Signal α)) (gs : List (Gate α)) (f : Signal α) : Prop :=
  match gs with
  | [] => Free B f
  | g :: rest => Free B g.1 ∧ Free B g.2 ∧ Valid (insert (join g.1 g.2) B) rest f

def Pass {α : Type} (t e z : α) (f : Signal α) : Prop :=
  f t = true → f e = true → f z = true

theorem free_pass {α : Type} {B : Set (Signal α)} {t e z : α} {f : Signal α}
    (base : ∀ a ∈ B, Pass t e z a) (ok : Free B f) : Pass t e z f := by
  apply ok {a | Pass t e z a}
  · exact base
  · intro h; contradiction
  · intro _ _; rfl
  · intro u hu v hv ht he
    have ⟨tu,tv⟩ : u t = true ∧ v t = true := by simpa [meet] using ht
    have ⟨eu,ev⟩ : u e = true ∧ v e = true := by simpa [meet] using he
    simp [meet,hu tu eu,hv tv ev]

theorem critical_gate {α : Type} (gs : List (Gate α)) (B : Set (Signal α)) (f : Signal α)
    (t e z : α) (base : ∀ a ∈ B, Pass t e z a) (ok : Valid B gs f)
    (ft : f t = true) (fe : f e = true) (fz : f z = false) :
    ∃ g ∈ gs, (g.1 t = false ∨ g.2 t = false) ∧
      join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false := by
  classical
  induction gs generalizing B with
  | nil =>
    have impossible := free_pass base ok ft fe
    simp [fz] at impossible
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    by_cases passes : Pass t e z (join g.1 g.2)
    · have next : ∀ a ∈ insert (join g.1 g.2) B, Pass t e z a := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact passes
        · exact base _ h
      obtain ⟨m,hm,p⟩ := ih _ next tail
      exact ⟨m,List.mem_cons_of_mem _ hm,p⟩
    · have hp : join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧
          join g.1 g.2 z = false := by simpa [Pass] using passes
      refine ⟨g,List.mem_cons_self,?_,hp⟩
      by_contra no
      have both : g.1 t = true ∧ g.2 t = true := by simpa using no
      have either : g.1 e = true ∨ g.2 e = true := by simpa [join] using hp.2.1
      rcases either with h | h
      · have yes := free_pass base ha both.1 h
        have nz := hp.2.2
        simp [join,yes] at nz
      · have yes := free_pass base hb both.2 h
        have nz := hp.2.2
        simp [join,yes] at nz

def Killed {α β : Type} (p : β → α) (g : Gate α) : Prop :=
  (∀ x, g.1 (p x) = false) ∨ (∀ x, g.2 (p x) = false)

def deadAt {α : Type} (t : α) (g : Gate α) : Bool := !(g.1 t && g.2 t)

theorem count_one_unique {α : Type} (gs : List α) (p : α → Bool) (a b : α)
    (ha : a ∈ gs) (hb : b ∈ gs) (pa : p a = true) (pb : p b = true)
    (one : gs.countP p ≤ 1) : a = b := by
  rw [List.countP_eq_length_filter] at one
  have a' := List.mem_filter.mpr ⟨ha,pa⟩
  have b' := List.mem_filter.mpr ⟨hb,pb⟩
  cases h : gs.filter p with
  | nil => simp [h] at a'
  | cons c rest =>
    have numeric : rest.length+1 ≤ 1 := by simpa only [h,List.length_cons] using one
    have nil : rest = [] := List.length_eq_zero_iff.mp (by omega)
    simp [h,nil] at a' b'
    exact a'.trans b'.symm

theorem single_charge_passes {α : Type} {B : Set (Signal α)} {gs : List (Gate α)}
    {f : Signal α} (ok : Valid B gs f) (g : Gate α) (hg : g ∈ gs) (t e z : α)
    (base : ∀ a ∈ B, Pass t e z a) (ft : f t = true) (fe : f e = true)
    (fz : f z = false) (dg : deadAt t g = true) (one : gs.countP (deadAt t) ≤ 1) :
    join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false := by
  obtain ⟨j,hj,charge,h⟩ := critical_gate gs B f t e z base ok ft fe fz
  have dj : deadAt t j = true := by simpa [deadAt] using charge
  exact (count_one_unique gs (deadAt t) j g hj hg dj dg one) ▸ h

theorem propagate_property {α : Type} (B S : Set (Signal α)) (gs : List (Gate α)) (f : Signal α)
    (incl : B ⊆ S) (ok : Valid B gs f)
    (stable : ∀ g ∈ gs, Free S g.1 → Free S g.2 → join g.1 g.2 ∈ S) :
    Free S f := by
  induction gs generalizing B with
  | nil => exact widen incl ok
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    have mem := stable g List.mem_cons_self (widen incl ha) (widen incl hb)
    exact ih (insert (join g.1 g.2) B) (Set.insert_subset mem incl) tail
      (fun a h => stable a (List.mem_cons_of_mem _ h))

noncomputable def killedBit {α β : Type} (p : β → α) (g : Gate α) : Bool :=
  @decide (Killed p g) (Classical.propDecidable _)

theorem restrict_transfer {α β : Type} (p : β → α) (gs : List (Gate α))
    (B : Set (Signal α)) (D : Set (Signal β)) (f : Signal α)
    (base : ∀ a ∈ B, Free D (a ∘ p)) (ok : Valid B gs f) :
    ∃ out : List (Gate β), Valid D out (f ∘ p) ∧
      out.length + gs.countP (killedBit p) = gs.length := by
  classical
  induction gs generalizing B D with
  | nil => exact ⟨[], transport p base ok, rfl⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    have left := transport p base ha
    have right := transport p base hb
    by_cases dead : Killed p g
    · have combined : Free D (join g.1 g.2 ∘ p) := by
        rcases dead with l | r
        · have e : join g.1 g.2 ∘ p = g.2 ∘ p := funext (fun x => by simp [join,l])
          exact e ▸ right
        · have e : join g.1 g.2 ∘ p = g.1 ∘ p := funext (fun x => by simp [join,r])
          exact e ▸ left
      have next : ∀ a ∈ insert (join g.1 g.2) B, Free D (a ∘ p) := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact combined
        · exact base _ h
      obtain ⟨out,sem,cost⟩ := ih _ D next tail
      refine ⟨out,sem,?_⟩
      have k : killedBit p g = true := by simp [killedBit,dead]
      simp [k]
      omega
    · let new := join (g.1 ∘ p) (g.2 ∘ p)
      have next : ∀ a ∈ insert (join g.1 g.2) B, Free (insert new D) (a ∘ p) := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact atom (Set.mem_insert _ _)
        · exact widen (Set.subset_insert _ _) (base _ h)
      obtain ⟨out,sem,cost⟩ := ih _ (insert new D) next tail
      refine ⟨(g.1 ∘ p,g.2 ∘ p)::out,⟨left,right,sem⟩,?_⟩
      have k : killedBit p g = false := by simp [killedBit,dead]
      simp [k]
      omega

abbrev PhysicalGate := PEqualNP.CircuitLowerBounds.Gate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def wire {α : Type} (w : List (Signal α)) (i : Nat) : Signal α := w.getD i (fun _ => false)

def step {α : Type} (w : List (Signal α)) (g : PhysicalGate) : List (Signal α) :=
  w ++ [fun x => g.op.eval (g.inputs.map fun i => wire w i x)]

def pairShape (g : PhysicalGate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat, g.inputs = [a,b]

theorem free_wire {α : Type} {B : Set (Signal α)} {w : List (Signal α)}
    (hw : ∀ a ∈ w, Free B a) (i : Nat) : Free B (wire w i) := by
  induction w generalizing i with
  | nil => cases i <;> exact free_zero
  | cons a w ih =>
    cases i with
    | zero => exact hw _ List.mem_cons_self
    | succ i => exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) i

def isOr (g : PhysicalGate) : Bool := PEqualNP.SharedBlockCost.isOrOp g.op

theorem compress {α : Type} (gs : List PhysicalGate) (output : Nat) (w : List (Signal α))
    (B : Set (Signal α)) (hw : ∀ a ∈ w, Free B a) (shapes : ∀ g ∈ gs, pairShape g) :
    ∃ ops : List (Gate α), Valid B ops (wire (gs.foldl step w) output) ∧
      ops.length = gs.countP isOr := by
  induction gs generalizing w B with
  | nil => exact ⟨[],free_wire hw output,rfl⟩
  | cons g gs ih =>
    obtain ⟨hop,i,j,pins⟩ := shapes g List.mem_cons_self
    have tail (h : PhysicalGate) (hh : h ∈ gs) := shapes h (List.mem_cons_of_mem _ hh)
    rcases hop with kind | kind
    · have eq : step w g = w ++ [meet (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have ext : ∀ a ∈ step w g, Free B a := by
        intro a ha
        rw [eq,List.mem_append,List.mem_singleton] at ha
        rcases ha with old | rfl
        · exact hw a old
        · exact free_meet (free_wire hw i) (free_wire hw j)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) B ext tail
      refine ⟨ops,sem,?_⟩
      have no : isOr g = false := by simp [isOr,kind,PEqualNP.SharedBlockCost.isOrOp]
      simpa [no] using cost
    · let a := wire w i
      let b := wire w j
      let D := insert (join a b) B
      have eq : step w g = w ++ [join a b] := by
        simp [step,pins,kind,GateOp.eval,a,b]
        rfl
      have ext : ∀ v ∈ step w g, Free D v := by
        intro v hv
        rw [eq,List.mem_append,List.mem_singleton] at hv
        rcases hv with old | rfl
        · exact widen (Set.subset_insert _ _) (hw v old)
        · exact atom (Set.mem_insert _ _)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) D ext tail
      refine ⟨(a,b)::ops,⟨free_wire hw i,free_wire hw j,sem⟩,?_⟩
      have yes : isOr g = true := by simp [isOr,kind,PEqualNP.SharedBlockCost.isOrOp]
      simp [cost,yes]

theorem wire_point {α : Type} (w : List (Signal α)) (x : α) (i : Nat) :
    (w.map (fun f => f x)).getD i false = wire w i x := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons f fs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem run_point {α : Type} (gs : List PhysicalGate) (w : List (Signal α)) (x : α) :
    (gs.foldl step w).map (fun f => f x) =
      gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
        (w.map (fun f => f x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    simp only [step,List.map_append,List.map_cons,List.map_nil,wire_point]

def inputs (n : Nat) : Set (Signal (Fin n → Bool)) := Set.range (fun (i : Fin n) x => x i)

def topMiss {n : Nat} (v : Fin n) (i : Fin n) : Bool := decide (i ≠ v)

theorem pass_inputs {n : Nat} (t e z : Fin n → Bool)
    (h : ∀ i, t i = true → e i = true → z i = true) : ∀ a ∈ inputs n, Pass t e z a := by
  rintro a ⟨i,rfl⟩
  exact h i

theorem one_charge {n : Nat} {gs f} (ok : Valid (inputs n) gs f)
    (v : Fin n) (e z : Fin n → Bool)
    (h : ∀ i, topMiss v i = true → e i = true → z i = true)
    (ft : f (topMiss v) = true) (fe : f e = true) (fz : f z = false) :
    1 ≤ gs.countP (deadAt (topMiss v)) := by
  obtain ⟨j,hj,hk,_⟩ := critical_gate gs (inputs n) f (topMiss v) e z
    (pass_inputs _ _ _ h) ok ft fe fz
  exact List.countP_pos_iff.mpr ⟨j,hj,by simpa [deadAt] using hk⟩

def Admissible {α : Type} (B : Set (Signal α)) (f : Signal α) (t : α) (g : Gate α) : Prop :=
  ∀ e z, (∀ a ∈ B, Pass t e z a) → f t = true → f e = true → f z = false →
    join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false

theorem double_from_classifier {n : Nat} (low : Set (Fin n)) (f : Signal (Fin n → Bool))
    (S : Set (Signal (Fin n → Bool))) (inc : inputs n ⊆ S) (nonfree : ¬ Free S f)
    (classify : ∀ g : Gate (Fin n → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) →
      join g.1 g.2 ∈ S)
    (gs : List (Gate (Fin n → Bool))) (ok : Valid (inputs n) gs f) :
    ∃ v ∈ low, 2 ≤ gs.countP (deadAt (topMiss v)) := by
  classical
  by_contra no
  apply nonfree
  apply propagate_property (inputs n) S gs f inc ok
  intro g hg ha hb
  apply classify g ha hb
  intro v hv dg e z raw ft fe fz
  have small : gs.countP (deadAt (topMiss v)) ≤ 1 := by
    by_contra h
    exact no ⟨v,hv,by omega⟩
  exact single_charge_passes ok g hg (topMiss v) e z raw ft fe fz dg small

def Increasing {n : Nat} (f : Signal (Fin n → Bool)) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

theorem free_increasing {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {a} (ha : Free B a) : Increasing a := by
  apply ha {v | Increasing v}
  · exact base
  · intro _ _ _ h; contradiction
  · intro _ _ _ _; rfl
  · intro u hu v hv x y le hx
    obtain ⟨lu,lv⟩ : u x = true ∧ v x = true := by simpa [meet] using hx
    simp [meet,hu x y le lu,hv x y le lv]

theorem active_monotone {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {gs f} (ok : Valid B gs f) :
    ∀ g ∈ gs, Increasing g.1 ∧ Increasing g.2 := by
  induction gs generalizing B with
  | nil => simp
  | cons h gs ih =>
    obtain ⟨left,right,tail⟩ := ok
    have l := free_increasing base left
    have r := free_increasing base right
    have next : ∀ a ∈ insert (join h.1 h.2) B, Increasing a := by
      intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl | old
      · intro x y le hx
        have one : h.1 x = true ∨ h.2 x = true := by simpa [join] using hx
        rcases one with p | p
        · simp [join,l x y le p]
        · simp [join,r x y le p]
      · exact base _ old
    intro g hg
    rcases List.mem_cons.mp hg with rfl | later
    · exact ⟨l,r⟩
    · exact ih next tail _ later

def pin {n : Nat} (v : Fin (n+1)) (x : Fin n → Bool) : Fin (n+1) → Bool :=
  v.insertNth false x

theorem pin_raw {n : Nat} (v : Fin (n+1)) :
    ∀ a ∈ inputs (n+1), Free (inputs n) (a ∘ pin v) := by
  rintro a ⟨i,rfl⟩
  refine v.succAboveCases ?_ (fun j => ?_) i
  · have eq : (fun t : Fin (n+1) → Bool => t v) ∘ pin v = (fun _ => false) :=
      funext (fun x => by simp [pin])
    exact eq ▸ free_zero
  · have eq : (fun t : Fin (n+1) → Bool => t (v.succAbove j)) ∘ pin v = (fun x => x j) :=
      funext (fun x => by simp [pin])
    exact eq ▸ atom ⟨j,rfl⟩

theorem delete_charge {n : Nat} {gs f} (ok : Valid (inputs (n+1)) gs f) (v : Fin (n+1)) :
    ∃ out, Valid (inputs n) out (f ∘ pin v) ∧
      out.length + gs.countP (deadAt (topMiss v)) ≤ gs.length := by
  obtain ⟨out,sem,cost⟩ := restrict_transfer (pin v) gs _ _ f (pin_raw v) ok
  refine ⟨out,sem,?_⟩
  have base : ∀ a ∈ inputs (n+1), Increasing a := by
    rintro a ⟨i,rfl⟩ x y le hx
    exact le i hx
  have zero {a : Signal (Fin (n+1) → Bool)} (inc : Increasing a) (ha : a (topMiss v) = false) :
      ∀ x, a (pin v x) = false := by
    intro x
    cases h : a (pin v x) with
    | false => rfl
    | true =>
      have le : ∀ i, pin v x i = true → topMiss v i = true := by
        intro i
        by_cases hi : i = v
        · subst i; simp [pin]
        · simp [topMiss,hi]
      simp [inc _ _ le h] at ha
  have keep (g) (hg : g ∈ gs) (h : deadAt (topMiss v) g = true) : killedBit (pin v) g = true := by
    obtain ⟨l,r⟩ := active_monotone base ok _ hg
    have either : g.1 (topMiss v) = false ∨ g.2 (topMiss v) = false := by simpa [deadAt] using h
    have killed : Killed (pin v) g := either.imp (zero l) (zero r)
    simp [killedBit,killed]
  have count : gs.countP (deadAt (topMiss v)) ≤ gs.countP (killedBit (pin v)) :=
    List.countP_mono_left keep
  omega

theorem of_circuit {n : Nat} (C : Circuit) (ao : IsAO2 n C) :
    ∃ ops : List (Gate (Fin n → Bool)), Valid (inputs n) ops (circuitFun n C) ∧
      ops.length = C.gates.countP isOr := by
  let w : List (Signal (Fin n → Bool)) := (List.finRange n).map (fun i x => x i)
  have ok (a) (ha : a ∈ w) : Free (inputs n) a := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    exact atom ⟨i,rfl⟩
  have shapes (g : PhysicalGate) (hg : g ∈ C.gates) : pairShape g := by
    refine ⟨ao.1 _ hg,?_⟩
    have len := ao.2.2 _ hg
    match h : g.inputs with
    | [] => simp [h] at len
    | [_] => simp [h] at len
    | a::b::rest =>
      have nil : rest = [] := List.length_eq_zero_iff.mp (by simpa [h] using len)
      exact ⟨a,b,by rw [nil]⟩
  obtain ⟨ops,sem,cost⟩ := compress C.gates C.output w (inputs n) ok shapes
  refine ⟨ops,?_,cost⟩
  have eq : wire (C.gates.foldl step w) C.output = circuitFun n C := by
    funext x
    rw [← wire_point,run_point]
    have start : w.map (fun f => f x) = List.ofFn x := by simp [w,List.ofFn_eq_map]
    rw [start]
    rfl
  exact eq ▸ sem

def Lower {n : Nat} (f : Signal (Fin n → Bool)) (k : Nat) : Prop :=
  ∀ ops, Valid (inputs n) ops f → k ≤ ops.length

theorem lower_zero {n : Nat} (f : Signal (Fin n → Bool)) : Lower f 0 :=
  fun _ _ => Nat.zero_le _

theorem lower_one_step {n k : Nat} (f : Signal (Fin (n+1) → Bool))
    (v : Fin (n+1)) (e z : Fin (n+1) → Bool)
    (h : ∀ i, topMiss v i = true → e i = true → z i = true)
    (ft : f (topMiss v) = true) (fe : f e = true) (fz : f z = false)
    (rec : Lower (f ∘ pin v) k) : Lower f (k+1) := by
  intro gs ok
  have saved := one_charge ok v e z h ft fe fz
  obtain ⟨out,sem,budget⟩ := delete_charge ok v
  have sub := rec out sem
  omega

theorem lower_two_step {n k : Nat} (f : Signal (Fin (n+1) → Bool)) (low : Set (Fin (n+1)))
    (S : Set (Signal (Fin (n+1) → Bool))) (inc : inputs (n+1) ⊆ S)
    (nonfree : ¬ Free S f)
    (classify : ∀ g : Gate (Fin (n+1) → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs (n+1)) f (topMiss v) g) →
      join g.1 g.2 ∈ S) (rec : ∀ v ∈ low, Lower (f ∘ pin v) k) : Lower f (k+2) := by
  intro gs ok
  obtain ⟨v,mem,saved⟩ := double_from_classifier low f S inc nonfree classify gs ok
  obtain ⟨out,sem,budget⟩ := delete_charge ok v
  have sub := rec v mem out sem
  omega

theorem lower_circuit {n k : Nat} {f : Signal (Fin n → Bool)} (lb : Lower f k)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = f) :
    k ≤ C.gates.countP isOr := by
  obtain ⟨ops,sem,cost⟩ := of_circuit C ao
  exact cost ▸ lb ops (correct ▸ sem)

theorem lower_transport {m n k : Nat} {f : Signal (Fin n → Bool)}
    (p : (Fin m → Bool) → (Fin n → Bool))
    (raw : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p))
    (sub : Lower (f ∘ p) k) : Lower f k := by
  intro gs ok
  obtain ⟨out,sem,budget⟩ := restrict_transfer p gs (inputs n) (inputs m) f raw ok
  have bound := sub out sem
  omega

theorem lower_rename {m n k : Nat} {f : Signal (Fin n → Bool)} (r : Fin n → Fin m)
    (sub : Lower (fun x => f (x ∘ r)) k) : Lower f k := by
  apply lower_transport (fun x => x ∘ r) _ sub
  rintro a ⟨i,rfl⟩
  exact atom ⟨r i,rfl⟩

end ThetaPin3241

namespace ThetaCores3241
open ThetaPin3241

def row {n : Nat} (mask : Nat) (i : Fin n) : Bool := mask.testBit i.val
def path2 (x : Fin 2 → Bool) : Bool := (x 0 && x 1)
def path3 (x : Fin 3 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2)
def path4 (x : Fin 4 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)
def path5 (x : Fin 5 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)
def cycle6 (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)
def pendant7 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6)

def low : Set (Fin 8) := {v | v ≠ 0 ∧ v ≠ 4}

theorem path2_lower : Lower path2 0 := lower_zero path2

theorem path3_from_core (rec : Lower path2 0) : Lower path3 1 := by
  have eq : path3 ∘ pin (2 : Fin 3) = path2 := by
    funext x
    exact (by decide +kernel : ∀ y, path3 (pin (2 : Fin 3) y) = path2 y) x
  apply lower_one_step path3 2 (row 6) (row 2)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path4_from_core (rec : Lower path3 1) : Lower path4 2 := by
  have eq : path4 ∘ pin (3 : Fin 4) = path3 := by
    funext x
    exact (by decide +kernel : ∀ y, path4 (pin (3 : Fin 4) y) = path3 y) x
  apply lower_one_step path4 3 (row 12) (row 4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path5_from_core (rec : Lower path4 2) : Lower path5 3 := by
  have eq : path5 ∘ pin (4 : Fin 5) = path4 := by
    funext x
    exact (by decide +kernel : ∀ y, path5 (pin (4 : Fin 5) y) = path4 y) x
  apply lower_one_step path5 4 (row 24) (row 8)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path5_lower : Lower path5 3 := path5_from_core (path4_from_core (path3_from_core path2_lower))

theorem pendant7_from_core (rec : Lower cycle6 5) : Lower pendant7 6 := by
  have eq : pendant7 ∘ pin (6 : Fin 7) = cycle6 := by
    funext x
    exact (by decide +kernel : ∀ y, pendant7 (pin (6 : Fin 7) y) = cycle6 y) x
  apply lower_one_step pendant7 6 (row 65) (row 1)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

def cycleRename : Fin 6 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,4,3,2,1],![1,0,4,3,2],![2,1,0,4,3],![1,2,3,4,0],![0,1,2,3,4]]

theorem cycle6_deleted (v : Fin 6) : Lower (cycle6 ∘ pin v) 3 := by
  have all : ∀ i x, (cycle6 ∘ pin i) (x ∘ cycleRename i) = path5 x := by decide +kernel
  apply lower_rename (cycleRename v)
  have eq : (fun x => (cycle6 ∘ pin v) (x ∘ cycleRename v)) = path5 := funext (all v)
  exact eq.symm ▸ path5_lower

def thetaRename : Fin 8 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6],![0,2,4,3,5,1,6],![0,2,4,3,5,6,1],![0,2,4,3,6,5,1],![0,1,2,3,4,5,6],![3,1,5,6,0,4,2],![3,1,6,5,0,4,2],![3,6,1,5,0,4,2]]

theorem theta_deleted (rec : Lower cycle6 5) (v : Fin 8) (hv : v ∈ low) :
    Lower (ThetaAnd3241.theta ∘ pin v) 6 := by
  have all : ∀ i : Fin 8, i ≠ 0 ∧ i ≠ 4 → ∀ x,
      (ThetaAnd3241.theta ∘ pin i) (x ∘ thetaRename i) = pendant7 x := by
    decide +kernel
  apply lower_rename (thetaRename v)
  have eq : (fun x => (ThetaAnd3241.theta ∘ pin v) (x ∘ thetaRename v)) = pendant7 :=
    funext (all v hv)
  exact eq.symm ▸ pendant7_from_core rec

def Classifier {n : Nat} (f : Signal (Fin n → Bool)) (L : Set (Fin n))
    (S : Set (Signal (Fin n → Bool))) : Prop :=
  inputs n ⊆ S ∧ ¬ Free S f ∧
    ∀ g : Gate (Fin n → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ L, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) →
      join g.1 g.2 ∈ S

theorem cycle6_of_classifier {S} (h : Classifier cycle6 Set.univ S) : Lower cycle6 5 :=
  lower_two_step cycle6 Set.univ S h.1 h.2.1 h.2.2 (fun v _ => cycle6_deleted v)

theorem theta_of_classifiers {S T} (cycle : Classifier cycle6 Set.univ S)
    (th : Classifier ThetaAnd3241.theta low T) : Lower ThetaAnd3241.theta 8 :=
  lower_two_step ThetaAnd3241.theta low T th.1 th.2.1 th.2.2
    (theta_deleted (cycle6_of_classifier cycle))

end ThetaCores3241

namespace ThetaClass3241
open ThetaPin3241

abbrev X (n : Nat) := Fin n → Bool
abbrev Sig (n : Nat) := Signal (X n)
def raw {n} (v : Fin n) : Sig n := fun x => x v
def bits {n} (s : Finset (Fin n)) : X n := fun i => decide (i ∈ s)

def High {n} (H : Finset (Fin n)) (a : Sig n) : Prop :=
  Monotone a ∧ ∀ x y : X n, (∀ i ∈ H, x i = y i) → a x = a y
def pool {n} (H : Finset (Fin n)) : Set (Sig n) :=
  {a | High H a ∨ ∃ i ∉ H, a = raw i}

theorem base_subset {n} (H : Finset (Fin n)) : inputs n ⊆ pool H := by
  rintro _ ⟨i,rfl⟩
  by_cases hi : i ∈ H
  · exact Or.inl ⟨fun _ _ h => h i, fun _ _ h => h i hi⟩
  · exact Or.inr ⟨i,hi,rfl⟩

theorem high_const {n} (H : Finset (Fin n)) (b : Bool) : High H (fun _ => b) :=
  ⟨fun _ _ _ => le_rfl, fun _ _ _ => rfl⟩

theorem high_join {n} {H : Finset (Fin n)} {a b : Sig n} (ha : High H a) (hb : High H b) :
    High H (join a b) := by
  constructor
  · intro x y xy
    exact sup_le_sup (ha.1 xy) (hb.1 xy)
  · intro x y h
    simp only [join,ha.2 x y h,hb.2 x y h]

theorem high_all {n} (H : Finset (Fin n)) (xs : List (Sig n))
    (hx : ∀ a ∈ xs, High H a) : High H (fun x => xs.all (fun a => a x)) := by
  induction xs with
  | nil => exact high_const H true
  | cons a xs ih =>
    have ha := hx a List.mem_cons_self
    have ht := ih (fun u hu => hx u (List.mem_cons_of_mem _ hu))
    constructor
    · intro x y xy
      exact inf_le_inf (ha.1 xy) (ht.1 xy)
    · intro x y eq
      simp only [List.all_cons, ha.2 x y eq, ht.2 x y eq]

theorem high_or_dead {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a) :
    High H a ∨ ∃ v ∉ H, a (topMiss v) = false := by
  classical
  by_contra! bad
  obtain ⟨notHigh,live⟩ := bad
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · exact notHigh (high_const _ _)
  apply notHigh (high_all H xs ?_)
  intro f hf
  rcases hxs f hf with h | ⟨v,hv,rfl⟩
  · exact h
  · have alive : xs.all (fun g => g (topMiss v)) = true := by simpa using live v hv
    have one := List.all_eq_true.mp alive (raw v) hf
    simp [raw,topMiss] at one

theorem arm_invariant {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a)
    {v : Fin n} (low : v ∉ H) (alive : a (topMiss v) = true)
    (x y : X n) (same : ∀ i, i ≠ v → x i = y i) : a x = a y := by
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · rfl
  have equal (f : Sig n) (hf : f ∈ xs) : f x = f y := by
    rcases hxs f hf with h | ⟨i,_,rfl⟩
    · exact h.2 x y (fun j hj => same j (fun eq => low (eq ▸ hj)))
    · have val := List.all_eq_true.mp alive (raw i) hf
      exact same i (by simpa [raw,topMiss] using val)
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun all f hf => equal f hf ▸ all f hf, fun all f hf => (equal f hf).symm ▸ all f hf⟩

theorem forced_raw {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a)
    {v u w : Fin n} (low : v ∉ H) (ulow : u ∉ H) (diff : u ≠ w)
    (dead : a (topMiss v) = false)
    (e1 : a (bits {v,u}) = true) (e2 : a (bits {v,w}) = true) : a = raw v := by
  classical
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · contradiction
  have classify (z : Sig n) (hz : z ∈ xs) : z = (fun _ => true) ∨ z = raw v := by
    have first := List.all_eq_true.mp e1 z hz
    have second := List.all_eq_true.mp e2 z hz
    rcases hxs z hz with high | ⟨i,_,rfl⟩
    · left
      have atZero : z (fun _ => false) = true := by
        rw [← first]
        apply high.2
        intro i hi
        have iv : i ≠ v := fun eq => low (eq ▸ hi)
        have iu : i ≠ u := fun eq => ulow (eq ▸ hi)
        simp [bits,iv,iu]
      funext x
      have le := high.1 (show (fun _ : Fin n => false) ≤ x from fun _ => bot_le)
      exact Bool.eq_true_of_true_le (atZero ▸ le)
    · right
      have h1 : i = v ∨ i = u := by simpa [raw,bits] using first
      have h2 : i = v ∨ i = w := by simpa [raw,bits] using second
      have eq : i = v := by grind
      rw [eq]
  have contains : raw v ∈ xs := by
    by_contra hn
    have t : xs.all (fun a => a (topMiss v)) = true := List.all_eq_true.mpr (by
      intro z hz
      rcases classify z hz with rfl | rfl
      · rfl
      · contradiction)
    simp [t] at dead
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro all
    exact List.all_eq_true.mp all _ contains
  · intro hv
    apply List.all_eq_true.mpr
    intro z hz
    rcases classify z hz with rfl | rfl
    · rfl
    · exact hv

end ThetaClass3241

namespace ThetaClass3241
open ThetaPin3241

structure Geometry {n : Nat} (H : Finset (Fin n)) (f : Sig n) : Prop where
  surviving : ∀ v ∉ H, f (topMiss v) = true
  singleton_false : ∀ u, f (bits {u}) = false
  neighbors : ∀ v ∉ H, ∃ u w, u ∉ H ∧ u ≠ w ∧
    f (bits {v,u}) = true ∧ f (bits {v,w}) = true
  poles : ∀ v ∉ H, ∃ u, f (bits {v,u}) = true ∧ f (bits (insert u H)) = false
  twins : ∀ v ∉ H, ∀ w ∉ H, v ≠ w → ∃ u, f (bits {v,u}) = true ∧ f (bits {u,w}) = false

def Checks {n} (H : Finset (Fin n)) (f a b : Sig n) : Prop := ∀ v ∉ H,
  deadAt (topMiss v) (a,b) = true → Admissible (inputs n) f (topMiss v) (a,b)

theorem checks_swap {n} {H : Finset (Fin n)} {f a b : Sig n} (c : Checks H f a b) :
    Checks H f b a := by
  intro v hv hd e z pass ft fe fz
  have h := c v hv (by simpa [deadAt,Bool.and_comm] using hd) e z pass ft fe fz
  simpa only [join,Bool.or_comm] using h

theorem probe {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    {v u : Fin n} (hv : v ∉ H) (c : Checks H f a b) (dead : a (topMiss v) = false)
    (z : Finset (Fin n)) (inside : u ∈ z) (fe : f (bits {v,u}) = true) (fz : f (bits z) = false) :
    join a b (topMiss v) = true ∧ join a b (bits {v,u}) = true ∧ join a b (bits z) = false := by
  apply c v hv (by simp [deadAt,dead]) _ _ _ (geo.surviving v hv) fe fz
  apply pass_inputs
  intro i ti ei
  have ne : i ≠ v := by simpa [topMiss] using ti
  have eq : i = u := by simpa [bits,ne] using ei
  simpa [bits,eq] using inside

theorem collapse {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    (ha : Free (pool H) a) (hb : Free (pool H) b) (c : Checks H f a b)
    {v : Fin n} (hv : v ∉ H) (dead : a (topMiss v) = false) : a = raw v := by
  obtain ⟨u,w,lu,ne,eu,ew⟩ := geo.neighbors v hv
  have activate (i : Fin n) (e : f (bits {v,i}) = true) : a (bits {v,i}) = true := by
    obtain ⟨st,se,sz⟩ := probe geo hv c dead {i} (by simp) e (geo.singleton_false i)
    have live : b (topMiss v) = true := by simpa [join,dead] using st
    have same := arm_invariant hb hv live (bits {v,i}) (bits {i}) (fun j hj => by simp [bits,hj])
    have bz : b (bits {i}) = false := (Bool.or_eq_false_iff.mp sz).2
    simpa [join,same,bz] using se
  exact forced_raw ha hv lu ne dead (activate u eu) (activate w ew)

theorem reject_side {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    (ha : Free (pool H) a) (hb : Free (pool H) b) (c : Checks H f a b)
    {v : Fin n} (hv : v ∉ H) (dead : a (topMiss v) = false) : False := by
  have av := collapse geo ha hb c hv dead
  rcases high_or_dead hb with high | ⟨w,hw,dw⟩
  · obtain ⟨u,eu,zu⟩ := geo.poles v hv
    obtain ⟨st,_,sz⟩ := probe geo hv c dead (insert u H) (by simp) eu zu
    have bt : b (topMiss v) = true := by simpa [join,dead] using st
    have bz : b (bits (insert u H)) = false := (Bool.or_eq_false_iff.mp sz).2
    have eq := high.2 (topMiss v) (bits (insert u H)) (fun i hi => by
      have ne : i ≠ v := fun e => hv (e ▸ hi)
      simp [topMiss,bits,ne,hi])
    simp [bt,bz] at eq
  · have bw := collapse geo hb ha (checks_swap c) hw dw
    have ne : v ≠ w := by
      rintro rfl
      obtain ⟨u,_,_,_,eu,_⟩ := geo.neighbors v hv
      have st := (probe geo hv c dead {u} (by simp) eu (geo.singleton_false u)).1
      simp [join,dead,dw] at st
    obtain ⟨u,eu,zu⟩ := geo.twins v hv w hw ne
    have sz := (probe geo hv c dead {u,w} (by simp) eu zu).2.2
    simp [join,bw,raw,bits] at sz

theorem classify {n} {H : Finset (Fin n)} {f : Sig n} (geo : Geometry H f)
    (g : Gate (X n)) (ha : Free (pool H) g.1) (hb : Free (pool H) g.2)
    (c : ∀ v ∈ {v | v ∉ H}, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) :
    join g.1 g.2 ∈ pool H := by
  have ck : Checks H f g.1 g.2 := c
  rcases high_or_dead ha with aa | ⟨v,hv,dead⟩
  · rcases high_or_dead hb with bb | ⟨v,hv,dead⟩
    · exact Or.inl (high_join aa bb)
    · exact (reject_side geo hb ha (checks_swap ck) hv dead).elim
  · exact (reject_side geo ha hb ck hv dead).elim

end ThetaClass3241

namespace ThetaClass3241
open ThetaPin3241 ThetaCores3241

theorem nonfree {n} (f : Sig n) (H : Finset (Fin n)) (x y z : X n)
    (hhigh : ∀ i ∈ H, x i = z i) (draw : ∀ i, x i = true → y i = true → z i = true)
    (fx : f x = true) (fy : f y = true) (fz : f z = false) : ¬ Free (pool H) f := by
  intro ok
  have base : ∀ a ∈ pool H, Pass x y z a := by
    intro a ha
    rcases ha with h | ⟨i,_,rfl⟩
    · intro ax _
      exact (h.2 x z hhigh) ▸ ax
    · exact draw i
  have pos := free_pass base ok fx fy
  simp [fz] at pos

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem cycle_geo : Geometry ∅ cycle6 := by constructor <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem theta_geo : Geometry {0,4} ThetaAnd3241.theta := by constructor <;> decide +kernel

theorem cycle_classifier : Classifier cycle6 Set.univ (pool ∅) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree cycle6 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle_geo g a b (fun v _ => h v (Set.mem_univ v))

theorem theta_classifier : Classifier ThetaAnd3241.theta low (pool {0,4}) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree ThetaAnd3241.theta {0,4} (bits {1,7}) (bits {2,6}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    apply classify theta_geo g a b
    intro v hv
    apply h v
    simpa [low,Set.mem_ofPred_eq,not_or] using hv

end ThetaClass3241

namespace ThetaPrune3241
open ThetaPin3241

def Private {α : Type} (P : Set α) (g : Gate α) : Prop :=
  (∃ e ∈ P, g.1 e = true ∧ g.2 e = false) ∧
  (∃ e ∈ P, g.2 e = true ∧ g.1 e = false)

def Refines {α : Type} (P : Set α) (new old : Signal α) : Prop :=
  (∀ e ∈ P, new e = old e) ∧ (∀ x, new x = true → old x = true)

theorem self_refines {α : Type} (P : Set α) (f : Signal α) : Refines P f f :=
  ⟨fun _ _ => rfl,fun _ h => h⟩

theorem ref_meet {α : Type} {P : Set α} {a b c d : Signal α}
    (h : Refines P a b) (i : Refines P c d) : Refines P (meet a c) (meet b d) := by
  constructor
  · intro e he
    simp [meet,h.1 e he,i.1 e he]
  · intro x hx
    obtain ⟨hx,hy⟩ : a x = true ∧ c x = true := by simpa [meet] using hx
    simp [meet,h.2 x hx,i.2 x hy]

theorem ref_join {α : Type} {P : Set α} {a b c d : Signal α}
    (h : Refines P a b) (i : Refines P c d) : Refines P (join a c) (join b d) := by
  constructor
  · intro e he
    simp [join,h.1 e he,i.1 e he]
  · intro x hx
    have one : a x = true ∨ c x = true := by simpa [join] using hx
    rcases one with p | p
    · simp [join,h.2 x p]
    · simp [join,i.2 x p]

theorem ref_comp {α : Type} {P : Set α} {a b c : Signal α}
    (h : Refines P a b) (i : Refines P b c) : Refines P a c :=
  ⟨fun e he => (h.1 e he).trans (i.1 e he),fun x p => i.2 x (h.2 x p)⟩

theorem refine_free {α : Type} (P : Set α) {B D : Set (Signal α)}
    (base : ∀ a ∈ B, ∃ b, Free D b ∧ Refines P b a) {a} (ok : Free B a) :
    ∃ b, Free D b ∧ Refines P b a := by
  apply ok {a | ∃ b, Free D b ∧ Refines P b a}
  · exact base
  · exact ⟨_,free_zero,self_refines _ _⟩
  · exact ⟨_,free_one,self_refines _ _⟩
  · intro a ha b hb
    obtain ⟨c,hc,rc⟩ := ha
    obtain ⟨d,hd,rd⟩ := hb
    exact ⟨meet c d,free_meet hc hd,ref_meet rc rd⟩

theorem choose_arm {α : Type} {P : Set α} {g : Gate α} (bad : ¬ Private P g) :
    ∃ u, (u = g.1 ∨ u = g.2) ∧ Refines P u (join g.1 g.2) := by
  classical
  by_cases left : ∃ e ∈ P, g.1 e = true ∧ g.2 e = false
  · have right : ¬∃ e ∈ P, g.2 e = true ∧ g.1 e = false := fun h => bad ⟨left,h⟩
    refine ⟨g.1,Or.inl rfl,?_,fun x h => by simp [join,h]⟩
    intro e he
    cases a : g.1 e <;> cases b : g.2 e <;> simp [join,a,b]
    exact right ⟨e,he,b,a⟩
  · refine ⟨g.2,Or.inr rfl,?_,fun x h => by simp [join,h]⟩
    intro e he
    cases a : g.1 e <;> cases b : g.2 e <;> simp [join,a,b]
    exact left ⟨e,he,a,b⟩

theorem prune {α : Type} (P : Set α) (B D : Set (Signal α)) (gs : List (Gate α)) (f : Signal α)
    (base : ∀ a ∈ B, ∃ b, Free D b ∧ Refines P b a) (ok : Valid B gs f) :
    ∃ out f', Valid D out f' ∧ Refines P f' f ∧ out.length ≤ gs.length ∧
      ∀ g ∈ out, Private P g := by
  classical
  induction gs generalizing B D with
  | nil =>
    obtain ⟨f',h,r⟩ := refine_free P base ok
    exact ⟨[],f',h,r,by simp,by simp⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    obtain ⟨a,fa,ra⟩ := refine_free P base ha
    obtain ⟨b,fb,rb⟩ := refine_free P base hb
    have combined := ref_join ra rb
    by_cases use : Private P (a,b)
    · let D' := insert (join a b) D
      have next : ∀ v ∈ insert (join g.1 g.2) B, ∃ w, Free D' w ∧ Refines P w v := by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | old
        · exact ⟨join a b, atom (Set.mem_insert _ _), combined⟩
        · obtain ⟨w,hw,hv⟩ := base _ old
          exact ⟨w,widen (Set.subset_insert _ _) hw,hv⟩
      obtain ⟨out,f',sem,r,cost,all⟩ := ih _ D' next tail
      refine ⟨(a,b)::out,f',⟨fa,fb,sem⟩,r,by simpa using cost,?_⟩
      intro u hu
      exact (List.mem_cons.mp hu).elim (fun h => h ▸ use) (all u)
    · obtain ⟨u,side,ref⟩ := choose_arm use
      have fu : Free D u := side.elim (fun h => h ▸ fa) (fun h => h ▸ fb)
      have next : ∀ v ∈ insert (join g.1 g.2) B, ∃ w, Free D w ∧ Refines P w v := by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | old
        · exact ⟨u,fu,ref_comp ref combined⟩
        · exact base _ old
      obtain ⟨out,f',sem,r,cost,all⟩ := ih _ D next tail
      exact ⟨out,f',sem,r,by simp; omega,all⟩

theorem increasing_output {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {gs f} (ok : Valid B gs f) : Increasing f := by
  induction gs generalizing B with
  | nil => exact free_increasing base ok
  | cons g gs ih =>
    obtain ⟨l,r,tail⟩ := ok
    apply ih _ tail
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | old
    · intro x y le hx
      have either : g.1 x = true ∨ g.2 x = true := by simpa [join] using hx
      rcases either with h | h
      · simp [join,free_increasing base l x y le h]
      · simp [join,free_increasing base r x y le h]
    · exact base _ old

def Generates {n : Nat} (P : Set (Fin n → Bool)) (f : Signal (Fin n → Bool)) : Prop :=
  ∀ x, f x = true → ∃ e ∈ P, f e = true ∧ ∀ i, e i = true → x i = true

theorem private_program {n : Nat} (P : Set (Fin n → Bool)) (f : Signal (Fin n → Bool))
    (cover : Generates P f) (gs : List (Gate (Fin n → Bool))) (ok : Valid (inputs n) gs f) :
    ∃ out, Valid (inputs n) out f ∧ out.length ≤ gs.length ∧ ∀ g ∈ out, Private P g := by
  have ids : ∀ a ∈ inputs n, ∃ b, Free (inputs n) b ∧ Refines P b a :=
    fun a h => ⟨a,atom h,self_refines _ _⟩
  obtain ⟨out,v,sem,ref,cost,all⟩ := prune P _ _ gs f ids ok
  have mon := increasing_output (fun a (h : a ∈ inputs n) => by
    obtain ⟨i,rfl⟩ := h
    exact fun _ _ le => le i) sem
  have eq : v = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    refine ⟨ref.2 x,?_⟩
    intro h
    obtain ⟨e,pe,pos,le⟩ := cover x h
    exact mon e x le ((ref.1 e pe).trans pos)
  exact ⟨out,eq ▸ sem,cost,all⟩

theorem private_lower_two_step {n k : Nat} (f : Signal (Fin (n+1) → Bool))
    (low : Set (Fin (n+1))) (S : Set (Signal (Fin (n+1) → Bool))) (P : Set (Fin (n+1) → Bool))
    (inc : inputs (n+1) ⊆ S) (nonfree : ¬ Free S f) (cover : Generates P f)
    (classify : ∀ g : Gate (Fin (n+1) → Bool), Free S g.1 → Free S g.2 → Private P g →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs (n+1)) f (topMiss v) g) →
      join g.1 g.2 ∈ S) (rec : ∀ v ∈ low, Lower (f ∘ pin v) k) : Lower f (k+2) := by
  classical
  intro gs ok
  obtain ⟨out,sem,short,priv⟩ := private_program P f cover gs ok
  have hit : ∃ v ∈ low, 2 ≤ out.countP (deadAt (topMiss v)) := by
    by_contra no
    apply nonfree
    apply propagate_property (inputs _) S out f inc sem
    intro g hg a b
    apply classify g a b (priv g hg)
    intro v hv dg e z raw ft fe fz
    have small : out.countP (deadAt (topMiss v)) ≤ 1 := by
      by_contra h
      exact no ⟨v,hv,by omega⟩
    exact single_charge_passes sem g hg (topMiss v) e z raw ft fe fz dg small
  obtain ⟨v,hv,charge⟩ := hit
  obtain ⟨sub,sok,cost⟩ := delete_charge sem v
  have lb := rec v hv sub sok
  omega

end ThetaPrune3241

namespace Theta244Cores
open ThetaPin3241 ThetaCores3241 ThetaPrune3241
def path6 (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)
def path7 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)
def cycle8 (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 0)
def twoEnds (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6) || (x 2 && x 7)
def tailTwo (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6) || (x 6 && x 7)
def theta (x : Fin 9 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 1 && x 8)

theorem path6_lower (rec : Lower path5 3) : Lower path6 4 := by
  have eq : path6 ∘ pin (5 : Fin 6) = path5 := by
    funext x
    exact (by decide +kernel : ∀ y, path6 (pin (5 : Fin 6) y) = path5 y) x
  apply lower_one_step path6 5 (row 48) (row 16)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path7_lower (rec : Lower path6 4) : Lower path7 5 := by
  have eq : path7 ∘ pin (6 : Fin 7) = path6 := by
    funext x
    exact (by decide +kernel : ∀ y, path7 (pin (6 : Fin 7) y) = path6 y) x
  apply lower_one_step path7 6 (row 96) (row 32)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem twoEnds_lower (rec : Lower pendant7 6) : Lower twoEnds 7 := by
  have eq : twoEnds ∘ pin (7 : Fin 8) = pendant7 := by
    funext x
    exact (by decide +kernel : ∀ y, twoEnds (pin (7 : Fin 8) y) = pendant7 y) x
  apply lower_one_step twoEnds 7 (row 132) (row 4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem tailTwo_lower (rec : Lower pendant7 6) : Lower tailTwo 7 := by
  have eq : tailTwo ∘ pin (7 : Fin 8) = pendant7 := by
    funext x
    exact (by decide +kernel : ∀ y, tailTwo (pin (7 : Fin 8) y) = pendant7 y) x
  apply lower_one_step tailTwo 7 (row 192) (row 64)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

def cycleRelabel : Fin 8 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6],![0,6,5,4,3,2,1],![1,0,6,5,4,3,2],![2,1,0,6,5,4,3],![3,2,1,0,6,5,4],![2,3,4,5,6,0,1],![1,2,3,4,5,6,0],![0,1,2,3,4,5,6]]
def thetaRelabel : Fin 9 → Fin 8 → Fin 8 := ![![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,4,1,2,3,7,6,5],![2,0,1,7,6,3,4,5],![0,2,1,6,7,5,4,3],![0,2,1,6,7,5,4,3],![2,0,1,3,4,5,7,6],![0,2,1,5,4,3,6,7],![0,2,1,5,4,3,6,7]]
def lows : Set (Fin 9) := {v | 2 ≤ v.val}
def cofactor (v : Fin 9) :=
  if v = 2 then cycle8 else if v = 4 ∨ v = 7 then twoEnds else tailTwo

theorem cycle8_deleted (v : Fin 8) : Lower (cycle8 ∘ pin v) 5 := by
  have all : ∀ i x, (cycle8 ∘ pin i) (x ∘ cycleRelabel i) = path7 x := by decide +kernel
  apply lower_rename (cycleRelabel v)
  have eq : (fun x => (cycle8 ∘ pin v) (x ∘ cycleRelabel v)) = path7 := funext (all v)
  exact eq.symm ▸ path7_lower (path6_lower path5_lower)

theorem theta_deleted (h6 : Lower cycle6 5) (h8 : Lower cycle8 7) (v : Fin 9) (hv : v ∈ lows) :
    Lower (theta ∘ pin v) 7 := by
  have all : ∀ i : Fin 9, 2 ≤ i.val → ∀ x, (theta ∘ pin i) (x ∘ thetaRelabel i) = cofactor i x := by
    decide +kernel
  apply lower_rename (thetaRelabel v)
  have eq : (fun x => (theta ∘ pin v) (x ∘ thetaRelabel v)) = cofactor v := funext (all v hv)
  rw [eq]
  unfold cofactor
  split
  · exact h8
  · split
    · exact twoEnds_lower (pendant7_from_core h6)
    · exact tailTwo_lower (pendant7_from_core h6)

theorem cycle8_of_classifier {S} (h : Classifier cycle8 Set.univ S) : Lower cycle8 7 :=
  lower_two_step cycle8 Set.univ S h.1 h.2.1 h.2.2 (fun v _ => cycle8_deleted v)

def positive : Set (Fin 9 → Bool) := {x |
  ∃ i j : Fin 9, ((i.val,j.val) ∈ ([(0, 2), (1, 2), (0, 3), (3, 4), (4, 5), (1, 5), (0, 6), (6, 7), (7, 8), (1, 8)] : List (Nat × Nat))) ∧
    x = row (2^i.val+2^j.val)}

theorem generates : Generates positive theta := by
  intro x hx
  have all : ∀ y : Fin 9 → Bool, theta y = true →
      ∃ i j : Fin 9, (i.val,j.val) ∈ ([(0, 2), (1, 2), (0, 3), (3, 4), (4, 5), (1, 5), (0, 6), (6, 7), (7, 8), (1, 8)] : List (Nat × Nat)) ∧
        theta (row (2^i.val+2^j.val)) = true ∧ ∀ l : Fin 9, row (2^i.val+2^j.val) l = true → y l = true := by
    decide +kernel
  obtain ⟨i,j,edge,yes,le⟩ := all x hx
  exact ⟨_,⟨i,j,edge,rfl⟩,yes,le⟩

end Theta244Cores

namespace Theta244Finish
open ThetaPin3241 ThetaPrune3241 Theta244Cores ThetaClass3241

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem cycle_geo : Geometry ∅ cycle8 := by constructor <;> decide +kernel

theorem cycle_classifier : ThetaCores3241.Classifier cycle8 Set.univ (pool ∅) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree cycle8 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle_geo g a b (fun v _ => h v (Set.mem_univ v))

theorem deleted (v : Fin 9) (hv : v ∈ lows) : Lower (theta ∘ pin v) 7 :=
  theta_deleted (ThetaCores3241.cycle6_of_classifier ThetaClass3241.cycle_classifier)
    (cycle8_of_classifier cycle_classifier) v hv

theorem nine_of_classifier {P : Set (Fin 9 → Bool)} {S : Set (Signal (Fin 9 → Bool))}
    (base : inputs 9 ⊆ S) (nonfree : ¬ Free S theta) (cover : Generates P theta)
    (classify : ∀ g : Gate (Fin 9 → Bool), Free S g.1 → Free S g.2 → Private P g →
      (∀ v ∈ lows, deadAt (topMiss v) g = true → Admissible (inputs 9) theta (topMiss v) g) →
      join g.1 g.2 ∈ S) : Lower theta 9 :=
  private_lower_two_step theta lows S P base nonfree cover classify deleted

def eleven : Fin 11 → Finset (Fin 9) :=
  ![{1,3,6}, {1,4,6}, {1,3,7}, {0,1,4,7}, {2,4,7}, {0,5,7}, {2,3,5,7}, {0,4,8},
    {0,5,8}, {2,4,6,8}, {2,3,5,6,8}]

def upper : PEqualNP.CircuitLowerBounds.Circuit := ⟨
  [⟨.or,[2,3]⟩,⟨.or,[9,6]⟩,⟨.and,[0,10]⟩,
   ⟨.or,[2,5]⟩,⟨.or,[12,8]⟩,⟨.and,[1,13]⟩,
   ⟨.or,[3,5]⟩,⟨.and,[4,15]⟩,⟨.or,[6,8]⟩,⟨.and,[7,17]⟩,
   ⟨.or,[11,14]⟩,⟨.or,[16,18]⟩,⟨.or,[19,20]⟩],21⟩

end Theta244Finish

namespace Theta244
open ThetaPin3241
abbrev X := Fin 9 → Bool
abbrev W := BitVec 28
def readBit (w : W) (i : Fin 28) : Bool := w[i.val]
def rowMasks : List Nat := [5,6,9,24,48,34,65,192,384,258,74,82,138,147,148,161,172,273,289,340,364,507,503,495,479,447,383,255]
def row (i : Fin 28) (v : Fin 9) : Bool := (rowMasks.getD i.val 0).testBit v.val
def target (x : X) : Bool := (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 1 && x 8)
def code : W := 266339327
def rawMasks : List W := [266772549,266354210,265895939,263263244,258631704,250970160,234360000,199356800,134087424]
def base : List W := [0,134087424,199356800,234360000,250970160,258631704,263263244,265895939,266346496,266354210,266772549,266780263,268435455]
def arm : List W := [0,2097152,4194304,6291456,8388608,10485760,12582912,14680064,16777216,18874368,20971520,23068672,25165824,27262976,29360128,31457280,33554432,35651584,37748736,39845888,41943040,44040192,46137344,48234496,50331648,52428800,54525952,56623104,58720256,60817408,62914560,65011712,65011968,67108864,69206016,71303168,73400320,75497472,76546048,77594624,78643200,79691776,80740352,81788928,82837504,83886080,85983232,88080384,88604672,90177536,90701824,92274688,93323264,94371840,95420416,96468992,98041856,98566144,100139008,100663296,102760448,104857600,106954752,109051904,110100480,111149056,112197632,113246208,114294784,115343360,115605504,116654080,117440512,119537664,121634816,122159104,123731968,123863040,124387328,125829120,126877696,127926272,128974848,130023424,131596288,132120576,132121088,132513792,132514304,134087424,134217728,136314880,138412032,140509184,142606336,144703488,146800640,148897792,150994944,153092096,155189248,157286400,159383552,161480704,163577856,165675008,165675136,167772160,169869312,171966464,174063616,176160768,176226304,178257920,178323456,180355072,180420608,182452224,182484992,182550528,184549376,186646528,188743680,188760064,190849024,190865408,192937984,193003520,195035136,195039232,195104768,197132288,197214208,199237632,199241728,199270400,199274496,199356800,201326592,203423744,205520896,207618048,209715200,210763776,211812352,212860928,213909504,214958080,216006656,217055232,218103808,220200960,222298112,222822400,224395264,224397312,224921600,226492416,227540992,228589568,228590592,229639168,230686720,232259584,232783872,232783936,232786944,232787008,234360000,234881024,236978176,239075328,241172480,241172496,243269632,244383744,245366784,246480896,247463936,248578048,249561088,249561120,249856000,249856032,250970160,251658240,253755392,253755400,255852544,256393216,257957888,257959936,258088960,258091008,258631704,260046848,261160960,262144000,262144004,262149120,262149124,263263244,264241152,264241153,264241154,264241155,265895939,266346496,266354210,266772549,266780263,268435455]
def posArm : List W := [65011968,132121088,132514304,134087424,165675136,199356800,232783936,232787008,234360000,241172496,249561120,249856032,250970160,253755400,258631704,262144004,262149124,263263244,264241153,264241154,264241155,265895939,266354210,266772549,266780263,268435455]
structure Test where
  v : Fin 9
  t : Fin 28
  e : Fin 28
  z : Fin 28
  deriving DecidableEq
def tests : List Test := [⟨2,21,0,13⟩,⟨2,21,0,15⟩,⟨2,21,0,17⟩,⟨2,21,0,18⟩,⟨2,21,1,10⟩,⟨2,21,1,11⟩,⟨2,21,1,12⟩,⟨2,21,1,13⟩,⟨3,22,2,13⟩,⟨3,22,2,15⟩,⟨3,22,2,17⟩,⟨3,22,2,18⟩,⟨3,22,3,11⟩,⟨3,22,3,13⟩,⟨3,22,3,14⟩,⟨3,22,3,17⟩,⟨3,22,3,19⟩,⟨4,23,3,10⟩,⟨4,23,3,12⟩,⟨4,23,3,16⟩,⟨4,23,3,20⟩,⟨4,23,4,15⟩,⟨4,23,4,16⟩,⟨4,23,4,18⟩,⟨4,23,4,20⟩,⟨5,24,4,11⟩,⟨5,24,4,13⟩,⟨5,24,4,14⟩,⟨5,24,4,17⟩,⟨5,24,4,19⟩,⟨5,24,5,10⟩,⟨5,24,5,11⟩,⟨5,24,5,12⟩,⟨5,24,5,13⟩,⟨6,25,6,13⟩,⟨6,25,6,15⟩,⟨6,25,6,17⟩,⟨6,25,6,18⟩,⟨6,25,7,12⟩,⟨6,25,7,13⟩,⟨6,25,7,14⟩,⟨6,25,7,15⟩,⟨6,25,7,16⟩,⟨7,26,7,10⟩,⟨7,26,7,11⟩,⟨7,26,7,19⟩,⟨7,26,7,20⟩,⟨7,26,8,17⟩,⟨7,26,8,18⟩,⟨7,26,8,19⟩,⟨7,26,8,20⟩,⟨8,27,8,12⟩,⟨8,27,8,13⟩,⟨8,27,8,14⟩,⟨8,27,8,15⟩,⟨8,27,8,16⟩,⟨8,27,9,10⟩,⟨8,27,9,11⟩,⟨8,27,9,12⟩,⟨8,27,9,13⟩]
def edgeIdx (i : Fin 10) : Fin 28 := i.castLE (by decide)
def positives : Set X := Set.range (fun i : Fin 10 => row (edgeIdx i))
def low : Set (Fin 9) := {v | 2 ≤ v.val}
def represents (a : Signal X) (w : W) : Prop := ∀ i, a (row i) = readBit w i
def pool : Set (Signal X) := {a | ∃ w ∈ base, represents a w}

def privateMask (a b : W) : Prop :=
  (∃ i : Fin 10, readBit a (edgeIdx i) = true ∧ readBit b (edgeIdx i) = false) ∧
  (∃ i : Fin 10, readBit b (edgeIdx i) = true ∧ readBit a (edgeIdx i) = false)

def good (a b : W) (q : Test) : Prop :=
  (readBit a q.t && readBit b q.t) = false →
    readBit (a ||| b) q.t = true ∧ readBit (a ||| b) q.e = true ∧ readBit (a ||| b) q.z = false

instance (a b : W) : Decidable (privateMask a b) := by unfold privateMask; infer_instance
instance (a b : W) (q : Test) : Decidable (good a b q) := by unfold good; infer_instance

theorem and_table (a b : W) (ha : a ∈ posArm) (hb : b ∈ base)
    (i : Fin 10) (hit : readBit (b &&& a) (edgeIdx i) = true) : (b &&& a) ∈ posArm := by
  have table : posArm.all (fun u => base.all (fun v => posArm.contains (v &&& u) ||
      decide (∀ j : Fin 10, readBit (v &&& u) (edgeIdx j) = false))) = true := by decide +kernel
  have either := List.all_eq_true.mp (List.all_eq_true.mp table a ha) b hb
  rcases Bool.or_eq_true_iff.mp either with yes | no
  · simpa using yes
  · have v := of_decide_eq_true no i
    simp [hit] at v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem or_table (a : W) (ha : a ∈ posArm) (b : W) (hb : b ∈ posArm)
    (p : privateMask a b) (h : ∀ q ∈ tests, good a b q) : (a ||| b) ∈ base := by
  have table : posArm.all (fun u => posArm.all (fun v =>
      base.contains (u ||| v) || !decide (privateMask u v) ||
      !tests.all (fun q => decide (good u v q)))) = true := by decide +kernel
  have atPair := List.all_eq_true.mp (List.all_eq_true.mp table a ha) b hb
  have gates : tests.all (fun q => decide (good a b q)) = true :=
    List.all_eq_true.mpr (fun q hq => decide_eq_true (h q hq))
  simpa [p,gates] using atPair

theorem probes : ∀ q ∈ tests, 2 ≤ q.v.val ∧ (∀ i, row q.t i = topMiss q.v i) ∧
    target (row q.t) = true ∧ target (row q.e) = true ∧ target (row q.z) = false ∧
    ∀ i, row q.t i = true → row q.e i = true → row q.z i = true := by decide +kernel

theorem represent_and {a b : Signal X} {u v : W} (ha : represents a u) (hb : represents b v) :
    represents (meet a b) (u &&& v) := by
  intro i
  simp [meet,ha i,hb i,readBit]

theorem represent_or {a b : Signal X} {u v : W} (ha : represents a u) (hb : represents b v) :
    represents (join a b) (u ||| v) := by
  intro i
  simp [join,ha i,hb i,readBit]

theorem free_arm {a : Signal X} (h : Free pool a) (i : Fin 10) (onEdge : a (row (edgeIdx i)) = true) :
    ∃ w ∈ posArm, represents a w := by
  rcases factors h with rfl | ⟨xs,hs,rfl⟩
  · contradiction
  · clear h
    induction xs with
    | nil => exact ⟨268435455,by decide +kernel,(by decide +kernel : ∀ i : Fin 28, true = readBit 268435455 i)⟩
    | cons a xs ih =>
      obtain ⟨u,hu,ra⟩ := hs a (by simp)
      obtain ⟨_,tail⟩ := Bool.and_eq_true_iff.mp onEdge
      obtain ⟨v,hv,rs⟩ := ih (fun b hb => hs b (by simp [hb])) tail
      have allRep : represents (fun x => (a::xs).all (fun f => f x)) (u &&& v) := by
        intro k
        change ((a::xs).all (fun f => f (row k))) = _
        rw [List.all_cons]
        exact (represent_and ra rs) k
      exact ⟨_,and_table v u hv hu i ((allRep _).symm.trans onEdge),allRep⟩

theorem inputs_pool : inputs 9 ⊆ pool := by
  rintro _ ⟨i,rfl⟩
  have tab : ∀ j : Fin 9, rawMasks.getD j.val 0 ∈ base ∧
      ∀ k, row k j = readBit (rawMasks.getD j.val 0) k := by decide +kernel
  exact ⟨_,(tab i).1,(tab i).2⟩

theorem target_nonfree : ¬ Free pool target := by
  intro h
  obtain ⟨a,ha,rep⟩ := free_arm h 0 (by decide +kernel)
  have fixed : ∀ i : Fin 28, target (row i) = readBit code i := by decide +kernel
  have different : code ∉ posArm := by decide +kernel
  have eq : a = code := by
    apply BitVec.eq_of_getElem_eq
    intro k hk
    exact (rep ⟨k,hk⟩).symm.trans (fixed ⟨k,hk⟩)
  exact different (eq ▸ ha)

theorem classify (g : Gate X) (fa : Free pool g.1) (fb : Free pool g.2)
    (priv : ThetaPrune3241.Private positives g)
    (valid : ∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs 9) target (topMiss v) g) :
    join g.1 g.2 ∈ pool := by
  obtain ⟨⟨_,⟨i,rfl⟩,ia,ib⟩,⟨_,⟨j,rfl⟩,jb,ja⟩⟩ := priv
  obtain ⟨a,pa,ra⟩ := free_arm fa i ia
  obtain ⟨b,pb,rb⟩ := free_arm fb j jb
  rw [ra] at ia ja
  rw [rb] at ib jb
  have joined := represent_or ra rb
  refine ⟨_,or_table a pa b pb ⟨⟨i,ia,ib⟩,⟨j,jb,ja⟩⟩ ?_,joined⟩
  intro q hq dead
  obtain ⟨lo,point,ft,fe,fz,pass⟩ := probes q hq
  have eq := funext point
  have dg : deadAt (topMiss q.v) g = true := by
    simp [← eq,deadAt,ra q.t,rb q.t,dead]
  have adm := valid q.v lo dg
  rw [← eq] at adm
  obtain ⟨st,se,sz⟩ := adm (row q.e) (row q.z) (pass_inputs _ _ _ pass) ft fe fz
  exact ⟨(joined q.t).symm.trans st,(joined q.e).symm.trans se,(joined q.z).symm.trans sz⟩

theorem generates : ThetaPrune3241.Generates positives target := by
  have all : ∀ x : X, target x = true → ∃ i : Fin 10, target (row (edgeIdx i)) = true ∧
      ∀ j, row (edgeIdx i) j = true → x j = true := by decide +kernel
  intro x hx
  obtain ⟨i,yes,le⟩ := all x hx
  exact ⟨_,⟨i,rfl⟩,yes,le⟩

theorem nine : Lower Theta244Cores.theta 9 :=
  Theta244Finish.nine_of_classifier inputs_pool target_nonfree generates classify

end Theta244

namespace LeafAnd3241
open ThetaPin3241 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

abbrev X (n : Nat) := Fin n → Bool
def dual {n : Nat} (f : Signal (X n)) : Signal (X n) := fun x => !(f fun i => !(x i))

theorem dual_wire {n : Nat} {B : Set (Signal (X n))} {w : List (Signal (X n))}
    (hw : ∀ a ∈ w, Free B (dual a)) (i : Nat) : Free B (dual (wire w i)) := by
  induction w generalizing i with
  | nil => cases i <;> exact free_one
  | cons a w ih => cases i with
    | zero => exact hw _ List.mem_cons_self
    | succ i => exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) i

theorem dual_compress {n : Nat} (gs : List PhysicalGate) (output : Nat) (w : List (Signal (X n)))
    (B : Set (Signal (X n))) (hw : ∀ a ∈ w, Free B (dual a)) (shapes : ∀ g ∈ gs, pairShape g) :
    ∃ ops : List (ThetaPin3241.Gate (X n)), Valid B ops (dual (wire (gs.foldl step w) output)) ∧
      ops.length = gs.countP ThetaAnd3241.andGate := by
  induction gs generalizing w B with
  | nil => exact ⟨[],dual_wire hw output,rfl⟩
  | cons g gs ih =>
    obtain ⟨hop,i,j,pins⟩ := shapes g List.mem_cons_self
    have tail (h : PhysicalGate) (hh : h ∈ gs) := shapes h (List.mem_cons_of_mem _ hh)
    let a := dual (wire w i)
    let b := dual (wire w j)
    rcases hop with kind | kind
    · let D := insert (join a b) B
      have eq : step w g = w ++ [meet (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have dual_and : dual (meet (wire w i) (wire w j)) = join a b := by
        funext x
        simp [dual,meet,join,a,b,Bool.not_and]
      have ext : ∀ f ∈ step w g, Free D (dual f) := by
        intro f hf
        rw [eq,List.mem_append,List.mem_singleton] at hf
        rcases hf with old | rfl
        · exact widen (Set.subset_insert _ _) (hw f old)
        · rw [dual_and]
          exact atom (Set.mem_insert _ _)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) D ext tail
      refine ⟨(a,b)::ops,⟨dual_wire hw i,dual_wire hw j,sem⟩,?_⟩
      have yes : ThetaAnd3241.andGate g = true := by simp [ThetaAnd3241.andGate,kind]
      simp [cost,yes]
    · have eq : step w g = w ++ [join (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have dual_or : dual (join (wire w i) (wire w j)) = meet a b := by
        funext x
        simp [dual,meet,join,a,b,Bool.not_or]
      have ext : ∀ f ∈ step w g, Free B (dual f) := by
        intro f hf
        rw [eq,List.mem_append,List.mem_singleton] at hf
        rcases hf with old | rfl
        · exact hw f old
        · rw [dual_or]
          exact free_meet (dual_wire hw i) (dual_wire hw j)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) B ext tail
      refine ⟨ops,sem,?_⟩
      have no : ThetaAnd3241.andGate g = false := by simp [ThetaAnd3241.andGate,kind]
      simpa [no] using cost

theorem and_lower_circuit {n k : Nat} (f : Signal (X n)) (lb : Lower (dual f) k)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = f) :
    k ≤ C.gates.countP ThetaAnd3241.andGate := by
  let w : List (Signal (X n)) := (List.finRange n).map (fun i x => x i)
  have ok (a) (ha : a ∈ w) : Free (inputs n) (dual a) := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    apply atom
    exact ⟨i,funext (fun x => by simp [dual])⟩
  have shapes (g : PhysicalGate) (hg : g ∈ C.gates) : pairShape g := by
    refine ⟨ao.1 _ hg,?_⟩
    have len := ao.2.2 _ hg
    match h : g.inputs with
    | [] => simp [h] at len
    | [_] => simp [h] at len
    | a::b::rest =>
      have nil : rest = [] := List.length_eq_zero_iff.mp (by simpa [h] using len)
      exact ⟨a,b,by rw [nil]⟩
  obtain ⟨ops,sem,cost⟩ := dual_compress C.gates C.output w (inputs n) ok shapes
  have eq : wire (C.gates.foldl step w) C.output = circuitFun n C := by
    funext x
    rw [← wire_point,run_point]
    have start : w.map (fun f => f x) = List.ofFn x := by simp [w,List.ofFn_eq_map]
    rw [start]
    rfl
  rw [eq,correct] at sem
  exact cost ▸ lb ops sem

theorem save_at {m n k : Nat} (f : Signal (X n)) (v : Fin n) (e z : X n) (p : X m → X n)
    (inputs_ok : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p))
    (bounded : ∀ x i, p x i = true → topMiss v i = true)
    (pass : ∀ i, topMiss v i = true → e i = true → z i = true)
    (top : f (topMiss v) = true) (edge : f e = true) (neg : f z = false)
    (sub : Lower (f ∘ p) k) : Lower f (k+1) := by
  intro gs ok
  obtain ⟨g,hg,dead,_⟩ := critical_gate gs (inputs n) f _ _ _ (pass_inputs _ _ _ pass) ok top edge neg
  obtain ⟨l,r⟩ := active_monotone (fun a (h : a ∈ inputs n) => by
    obtain ⟨i,rfl⟩ := h
    exact fun _ _ le => le i) ok g hg
  have zero {a : Signal (X n)} (inc : Increasing a) (off : a (topMiss v) = false) :
      ∀ x, a (p x) = false := by
    intro x
    cases h : a (p x) with
    | false => rfl
    | true => simp [inc _ _ (bounded x) h] at off
  have killed : Killed p g := dead.imp (zero l) (zero r)
  have charge : 0 < gs.countP (killedBit p) :=
    List.countP_pos_iff.mpr ⟨g,hg,by simp [killedBit,killed]⟩
  obtain ⟨out,sem,cost⟩ := restrict_transfer p gs _ _ f inputs_ok ok
  have lower := sub out sem
  omega

def cover {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : X n) : Bool :=
  decide (∀ a b, G.Adj a b → x a = true ∨ x b = true)

theorem cover_dual {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    dual (NestedCover.graphFun G ∅) = cover G := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [dual,NestedCover.graphFun,cover]
  grind

def pinLeaf {n : Nat} (v w : Fin n) (x : X n) (i : Fin n) : Bool :=
  if i = v then false else if i = w then true else x i

theorem leaf_step {n k : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) (adj : G.Adj v w) (leaf : ∀ i, G.Adj v i → i = w)
    (sub : Lower (cover (G.deleteIncidenceSet w)) k) : Lower (cover G) (k+1) := by
  have ne := G.ne_of_adj adj
  have hi (i : Fin n) : cover G (topMiss i) = true := by
    simp only [cover,decide_eq_true_eq,topMiss]
    intro a b ab
    by_cases av : a = i
    · exact Or.inr (fun (bv : b = i) => G.ne_of_adj ab (av.trans bv.symm))
    · exact Or.inl (by simp [av])
  let z : X n := fun i => decide (i ≠ v ∧ i ≠ w)
  have neg : cover G z = false := by
    apply decide_eq_false_iff_not.mpr
    intro h
    simpa [z] using h v w adj
  have cof : cover G ∘ pinLeaf v w = cover (G.deleteIncidenceSet w) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq,SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · intro h a b ⟨ab,aw,bw⟩
      have av : a ≠ v := fun e => bw (leaf b (e ▸ ab))
      have bv : b ≠ v := fun e => aw (leaf a (e ▸ ab.symm))
      simpa [pinLeaf,av,bv,aw,bw] using h a b ab
    · intro h a b ab
      by_cases aw : a = w
      · simp [pinLeaf,aw,ne.symm]
      by_cases bw : b = w
      · simp [pinLeaf,bw,ne.symm]
      have av : a ≠ v := fun e => bw (leaf b (e ▸ ab))
      have bv : b ≠ v := fun e => aw (leaf a (e ▸ ab.symm))
      simpa [pinLeaf,av,bv,aw,bw] using h a b ⟨ab,aw,bw⟩
  apply save_at (cover G) v (topMiss w) z (pinLeaf v w) _ _ _ (hi v) (hi w) neg (cof.symm ▸ sub)
  · rintro _ ⟨i,rfl⟩
    by_cases iv : i = v
    · simpa [Function.comp_def,pinLeaf,iv] using (free_zero (B := inputs n))
    by_cases iw : i = w
    · simpa [Function.comp_def,pinLeaf,iv,iw,ne.symm] using (free_one (B := inputs n))
    · simpa [Function.comp_def,pinLeaf,iv,iw] using (atom (B := inputs n) ⟨i,rfl⟩)
  · intro x i pi
    by_contra h
    have iv : i = v := by simpa [topMiss] using h
    simp [pinLeaf,iv] at pi
  · intro i tv tw
    simpa [z,topMiss] using And.intro tv tw

end LeafAnd3241

namespace LeafCore3241
open ThetaPin3241 LeafAnd3241 PEqualNP.MetaComplexity PEqualNP.TopForm

def edgeFun {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : X n) : Bool :=
  decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)

theorem ordinary_eq {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    NestedCover.graphFun G ∅ = edgeFun G := by
  funext x
  simp [NestedCover.graphFun,edgeFun]

def Leafless {n : Nat} (G : SimpleGraph (Fin n)) : Prop :=
  ¬ ∃ v w, G.Adj v w ∧ ∀ a, G.Adj v a → a = w

def Counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  Lower (edgeFun G) (G.edgeFinset.card - 1) ∧
    ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ Lower (cover G) S.card

def pinZero {n : Nat} (v : Fin n) (x : X n) (i : Fin n) := if i = v then false else x i

theorem or_leaf {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n)
    (vw : G.Adj v w) (leaf : ∀ a, G.Adj v a → a = w)
    (sub : Lower (edgeFun (G.deleteIncidenceSet v)) ((G.deleteIncidenceSet v).edgeFinset.card - 1)) :
    Lower (edgeFun G) (G.edgeFinset.card - 1) := by
  have dg : G.degree v = 1 := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨w,vw,leaf⟩
  have card := G.card_edgeFinset_deleteIncidenceSet v
  rw [dg] at card
  by_cases small : G.edgeFinset.card ≤ 1
  · have h : G.edgeFinset.card - 1 = 0 := by omega
    rw [h]
    exact lower_zero _
  have pos : (G.deleteIncidenceSet v).edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have nonzero := (G.deleteIncidenceSet v).edgeFinset_nonempty.mp pos
  have pair : ∃ a b, (G.deleteIncidenceSet v).Adj a b := by
    by_contra! no
    exact nonzero (SimpleGraph.eq_bot_iff_forall_not_adj.mpr no)
  obtain ⟨a,b,ab⟩ := pair
  obtain ⟨edge,av,bv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp ab
  have top : edgeFun G (topMiss v) = true := by
    exact decide_eq_true ⟨a,b,edge,by simp [topMiss,av],by simp [topMiss,bv]⟩
  let e : X n := fun i => decide (i = v ∨ i = w)
  let z : X n := fun i => decide (i = w)
  have fe : edgeFun G e = true := decide_eq_true ⟨v,w,vw,by simp [e],by simp [e]⟩
  have fz : edgeFun G z = false := by
    apply decide_eq_false_iff_not.mpr
    rintro ⟨c,d,hcd,hc,hd⟩
    exact hcd.ne ((by simpa [z] using hc : c = w).trans (by simpa [z] using hd : d = w).symm)
  have cof : edgeFun G ∘ pinZero v = edgeFun (G.deleteIncidenceSet v) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq,SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · rintro ⟨i,j,ij,hi,hj⟩
      have iv : i ≠ v := fun eq => by simp [pinZero,eq] at hi
      have jv : j ≠ v := fun eq => by simp [pinZero,eq] at hj
      exact ⟨i,j,⟨ij,iv,jv⟩,by simpa [pinZero,iv] using hi,by simpa [pinZero,jv] using hj⟩
    · rintro ⟨i,j,⟨ij,iv,jv⟩,hi,hj⟩
      exact ⟨i,j,ij,by simpa [pinZero,iv] using hi,by simpa [pinZero,jv] using hj⟩
  have eq : G.edgeFinset.card - 1 = ((G.deleteIncidenceSet v).edgeFinset.card - 1) + 1 := by omega
  rw [eq]
  apply save_at (edgeFun G) v e z (pinZero v) _ _ _ top fe fz (cof.symm ▸ sub)
  · rintro _ ⟨i,rfl⟩
    by_cases iv : i = v
    · simpa [Function.comp_def,pinZero,iv] using (free_zero (B := inputs n))
    · simpa [Function.comp_def,pinZero,iv] using (atom (B := inputs n) ⟨i,rfl⟩)
  · intro x i h
    by_contra no
    have iv : i = v := by simpa [topMiss] using no
    simp [pinZero,iv] at h
  · intro i tv ei
    have iv : i ≠ v := by simpa [topMiss] using tv
    simpa [e,z,iv] using ei

theorem add_leaf {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n)
    (adj : G.Adj v w) (leaf : ∀ a, G.Adj v a → a = w)
    (dropV : Counts (G.deleteIncidenceSet v)) (dropW : Counts (G.deleteIncidenceSet w)) :
    Counts G := by
  refine ⟨or_leaf G v w adj leaf dropV.1,?_⟩
  obtain ⟨S,cv,lo⟩ := dropW.2
  refine ⟨insert w S,?_,?_⟩
  · intro a b ab
    by_cases aw : a = w
    · exact Or.inl (by simp [aw])
    by_cases bw : b = w
    · exact Or.inr (by simp [bw])
    exact (cv (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨ab,aw,bw⟩)).imp
      (fun h => Finset.mem_insert_of_mem h) (fun h => Finset.mem_insert_of_mem h)
  · have pay := leaf_step G v w adj leaf lo
    intro ops valid
    exact (Finset.card_insert_le _ _).trans (pay ops valid)

theorem peel_to_core {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (base : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H ≤ G → Leafless H → Counts H) :
    Counts G := by
  classical
  have work (k : Nat) : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H ≤ G → H.edgeFinset.card = k → Counts H := by
    induction k using Nat.strong_induction_on with
    | ind k rec =>
      intro H _ hg count
      by_cases last : Leafless H
      · exact base H hg last
      obtain ⟨v,w,adj,leaf⟩ := not_not.mp last
      apply add_leaf H v w adj leaf
      all_goals
        apply rec _ _ _ (le_trans (H.deleteIncidenceSet_le _) hg) rfl
        rw [H.card_edgeFinset_deleteIncidenceSet,← count]
      · have h := (H.degree_pos_iff_exists_adj v).mpr ⟨w,adj⟩
        have c := H.degree_le_card_edgeFinset v
        omega
      · have h := (H.degree_pos_iff_exists_adj w).mpr ⟨v,adj.symm⟩
        have c := H.degree_le_card_edgeFinset w
        omega
  exact work _ G le_rfl rfl

theorem forest_leaf {n : Nat} (G : SimpleGraph (Fin n)) (h : G.IsAcyclic)
    (a b : Fin n) (adj : G.Adj a b) : ¬ Leafless G := by
  let _ : Nonempty (Fin n) := ⟨a⟩
  obtain ⟨u,t,p,path,maximal⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have pathAB : (SimpleGraph.Walk.cons adj .nil).IsPath :=
    SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [adj.ne])
  have pos : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 1) (maximal a b _ pathAB)
  have nonempty : ¬p.Nil := by grind
  intro none
  apply none
  refine ⟨u,p.snd,p.adj_snd nonempty,?_⟩
  intro w uw
  apply h.eq_snd_of_adj_start path uw
  by_contra miss
  have bigger := maximal _ _ (p.cons uw.symm) (path.cons miss)
  simp at bigger

theorem forest_counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.IsAcyclic) : Counts G := by
  apply peel_to_core G
  intro H _ hg last
  have all (v w) : ¬ H.Adj v w := fun adj => forest_leaf H (h.anti hg) v w adj last
  have empty : H = ⊥ := SimpleGraph.eq_bot_iff_forall_not_adj.mpr all
  refine ⟨?_,∅,?_,lower_zero _⟩
  · have zero : H.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun he => H.edgeFinset_nonempty.mp he empty)
    have eq : H.edgeFinset.card - 1 = 0 := by simp [zero]
    rw [eq]
    exact lower_zero _
  · exact fun a b ab => (all a b ab).elim

theorem bound_of_counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (proof : Counts G)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (ao : IsAO2 n C)
    (h : circuitFun n C = edgeFun G) : ∃ S : Finset (Fin n),
    G.IsVertexCover (S : Set (Fin n)) ∧ G.edgeFinset.card + S.card ≤ C.size + 1 := by
  obtain ⟨orr,S,cv,andd⟩ := proof
  have ol := lower_circuit orr C ao h
  rw [← ordinary_eq] at h
  have al := and_lower_circuit _ ((cover_dual G).symm ▸ andd) C ao h
  rw [← ThetaAnd3241.subtract_or_eq_and C ao] at al
  change G.edgeFinset.card - 1 ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) at ol
  have le := List.countP_le_length (p := fun g => PEqualNP.SharedBlockCost.isOrOp g.op) (l := C.gates)
  change _ ≤ C.size at le
  exact ⟨S,cv,by omega⟩

end LeafCore3241

namespace ForestBipartite3241
open LeafCore3241 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

abbrev bip {n m : Nat} (E : Finset (Fin n × Fin m)) : SimpleGraph (Fin (n+m)) :=
  SimpleGraph.fromRel fun a b => ∃ e ∈ E, a = Fin.castAdd m e.1 ∧ b = Fin.natAdd n e.2

theorem sides {n m : Nat} (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
  intro eq
  have h := congrArg Fin.val eq
  change a.val = n + b.val at h
  omega

def pair {n m : Nat} (e : Fin n × Fin m) : Sym2 (Fin (n+m)) :=
  s(Fin.castAdd m e.1,Fin.natAdd n e.2)

theorem injective_pair {n m : Nat} : Function.Injective (pair (n := n) (m := m)) := by
  intro e f eq
  rcases Sym2.eq_iff.mp eq with ⟨a,b⟩ | ⟨a,_⟩
  · exact Prod.ext (Fin.castAdd_injective n m a) (Fin.ext (by
      have h := congrArg Fin.val b
      change n + e.2.val = n + f.2.val at h
      omega))
  · exact (sides _ _ a).elim

theorem bip_adjacency {n m : Nat} {E : Finset (Fin n × Fin m)} {e : Fin n × Fin m} (he : e ∈ E) :
    (bip E).Adj (Fin.castAdd m e.1) (Fin.natAdd n e.2) :=
  ⟨sides _ _,Or.inl ⟨e,he,rfl,rfl⟩⟩

theorem bip_edges {n m : Nat} (E : Finset (Fin n × Fin m)) [DecidableRel (bip E).Adj] :
    (bip E).edgeFinset.card = E.card := by
  have eq : (bip E).edgeFinset = E.image pair := by
    ext t
    induction t using Sym2.inductionOn with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
        · exact Finset.mem_image.mpr ⟨e,he,rfl⟩
        · exact Finset.mem_image.mpr ⟨e,he,Sym2.eq_swap⟩
      · intro h
        obtain ⟨e,he,eq⟩ := Finset.mem_image.mp h
        rcases Sym2.eq_iff.mp eq with ⟨a,b⟩ | ⟨a,b⟩
        · exact a ▸ b ▸ bip_adjacency he
        · exact a ▸ b ▸ (bip_adjacency he).symm
  rw [eq,Finset.card_image_of_injective _ injective_pair]

theorem formula {n m : Nat} (E : Finset (Fin n × Fin m)) [DecidableRel (bip E).Adj]
    (x : Fin (n+m) → Bool) : edgeFun (bip E) x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [edgeFun,decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩,ha,hb⟩
    · exact ⟨e,he,ha,hb⟩
    · exact ⟨e,he,hb,ha⟩
  · rintro ⟨e,he,l,r⟩
    exact ⟨_,_,bip_adjacency he,l,r⟩

end ForestBipartite3241

namespace CoreTransfer3241
open ThetaPin3241 LeafAnd3241 LeafCore3241

theorem padded {m n : Nat} (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (f : Fin m → Fin n) (inj : Function.Injective f)
    (adj : ∀ i j, H.Adj i j ↔ ∃ u v, G.Adj u v ∧ f u = i ∧ f v = j)
    (src : Counts G) : Counts H := by
  classical
  let p : X m → X n := fun x => Function.extend f x (fun _ => false)
  have put (x : X m) (i : Fin m) : p x (f i) = x i := inj.extend_apply x _ i
  have raw : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p) := by
    rintro _ ⟨i,rfl⟩
    by_cases mem : ∃ t, f t = i
    · obtain ⟨t,rfl⟩ := mem
      have eq : (fun (x : X n) => x (f t)) ∘ p = (fun (x : X m) => x t) := funext (fun x => put x t)
      exact eq ▸ atom ⟨t,rfl⟩
    · have eq : (fun (x : X n) => x i) ∘ p = (fun _ => false) :=
        funext (fun x => Function.extend_apply' x (fun _ => false) i mem)
      exact eq ▸ free_zero
  have spec (u v : Fin m) (uv : G.Adj u v) : H.Adj (f u) (f v) := (adj _ _).mpr ⟨u,v,uv,rfl,rfl⟩
  have edge : edgeFun H ∘ p = edgeFun G := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq]
    constructor
    · rintro ⟨i,j,ij,yes,also⟩
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj _ _).mp ij
      exact ⟨u,v,uv,(put x u).symm.trans yes,(put x v).symm.trans also⟩
    · rintro ⟨u,v,uv,yes,also⟩
      exact ⟨_,_,spec u v uv,(put x u).trans yes,(put x v).trans also⟩
  have covers : cover H ∘ p = cover G := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq]
    constructor
    · intro ok u v uv
      simpa only [put] using ok _ _ (spec u v uv)
    · intro ok i j ij
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj _ _).mp ij
      simpa only [put] using ok _ _ uv
  have subset : H.edgeFinset ⊆ G.edgeFinset.image (Sym2.map f) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ i j =>
      intro he
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj i j).mp (H.mem_edgeFinset.mp he)
      exact Finset.mem_image.mpr ⟨s(u,v),G.mem_edgeFinset.mpr uv,rfl⟩
  have count := (Finset.card_le_card subset).trans Finset.card_image_le
  obtain ⟨ors,S,cv,ands⟩ := src
  refine ⟨?_,S.image f,?_,?_⟩
  · have lo : Lower (edgeFun H) (G.edgeFinset.card - 1) := lower_transport p raw (edge.symm ▸ ors)
    exact fun gs ok => (Nat.sub_le_sub_right count 1).trans (lo gs ok)
  · intro i j ij
    obtain ⟨u,v,uv,rfl,rfl⟩ := (adj i j).mp ij
    exact (cv uv).imp (fun hu => Finset.mem_image_of_mem _ hu) (fun hv => Finset.mem_image_of_mem _ hv)
  · rw [Finset.card_image_of_injective _ inj]
    exact lower_transport p raw (covers.symm ▸ ands)

theorem pass_of_choices {n : Nat} (gs : List (ThetaPin3241.Gate (X n))) (B : Set (Signal (X n)))
    (f : Signal (X n)) (x y z : X n) (base : ∀ a ∈ B, Pass x y z a)
    (agree : ∀ g ∈ gs, g.1 x = g.1 y) (ok : Valid B gs f) : Pass x y z f := by
  induction gs generalizing B with
  | nil => exact free_pass base ok
  | cons g gs ih =>
    obtain ⟨fa,fb,tail⟩ := ok
    have pass_a := free_pass base fa
    have pass_b := free_pass base fb
    have pass_g : Pass x y z (join g.1 g.2) := by
      have eq := agree g List.mem_cons_self
      intro gx gy
      cases ax : g.1 x with
      | true =>
        have az := pass_a ax (eq.symm.trans ax)
        simp [join,az]
      | false =>
        have ay := eq.symm.trans ax
        have bz := pass_b (by simpa [join,ax] using gx) (by simpa [join,ay] using gy)
        simp [join,bz]
    refine ih (insert (join g.1 g.2) B) ?_ ?_ tail
    · intro a ha
      exact (Set.mem_insert_iff.mp ha).elim (fun eq => eq ▸ pass_g) (base a)
    · exact fun g hg => agree g (List.mem_cons_of_mem _ hg)

theorem separated_rows {n k r : Nat} (f : Signal (X n)) (rows : Fin r → X n)
    (yes : ∀ i, f (rows i) = true)
    (off : ∀ i j, i ≠ j → f (fun v => rows i v && rows j v) = false)
    (many : 2^(k-1) < r) : Lower f k := by
  intro gs ok
  let key (i : Fin r) (g : Fin gs.length) := (gs.get g).1 (rows i)
  have distinguish : Function.Injective key := by
    intro i j eq
    by_contra ne
    have agree (g) (hg : g ∈ gs) : g.1 (rows i) = g.1 (rows j) := by
      obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hg
      exact congrFun eq t
    have pass := pass_of_choices gs (inputs n) f (rows i) (rows j) (fun v => rows i v && rows j v)
      (pass_inputs _ _ _ (fun v a b => by simp [a,b])) agree ok
    have both := pass (yes i) (yes j)
    simp [off i j ne] at both
  have count := Fintype.card_le_of_injective key distinguish
  simp only [Fintype.card_fin,Fintype.card_fun,Fintype.card_bool] at count
  by_contra bad
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) (show gs.length ≤ k-1 by omega)
  omega

end CoreTransfer3241

namespace SmallCores3241
open ThetaPin3241 LeafAnd3241 LeafCore3241 CoreTransfer3241
open ThetaCores3241 Theta244Cores ThetaClass3241

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def path8 (x : LeafAnd3241.X 8) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem path8_lower (rec : Lower path7 5) : Lower path8 6 := by
  have eq : path8 ∘ pin (7 : Fin 8) = path7 := by
    funext x
    exact (by decide +kernel : ∀ y, path8 (pin (7 : Fin 8) y) = path7 y) x
  apply lower_one_step path8 7 (row 192) (row 64)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def path9 (x : LeafAnd3241.X 9) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem path9_lower (rec : Lower path8 6) : Lower path9 7 := by
  have eq : path9 ∘ pin (8 : Fin 9) = path8 := by
    funext x
    exact (by decide +kernel : ∀ y, path9 (pin (8 : Fin 9) y) = path8 y) x
  apply lower_one_step path9 8 (row 384) (row 128)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def cycle10 (x : LeafAnd3241.X 10) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def cycleRename : Fin 10 → Fin 9 → Fin 9 := ![![0,1,2,3,4,5,6,7,8],![8,0,1,2,3,4,5,6,7],![7,8,0,1,2,3,4,5,6],![6,7,8,0,1,2,3,4,5],![5,6,7,8,0,1,2,3,4],![4,5,6,7,8,0,1,2,3],![3,4,5,6,7,8,0,1,2],![2,3,4,5,6,7,8,0,1],![1,2,3,4,5,6,7,8,0],![0,1,2,3,4,5,6,7,8]]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_deleted (v : Fin 10) : Lower (cycle10 ∘ pin v) 7 := by
  have all : ∀ i x, (cycle10 ∘ pin i) (x ∘ cycleRename i) = path9 x := by decide +kernel
  apply lower_rename (cycleRename v)
  have eq : (fun x => (cycle10 ∘ pin v) (x ∘ cycleRename v)) = path9 := funext (all v)
  exact eq.symm ▸ path9_lower (path8_lower (path7_lower (path6_lower path5_lower)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_geometry : Geometry ∅ cycle10 := by constructor <;> decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_lower : Lower cycle10 9 := by
  apply lower_two_step cycle10 Set.univ (pool ∅) (base_subset _)
  · exact nonfree cycle10 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle10_geometry g a b (fun v _ => h v (Set.mem_univ v))
  · exact fun v _ => cycle10_deleted v

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev graph (n : Nat) (edges : List (Nat × Nat)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun (i j : Fin n) => (i.val,j.val) ∈ edges)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev six := graph 6 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def sixRows : Fin 5 → Nat := ![21,27,42,45,54]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem sixCounts : Counts six := by
  have eq : edgeFun six = cycle6 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun six y = cycle6 y) x
  have card : six.edgeFinset.card - 1 = 5 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle6_of_classifier ThetaClass3241.cycle_classifier
  · let S : Finset (Fin 6) := {0,2,4}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, six.Adj a b → a ∈ ({0,2,4} : Finset (Fin 6)) ∨ b ∈ ({0,2,4} : Finset (Fin 6)))
    have sc : S.card = 3 := by decide +kernel
    have dualEq : cover six = dual cycle6 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle6) (fun i => row (sixRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev eight := graph 8 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def eightRows : Fin 9 → Nat := ![85,91,107,109,170,173,181,182,214]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem eightCounts : Counts eight := by
  have eq : edgeFun eight = cycle8 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun eight y = cycle8 y) x
  have card : eight.edgeFinset.card - 1 = 7 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle8_of_classifier Theta244Finish.cycle_classifier
  · let S : Finset (Fin 8) := {0,2,4,6}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, eight.Adj a b → a ∈ ({0,2,4,6} : Finset (Fin 8)) ∨ b ∈ ({0,2,4,6} : Finset (Fin 8)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover eight = dual cycle8 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle8) (fun i => row (eightRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev ten := graph 10 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def tenRows : Fin 17 → Nat := ![341,347,363,365,427,429,437,682,685,693,694,725,726,730,854,858,874]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem tenCounts : Counts ten := by
  have eq : edgeFun ten = cycle10 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun ten y = cycle10 y) x
  have card : ten.edgeFinset.card - 1 = 9 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle10_lower
  · let S : Finset (Fin 10) := {0,2,4,6,8}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, ten.Adj a b → a ∈ ({0,2,4,6,8} : Finset (Fin 10)) ∨ b ∈ ({0,2,4,6,8} : Finset (Fin 10)))
    have sc : S.card = 5 := by decide +kernel
    have dualEq : cover ten = dual cycle10 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle10) (fun i => row (tenRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev threeThreeThree := graph 8 [(0,5),(0,6),(0,7),(1,4),(1,7),(2,4),(2,6),(3,4),(3,5)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def threeThreeThreeRows : Fin 9 → Nat := ![15,55,91,115,157,181,217,238,240]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem threeThreeThreeCounts : Counts threeThreeThree := by
  have eq : edgeFun threeThreeThree = ThetaAnd3241.theta := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun threeThreeThree y = ThetaAnd3241.theta y) x
  have card : threeThreeThree.edgeFinset.card - 1 = 8 := by decide +kernel
  constructor
  · rw [eq,card]
    exact theta_of_classifiers ThetaClass3241.cycle_classifier theta_classifier
  · let S : Finset (Fin 8) := {0,1,2,3}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, threeThreeThree.Adj a b → a ∈ ({0,1,2,3} : Finset (Fin 8)) ∨ b ∈ ({0,1,2,3} : Finset (Fin 8)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover threeThreeThree = dual ThetaAnd3241.theta := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual ThetaAnd3241.theta) (fun i => row (threeThreeThreeRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev twoFourFour := graph 9 [(0,2),(1,2),(0,3),(3,4),(4,5),(1,5),(0,6),(6,7),(7,8),(1,8)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def twoFourFourRows : Fin 9 → Nat := ![147,171,222,238,339,350,363,364,373]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem twoFourFourCounts (extra : Lower Theta244Cores.theta 9) : Counts twoFourFour := by
  have eq : edgeFun twoFourFour = Theta244Cores.theta := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun twoFourFour y = Theta244Cores.theta y) x
  have card : twoFourFour.edgeFinset.card - 1 = 9 := by decide +kernel
  constructor
  · rw [eq,card]
    exact extra
  · let S : Finset (Fin 9) := {0,1,4,7}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, twoFourFour.Adj a b → a ∈ ({0,1,4,7} : Finset (Fin 9)) ∨ b ∈ ({0,1,4,7} : Finset (Fin 9)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover twoFourFour = dual Theta244Cores.theta := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual Theta244Cores.theta) (fun i => row (twoFourFourRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

end SmallCores3241

namespace GraphPacking3241
open ThetaPin3241 LeafAnd3241 LeafCore3241 ForestBipartite3241

abbrev Matrix (n m : Nat) := Finset (Fin n × Fin m)
abbrev Left {n m : Nat} (a : Fin n) := Fin.castAdd m a
abbrev Right {n m : Nat} (b : Fin m) := Fin.natAdd n b

def FourFree {n m : Nat} (E : Matrix n m) : Prop :=
  ∀ p q l s, p ≠ q → l ≠ s → ¬((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)

def HasPartners {n m : Nat} (E : Matrix n m) : Prop :=
  ∀ a b, (a,b) ∈ E →
    (∃ c, c ≠ b ∧ (a,c) ∈ E) ∧ (∃ d, d ≠ a ∧ (d,b) ∈ E)

theorem adj_left {n m : Nat} (E : Matrix n m) (a : Fin n) (j : Fin (n+m)) :
    (bip E).Adj (Left a) j ↔ ∃ b, (a,b) ∈ E ∧ j = Right b := by
  constructor
  · rintro ⟨_,⟨e,he,eq,rfl⟩ | ⟨e,_,_,eq⟩⟩
    · have ea : a = e.1 := Fin.castAdd_injective n m eq
      exact ⟨e.2,ea ▸ he,rfl⟩
    · exact (sides _ _ eq).elim
  · rintro ⟨b,h,rfl⟩
    exact bip_adjacency h

theorem adj_right {n m : Nat} (E : Matrix n m) (b : Fin m) (i : Fin (n+m)) :
    (bip E).Adj (Right b) i ↔ ∃ a, (a,b) ∈ E ∧ i = Left a := by
  constructor
  · rintro ⟨_,⟨e,_,eq,_⟩ | ⟨e,he,rfl,eq⟩⟩
    · exact (sides _ _ eq.symm).elim
    · have eb : b = e.2 := Fin.natAdd_injective m n eq
      exact ⟨e.1,eb ▸ he,rfl⟩
  · rintro ⟨a,h,rfl⟩
    exact (bip_adjacency h).symm

theorem leafless_iff {n m : Nat} (E : Matrix n m) : Leafless (bip E) ↔ HasPartners E := by
  classical
  constructor
  · intro no a b ab
    constructor
    · by_contra! bad
      apply no
      refine ⟨Left a,Right b,bip_adjacency ab,?_⟩
      intro i hi
      obtain ⟨c,hc,rfl⟩ := (adj_left E a i).mp hi
      have cb : c = b := by_contra (fun ne => bad c ne hc)
      rw [cb]
    · by_contra! bad
      apply no
      refine ⟨Right b,Left a,(bip_adjacency ab).symm,?_⟩
      intro i hi
      obtain ⟨d,hd,rfl⟩ := (adj_right E b i).mp hi
      have da : d = a := by_contra (fun ne => bad d ne hd)
      rw [da]
  · rintro partners ⟨i,j,ij,leaf⟩
    rcases ij with ⟨_,⟨⟨a,b⟩,h,rfl,rfl⟩ | ⟨⟨a,b⟩,h,rfl,rfl⟩⟩
    · obtain ⟨c,ne,hc⟩ := (partners a b h).1
      exact ne (Fin.natAdd_injective m n (leaf _ (bip_adjacency hc)))
    · obtain ⟨d,ne,hd⟩ := (partners a b h).2
      exact ne (Fin.castAdd_injective n m (leaf _ (bip_adjacency hd).symm))

theorem side_count {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (two : ∀ a b, (a,b) ∈ E → ∃ c, c ≠ b ∧ (a,c) ∈ E) :
    (E.image Prod.fst).card * 2 ≤ E.card := by
  classical
  let P := E.image Prod.fst
  have picks (p : P) : ∃ b c, b ≠ c ∧ (p.val,b) ∈ E ∧ (p.val,c) ∈ E := by
    obtain ⟨⟨a,b⟩,ab,e⟩ := Finset.mem_image.mp p.property
    change a = p.val at e
    obtain ⟨c,ne,ac⟩ := two a b ab
    exact ⟨b,c,ne.symm,e ▸ ab,e ▸ ac⟩
  choose first second diff one two using picks
  let edge (p : P) (b : Bool) : E := if b then ⟨(p.val,first p),one p⟩ else ⟨(p.val,second p),two p⟩
  have inj : Function.Injective (fun x : P × Bool => edge x.1 x.2) := by
    rintro ⟨p,i⟩ ⟨q,j⟩ eq
    have row (r : P) (b : Bool) : (edge r b).val.1 = r.val := by cases b <;> rfl
    have pe : p = q := Subtype.ext ((row p i).symm.trans ((congrArg (fun t : E => t.val.1) eq).trans (row q j)))
    subst q
    cases i <;> cases j
    · rfl
    · exact ((diff p).symm (congrArg (fun t : E => t.val.2) eq)).elim
    · exact (diff p (congrArg (fun t : E => t.val.2) eq)).elim
    · rfl
  have bound := Fintype.card_le_of_injective _ inj
  simpa [P] using bound

theorem both_sides {n m : Nat} (E : Matrix n m) (partners : HasPartners E) (small : E.card ≤ 10) :
    (E.image Prod.fst).card ≤ 5 ∧ (E.image Prod.snd).card ≤ 5 := by
  have left := side_count E (fun a b ab => (partners a b ab).1)
  have flip {a : Fin n} {b : Fin m} : (b,a) ∈ E.image Prod.swap ↔ (a,b) ∈ E := by
    constructor
    · rintro h
      obtain ⟨⟨p,q⟩,pq,eq⟩ := Finset.mem_image.mp h
      cases eq
      exact pq
    · exact fun h => Finset.mem_image_of_mem Prod.swap h
  have right := side_count (E.image Prod.swap) (fun b a ba => by
    obtain ⟨d,ne,db⟩ := (partners a b (flip.mp ba)).2
    exact ⟨d,ne,flip.mpr db⟩)
  rw [Finset.image_image,Finset.card_image_of_injective _ Prod.swap_injective] at right
  change (E.image Prod.snd).card * 2 ≤ E.card at right
  omega

theorem from_index {n k : Nat} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin k))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (lab : Fin n → Option (Fin k))
    (unique : ∀ i j a, lab i = some a → lab j = some a → i = j)
    (forward : ∀ i j, G.Adj i j → ∃ a b, lab i = some a ∧ lab j = some b ∧ H.Adj a b)
    (back : ∀ a b, H.Adj a b → ∃ i j, lab i = some a ∧ lab j = some b ∧ G.Adj i j)
    (size : G.edgeFinset.card ≤ H.edgeFinset.card) (h : Counts H) : Counts G := by
  classical
  let p : X k → X n := fun x i => (lab i).elim false x
  have read (x : X k) (i a) (hi : lab i = some a) : p x i = x a := by simp [p,hi]
  have raw : ∀ t ∈ inputs n, Free (inputs k) (t ∘ p) := by
    rintro _ ⟨i,rfl⟩
    cases hi : lab i with
    | none => simpa [Function.comp_def,p,hi] using (free_zero (B := inputs k))
    | some a => simpa [Function.comp_def,p,hi] using (atom (B := inputs k) ⟨a,rfl⟩)
  have edge : edgeFun G ∘ p = edgeFun H := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq]
    constructor
    · rintro ⟨i,j,ij,pi,pj⟩
      obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
      exact ⟨a,b,ab,(read x i a li).symm.trans pi,(read x j b lj).symm.trans pj⟩
    · rintro ⟨a,b,ab,pa,pb⟩
      obtain ⟨i,j,li,lj,ij⟩ := back a b ab
      exact ⟨i,j,ij,(read x i a li).trans pa,(read x j b lj).trans pb⟩
  have cover_eq : cover G ∘ p = cover H := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq]
    constructor
    · intro ok a b ab
      obtain ⟨i,j,li,lj,ij⟩ := back a b ab
      simpa only [read x i a li,read x j b lj] using ok i j ij
    · intro ok i j ij
      obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
      simpa only [read x i a li,read x j b lj] using ok a b ab
  obtain ⟨ors,S,cv,ands⟩ := h
  let T := Finset.univ.filter fun i => ∃ a ∈ S, lab i = some a
  have lift (i : T) : ∃ a : S, lab i.val = some a.val := by
    obtain ⟨a,ha,eq⟩ := (Finset.mem_filter.mp i.property).2
    exact ⟨⟨a,ha⟩,eq⟩
  choose assign spec using lift
  have inj : Function.Injective assign := fun i j eq =>
    Subtype.ext (unique _ _ _ (spec i) (eq ▸ spec j))
  have card : T.card ≤ S.card := by simpa using Fintype.card_le_of_injective _ inj
  refine ⟨?_,T,?_,?_⟩
  · have bound : Lower (edgeFun G) (H.edgeFinset.card-1) := lower_transport p raw (edge.symm ▸ ors)
    exact fun gs val => (Nat.sub_le_sub_right size 1).trans (bound gs val)
  · intro i j ij
    obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
    exact (cv ab).imp (fun mem => Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,mem,li⟩)
      (fun mem => Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,mem,lj⟩)
  · have bound : Lower (cover G) S.card := lower_transport p raw (cover_eq.symm ▸ ands)
    exact fun gs val => card.trans (bound gs val)

end GraphPacking3241

namespace MatrixPacking3241
open GraphPacking3241 LeafCore3241 ForestBipartite3241

def optional {α β : Type} [DecidableEq α] (P : Finset α) (f : P → β) (i : α) : Option β :=
  if h : i ∈ P then some (f ⟨i,h⟩) else none

theorem optional_unique {α β : Type} [DecidableEq α] (P : Finset α) (f : P → β)
    (inj : Function.Injective f) (i j : α) (a : β) (hi : optional P f i = some a)
    (hj : optional P f j = some a) : i = j := by
  unfold optional at hi hj
  split at hi <;> rename_i pi
  · split at hj <;> rename_i pj
    · exact congrArg Subtype.val (inj ((Option.some.inj hi).trans (Option.some.inj hj).symm))
    · contradiction
  · contradiction

def combine {n m : Nat} (r : Fin n → Option (Fin 5)) (c : Fin m → Option (Fin 5)) :
    Fin (n+m) → Option (Fin 10) :=
  Fin.addCases (fun a => (r a).map (Fin.castAdd 5)) (fun b => (c b).map (Fin.natAdd 5))

theorem combined_unique {n m : Nat} (r : Fin n → Option (Fin 5)) (c : Fin m → Option (Fin 5))
    (ri : ∀ i j a, r i = some a → r j = some a → i = j)
    (ci : ∀ i j b, c i = some b → c j = some b → i = j) :
    ∀ i j t, combine r c i = some t → combine r c j = some t → i = j := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
    intro j <;> refine Fin.addCases (fun u => ?_) (fun v => ?_) j <;>
    intro t hi hj <;> simp only [combine,Fin.addCases_left,Fin.addCases_right,Option.map_eq_some_iff] at hi hj <;>
    obtain ⟨x,hx,rfl⟩ := hi <;> obtain ⟨y,hy,eq⟩ := hj
  · obtain rfl : y = x := Fin.castAdd_injective 5 5 eq
    exact congrArg _ (ri _ _ _ hx hy)
  · exact (sides x y eq.symm).elim
  · exact (sides y x eq).elim
  · obtain rfl : y = x := Fin.natAdd_injective 5 5 eq
    exact congrArg _ (ci _ _ _ hx hy)

abbrev Rows {n m} (E : Matrix n m) := E.image Prod.fst
abbrev Cols {n m} (E : Matrix n m) := E.image Prod.snd
def erow {n m} {E : Matrix n m} (e : E) : Rows E := ⟨e.val.1,Finset.mem_image_of_mem _ e.property⟩
def ecol {n m} {E : Matrix n m} (e : E) : Cols E := ⟨e.val.2,Finset.mem_image_of_mem _ e.property⟩

def pack {n m} (E : Matrix n m) (r : Rows E → Fin 5) (c : Cols E → Fin 5) : Matrix 5 5 :=
  E.attach.image (fun e => (r (erow e),c (ecol e)))

theorem decode {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5} {a b} :
    (a,b) ∈ pack E r c ↔ ∃ e : E, r (erow e) = a ∧ c (ecol e) = b := by
  simp [pack]

theorem rows_eq {n m} {E : Matrix n m} {r : Rows E → Fin 5} (inj : Function.Injective r) (e f : E) :
    r (erow e) = r (erow f) ↔ e.val.1 = f.val.1 := ⟨fun h => congrArg Subtype.val (inj h),
      fun h => congrArg r (Subtype.ext h)⟩

theorem cols_eq {n m} {E : Matrix n m} {c : Cols E → Fin 5} (inj : Function.Injective c) (e f : E) :
    c (ecol e) = c (ecol f) ↔ e.val.2 = f.val.2 := ⟨fun h => congrArg Subtype.val (inj h),
      fun h => congrArg c (Subtype.ext h)⟩

theorem pack_card {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) : (pack E r c).card = E.card := by
  unfold pack
  rw [Finset.card_image_of_injective,Finset.card_attach]
  intro e f eq
  exact Subtype.ext (Prod.ext ((rows_eq ri _ _).mp (congrArg Prod.fst eq))
    ((cols_eq ci _ _).mp (congrArg Prod.snd eq)))

theorem pack_free {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) (free : FourFree E) :
    FourFree (pack E r c) := by
  intro p q l s pq ls h
  obtain ⟨a,ap,al⟩ := decode.mp h.1
  obtain ⟨b,bp,bs⟩ := decode.mp h.2.1
  obtain ⟨d,dq,dl⟩ := decode.mp h.2.2.1
  obtain ⟨e,eq,es⟩ := decode.mp h.2.2.2
  have ab := (rows_eq ri a b).mp (ap.trans bp.symm)
  have de := (rows_eq ri d e).mp (dq.trans eq.symm)
  have ad := (cols_eq ci a d).mp (al.trans dl.symm)
  have be := (cols_eq ci b e).mp (bs.trans es.symm)
  have pr : a.val.1 ≠ d.val.1 := fun hh => pq (ap.symm.trans (((rows_eq ri a d).mpr hh).trans dq))
  have lc : a.val.2 ≠ b.val.2 := fun hh => ls (al.symm.trans (((cols_eq ci a b).mpr hh).trans bs))
  apply free _ _ _ _ pr lc
  exact ⟨a.property,ab ▸ b.property,ad ▸ d.property,de ▸ be ▸ e.property⟩

theorem pack_partners {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) (has : HasPartners E) :
    HasPartners (pack E r c) := by
  intro a b ab
  obtain ⟨e,rfl,rfl⟩ := decode.mp ab
  obtain ⟨⟨v,ne,ev⟩,⟨u,diff,ue⟩⟩ := has _ _ e.property
  let f : E := ⟨(e.val.1,v),ev⟩
  let g : E := ⟨(u,e.val.2),ue⟩
  exact ⟨⟨c (ecol f),fun eq => ne ((cols_eq ci f e).mp eq),
      decode.mpr ⟨f,(rows_eq ri f e).mpr rfl,rfl⟩⟩,
    ⟨r (erow g),fun eq => diff ((rows_eq ri g e).mp eq),
      decode.mpr ⟨g,rfl,(cols_eq ci g e).mpr rfl⟩⟩⟩

theorem unpack_counts {n m} (E : Matrix n m) (r : Rows E → Fin 5) (c : Cols E → Fin 5)
    (ri : Function.Injective r) (ci : Function.Injective c)
    (src : Counts (bip (pack E r c))) : Counts (bip E) := by
  let lab := combine (optional (Rows E) r) (optional (Cols E) c)
  have l (e : E) : lab (Left e.val.1) = some (Fin.castAdd 5 (r (erow e))) := by
    simp only [lab,combine,Left,Fin.addCases_left,optional]
    split
    · rfl
    · rename_i missing
      exact (missing (erow e).property).elim
  have rr (e : E) : lab (Right e.val.2) = some (Fin.natAdd 5 (c (ecol e))) := by
    simp only [lab,combine,Right,Fin.addCases_right,optional]
    split
    · rfl
    · rename_i missing
      exact (missing (ecol e).property).elim
  apply from_index (bip E) (bip (pack E r c)) lab
    (combined_unique _ _ (optional_unique _ _ ri) (optional_unique _ _ ci)) _ _ _ src
  · rintro i j ⟨_,⟨p,h,rfl,rfl⟩ | ⟨p,h,rfl,rfl⟩⟩
    · let e : E := ⟨p,h⟩
      exact ⟨_,_,l e,rr e,bip_adjacency (decode.mpr ⟨e,rfl,rfl⟩)⟩
    · let e : E := ⟨p,h⟩
      exact ⟨_,_,rr e,l e,(bip_adjacency (decode.mpr ⟨e,rfl,rfl⟩)).symm⟩
  · rintro i j ⟨_,⟨⟨a,b⟩,h,rfl,rfl⟩ | ⟨⟨a,b⟩,h,rfl,rfl⟩⟩
    · obtain ⟨e,rfl,rfl⟩ := decode.mp h
      exact ⟨_,_,l e,rr e,bip_adjacency e.property⟩
    · obtain ⟨e,rfl,rfl⟩ := decode.mp h
      exact ⟨_,_,rr e,l e,(bip_adjacency e.property).symm⟩
  · rw [bip_edges,bip_edges,pack_card ri ci]

def Census : Prop := ∀ E : Matrix 5 5, E.card ≤ 10 → FourFree E → Leafless (bip E) → Counts (bip E)

theorem compressed {n m} (E : Matrix n m) (free : FourFree E) (size : E.card ≤ 10)
    (last : Leafless (bip E)) (census : Census) : Counts (bip E) := by
  let h := (leafless_iff E).mp last
  obtain ⟨pr,pc⟩ := both_sides E h size
  let r (p : Rows E) := Fin.castLE pr (((Rows E).orderIsoOfFin rfl).symm p)
  let c (p : Cols E) := Fin.castLE pc (((Cols E).orderIsoOfFin rfl).symm p)
  have ri : Function.Injective r := (Fin.castLE_injective pr).comp ((Rows E).orderIsoOfFin rfl).symm.injective
  have ci : Function.Injective c := (Fin.castLE_injective pc).comp ((Cols E).orderIsoOfFin rfl).symm.injective
  apply unpack_counts E r c ri ci
  apply census
  · simpa [pack_card ri ci] using size
  · exact pack_free ri ci free
  · exact (leafless_iff _).mpr (pack_partners ri ci h)

end MatrixPacking3241

namespace CoreCensus
open LeafCore3241 SmallCores3241 ForestBipartite3241

inductive Shape | six | eight | ten | theta333 | theta244 deriving DecidableEq, Repr

abbrev order : Shape → Nat
  | .six => 6 | .eight => 8 | .ten => 10 | .theta333 => 8 | .theta244 => 9

instance (s : Shape) : NeZero (order s) := by cases s <;> exact ⟨by decide⟩

def edges : Shape → List (Nat × Nat)
  | .six => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]
  | .eight => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]
  | .ten => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,0)]
  | .theta333 => [(0,5),(0,6),(0,7),(1,4),(1,7),(2,4),(2,6),(3,4),(3,5)]
  | .theta244 => [(0,2),(1,2),(0,3),(3,4),(4,5),(1,5),(0,6),(6,7),(7,8),(1,8)]

abbrev source (s : Shape) := graph (order s) (edges s)

theorem counts_source (s) (h : ThetaPin3241.Lower Theta244Cores.theta 9) : Counts (source s) := by
  cases s
  · exact sixCounts
  · exact eightCounts
  · exact tenCounts
  · exact threeThreeThreeCounts
  · exact twoFourFourCounts h

def pairs (rows : List Nat) : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter fun (i,j) => (rows.getD i.val 0).testBit j.val

def matrix (rows : List Nat) := bip (pairs rows)

instance (rows : List Nat) : DecidableRel (matrix rows).Adj := by unfold matrix bip; infer_instance

structure Item where
  rows : List Nat
  shape : Shape
  forward : List Nat
  backward : List Nat
  deriving Repr

def emb (r : Item) (i : Fin (order r.shape)) : Fin 10 := Fin.ofNat 10 (r.forward.getD i.val 0)
def inv (r : Item) (i : Fin 10) : Fin (order r.shape) := Fin.ofNat (order r.shape) (r.backward.getD i.val 0)

def Certified (r : Item) : Prop :=
  (∀ u, inv r (emb r u) = u) ∧ ∀ i j, (matrix r.rows).Adj i j ↔
     emb r (inv r i) = i ∧ emb r (inv r j) = j ∧ (source r.shape).Adj (inv r i) (inv r j)

instance (r : Item) : Decidable (Certified r) := by unfold Certified; infer_instance

theorem count_item (r : Item) (hc : Certified r) (h : ThetaPin3241.Lower Theta244Cores.theta 9) :
    Counts (matrix r.rows) := by
  apply CoreTransfer3241.padded (source r.shape) (matrix r.rows) (emb r) (Function.LeftInverse.injective hc.1) _ (counts_source _ h)
  intro i j
  constructor
  · intro a
    obtain ⟨hi,hj,adj⟩ := (hc.2 i j).mp a
    exact ⟨_,_,adj,hi,hj⟩
  · rintro ⟨u,v,a,rfl,rfl⟩
    apply (hc.2 _ _).mpr
    rw [hc.1 u,hc.1 v]
    exact ⟨rfl,rfl,a⟩

end CoreCensus

namespace CoreCensus

def batch0 : List Item := [
  ⟨[3, 5, 6],.six,[1, 5, 0, 6, 2, 7],[2, 0, 4, 0, 0, 1, 3, 5, 0, 0]⟩,
  ⟨[3, 5, 6, 9, 10],.theta244,[5, 6, 0, 1, 7, 2, 3, 8, 4],[2, 3, 5, 6, 8, 0, 1, 4, 7, 0]⟩,
  ⟨[3, 5, 6, 9, 12],.theta244,[5, 7, 1, 0, 6, 2, 3, 8, 4],[3, 2, 5, 6, 8, 0, 4, 1, 7, 0]⟩,
  ⟨[3, 5, 6, 10, 12],.theta244,[6, 7, 2, 0, 5, 1, 3, 8, 4],[3, 5, 2, 6, 8, 4, 0, 1, 7, 0]⟩,
  ⟨[3, 5, 6, 17, 18],.theta244,[5, 6, 0, 1, 7, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 1, 4, 0, 7]⟩,
  ⟨[3, 5, 6, 17, 20],.theta244,[5, 7, 1, 0, 6, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 4, 1, 0, 7]⟩]

def batch1 : List Item := [
  ⟨[3, 5, 6, 18, 20],.theta244,[6, 7, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 1, 0, 7]⟩,
  ⟨[3, 5, 9, 10, 12],.theta244,[5, 8, 2, 0, 6, 3, 1, 7, 4],[3, 6, 2, 5, 8, 0, 4, 7, 1, 0]⟩,
  ⟨[3, 5, 9, 14],.theta333,[3, 2, 1, 0, 5, 6, 7, 8],[3, 2, 1, 0, 0, 4, 5, 6, 7, 0]⟩,
  ⟨[3, 5, 10, 12],.eight,[1, 5, 0, 6, 2, 8, 3, 7],[2, 0, 4, 6, 0, 1, 3, 7, 5, 0]⟩,
  ⟨[3, 5, 10, 20, 24],.ten,[1, 5, 0, 6, 2, 8, 4, 9, 3, 7],[2, 0, 4, 8, 6, 1, 3, 9, 5, 7]⟩,
  ⟨[3, 5, 12, 18, 24],.ten,[1, 5, 0, 6, 3, 9, 4, 8, 2, 7],[2, 0, 8, 4, 6, 1, 3, 9, 7, 5]⟩]

def batch2 : List Item := [
  ⟨[3, 5, 17, 18, 20],.theta244,[5, 9, 2, 0, 6, 3, 1, 7, 4],[3, 6, 2, 5, 8, 0, 4, 7, 0, 1]⟩,
  ⟨[3, 5, 17, 22],.theta333,[3, 2, 1, 0, 5, 6, 7, 9],[3, 2, 1, 0, 0, 4, 5, 6, 0, 7]⟩,
  ⟨[3, 5, 18, 20],.eight,[1, 5, 0, 6, 2, 9, 3, 7],[2, 0, 4, 6, 0, 1, 3, 7, 0, 5]⟩,
  ⟨[3, 6, 9, 10, 12],.theta244,[6, 8, 3, 0, 5, 2, 1, 7, 4],[3, 6, 5, 2, 8, 4, 0, 7, 1, 0]⟩,
  ⟨[3, 6, 9, 12],.eight,[2, 5, 0, 6, 1, 7, 3, 8],[2, 4, 0, 6, 0, 1, 3, 5, 7, 0]⟩,
  ⟨[3, 6, 9, 20, 24],.ten,[2, 5, 0, 6, 1, 7, 3, 9, 4, 8],[2, 4, 0, 6, 8, 1, 3, 5, 9, 7]⟩]

def batch3 : List Item := [
  ⟨[3, 6, 10, 13],.theta333,[3, 2, 1, 0, 6, 5, 7, 8],[3, 2, 1, 0, 0, 5, 4, 6, 7, 0]⟩,
  ⟨[3, 6, 12, 17, 24],.ten,[3, 5, 0, 6, 1, 7, 2, 8, 4, 9],[2, 4, 6, 0, 8, 1, 3, 5, 7, 9]⟩,
  ⟨[3, 6, 17, 18, 20],.theta244,[6, 9, 3, 0, 5, 2, 1, 7, 4],[3, 6, 5, 2, 8, 4, 0, 7, 0, 1]⟩,
  ⟨[3, 6, 17, 20],.eight,[2, 5, 0, 6, 1, 7, 3, 9],[2, 4, 0, 6, 0, 1, 3, 5, 0, 7]⟩,
  ⟨[3, 6, 18, 21],.theta333,[3, 2, 1, 0, 6, 5, 7, 9],[3, 2, 1, 0, 0, 5, 4, 6, 0, 7]⟩,
  ⟨[3, 9, 10],.six,[1, 5, 0, 6, 2, 8],[2, 0, 4, 0, 0, 1, 3, 0, 5, 0]⟩]

def batch4 : List Item := [
  ⟨[3, 9, 10, 17, 18],.theta244,[5, 6, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 1, 0, 4, 7]⟩,
  ⟨[3, 9, 10, 17, 24],.theta244,[5, 8, 1, 0, 6, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 4, 0, 1, 7]⟩,
  ⟨[3, 9, 10, 18, 24],.theta244,[6, 8, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 0, 1, 7]⟩,
  ⟨[3, 9, 12, 18, 20],.ten,[1, 5, 0, 6, 3, 9, 4, 7, 2, 8],[2, 0, 8, 4, 6, 1, 3, 7, 9, 5]⟩,
  ⟨[3, 9, 17, 18, 24],.theta244,[5, 9, 2, 0, 6, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 4, 0, 7, 1]⟩,
  ⟨[3, 9, 17, 26],.theta333,[3, 2, 1, 0, 5, 6, 8, 9],[3, 2, 1, 0, 0, 4, 5, 0, 6, 7]⟩]

def batch5 : List Item := [
  ⟨[3, 9, 18, 24],.eight,[1, 5, 0, 6, 2, 9, 3, 8],[2, 0, 4, 6, 0, 1, 3, 0, 7, 5]⟩,
  ⟨[3, 10, 12, 17, 20],.ten,[3, 5, 0, 6, 1, 8, 2, 7, 4, 9],[2, 4, 6, 0, 8, 1, 3, 7, 5, 9]⟩,
  ⟨[3, 10, 17, 18, 24],.theta244,[6, 9, 3, 0, 5, 2, 1, 8, 4],[3, 6, 5, 2, 8, 4, 0, 0, 7, 1]⟩,
  ⟨[3, 10, 17, 24],.eight,[2, 5, 0, 6, 1, 8, 3, 9],[2, 4, 0, 6, 0, 1, 3, 0, 5, 7]⟩,
  ⟨[3, 10, 18, 25],.theta333,[3, 2, 1, 0, 6, 5, 8, 9],[3, 2, 1, 0, 0, 5, 4, 0, 6, 7]⟩,
  ⟨[3, 12, 21, 26],.theta244,[2, 3, 9, 5, 0, 6, 7, 1, 8],[4, 7, 0, 1, 0, 3, 5, 6, 8, 2]⟩]

def batch6 : List Item := [
  ⟨[3, 12, 22, 25],.theta244,[3, 2, 9, 5, 0, 6, 8, 1, 7],[4, 7, 1, 0, 0, 3, 5, 8, 6, 2]⟩,
  ⟨[3, 13, 20, 26],.theta244,[1, 3, 8, 5, 0, 6, 7, 2, 9],[4, 0, 7, 1, 0, 3, 5, 6, 2, 8]⟩,
  ⟨[3, 13, 22, 24],.theta244,[1, 2, 7, 5, 0, 6, 8, 3, 9],[4, 0, 1, 7, 0, 3, 5, 2, 6, 8]⟩,
  ⟨[3, 14, 20, 25],.theta244,[3, 1, 8, 5, 0, 6, 9, 2, 7],[4, 1, 7, 0, 0, 3, 5, 8, 2, 6]⟩,
  ⟨[3, 14, 21, 24],.theta244,[2, 1, 7, 5, 0, 6, 9, 3, 8],[4, 1, 0, 7, 0, 3, 5, 2, 8, 6]⟩,
  ⟨[3, 17, 18],.six,[1, 5, 0, 6, 2, 9],[2, 0, 4, 0, 0, 1, 3, 0, 0, 5]⟩]

def batch7 : List Item := [
  ⟨[5, 6, 9, 10],.eight,[2, 5, 0, 7, 1, 6, 3, 8],[2, 4, 0, 6, 0, 1, 5, 3, 7, 0]⟩,
  ⟨[5, 6, 9, 10, 12],.theta244,[7, 8, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 1, 0]⟩,
  ⟨[5, 6, 9, 18, 24],.ten,[2, 5, 0, 7, 1, 6, 3, 9, 4, 8],[2, 4, 0, 6, 8, 1, 5, 3, 9, 7]⟩,
  ⟨[5, 6, 10, 17, 24],.ten,[3, 5, 0, 7, 1, 6, 2, 8, 4, 9],[2, 4, 6, 0, 8, 1, 5, 3, 7, 9]⟩,
  ⟨[5, 6, 11, 12],.theta333,[2, 3, 1, 0, 7, 5, 6, 8],[3, 2, 0, 1, 0, 5, 6, 4, 7, 0]⟩,
  ⟨[5, 6, 17, 18],.eight,[2, 5, 0, 7, 1, 6, 3, 9],[2, 4, 0, 6, 0, 1, 5, 3, 0, 7]⟩]

def batch8 : List Item := [
  ⟨[5, 6, 17, 18, 20],.theta244,[7, 9, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 0, 1]⟩,
  ⟨[5, 6, 19, 20],.theta333,[2, 3, 1, 0, 7, 5, 6, 9],[3, 2, 0, 1, 0, 5, 6, 4, 0, 7]⟩,
  ⟨[5, 9, 10, 18, 20],.ten,[1, 5, 0, 7, 4, 9, 3, 6, 2, 8],[2, 0, 8, 6, 4, 1, 7, 3, 9, 5]⟩,
  ⟨[5, 9, 12],.six,[1, 5, 0, 7, 2, 8],[2, 0, 4, 0, 0, 1, 0, 3, 5, 0]⟩,
  ⟨[5, 9, 12, 17, 20],.theta244,[5, 7, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 0, 1, 4, 7]⟩,
  ⟨[5, 9, 12, 17, 24],.theta244,[5, 8, 1, 0, 7, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 0, 4, 1, 7]⟩]

def batch9 : List Item := [
  ⟨[5, 9, 12, 20, 24],.theta244,[7, 8, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 0, 1, 7]⟩,
  ⟨[5, 9, 17, 20, 24],.theta244,[5, 9, 2, 0, 7, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 0, 4, 7, 1]⟩,
  ⟨[5, 9, 17, 28],.theta333,[3, 2, 1, 0, 5, 7, 8, 9],[3, 2, 1, 0, 0, 4, 0, 5, 6, 7]⟩,
  ⟨[5, 9, 20, 24],.eight,[1, 5, 0, 7, 2, 9, 3, 8],[2, 0, 4, 6, 0, 1, 0, 3, 7, 5]⟩,
  ⟨[5, 10, 12, 17, 18],.ten,[3, 5, 0, 7, 2, 8, 1, 6, 4, 9],[2, 6, 4, 0, 8, 1, 7, 3, 5, 9]⟩,
  ⟨[5, 10, 19, 28],.theta244,[2, 3, 9, 5, 0, 7, 6, 1, 8],[4, 7, 0, 1, 0, 3, 6, 5, 8, 2]⟩]

def batch10 : List Item := [
  ⟨[5, 10, 22, 25],.theta244,[3, 2, 9, 5, 0, 7, 8, 1, 6],[4, 7, 1, 0, 0, 3, 8, 5, 6, 2]⟩,
  ⟨[5, 11, 18, 28],.theta244,[1, 3, 8, 5, 0, 7, 6, 2, 9],[4, 0, 7, 1, 0, 3, 6, 5, 2, 8]⟩,
  ⟨[5, 11, 22, 24],.theta244,[1, 2, 6, 5, 0, 7, 8, 3, 9],[4, 0, 1, 7, 0, 3, 2, 5, 6, 8]⟩,
  ⟨[5, 12, 17, 20, 24],.theta244,[7, 9, 3, 0, 5, 2, 1, 8, 4],[3, 6, 5, 2, 8, 4, 0, 0, 7, 1]⟩,
  ⟨[5, 12, 17, 24],.eight,[2, 5, 0, 7, 1, 8, 3, 9],[2, 4, 0, 6, 0, 1, 0, 3, 5, 7]⟩,
  ⟨[5, 12, 20, 25],.theta333,[3, 2, 1, 0, 7, 5, 8, 9],[3, 2, 1, 0, 0, 5, 0, 4, 6, 7]⟩]

def batch11 : List Item := [
  ⟨[5, 14, 18, 25],.theta244,[3, 1, 8, 5, 0, 7, 9, 2, 6],[4, 1, 7, 0, 0, 3, 8, 5, 2, 6]⟩,
  ⟨[5, 14, 19, 24],.theta244,[2, 1, 6, 5, 0, 7, 9, 3, 8],[4, 1, 0, 7, 0, 3, 2, 5, 8, 6]⟩,
  ⟨[5, 17, 20],.six,[1, 5, 0, 7, 2, 9],[2, 0, 4, 0, 0, 1, 0, 3, 0, 5]⟩,
  ⟨[6, 9, 10, 17, 20],.ten,[3, 5, 1, 8, 2, 6, 0, 7, 4, 9],[6, 2, 4, 0, 8, 1, 5, 7, 3, 9]⟩,
  ⟨[6, 9, 12, 17, 18],.ten,[3, 5, 1, 8, 2, 7, 0, 6, 4, 9],[6, 2, 4, 0, 8, 1, 7, 5, 3, 9]⟩,
  ⟨[6, 9, 19, 28],.theta244,[2, 3, 9, 5, 1, 8, 6, 0, 7],[7, 4, 0, 1, 0, 3, 6, 8, 5, 2]⟩]

def batch12 : List Item := [
  ⟨[6, 9, 21, 26],.theta244,[2, 3, 9, 5, 1, 8, 7, 0, 6],[7, 4, 0, 1, 0, 3, 8, 6, 5, 2]⟩,
  ⟨[6, 10, 12],.six,[1, 6, 0, 7, 2, 8],[2, 0, 4, 0, 0, 0, 1, 3, 5, 0]⟩,
  ⟨[6, 10, 12, 18, 20],.theta244,[6, 7, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 0, 1, 4, 7]⟩,
  ⟨[6, 10, 12, 18, 24],.theta244,[6, 8, 1, 0, 7, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 0, 4, 1, 7]⟩,
  ⟨[6, 10, 12, 20, 24],.theta244,[7, 8, 2, 0, 6, 1, 3, 9, 4],[3, 5, 2, 6, 8, 0, 4, 0, 1, 7]⟩,
  ⟨[6, 10, 18, 20, 24],.theta244,[6, 9, 2, 0, 7, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 0, 4, 7, 1]⟩]

def batch13 : List Item := [
  ⟨[6, 10, 18, 28],.theta333,[3, 2, 1, 0, 6, 7, 8, 9],[3, 2, 1, 0, 0, 0, 4, 5, 6, 7]⟩,
  ⟨[6, 10, 20, 24],.eight,[1, 6, 0, 7, 2, 9, 3, 8],[2, 0, 4, 6, 0, 0, 1, 3, 7, 5]⟩,
  ⟨[6, 11, 17, 28],.theta244,[1, 3, 8, 5, 2, 9, 6, 0, 7],[7, 0, 4, 1, 0, 3, 6, 8, 2, 5]⟩,
  ⟨[6, 11, 21, 24],.theta244,[1, 2, 5, 6, 0, 7, 8, 3, 9],[4, 0, 1, 7, 0, 2, 3, 5, 6, 8]⟩,
  ⟨[6, 12, 18, 20, 24],.theta244,[7, 9, 3, 0, 6, 2, 1, 8, 4],[3, 6, 5, 2, 8, 0, 4, 0, 7, 1]⟩,
  ⟨[6, 12, 18, 24],.eight,[2, 6, 0, 7, 1, 8, 3, 9],[2, 4, 0, 6, 0, 0, 1, 3, 5, 7]⟩]

def batch14 : List Item := [
  ⟨[6, 12, 20, 26],.theta333,[3, 2, 1, 0, 7, 6, 8, 9],[3, 2, 1, 0, 0, 0, 5, 4, 6, 7]⟩,
  ⟨[6, 13, 17, 26],.theta244,[1, 3, 8, 5, 2, 9, 7, 0, 6],[7, 0, 4, 1, 0, 3, 8, 6, 2, 5]⟩,
  ⟨[6, 13, 19, 24],.theta244,[2, 1, 5, 6, 0, 7, 9, 3, 8],[4, 1, 0, 7, 0, 2, 3, 5, 8, 6]⟩,
  ⟨[6, 18, 20],.six,[1, 6, 0, 7, 2, 9],[2, 0, 4, 0, 0, 0, 1, 3, 0, 5]⟩,
  ⟨[7, 9, 10, 12],.theta333,[0, 3, 2, 1, 8, 5, 6, 7],[0, 3, 2, 1, 0, 5, 6, 7, 4, 0]⟩,
  ⟨[7, 9, 18, 28],.theta244,[0, 3, 7, 5, 1, 8, 6, 2, 9],[0, 4, 7, 1, 0, 3, 6, 2, 5, 8]⟩]

def batch15 : List Item := [
  ⟨[7, 9, 20, 26],.theta244,[0, 3, 6, 5, 1, 8, 7, 2, 9],[0, 4, 7, 1, 0, 3, 2, 6, 5, 8]⟩,
  ⟨[7, 10, 17, 28],.theta244,[0, 3, 7, 5, 2, 9, 6, 1, 8],[0, 7, 4, 1, 0, 3, 6, 2, 8, 5]⟩,
  ⟨[7, 10, 20, 25],.theta244,[0, 3, 5, 6, 1, 8, 7, 2, 9],[0, 4, 7, 1, 0, 2, 3, 6, 5, 8]⟩,
  ⟨[7, 12, 17, 26],.theta244,[0, 3, 6, 5, 2, 9, 7, 1, 8],[0, 7, 4, 1, 0, 3, 2, 6, 8, 5]⟩,
  ⟨[7, 12, 18, 25],.theta244,[0, 3, 5, 6, 2, 9, 7, 1, 8],[0, 7, 4, 1, 0, 2, 3, 6, 8, 5]⟩,
  ⟨[7, 17, 18, 20],.theta333,[0, 3, 2, 1, 9, 5, 6, 7],[0, 3, 2, 1, 0, 5, 6, 7, 0, 4]⟩]

def batch16 : List Item := [
  ⟨[9, 10, 17, 18],.eight,[2, 5, 0, 8, 1, 6, 3, 9],[2, 4, 0, 6, 0, 1, 5, 0, 3, 7]⟩,
  ⟨[9, 10, 17, 18, 24],.theta244,[8, 9, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 0, 1]⟩,
  ⟨[9, 10, 19, 24],.theta333,[2, 3, 1, 0, 8, 5, 6, 9],[3, 2, 0, 1, 0, 5, 6, 0, 4, 7]⟩,
  ⟨[9, 12, 17, 20],.eight,[2, 5, 0, 8, 1, 7, 3, 9],[2, 4, 0, 6, 0, 1, 0, 5, 3, 7]⟩,
  ⟨[9, 12, 17, 20, 24],.theta244,[8, 9, 4, 0, 5, 2, 1, 7, 3],[3, 6, 5, 8, 2, 4, 0, 7, 0, 1]⟩,
  ⟨[9, 12, 21, 24],.theta333,[2, 3, 1, 0, 8, 5, 7, 9],[3, 2, 0, 1, 0, 5, 0, 6, 4, 7]⟩]

def batch17 : List Item := [
  ⟨[9, 14, 18, 21],.theta244,[3, 1, 7, 5, 0, 8, 9, 2, 6],[4, 1, 7, 0, 0, 3, 8, 2, 5, 6]⟩,
  ⟨[9, 14, 19, 20],.theta244,[2, 1, 6, 5, 0, 8, 9, 3, 7],[4, 1, 0, 7, 0, 3, 2, 8, 5, 6]⟩,
  ⟨[9, 17, 24],.six,[1, 5, 0, 8, 2, 9],[2, 0, 4, 0, 0, 1, 0, 0, 3, 5]⟩,
  ⟨[10, 12, 18, 20],.eight,[2, 6, 0, 8, 1, 7, 3, 9],[2, 4, 0, 6, 0, 0, 1, 5, 3, 7]⟩,
  ⟨[10, 12, 18, 20, 24],.theta244,[8, 9, 4, 0, 6, 2, 1, 7, 3],[3, 6, 5, 8, 2, 0, 4, 7, 0, 1]⟩,
  ⟨[10, 12, 22, 24],.theta333,[2, 3, 1, 0, 8, 6, 7, 9],[3, 2, 0, 1, 0, 0, 5, 6, 4, 7]⟩]

def batch18 : List Item := [
  ⟨[10, 13, 17, 22],.theta244,[1, 3, 7, 5, 2, 9, 8, 0, 6],[7, 0, 4, 1, 0, 3, 8, 2, 6, 5]⟩,
  ⟨[10, 13, 19, 20],.theta244,[2, 1, 5, 6, 0, 8, 9, 3, 7],[4, 1, 0, 7, 0, 2, 3, 8, 5, 6]⟩,
  ⟨[10, 18, 24],.six,[1, 6, 0, 8, 2, 9],[2, 0, 4, 0, 0, 0, 1, 0, 3, 5]⟩,
  ⟨[11, 12, 17, 22],.theta244,[0, 3, 6, 5, 2, 9, 8, 1, 7],[0, 7, 4, 1, 0, 3, 2, 8, 6, 5]⟩,
  ⟨[11, 12, 18, 21],.theta244,[0, 3, 5, 6, 2, 9, 8, 1, 7],[0, 7, 4, 1, 0, 2, 3, 8, 6, 5]⟩,
  ⟨[11, 17, 18, 24],.theta333,[0, 3, 2, 1, 9, 5, 6, 8],[0, 3, 2, 1, 0, 5, 6, 0, 7, 4]⟩]

def batch19 : List Item := [
  ⟨[12, 20, 24],.six,[1, 7, 0, 8, 2, 9],[2, 0, 4, 0, 0, 0, 0, 1, 3, 5]⟩,
  ⟨[13, 17, 20, 24],.theta333,[0, 3, 2, 1, 9, 5, 7, 8],[0, 3, 2, 1, 0, 5, 0, 6, 7, 4]⟩,
  ⟨[14, 18, 20, 24],.theta333,[0, 3, 2, 1, 9, 6, 7, 8],[0, 3, 2, 1, 0, 0, 5, 6, 7, 4]⟩]

def items := batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4 ++ batch5 ++ batch6 ++ batch7 ++ batch8 ++ batch9 ++ batch10 ++ batch11 ++ batch12 ++ batch13 ++ batch14 ++ batch15 ++ batch16 ++ batch17 ++ batch18 ++ batch19

end CoreCensus

namespace CoreCensus

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check0 : batch0.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check1 : batch1.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check2 : batch2.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check3 : batch3.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check4 : batch4.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check5 : batch5.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check6 : batch6.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check7 : batch7.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check8 : batch8.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check9 : batch9.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check10 : batch10.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check11 : batch11.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check12 : batch12.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check13 : batch13.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check14 : batch14.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check15 : batch15.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check16 : batch16.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check17 : batch17.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check18 : batch18.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check19 : batch19.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem validated {r : Item} (hr : r ∈ items) : Certified r := by
  have h : items.all (fun e => decide (Certified e)) = true := by
    simp only [items,List.all_append,check0,check1,check2,check3,check4,check5,check6,check7,check8,check9,check10,check11,check12,check13,check14,check15,check16,check17,check18,check19,Bool.true_and]
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

end CoreCensus

namespace CoreCensus
open List

def wt (r : Nat) := (r % 2) + (r / 2 % 2) + (r / 4 % 2) + (r / 8 % 2) + (r / 16 % 2)

def eligible (lo budget : Nat) (pre : List Nat) (r : Nat) : Bool :=
  decide (lo < r ∧ 2 ≤ wt r ∧ wt r ≤ budget) && pre.all (fun p => decide (wt (p &&& r) ≤ 1))

def generate : Nat → Nat → Nat → List Nat → List (List Nat)
  | 0, _, _, pre => [pre]
  | k+1, lo, budget, pre => pre :: ((range 32).filter (eligible lo budget pre)).flatMap
      fun r => generate k r (budget - wt r) (pre ++ [r])

theorem current_mem (k lo budget) (pre : List Nat) : pre ∈ generate k lo budget pre := by
  cases k <;> simp [generate]

def Compatible (r s : Nat) := r < s ∧ wt (r &&& s) ≤ 1

theorem listed (ys : List Nat) (fuel lo budget : Nat) (pre : List Nat)
    (len : ys.length ≤ fuel) (bounds : ∀ r ∈ ys, lo < r ∧ r < 32 ∧ 2 ≤ wt r)
    (total : (ys.map wt).sum ≤ budget) (pair : ys.Pairwise Compatible)
    (past : ∀ r ∈ ys, ∀ p ∈ pre, wt (p &&& r) ≤ 1) :
    pre ++ ys ∈ generate fuel lo budget pre := by
  induction ys generalizing fuel lo budget pre with
  | nil => simpa using current_mem fuel lo budget pre
  | cons r rs ih =>
    cases fuel with
    | zero => simp at len
    | succ k =>
      obtain ⟨rtop,rr,rlower⟩ := bounds r (by simp)
      have cost : wt r + (rs.map wt).sum ≤ budget := by simpa using total
      obtain ⟨first,tail⟩ := List.pairwise_cons.mp pair
      have elig : eligible lo budget pre r = true := by
        unfold eligible
        apply Bool.and_eq_true_iff.mpr
        exact ⟨decide_eq_true ⟨rtop,rlower,by omega⟩,
          List.all_eq_true.mpr (fun p hp => decide_eq_true (past r (by simp) p hp))⟩
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨r,List.mem_filter.mpr ⟨List.mem_range.mpr rr,elig⟩,?_⟩
      have hmem := ih k r (budget - wt r) (pre ++ [r]) (by simpa using len)
          (fun s hs => ⟨(first s hs).1,(bounds s (by simp [hs])).2⟩) (by omega) tail (by
            intro s hs p hp
            rcases List.mem_append.mp hp with old | new
            · exact past s (by simp [hs]) p old
            · obtain rfl : p = r := by simpa using new
              exact (first s hs).2)
      simpa only [List.append_assoc,List.singleton_append] using hmem

def liveCols (xs : List Nat) : Bool :=
  (range 5).all fun i => decide (xs.countP (fun r => r.testBit i) ≠ 1)

def recognized (xs : List Nat) : Bool := items.any (fun c => c.rows == xs)

def acceptedRows (xs : List Nat) : Bool := xs.isEmpty || !liveCols xs || recognized xs

theorem exists_item {xs : List Nat} (h : recognized xs = true) : ∃ r ∈ items, r.rows = xs := by
  obtain ⟨r,hr,eq⟩ := List.any_eq_true.mp h
  exact ⟨r,hr,by simpa using eq⟩

end CoreCensus

namespace CoreCensus
open List

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first3 : (generate 4 3 (10 - wt 3) [3]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first5 : (generate 4 5 (10 - wt 5) [5]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first6 : (generate 4 6 (10 - wt 6) [6]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first7 : (generate 4 7 (10 - wt 7) [7]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first9 : (generate 4 9 (10 - wt 9) [9]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first10 : (generate 4 10 (10 - wt 10) [10]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first11 : (generate 4 11 (10 - wt 11) [11]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first12 : (generate 4 12 (10 - wt 12) [12]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first13 : (generate 4 13 (10 - wt 13) [13]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first14 : (generate 4 14 (10 - wt 14) [14]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first15 : (generate 4 15 (10 - wt 15) [15]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first17 : (generate 4 17 (10 - wt 17) [17]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first18 : (generate 4 18 (10 - wt 18) [18]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first19 : (generate 4 19 (10 - wt 19) [19]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first20 : (generate 4 20 (10 - wt 20) [20]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first21 : (generate 4 21 (10 - wt 21) [21]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first22 : (generate 4 22 (10 - wt 22) [22]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first23 : (generate 4 23 (10 - wt 23) [23]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first24 : (generate 4 24 (10 - wt 24) [24]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first25 : (generate 4 25 (10 - wt 25) [25]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first26 : (generate 4 26 (10 - wt 26) [26]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first27 : (generate 4 27 (10 - wt 27) [27]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first28 : (generate 4 28 (10 - wt 28) [28]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first29 : (generate 4 29 (10 - wt 29) [29]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first30 : (generate 4 30 (10 - wt 30) [30]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first31 : (generate 4 31 (10 - wt 31) [31]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem all_rows : (generate 5 0 10 []).all acceptedRows = true := by
  have opts : (range 32).filter (eligible 0 10 []) = [3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] := by decide +kernel
  change (acceptedRows [] && (((range 32).filter (eligible 0 10 [])).flatMap (fun r => generate 4 r (10 - wt r) ([] ++ [r]))).all acceptedRows) = true
  rw [List.all_flatMap,opts]
  have empty : acceptedRows [] = true := rfl
  simp only [empty,List.nil_append,List.all_cons,List.all_nil,Bool.true_and,first3,first5,first6,first7,first9,first10,first11,first12,first13,first14,first15,first17,first18,first19,first20,first21,first22,first23,first24,first25,first26,first27,first28,first29,first30,first31]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem recognized_of_rows (xs : List Nat) (hne : xs ≠ [])
    (len : xs.length ≤ 5) (bounds : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r)
    (w : (xs.map wt).sum ≤ 10) (s : xs.Pairwise Compatible) (hcol : liveCols xs = true) :
    ∃ c ∈ items, c.rows = xs := by
  have mem := listed xs 5 0 10 [] len bounds w s (by simp)
  have result := List.all_eq_true.mp all_rows xs (by simpa using mem)
  apply exists_item
  have notEmpty : xs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simpa [acceptedRows,notEmpty,hcol] using result

end CoreCensus

namespace CoreCensus
open LeafCore3241

theorem sorted_counts (xs : List Nat) (hne : xs ≠ []) (len : xs.length ≤ 5)
    (bounds : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r) (w : (xs.map wt).sum ≤ 10)
    (s : xs.Pairwise Compatible) (hcol : liveCols xs = true) : Counts (matrix xs) := by
  obtain ⟨r,member,rfl⟩ := recognized_of_rows xs hne len bounds w s hcol
  exact count_item r (validated member) Theta244.nine

end CoreCensus

namespace NormalizeCores3241
open CoreCensus GraphPacking3241 MatrixPacking3241 LeafCore3241 ForestBipartite3241

def encode (x : Fin 5 → Bool) : Nat :=
  (x 0).toNat + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16

theorem encode_bound : ∀ x : Fin 5 → Bool, encode x < 32 := by decide +kernel
theorem encode_bit : ∀ (x : Fin 5 → Bool) (i : Fin 5), (encode x).testBit i.val = x i := by decide +kernel
theorem encode_weight : ∀ x : Fin 5 → Bool, wt (encode x) = (Finset.univ.filter (fun i => x i)).card := by
  decide +kernel
theorem weight_two : ∀ (r : Fin 32) (a b : Fin 5), a ≠ b → r.val.testBit a.val = true →
    r.val.testBit b.val = true → 2 ≤ wt r.val := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem weight_shared : ∀ a b : Fin 32,
    (∀ i j : Fin 5, a.val.testBit i.val = true → b.val.testBit i.val = true →
      a.val.testBit j.val = true → b.val.testBit j.val = true → i = j) → wt (a.val &&& b.val) ≤ 1 := by
  decide +kernel

def mask (E : Matrix 5 5) (i : Fin 5) : Nat := encode fun j => decide ((i,j) ∈ E)

theorem bit_iff (E : Matrix 5 5) (i j : Fin 5) : (mask E i).testBit j.val = true ↔ (i,j) ∈ E := by
  simp [mask,encode_bit]

theorem wt_fiber (E : Matrix 5 5) (i : Fin 5) :
    wt (mask E i) = (E.filter (fun p => p.1 = i)).card := by
  let T := Finset.univ.filter (fun j : Fin 5 => (i,j) ∈ E)
  have eq : E.filter (fun p => p.1 = i) = T.image (Prod.mk i) := by
    ext p
    constructor
    · rintro h
      obtain ⟨he,pi⟩ := Finset.mem_filter.mp h
      exact Finset.mem_image.mpr ⟨p.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [← pi] using he⟩,
        Prod.ext pi.symm rfl⟩
    · intro h
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2,rfl⟩
  have wt_eq := encode_weight (fun j : Fin 5 => decide ((i,j) ∈ E))
  rw [eq,Finset.card_image_of_injective _ (fun j k h => congrArg Prod.snd h)]
  simpa [mask,T] using wt_eq

theorem separated (E : Matrix 5 5) (free : FourFree E) (p q : Fin 5) (ne : p ≠ q) :
    wt (mask E p &&& mask E q) ≤ 1 := by
  apply weight_shared ⟨mask E p,encode_bound _⟩ ⟨mask E q,encode_bound _⟩
  intro i j pi qi pj qj
  by_contra ij
  exact free p q i j ne ij ⟨(bit_iff E p i).mp pi,(bit_iff E p j).mp pj,
    (bit_iff E q i).mp qi,(bit_iff E q j).mp qj⟩

theorem row_bounds (E : Matrix 5 5) (rich : HasPartners E) (p : Fin 5) (hp : p ∈ Rows E) :
    0 < mask E p ∧ mask E p < 32 ∧ 2 ≤ wt (mask E p) := by
  obtain ⟨⟨a,b⟩,ab,eq⟩ := Finset.mem_image.mp hp
  change a = p at eq
  subst a
  obtain ⟨c,cb,pc⟩ := (rich p b ab).1
  have positive : mask E p ≠ 0 := by
    intro bad
    have bit := (bit_iff E p b).mpr ab
    simp [bad] at bit
  exact ⟨Nat.pos_of_ne_zero positive,encode_bound _,
    weight_two ⟨mask E p,encode_bound _⟩ c b cb ((bit_iff E p c).mpr pc) ((bit_iff E p b).mpr ab)⟩

theorem mask_inj (E : Matrix 5 5) (free : FourFree E) (rich : HasPartners E) :
    Set.InjOn (mask E) (Rows E : Set (Fin 5)) := by
  intro a ha b _ eq
  by_contra ne
  have cap := separated E free a b ne
  rw [← eq,Nat.and_self] at cap
  have low := (row_bounds E rich a ha).2.2
  omega

theorem sum_list (xs : List Nat) (f : Nat → Nat) (distinct : xs.Nodup) :
    (xs.map f).sum = ∑ i ∈ xs.toFinset, f i := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have h := List.nodup_cons.mp distinct
    simp [h.1,ih h.2]

def SortedProof := ∀ xs : List Nat, xs ≠ [] → xs.length ≤ 5 →
  (∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r) → (xs.map wt).sum ≤ 10 →
  xs.Pairwise Compatible → liveCols xs = true → Counts (matrix xs)

theorem census_of_sorted (done : SortedProof) : MatrixPacking3241.Census := by
  classical
  intro E size free last
  by_cases zero : E = ∅
  · have ac : (bip E).IsAcyclic := by
      have bot : bip E = ⊥ := by
        apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
        intro i j h
        rcases h with ⟨_,⟨e,he,_,_⟩ | ⟨e,he,_,_⟩⟩ <;> simp [zero] at he
      rw [bot]
      exact SimpleGraph.isAcyclic_bot
    exact forest_counts _ ac
  have rich := (leafless_iff E).mp last
  let A := (Rows E).image (mask E)
  let xs := A.sort
  have inj := mask_inj E free rich
  have cap : A.card ≤ 5 := (Finset.card_image_le).trans (Finset.card_le_univ (Rows E))
  have len : xs.length ≤ 5 := by simpa [xs] using cap
  have mem (r : Nat) : r ∈ xs ↔ ∃ p ∈ Rows E, mask E p = r := by simp [xs,A]
  have nonempty : xs ≠ [] := by
    obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr zero
    have hm := (mem _).mpr ⟨e.1,Finset.mem_image_of_mem _ he,rfl⟩
    intro eq
    simp [eq] at hm
  have rn : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r := by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := (mem r).mp hr
    exact row_bounds E rich p hp
  have total : (xs.map wt).sum = E.card := by
    rw [sum_list _ _ (A.sort_nodup _)]
    have eq : xs.toFinset = A := by ext r; simp [xs]
    rw [eq,Finset.sum_image]
    · rw [Finset.card_eq_sum_card_image Prod.fst E]
      exact Finset.sum_congr rfl (fun x _ => wt_fiber E x)
    · exact inj
  have sorted : xs.Pairwise (· < ·) := A.sortedLT_sort.pairwise
  have pair : xs.Pairwise Compatible := by
    apply sorted.imp_of_mem
    intro a b ha hb lt
    obtain ⟨p,_,rfl⟩ := (mem a).mp ha
    obtain ⟨q,_,rfl⟩ := (mem b).mp hb
    exact ⟨lt,separated E free p q (fun eq => (Nat.ne_of_lt lt) (congrArg (mask E) eq))⟩
  have cols : liveCols xs = true := by
    apply List.all_eq_true.mpr
    intro j hj
    apply decide_eq_true
    intro unique
    have pos : 0 < xs.countP (fun r => r.testBit j) := by omega
    obtain ⟨r,hr,bit⟩ := List.countP_pos_iff.mp pos
    obtain ⟨p,hp,rfl⟩ := (mem r).mp hr
    let c : Fin 5 := ⟨j,List.mem_range.mp hj⟩
    have pc : (p,c) ∈ E := (bit_iff E p c).mp bit
    obtain ⟨q,qp,qc⟩ := (rich p c pc).2
    have hq : q ∈ Rows E := Finset.mem_image_of_mem Prod.fst qc
    have hq' := (mem _).mpr ⟨q,hq,rfl⟩
    have diff := ThetaPin3241.count_one_unique xs (fun a => a.testBit j) _ _ hq' hr
      ((bit_iff E q c).mpr qc) bit (by omega)
    exact qp (inj hq hp diff)
  have ok := done xs nonempty len rn (total ▸ size) pair cols
  let val (p : Rows E) : A := ⟨mask E p.val,Finset.mem_image_of_mem _ p.property⟩
  have bij : Function.Bijective val := by
    refine ⟨fun p q eq => Subtype.ext (inj p.property q.property (congrArg Subtype.val eq)),?_⟩
    intro a
    obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp a.property
    exact ⟨⟨p,hp⟩,Subtype.ext eq⟩
  let order := (Equiv.ofBijective val bij).trans ((A.orderIsoOfFin rfl).symm.toEquiv)
  let r (p : Rows E) : Fin 5 := (order p).castLE cap
  have ri : Function.Injective r := (Fin.castLE_injective cap).comp order.injective
  let c (p : Cols E) : Fin 5 := p.val
  have read (p : Rows E) : xs.getD (r p).val 0 = mask E p.val := by
    have hl : (r p).val < xs.length := by simp [xs,r]
    rw [List.getD_eq_getElem _ _ hl]
    have ev := congrArg Subtype.val ((A.orderIsoOfFin rfl).apply_symm_apply (val p))
    exact ev
  have pe : pack E r c = pairs xs := by
    ext ij
    obtain ⟨i,j⟩ := ij
    change (i,j) ∈ pack E r c ↔ (i,j) ∈ pairs xs
    rw [decode]
    simp only [pairs,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨e,rfl,rfl⟩
      rw [read]
      exact (bit_iff E _ _).mpr e.property
    · intro bit
      have hl : i.val < xs.length := by
        by_contra! bad
        rw [List.getD_eq_default _ _ bad] at bit
        simp at bit
      have ha : i.val < A.card := by simpa [xs] using hl
      let p := order.symm ⟨i.val,ha⟩
      have pos : r p = i := Fin.ext (by simp [r,p])
      rw [← pos,read] at bit
      have cell := (bit_iff E p.val j).mp bit
      let e : E := ⟨(p.val,j),cell⟩
      exact ⟨e,pos,rfl⟩
  apply unpack_counts E r c ri Subtype.val_injective
  rw [pe]
  exact ok

theorem census : MatrixPacking3241.Census := census_of_sorted CoreCensus.sorted_counts

end NormalizeCores3241

end PEqualNP.Outside.L_meta_8181.Ten

namespace PEqualNP.Outside.L_meta_8181.Ten

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open LeafCore3241 ForestBipartite3241 GraphPacking3241 MatrixPacking3241

end PEqualNP.Outside.L_meta_8181.Ten

namespace PEqualNP.Outside.L_meta_8181.Puncture

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepW_len (gs : List Gate) (inp : List Bool) :
    (gs.foldl stepW inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp
  | cons g rest ih =>
    simp [List.foldl, stepW, ih]
    omega

private lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_self (l1 : List Bool) (b : Bool) :
    (l1 ++ [b]).getD l1.length false = b := by
  simp [List.getD]

private lemma getD_of_ge (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none hi]

private lemma getD_ofFn {n : ℕ} (z : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn z).getD i false = z ⟨i, hi⟩ := by
  simp [List.getD, hi]

private def wireVal (n : ℕ) (gs : List Gate) (z : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl stepW (List.ofFn z)).getD i false

private lemma wireVal_append_gate_lt (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool)
    (i : ℕ) (hi : i < n + gs.length) :
    wireVal n (gs ++ [g]) z i = wireVal n gs z i := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  exact getD_append_left _ _ i (by omega)

private lemma wireVal_append_gate_self (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool) :
    wireVal n (gs ++ [g]) z (n + gs.length) =
      g.op.eval (g.inputs.map (fun i => wireVal n gs z i)) := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  rw [← hlen]
  exact getD_append_self (gs.foldl stepW (List.ofFn z)) _

private def gateAtL (gs : List Gate) (j : ℕ) : Gate :=
  gs.getD j ⟨GateOp.or, []⟩

private lemma gateAtL_append_lt (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtL (gs ++ [g]) j = gateAtL gs j := by
  simp [gateAtL, List.getD, List.getElem?_append_left hj]

private lemma gateAtL_append_self (gs : List Gate) (g : Gate) :
    gateAtL (gs ++ [g]) gs.length = g := by
  simp [gateAtL, List.getD]

private def Good (x1 x2 : ℕ) (S : Bool → Finset ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gateAtL gs j).inputs, i < x1 + x2 + j) ∧
  (∀ b : Bool, ∀ w ∈ S b, w < x1 + x2 + gs.length) ∧
  (∀ b : Bool, ∀ w ∈ S b,
    (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
    ∃ j < gs.length, w = x1 + x2 + j ∧ (gateAtL gs j).op = GateOp.or ∧
      ∀ u ∈ (gateAtL gs j).inputs, u ∈ S b) ∧
  (∀ j < gs.length, (gateAtL gs j).op = GateOp.and →
    ∃ a c : ℕ, ∃ b : Bool, (gateAtL gs j).inputs = [a, c] ∧ a ∈ S b ∧ c ∈ S (!b))

private def S0 (x1 x2 : ℕ) (b : Bool) : Finset ℕ :=
  if b then Finset.Ico x1 (x1 + x2) else Finset.range x1

private lemma good_init (x1 x2 : ℕ) : Good x1 x2 (S0 x1 x2) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; cases hg
  · intro j hj; simp at hj
  · intro b w hw
    cases b <;> simp [S0] at hw <;> omega
  · intro b w hw
    left
    cases b <;> simp [S0] at hw
    · exact ⟨by omega, by simp [show ¬(x1 ≤ w) by omega]⟩
    · exact ⟨hw.2, by simp [hw.1]⟩
  · intro j hj; simp at hj

private lemma mem_S0_false {x1 x2 : ℕ} (p : Fin x1) : p.1 ∈ S0 x1 x2 false := by
  simp [S0, p.2]

private lemma mem_S0_true {x1 x2 : ℕ} (l : Fin x2) : x1 + l.1 ∈ S0 x1 x2 true := by
  simp [S0]

private lemma good_append_or_side {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {u v : ℕ} (hu : u ∈ S b) (hv : v ∈ S b) :
    let w := x1 + x2 + gs.length
    let S' : Bool → Finset ℕ := fun b' => if b' = b then insert w (S b') else S b'
    Good x1 x2 S' (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have hu_lt : u < x1 + x2 + gs.length := hLt b u hu
  have hv_lt : v < x1 + x2 + gs.length := hLt b v hv
  dsimp only
  have hSub : ∀ b' : Bool, S b' ⊆ (if b' = b then insert (x1 + x2 + gs.length) (S b') else S b') := by
    intro b'
    by_cases hbb : b' = b
    · simp [hbb]
    · simp [hbb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    by_cases hbb : b' = b
    · simp only [hbb, ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · omega
      · have := hLt b w hw; omega
    · simp only [hbb, ite_false] at hw
      have := hLt b' w hw; omega
  · intro b' w hw
    by_cases hbb : b' = b
    · subst hbb
      simp only [ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · right
        refine ⟨gs.length, by simp, rfl, ?_, ?_⟩
        · rw [gateAtL_append_self]
        · rw [gateAtL_append_self]
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hSub b' hu
          · exact hSub b' hv
      · rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
        · exact Or.inl h1
        · right
          refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
          · rw [gateAtL_append_lt _ _ _ hj]; exact hop
          · rw [gateAtL_append_lt _ _ _ hj]
            intro t ht
            exact hSub b' (hin t ht)
    · simp only [hbb, ite_false] at hw
      rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
      · exact Or.inl h1
      · right
        refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
        · rw [gateAtL_append_lt _ _ _ hj]; exact hop
        · rw [gateAtL_append_lt _ _ _ hj]
          intro t ht
          simp only [hbb, ite_false]
          exact hin t ht
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      rcases hAnd j hlt hop with ⟨a, c, b0, hin, ha, hc⟩
      exact ⟨a, c, b0, hin, hSub b0 ha, hSub (!b0) hc⟩
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_or_top {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {u v : ℕ} (hu : u < x1 + x2 + gs.length) (hv : v < x1 + x2 + gs.length) :
    Good x1 x2 S (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b w hw; omega
  · intro b w hw
    rcases hSide b w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_and {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {a c : ℕ} (ha : a ∈ S b) (hc : c ∈ S (!b)) :
    Good x1 x2 S (gs ++ [⟨GateOp.and, [a, c]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have ha_lt : a < x1 + x2 + gs.length := hLt b a ha
  have hc_lt : c < x1 + x2 + gs.length := hLt (!b) c hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inl rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b' w hw; omega
  · intro b' w hw
    rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self]
      exact ⟨a, c, b, rfl, ha, hc⟩

private lemma addOrInSide {x1 x2 : ℕ} (b : Bool) (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u ∈ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S' gs' ∧
        (∀ b', S b' ⊆ S' b') ∧
        w ∈ S' b ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨S, gs, u, by simp, hG, fun _ => Finset.Subset.rfl, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t ∈ S b := fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
      have hu1 : u ∈ S1 b := hSub1 b (hws u (by simp))
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      let S2 : Bool → Finset ℕ := fun b' => if b' = b then insert w (S1 b') else S1 b'
      have hG2 : Good x1 x2 S2 gs2 := good_append_or_side hG1 b hu1 hw1
      have hSub2 : ∀ b', S b' ⊆ S2 b' := by
        intro b'
        refine Finset.Subset.trans (hSub1 b') ?_
        by_cases hbb : b' = b
        · simp [S2, hbb]
        · simp [S2, hbb]
      have hw2 : w ∈ S2 b := by simp [S2]
      have hu_lt : u < x1 + x2 + gs.length := hG.2.2.1 b u (hws u (by simp))
      refine ⟨S2, gs2, w, ?_, hG2, hSub2, hw2, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private lemma addOrTop {x1 x2 : ℕ} (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u < x1 + x2 + gs.length) →
      ∃ (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S gs' ∧
        w < x1 + x2 + gs'.length ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨gs, u, by simp, hG, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t < x1 + x2 + gs.length :=
        fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨gs1, w1, hlen1, hG1, hw1, hPres1, hVal1⟩
      have hu_lt : u < x1 + x2 + gs.length := hws u (by simp)
      have hu1 : u < x1 + x2 + gs1.length := by omega
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      have hG2 : Good x1 x2 S gs2 := good_append_or_top hG1 hu1 hw1
      refine ⟨gs2, w, ?_, hG2, ?_, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · simp [gs2, w]
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private abbrev Star (x1 x2 : ℕ) := (Fin x1 × List (Fin x2)) ⊕ (Fin x2 × List (Fin x1))

private def starSize {x1 x2 : ℕ} : Star x1 x2 → ℕ
  | Sum.inl (_, ls) => ls.length
  | Sum.inr (_, ps) => ps.length

private def starEval {x1 x2 : ℕ} (z : Fin (x1 + x2) → Bool) : Star x1 x2 → Bool
  | Sum.inl (p, ls) => z (Fin.castAdd x2 p) && ls.any (fun l => z (Fin.natAdd x1 l))
  | Sum.inr (l, ps) => ps.any (fun p => z (Fin.castAdd x2 p)) && z (Fin.natAdd x1 l)

private lemma wireVal_input_left {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (p : Fin x1) :
    wireVal (x1 + x2) gs z p.1 = z (Fin.castAdd x2 p) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : p.1 < x1 + x2 := by omega
    rw [getD_ofFn z p.1 hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma wireVal_input_right {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (l : Fin x2) :
    wireVal (x1 + x2) gs z (x1 + l.1) = z (Fin.natAdd x1 l) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : x1 + l.1 < x1 + x2 := by omega
    rw [getD_ofFn z (x1 + l.1) hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma addStar {x1 x2 : ℕ} (st : Star x1 x2) (hpos : 0 < starSize st)
    (S : Bool → Finset ℕ) (gs : List Gate)
    (hG : Good x1 x2 S gs) (hBase : ∀ b, S0 x1 x2 b ⊆ S b) :
    ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
      gs'.length = gs.length + starSize st ∧
      Good x1 x2 S' gs' ∧
      (∀ b, S b ⊆ S' b) ∧
      w < x1 + x2 + gs'.length ∧
      (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
      (∀ z, wireVal (x1 + x2) gs' z w = starEval z st) := by
  cases st with
  | inl pl =>
    rcases pl with ⟨p, ls⟩
    have hne_ls : ls ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ls.map (fun l => x1 + l.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ls]
    have hws_mem : ∀ u ∈ ws, u ∈ S true := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨l, _, rfl⟩
      exact hBase true (mem_S0_true l)
    rcases addOrInSide true ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wL, hlen1, hG1, hSub1, hwL, hPres1, hVal1⟩
    have hp1 : p.1 ∈ S1 false := hSub1 false (hBase false (mem_S0_false p))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [p.1, wL]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 false hp1 hwL
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ls.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_left, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun l : Fin x2 => wireVal (x1 + x2) gs z (x1 + l.1)) =
          (fun l : Fin x2 => z (Fin.natAdd x1 l)) := by
        funext l
        exact wireVal_input_right gs z l
      simp [Function.comp_def, hfn]
  | inr lp =>
    rcases lp with ⟨l, ps⟩
    have hne_ps : ps ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ps.map (fun p => p.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ps]
    have hws_mem : ∀ u ∈ ws, u ∈ S false := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨p, _, rfl⟩
      exact hBase false (mem_S0_false p)
    rcases addOrInSide false ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wP, hlen1, hG1, hSub1, hwP, hPres1, hVal1⟩
    have hl1 : x1 + l.1 ∈ S1 true := hSub1 true (hBase true (mem_S0_true l))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [wP, x1 + l.1]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 false hwP hl1
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ps.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_right, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun p : Fin x1 => wireVal (x1 + x2) gs z p.1) =
          (fun p : Fin x1 => z (Fin.castAdd x2 p)) := by
        funext p
        exact wireVal_input_left gs z p
      simp [Function.comp_def, hfn]

private lemma addStars {x1 x2 : ℕ} (stars : List (Star x1 x2))
    (hpos : ∀ st ∈ stars, 0 < starSize st) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ b, S0 x1 x2 b ⊆ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (ws : List ℕ),
        gs'.length = gs.length + (stars.map starSize).sum ∧
        ws.length = stars.length ∧
        Good x1 x2 S' gs' ∧
        (∀ w ∈ ws, w < x1 + x2 + gs'.length) ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, ws.any (fun w => wireVal (x1 + x2) gs' z w) = stars.any (fun st => starEval z st)) := by
  induction stars with
  | nil =>
    intro S gs hG _
    refine ⟨S, gs, [], by simp, rfl, hG, by simp, ?_, ?_⟩
    · intro z i _; rfl
    · intro z; simp
  | cons st rest ih =>
    intro S gs hG hBase
    rcases addStar st (hpos st (by simp)) S gs hG hBase with
      ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
    have hBase1 : ∀ b, S0 x1 x2 b ⊆ S1 b := fun b => Finset.Subset.trans (hBase b) (hSub1 b)
    have hpos_rest : ∀ s ∈ rest, 0 < starSize s := fun s hs => hpos s (List.mem_cons_of_mem st hs)
    rcases ih hpos_rest S1 gs1 hG1 hBase1 with
      ⟨S2, gs2, ws2, hlen2, hwslen2, hG2, hws2_lt, hPres2, hVal2⟩
    refine ⟨S2, gs2, w1 :: ws2, ?_, ?_, hG2, ?_, ?_, ?_⟩
    · simp [hlen2, hlen1, Nat.add_assoc]
    · simp [hwslen2]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact hws2_lt w hw
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [hPres2 z i hi1]
      exact hPres1 z i hi
    · intro z
      simp only [List.any_cons]
      rw [hPres2 z w1 hw1, hVal1 z, hVal2 z]

private lemma circuit_from_good {x1 x2 : ℕ} (S : Bool → Finset ℕ) (gs : List Gate) (out : ℕ)
    (hG : Good x1 x2 S gs) :
    let C : Circuit := ⟨gs, out⟩
    IsAO2 (x1 + x2) C ∧
    (∀ b : Bool, ∀ w ∈ S b,
      (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ u ∈ (gateAt C j).inputs, u ∈ S b) ∧
    (∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ a c : ℕ, ∃ b : Bool, (gateAt C j).inputs = [a, c] ∧ a ∈ S b ∧ c ∈ S (!b)) := by
  rcases hG with ⟨hAO, hRB, _, hSide, hAnd⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg; exact (hAO g hg).1
  · intro j hj i hi; exact hRB j hj i hi
  · intro g hg; exact (hAO g hg).2
  · intro b w hw; exact hSide b w hw
  · intro j hj hop; exact hAnd j hj hop

end PEqualNP.Outside.L_meta_8181.Puncture

open PEqualNP.Outside.L_meta_8181.Puncture in
theorem PEqualNP.Outside.L_meta_8181.Puncture.stars :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),
      (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →
        ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),
          PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧
            x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧
              (∀ (x9 : Fin (x1 + x2) → Bool),
                PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 =
                  Decidable.decide
                    (∃ (x10 : Fin x1) (x11 : Fin x2),
                      (x10, x11) ∈ x3 ∧
                        x9 (Fin.castAdd x2 x10) = Bool.true ∧
                          x9 (Fin.natAdd x1 x11) = Bool.true)) ∧
                have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate :=
                  PEqualNP.MetaComplexity.NestedCover.gateAt x7;
                (∀ (x10 : Bool), ∀ x11 ∈ x8 x10,
                  x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨
                    ∃ x13 < x7.size,
                      x11 = x1 + x2 + x13 ∧
                        (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
                          ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧
                  ∀ x10 < x7.size,
                    (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and →
                      ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool),
                        (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 x15 ∧ x14 ∈ x8 !x15 := by
  intro x1 x2 E A B hcov
  by_cases hE : E = ∅
  · subst hE
    refine ⟨⟨[], x1 + x2⟩, fun _ => ∅, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; cases hg
      · intro j hj; simp at hj
      · intro g hg; cases hg
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro z
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil, Finset.notMem_empty,
        false_and, exists_false, decide_false]
      exact getD_of_ge (List.ofFn z) (x1 + x2) (by simp)
    · intro b w hw; simp at hw
    · intro j hj; simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hj
  · have hE_ne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    let NA : Fin x1 → Finset (Fin x2) := fun p => Finset.univ.filter (fun l => (p, l) ∈ E)
    let NB : Fin x2 → Finset (Fin x1) := fun l => Finset.univ.filter (fun p => (p, l) ∈ E ∧ p ∉ A)
    let A' : Finset (Fin x1) := A.filter (fun p => (NA p).Nonempty)
    let B' : Finset (Fin x2) := B.filter (fun l => (NB l).Nonempty)
    let starsA : List (Star x1 x2) := A'.toList.map (fun p => Sum.inl (p, (NA p).toList))
    let starsB : List (Star x1 x2) := B'.toList.map (fun l => Sum.inr (l, (NB l).toList))
    let stars : List (Star x1 x2) := starsA ++ starsB
    have hpos : ∀ st ∈ stars, 0 < starSize st := by
      intro st hst
      simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
      rcases hst with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hp).2
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hl).2
    have hsumA : (starsA.map starSize).sum = ∑ p ∈ A', (NA p).card := by
      have h1 : (starsA.map starSize) = A'.toList.map (fun p => (NA p).card) := by
        simp [starsA, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hsumB : (starsB.map starSize).sum = ∑ l ∈ B', (NB l).card := by
      have h1 : (starsB.map starSize) = B'.toList.map (fun l => (NB l).card) := by
        simp [starsB, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hcardE : (∑ p ∈ A', (NA p).card) + (∑ l ∈ B', (NB l).card) = E.card := by
      let EA : Finset (Fin x1 × Fin x2) := A'.biUnion (fun p => (NA p).image (fun l => (p, l)))
      let EB : Finset (Fin x1 × Fin x2) := B'.biUnion (fun l => (NB l).image (fun p => (p, l)))
      have hEA_card : EA.card = ∑ p ∈ A', (NA p).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
        · intro p1 _ p2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨l1, _, rfl⟩
          rcases he2 with ⟨l2, _, heq⟩
          exact hne (Prod.mk.inj heq).1.symm
      have hEB_card : EB.card = ∑ l ∈ B', (NB l).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro l _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
        · intro l1 _ l2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨p1, _, rfl⟩
          rcases he2 with ⟨p2, _, heq⟩
          exact hne (Prod.mk.inj heq).2.symm
      have hdisj : Disjoint EA EB := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        simp only [EA, EB, Finset.mem_biUnion, Finset.mem_image] at he1 he2
        rcases he1 with ⟨p1, hp1, l1, _, rfl⟩
        rcases he2 with ⟨l2, _, p2, hp2, heq⟩
        have hp_eq : p2 = p1 := (Prod.mk.inj heq).1
        subst hp_eq
        have hp1A : p2 ∈ A := (Finset.mem_filter.mp hp1).1
        have hp2nA : p2 ∉ A := (Finset.mem_filter.mp hp2).2.2
        exact hp2nA hp1A
      have hunion : EA ∪ EB = E := by
        ext ⟨p, l⟩
        simp only [EA, EB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro (⟨p1, _, l1, hl1, heq⟩ | ⟨l1, _, p1, hp1, heq⟩)
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hl1).2
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hp1).2.1
        · intro hpl
          by_cases hpA : p ∈ A
          · left
            refine ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩,
              l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, rfl⟩
          · right
            have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
            refine ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩,
              p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, rfl⟩
      rw [← hEA_card, ← hEB_card, ← Finset.card_union_of_disjoint hdisj, hunion]
    have hsum_stars : (stars.map starSize).sum = E.card := by
      simp only [stars, List.map_append, List.sum_append, hsumA, hsumB, hcardE]
    have hstars_len : stars.length = A'.card + B'.card := by
      simp [stars, starsA, starsB]
    have hstars_ne : stars ≠ [] := by
      intro hnil
      have h0 : E.card = 0 := by
        rw [← hsum_stars, hnil]; rfl
      exact (Finset.card_pos.mpr hE_ne).ne' h0
    rcases addStars stars hpos (S0 x1 x2) [] (good_init x1 x2) (fun _ => Finset.Subset.rfl) with
      ⟨S1, gs1, ws1, hlen1, hwslen1, hG1, hws1_lt, _, hVal1⟩
    have hws1_ne : ws1 ≠ [] := by
      intro hnil
      apply hstars_ne
      apply List.eq_nil_of_length_eq_zero
      rw [← hwslen1, hnil]
      rfl
    rcases addOrTop ws1 hws1_ne S1 gs1 hG1 hws1_lt with
      ⟨gs2, wOut, hlen2, hG2, _, hPres2, hVal2⟩
    let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs2, wOut⟩
    have hC := circuit_from_good S1 gs2 wOut hG2
    refine ⟨C, S1, hC.1, ?_, ?_, hC.2.1, hC.2.2⟩
    · have hA' : A'.card ≤ A.card := Finset.card_filter_le _ _
      have hB' : B'.card ≤ B.card := Finset.card_filter_le _ _
      have hk_pos : 1 ≤ ws1.length := by
        cases ws1 with
        | nil => exact absurd rfl hws1_ne
        | cons _ _ => simp
      simp only [C, PEqualNP.CircuitLowerBounds.Circuit.size, hlen2, hlen1, List.length_nil,
        Nat.zero_add, hsum_stars, hwslen1, hstars_len]
      omega
    · intro z
      have hcf : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C z = wireVal (x1 + x2) gs2 z wOut := rfl
      rw [hcf, hVal2 z, hVal1 z]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨st, hst, hst_eval⟩
        simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
        rcases hst with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨hzp, l, hl, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hl).2, hzp, hzl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨⟨p, hp, hzp⟩, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hp).2.1, hzp, hzl⟩
      · rintro ⟨p, l, hpl, hzp, hzl⟩
        by_cases hpA : p ∈ A
        · refine ⟨Sum.inl (p, (NA p).toList), ?_, ?_⟩
          · simp only [stars, starsA, List.mem_append, List.mem_map, Finset.mem_toList]
            left
            exact ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨hzp, l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, hzl⟩
        · have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
          refine ⟨Sum.inr (l, (NB l).toList), ?_, ?_⟩
          · simp only [stars, starsB, List.mem_append, List.mem_map, Finset.mem_toList]
            right
            exact ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, hzp⟩, hzl⟩

/- The star construction above follows L-meta-2874. The matching and cover
   construction below follows the Hall argument of R-meta-2685-41. -/

namespace PEqualNP.Outside.L_meta_8181

open PEqualNP.TopForm

open Ten.LeafCore3241 Ten.ForestBipartite3241 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def SmallCoreCovers {k : Nat} (G : SimpleGraph (Fin k)) : Prop :=
  ∀ H : SimpleGraph (Fin k), H ≤ G → Leafless H → ∃ T : Finset (Fin k),
    T.card ≤ 3 ∧ ∀ u v, H.Adj u v → u ∈ T ∨ v ∈ T

private theorem unmatched (n m : ℕ) (E M : Finset (Fin n × Fin m)) (G : SimpleGraph (Fin (n+m)))
    (adj : ∀ u v, G.Adj u v ↔ ∃ e ∈ E,
      (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
      (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2))
    (cyc : ¬G.IsAcyclic)
    (ml : ∀ a ∈ M, ∀ b ∈ M, a.1 = b.1 → a = b)
    (mr : ∀ a ∈ M, ∀ b ∈ M, a.2 = b.2 → a = b) : ∃ e ∈ E, e ∉ M := by
  classical
  by_contra! allM
  have sep (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
    intro eq
    have h := congrArg Fin.val eq
    change a.val = n + b.val at h
    omega
  have unique (v u w : Fin (n+m)) (hu : G.Adj v u) (hw : G.Adj v w) : u = w := by
    obtain ⟨e, he, ⟨ve,ue⟩ | ⟨ue,ve⟩⟩ := (adj _ _).mp hu <;>
      obtain ⟨f, hf, ⟨vf,wf⟩ | ⟨wf,vf⟩⟩ := (adj _ _).mp hw
    · have ef := ml e (allM e he) f (allM f hf) (Fin.castAdd_inj.mp (ve.symm.trans vf))
      simp [ue,wf,ef]
    · exact (sep _ _ (ve.symm.trans vf)).elim
    · exact (sep _ _ (vf.symm.trans ve)).elim
    · have eq := congrArg Fin.val (ve.symm.trans vf)
      have ef := mr e (allM e he) f (allM f hf) (by simpa [Fin.ext_iff] using eq)
      simp [ue,wf,ef]
  obtain ⟨v,w,hw⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cyc
  have h3 := hw.three_le_length
  have eq := unique (w.getVert 1) (w.getVert 0) (w.getVert 2)
    (w.adj_getVert_succ (i:=0) (by omega)).symm (w.adj_getVert_succ (i:=1) (by omega))
  have bad := hw.getVert_injOn' (x₁:=0) (x₂:=2) (by change 0 ≤ w.length-1; omega)
    (by change 2 ≤ w.length-1; omega) eq
  contradiction


private theorem girth (n m : ℕ) (E : Finset (Fin n × Fin m)) (G : SimpleGraph (Fin (n+m)))
    (adj : ∀ u v, G.Adj u v ↔ ∃ e ∈ E,
      (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
      (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2))
    (cyc : ¬G.IsAcyclic)
    (rect : ∀ a b i j, a ≠ b → i ≠ j → ¬ ((a,i) ∈ E ∧ (a,j) ∈ E ∧ (b,i) ∈ E ∧ (b,j) ∈ E)) :
    6 ≤ E.card := by
  classical
  have sep (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
    intro eq
    have h := congrArg Fin.val eq
    change a.val = n + b.val at h
    omega
  have left (a b : Fin n) : ¬G.Adj (Fin.castAdd m a) (Fin.castAdd m b) := by
    rintro h
    obtain ⟨e, _, ⟨_, bad⟩ | ⟨_, bad⟩⟩ := (adj _ _).1 h <;> exact sep _ _ bad
  have right (a b : Fin m) : ¬G.Adj (Fin.natAdd n a) (Fin.natAdd n b) := by
    intro h
    obtain ⟨e, _, ⟨bad,_⟩ | ⟨bad,_⟩⟩ := (adj _ _).1 h <;> exact sep _ _ bad.symm
  have lr (a : Fin n) (b : Fin m) (h : G.Adj (Fin.castAdd m a) (Fin.natAdd n b)) : (a,b) ∈ E := by
    obtain ⟨⟨c,d⟩, he, ⟨ac,bd⟩ | ⟨bad,_⟩⟩ := (adj _ _).1 h
    · have : a = c := Fin.castAdd_inj.mp ac
      have : b = d := by simpa [Fin.ext_iff] using congrArg Fin.val bd
      subst c; subst d; exact he
    · exact (sep _ _ bad.symm).elim
  have square (v w x y : Fin (n+m)) (hv : v ≠ x) (hw : w ≠ y)
      (h1 : G.Adj v w) (h2 : G.Adj w x) (h3 : G.Adj x y) (h4 : G.Adj y v) : False := by
    cases v using Fin.addCases <;> cases w using Fin.addCases <;> cases x using Fin.addCases <;>
      cases y using Fin.addCases <;> first
      | exact (left _ _) h1 | exact (right _ _) h1 | exact (left _ _) h2 | exact (right _ _) h2
      | exact (left _ _) h3 | exact (right _ _) h3
      | exact rect _ _ _ _ (fun h => hv (congrArg _ h)) (fun h => hw (congrArg _ h))
          ⟨lr _ _ h1,lr _ _ h4.symm,lr _ _ h2.symm,lr _ _ h3⟩
      | exact rect _ _ _ _ (fun h => hw (congrArg _ h)) (fun h => hv (congrArg _ h))
          ⟨lr _ _ h1.symm,lr _ _ h2,lr _ _ h4,lr _ _ h3.symm⟩
  obtain ⟨v,w,hw⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cyc
  let col : G.Coloring Bool := SimpleGraph.Coloring.mk (fun u => decide (u.val < n)) (by
    intro i j hij
    obtain ⟨⟨a,b⟩, _, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adj _ _).1 hij <;> simp)
  have ev := (col.even_length_iff_congr w).2 Iff.rfl
  have three := hw.three_le_length
  have six : 6 ≤ w.length := by
    by_contra! h
    obtain ⟨k,hk⟩ := ev
    have four : w.length = 4 := by omega
    have neq (a b : ℕ) (ha : a < 4) (hb : b < 4) (ne : a ≠ b) : w.getVert a ≠ w.getVert b :=
      fun eq => ne (hw.getVert_injOn' (by change a ≤ w.length-1; omega) (by change b ≤ w.length-1; omega) eq)
    apply square (w.getVert 0) (w.getVert 1) (w.getVert 2) (w.getVert 3)
      (neq _ _ (by decide) (by decide) (by decide)) (neq _ _ (by decide) (by decide) (by decide))
      (w.adj_getVert_succ (by omega)) (w.adj_getVert_succ (by omega)) (w.adj_getVert_succ (by omega))
    simpa [←four, SimpleGraph.Walk.getVert_length] using (w.adj_getVert_succ (i:=3) (by omega))
  let edge := fun e : Fin n × Fin m => s(Fin.castAdd m e.1, Fin.natAdd n e.2)
  have sub : G.edgeSet ⊆ ↑(E.image edge) := by
    intro z hz
    induction z using Sym2.inductionOn with
    | _ i j =>
      obtain ⟨e, he, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adj i j).1 hz
      · exact Finset.mem_image_of_mem edge he
      · rw [Sym2.eq_swap]; exact Finset.mem_image_of_mem edge he
  exact six.trans (hw.isTrail.length_le_ncard_edgeSet.trans
    ((Set.ncard_le_ncard sub).trans (by simpa only [Set.ncard_coe_finset] using Finset.card_image_le (s:=E) (f:=edge))))


private theorem counts_irrel {k : Nat} {H : SimpleGraph (Fin k)}
    {I J : DecidableRel H.Adj} : @Counts k H I → @Counts k H J := by
  cases Subsingleton.elim I J
  exact id

theorem price_with_counts (n m : Nat) (E : Finset (Fin n × Fin m)) (C : Circuit)
    (counts : Counts (bip E)) (ao : IsAO2 (n+m) C)
    (h : ∀ x, circuitFun (n+m) C x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)) :
    ∃ (P : Finset (Fin n)) (Q : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧
      E.card + P.card + Q.card ≤ C.size + 1 := by
  classical
  obtain ⟨S,cv,budget⟩ := bound_of_counts (bip E) counts C ao
    (funext (fun x => (h x).trans (formula E x).symm))
  let P := Finset.univ.filter fun i : Fin n => Fin.castAdd m i ∈ S
  let Q := Finset.univ.filter fun i : Fin m => Fin.natAdd n i ∈ S
  let L := P.image (Fin.castAdd m)
  let R := Q.image (Fin.natAdd n)
  have dis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    rintro i hl hr
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨b,_,eq⟩ := Finset.mem_image.mp hr
    exact sides a b eq.symm
  have inc : L ∪ R ⊆ S := by
    intro i hi
    rcases Finset.mem_union.mp hi with l | r
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp l
      exact (Finset.mem_filter.mp ha).2
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp r
      exact (Finset.mem_filter.mp hb).2
  have card := Finset.card_le_card inc
  rw [Finset.card_union_of_disjoint dis] at card
  change (P.image (Fin.castAdd m)).card + (Q.image (Fin.natAdd n)).card ≤ S.card at card
  rw [Finset.card_image_of_injective _ (Fin.castAdd_injective n m),
    Finset.card_image_of_injective _ (Fin.natAdd_injective m n)] at card
  rw [bip_edges] at budget
  refine ⟨P,Q,?_,by omega⟩
  intro e he
  exact (cv (bip_adjacency he)).imp (fun l => Finset.mem_filter.mpr ⟨Finset.mem_univ _,l⟩)
    (fun r => Finset.mem_filter.mpr ⟨Finset.mem_univ _,r⟩)

end PEqualNP.Outside.L_meta_8181

namespace PEqualNP.Outside.L_meta_8181.Pairs

private theorem side_bound {A B : Type*} [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) (P : Finset A) (Q : Finset B)
    (cv : ∀ p ∈ F, p.1 ∈ P ∨ p.2 ∈ Q)
    (partner : ∀ i j, (i,j) ∈ F → ∃ i', i' ≠ i ∧ (i',j) ∈ F)
    (free : ∀ i k j l, i ≠ k → j ≠ l → ¬ ((i,j) ∈ F ∧ (i,l) ∈ F ∧ (k,j) ∈ F ∧ (k,l) ∈ F)) :
    (F.filter (fun e => e.2 ∉ Q)).card ≤ P.card*(P.card-1) := by
  classical
  let alt (e : A × B) := if h : e ∈ F then (partner _ _ h).choose else e.1
  have legal (e : A × B) (h : e ∈ F) : alt e ≠ e.1 ∧ (alt e,e.2) ∈ F := by
    simpa only [alt,dif_pos h] using (partner e.1 e.2 h).choose_spec
  have bound : (F.filter (fun e => e.2 ∉ Q)).card ≤ P.offDiag.card := by
    apply Finset.card_le_card_of_injOn (fun e => (e.1,alt e))
    · intro e he
      obtain ⟨h,nq⟩ := Finset.mem_filter.mp he
      obtain ⟨nd,ok⟩ := legal e h
      exact Finset.mem_offDiag.mpr ⟨(cv e h).resolve_right nq,(cv _ ok).resolve_right nq,nd.symm⟩
    · intro e he f hf h
      have er := Finset.mem_filter.mp he
      have fr := Finset.mem_filter.mp hf
      obtain ⟨nd,ok⟩ := legal e er.1
      have fok := (legal f fr.1).2
      have fst : e.1 = f.1 := congrArg (Prod.fst : A × A → A) h
      have snd : alt e = alt f := congrArg (Prod.snd : A × A → A) h
      apply Prod.ext fst
      by_contra no
      apply free e.1 (alt e) e.2 f.2 nd.symm no
      exact ⟨er.1,by rw [fst]; exact fr.1,ok,by rw [snd]; exact fok⟩
  calc _ ≤ P.offDiag.card := bound
       _ = _ := by rw [Finset.offDiag_card,Nat.mul_sub, Nat.mul_one]

theorem mixed_cover_bound {A B : Type*} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (P : Finset A) (Q : Finset B)
    (cv : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q)
    (partners : ∀ i j, (i,j) ∈ E →
      (∃ l, l ≠ j ∧ (i,l) ∈ E) ∧ (∃ k, k ≠ i ∧ (k,j) ∈ E))
    (free : ∀ i k j l, i ≠ k → j ≠ l → ¬ ((i,j) ∈ E ∧ (i,l) ∈ E ∧ (k,j) ∈ E ∧ (k,l) ∈ E)) :
    E.card ≤ P.card * (P.card - 1) + Q.card * (Q.card - 1) + P.card * Q.card := by
  classical
  let X := E.filter fun e => e.2 ∉ Q
  let Y := E.filter fun e => e.1 ∉ P
  let Z := E.image Prod.swap
  have zm (i : B) (j : A) : (i,j) ∈ Z ↔ (j,i) ∈ E := by
    constructor
    · rintro h
      obtain ⟨⟨a,b⟩,he,eq⟩ := Finset.mem_image.mp h
      cases eq
      exact he
    · intro h
      exact Finset.mem_image.mpr ⟨(j,i),h,rfl⟩
  have top : X.card ≤ P.card*(P.card-1) := side_bound E P Q cv (fun i j h => (partners i j h).2) free
  have back := side_bound Z Q P (by
    rintro ⟨i,j⟩ h
    exact (cv (j,i) ((zm i j).mp h)).symm)
    (by
      intro i j h
      obtain ⟨l,ne,m⟩ := (partners j i ((zm i j).mp h)).1
      exact ⟨l,ne,(zm l j).mpr m⟩)
    (by
      rintro i k j l ik jl ⟨h1,h2,h3,h4⟩
      exact free j l i k jl ik ⟨(zm _ _).mp h1,(zm _ _).mp h3,(zm _ _).mp h2,(zm _ _).mp h4⟩)
  have symmCard : Y.card ≤ (Z.filter (fun e => e.2 ∉ P)).card := by
    apply Finset.card_le_card_of_injOn Prod.swap
    · rintro ⟨i,j⟩ he
      obtain ⟨h,p⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨(zm _ _).mpr h,p⟩
    · intro a _ b _ eq
      simpa only [Prod.swap_swap] using congrArg Prod.swap eq
  have incl : E ⊆ (X ∪ Y) ∪ (P ×ˢ Q) := by
    intro e he
    by_cases h : e.1 ∈ P
    · by_cases k : e.2 ∈ Q
      · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨h,k⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,k⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,h⟩))
  have t := Finset.card_le_card incl
  have u := Finset.card_union_le (X ∪ Y) (P ×ˢ Q)
  have v := Finset.card_union_le X Y
  rw [Finset.card_product] at u
  omega

theorem mixed_four {p q e : Nat} (hp : 0 < p) (hq : 0 < q) (h : p + q ≤ 4)
    (cost : e ≤ p * (p-1) + q * (q-1) + p*q) : e ≤ 9 := by
  have h1 : p ≤ 3 := by omega
  have h2 : q ≤ 3 := by omega
  interval_cases p <;> interval_cases q <;> omega

end PEqualNP.Outside.L_meta_8181.Pairs

namespace PEqualNP.Outside.L_meta_8181.Closure
open Finset
variable {P L : Type*} [DecidableEq P] [DecidableEq L]
def Linear (A : L → Finset P) := ∀ ⦃l k⦄, l ≠ k → ∀ ⦃p q⦄, p ≠ q →
  p ∈ A l → q ∈ A l → p ∈ A k → q ∈ A k → False

theorem pair_budget (A : L → Finset P) (lin : Linear A) (S : Finset L) :
    (∑ l ∈ S, (A l).card.choose 2) ≤ (S.biUnion A).card.choose 2 := by
  classical
  let B := fun l => (A l).powersetCard 2
  have dis : (S : Set L).PairwiseDisjoint B := by
    intro l hl k hk diff
    apply Finset.disjoint_left.mpr
    intro K hK hK'
    obtain ⟨h₁,hc⟩ := Finset.mem_powersetCard.mp hK
    obtain ⟨h₂,_⟩ := Finset.mem_powersetCard.mp hK'
    obtain ⟨p,q,pq,rfl⟩ := Finset.card_eq_two.mp hc
    exact lin diff pq (h₁ (by simp)) (h₁ (by simp)) (h₂ (by simp)) (h₂ (by simp))
  have sub : S.biUnion B ⊆ (S.biUnion A).powersetCard 2 := by
    intro K hK
    obtain ⟨l,hl,h⟩ := Finset.mem_biUnion.mp hK
    obtain ⟨h₁,h₂⟩ := Finset.mem_powersetCard.mp h
    exact Finset.mem_powersetCard.mpr ⟨fun p hp => Finset.mem_biUnion.mpr ⟨l,hl,h₁ hp⟩,h₂⟩
  have h := Finset.card_le_card sub
  rw [Finset.card_biUnion dis,Finset.card_powersetCard] at h
  simpa only [B,Finset.card_powersetCard] using h

open Finset

theorem five_columns {n m : Nat} (E : Finset (Fin n × Fin m))
    (free : ∀ i k j l, i ≠ k → j ≠ l → ¬((i,j)∈E ∧ (i,l)∈E ∧ (k,j)∈E ∧ (k,l)∈E))
    (rows : (E.image Prod.fst).card ≤ 4) (cols : (E.image Prod.snd).card ≤ 5)
    (noLeaf : ∀ i j, (i,j) ∈ E → ∃ k, k ≠ i ∧ (k,j) ∈ E) : E.card ≤ 10 := by
  classical
  let S := E.image Prod.snd
  let N (l : Fin m) := Finset.univ.filter fun p => (p,l) ∈ E
  have nm (p : Fin n) (l : Fin m) : p ∈ N l ↔ (p,l) ∈ E := by simp [N]
  have lin : Linear N := by
    rintro j l jl i k ik a b c d
    exact free i k j l ik jl ⟨(nm i j).mp a,(nm i l).mp c,(nm k j).mp b,(nm k l).mp d⟩
  have sub : S.biUnion N ⊆ E.image Prod.fst := by
    intro u hu
    obtain ⟨l,_,h⟩ := Finset.mem_biUnion.mp hu
    exact Finset.mem_image.mpr ⟨(u,l),(nm u l).mp h,rfl⟩
  have four := (card_le_card sub).trans rows
  have pair := (pair_budget N lin S).trans (Nat.choose_le_choose 2 four)
  change ∑ l ∈ S, (N l).card.choose 2 ≤ 6 at pair
  have sz (l : Fin m) (hl : l ∈ S) : 2 ≤ (N l).card ∧ (N l).card ≤ 4 := by
    obtain ⟨⟨i,j⟩,h,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨k,ne,hk⟩ := noLeaf i j h
    constructor
    · by_contra! small
      change (N j).card < 2 at small
      exact ne (Finset.card_le_one.mp (show (N j).card ≤ 1 by omega) k ((nm _ _).mpr hk) i ((nm _ _).mpr h))
    · exact (Finset.card_le_card (show N j ⊆ S.biUnion N from fun x hx => Finset.mem_biUnion.mpr ⟨j,Finset.mem_image.mpr ⟨(i,j),h,rfl⟩,hx⟩)).trans four
  have inc : E.card ≤ (S.sigma N).card := by
    apply Finset.card_le_card_of_injOn (fun e => Sigma.mk e.2 e.1)
    · intro e he
      exact Finset.mem_sigma.mpr ⟨Finset.mem_image_of_mem _ he,(nm _ _).mpr he⟩
    · intro a _ b _ eq
      exact Prod.ext (congrArg (fun j : Σ _ : Fin m, Fin n => j.2) eq) (congrArg Sigma.fst eq)
  rw [Finset.card_sigma] at inc
  have cmp (l : Fin m) (hl : l ∈ S) : 2*(N l).card ≤ 3+(N l).card.choose 2 := by
    obtain ⟨lo,hi⟩ := sz l hl
    generalize (N l).card = t at lo hi ⊢
    interval_cases t <;> decide
  have twice : 2*∑ l ∈ S, (N l).card ≤ 3*S.card+∑ l ∈ S,(N l).card.choose 2 := by
    calc
      _ = ∑ l ∈ S, 2*(N l).card := Finset.mul_sum ..
      _ ≤ ∑ l ∈ S, (3+(N l).card.choose 2) := Finset.sum_le_sum cmp
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Nat.mul_comm]
  change S.card ≤ 5 at cols
  omega

end PEqualNP.Outside.L_meta_8181.Closure

namespace PEqualNP.Outside.L_meta_8181
open Ten Ten.LeafCore3241 Ten.ForestBipartite3241 Ten.GraphPacking3241 Ten.MatrixPacking3241
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def SmallMatrix {n m : Nat} (E : Finset (Fin n × Fin m)) : Prop :=
   ∀ F ⊆ E, HasPartners F → F.card ≤ 10

def HasMixedCover {n m : Nat} (E : Finset (Fin n × Fin m)) : Prop :=
  ∃ (P : Finset (Fin n)) (Q : Finset (Fin m)), 0 < P.card ∧ 0 < Q.card ∧
    P.card+Q.card ≤ 4 ∧ ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q

theorem from_mixed {n m : Nat} (E : Finset (Fin n × Fin m)) (free : FourFree E)
    (mixed : HasMixedCover E) : SmallMatrix E := by
  obtain ⟨P,Q,hp,hq,size,cov⟩ := mixed
  intro F sub both
  have ff : FourFree F := fun i k j l ik jl ⟨a,b,c,d⟩ => free i k j l ik jl ⟨sub a,sub b,sub c,sub d⟩
  have cost := Pairs.mixed_cover_bound F P Q (fun e he => cov e (sub he)) both ff
  exact (Pairs.mixed_four hp hq size cost).trans (by decide)

def thickCols {n m : Nat} (E : Finset (Fin n × Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun l => ∃ p q : Fin n, p ≠ q ∧ (p,l) ∈ E ∧ (q,l) ∈ E

theorem from_four_five {n m : Nat} (E : Finset (Fin n × Fin m)) (free : FourFree E)
    (rows : (E.image Prod.fst).card ≤ 4) (heavy : (thickCols E).card ≤ 5) : SmallMatrix E := by
  intro F sub both
  have ff : FourFree F := fun i k j l ik jl ⟨a,b,c,d⟩ => free i k j l ik jl ⟨sub a,sub b,sub c,sub d⟩
  have sc : F.image Prod.snd ⊆ thickCols E := by
    rintro l h
    obtain ⟨⟨p,j⟩,he,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨k,ne,hk⟩ := (both p j he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,p,ne,sub hk,sub he⟩
  apply Closure.five_columns F ff ((Finset.card_le_card (Finset.image_subset_image sub)).trans rows)
    ((Finset.card_le_card sc).trans heavy)
  exact fun i j h => (both i j h).2

theorem from_core_census {n m} (E : Finset (Fin n × Fin m)) (free : FourFree E) (small : SmallMatrix E)
    (census : Census) : Counts (bip E) := by
  classical
  apply peel_to_core (bip E)
  intro H _ sub last
  let F := E.filter (fun p => H.Adj (Left p.1) (Right p.2))
  have eq : H = bip F := by
    ext i j
    constructor
    · intro ij
      rcases sub ij with ⟨ne,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
      · exact bip_adjacency (Finset.mem_filter.mpr ⟨he,ij⟩ : e ∈ F)
      · exact (bip_adjacency (Finset.mem_filter.mpr ⟨he,ij.symm⟩ : e ∈ F)).symm
    · rintro ⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
      · exact (Finset.mem_filter.mp he).2
      · exact ((Finset.mem_filter.mp he).2).symm
  have subset : F ⊆ E := Finset.filter_subset _ _
  have freeF : FourFree F := fun p q l s pq ls ⟨a,b,c,d⟩ =>
    free p q l s pq ls ⟨subset a,subset b,subset c,subset d⟩
  have carry {K L : SimpleGraph (Fin (n+m))} [d : DecidableRel K.Adj] [e : DecidableRel L.Adj]
      (same : K = L) (ok : Counts L) : Counts K := by
    subst L
    have sameInst : d = e := Subsingleton.elim _ _
    cases sameInst
    exact ok
  exact carry eq (compressed F freeF (small F subset ((leafless_iff F).mp (eq ▸ last))) (eq ▸ last) census)

theorem posted_on_matrix_core : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), SmallMatrix x3 →   have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);   have x8 : Prop :=     ∃ (x8 : Fin (x1 + x2)),       have x9 : ℕ := (x6.neighborSet x8).ncard;       have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;       (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);   (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) → ¬x6.IsAcyclic → x7 x3 x5 → (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 → x12 = x14) → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.2 = x15.2 → x13 = x15) → x4 ⊆ x3 → (∀ (x15 x16 : Fin x1) (x17 x18 : Fin x2), x15 ≠ x16 → x17 ≠ x18 → ¬((x15, x17) ∈ x3 ∧ (x15, x18) ∈ x3 ∧ (x16, x17) ∈ x3 ∧ (x16, x18) ∈ x3)) → (∀ x16 ∈ x3, ((∀ x18 ∈ x3, x18.1 = x16.1 → x18 = x16) ∨ ∀ x18 ∈ x3, x18.2 = x16.2 → x18 = x16) → (x3.erase x16).Nonempty → x16 ∈ x4) → ¬x8 → ∃ x18 ∈ x3, x18 ∉ x4 ∧ ∃ (x19 : PEqualNP.CircuitLowerBounds.Circuit), x19.size < x5.size ∧ x7 (x3.erase x18) x19 := by
  classical
  intro n m E M C G small fit high adj cyc ok ml mr ss square lp reg
  have graphEq : G = bip E := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    rw [adj]
    constructor
    · rintro ⟨e,he,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
      · exact bip_adjacency he
      · exact (bip_adjacency he).symm
    · rintro ⟨_,⟨e,he,hu,hv⟩ | ⟨e,he,hv,hu⟩⟩
      · exact ⟨e,he,Or.inl ⟨hu,hv⟩⟩
      · exact ⟨e,he,Or.inr ⟨hv,hu⟩⟩
  let c := fun u : Fin (n+m) => decide (u.val < n)
  have color (i j : Fin (n+m)) (e : G.Adj i j) : c i ≠ c j := by
    obtain ⟨⟨a,b⟩,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (adj _ _).mp e <;> simp [c]
  have ge := girth n m E G adj cyc square
  obtain ⟨e,he,excluded⟩ := unmatched n m E M G adj cyc ml mr
  have cnt := from_core_census E square small Ten.NormalizeCores3241.census
  subst G
  obtain ⟨P,Q,cover,cap⟩ := price_with_counts n m E C (counts_irrel cnt) ok.1 (by
    intro x
    rw [ok.2 x]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨p,l,mem,hp,hl⟩; exact ⟨(p,l),mem,hp,hl⟩
    · rintro ⟨⟨p,l⟩,mem,hp,hl⟩; exact ⟨p,l,mem,hp,hl⟩)
  obtain ⟨D,_,ao,dc,ev,_⟩ := Puncture.stars n m (E.erase e) P Q
    (fun f hf => cover f (Finset.mem_of_mem_erase hf))
  rw [Finset.card_erase_of_mem he] at dc
  exact ⟨e,he,excluded,D,by omega,ao,ev⟩

def LightPrice : Prop :=
  ∀ (m : Nat) (E : Finset (Fin 4 × Fin m)),
    (∀ p q l s, p ≠ q → l ≠ s → ¬((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
    (Finset.univ.filter (fun l : Fin m =>
      2 ≤ (Finset.univ.filter (fun p : Fin 4 => (p,l) ∈ E)).card)).card ≤ 5 →
    ∀ T ⊆ E, (∀ e ∈ T, ∀ f ∈ T, e.1 = f.1 → e=f) → (∀ e ∈ T, ∀ f ∈ T, e.2 = f.2 → e=f) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (4+m) C →
    (∀ x : Fin (4+m) → Bool, PEqualNP.MetaComplexity.circuitFun (4+m) C x =
      decide (∃ p l, (p,l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd 4 l) = true)) →
    E.card+T.card-1 ≤ C.size

theorem light_price : LightPrice := by
  classical
  intro m E free small T sub row col C ao ev
  have heavy : thickCols E ⊆ (Finset.univ.filter (fun l : Fin m =>
      2 ≤ (Finset.univ.filter (fun p : Fin 4 => (p,l) ∈ E)).card)) := by
    intro l hl
    obtain ⟨_,p,q,ne,pe,qe⟩ := Finset.mem_filter.mp hl
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    by_contra! lt
    exact ne (Finset.card_le_one.mp (show (Finset.univ.filter (fun v : Fin 4 => (v,l) ∈ E)).card ≤ 1 by omega) p (Finset.mem_filter.mpr ⟨Finset.mem_univ _,pe⟩)
      q (Finset.mem_filter.mpr ⟨Finset.mem_univ _,qe⟩))
  have rows : (E.image Prod.fst).card ≤ 4 := (Finset.card_le_univ _)
  have sm := from_four_five E free rows ((Finset.card_le_card heavy).trans small)
  have z := from_core_census E free sm Ten.NormalizeCores3241.census
  obtain ⟨P,Q,cv,cap⟩ := price_with_counts 4 m E C (counts_irrel z) ao (by
    intro x; rw [ev x]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨p,l,h,hp,hl⟩;exact ⟨(p,l),h,hp,hl⟩
    · rintro ⟨⟨p,l⟩,h,hp,hl⟩;exact ⟨p,l,h,hp,hl⟩)
  have one : (T.filter (fun e => e.1 ∈ P)).card ≤ P.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · exact fun e he => (Finset.mem_filter.mp he).2
    · exact fun e he f hf => row e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
  have two : (T.filter (fun e => e.1 ∉ P)).card ≤ Q.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro e he
      obtain ⟨h,np⟩ := Finset.mem_filter.mp he
      exact (cv e (sub h)).resolve_left np
    · exact fun e he f hf => col e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
  have total := Finset.card_filter_add_card_filter_not (s:=T) (fun e => e.1 ∈ P)
  omega

end PEqualNP.Outside.L_meta_8181

namespace PEqualNP.Outside.L_meta_8181.Support
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

namespace FiniteFour
abbrev V := Fin 4
abbrev R := Fin 8
def raw (masks : List ℕ) (p l : V) : Prop := (masks.getD p.val 0).testBit l.val = true
instance (masks : List ℕ) : DecidableRel (raw masks) := fun p l => inferInstanceAs (Decidable (_ = true))
def rowBit (p : V) (a : R) (l : V) := p=l ∨ a.val.testBit (if l.val<p.val then l.val else l.val-1) = true
instance (p : V) (a : R) (l : V) : Decidable (rowBit p a l) := inferInstanceAs (Decidable (_ ∨ _))
def B (a b c d : R) (p l : V) := rowBit p (if p=0 then a else if p=1 then b else if p=2 then c else d) l
instance (a b c d : R) : DecidableRel (B a b c d) := fun p l => inferInstanceAs (Decidable (rowBit p _ l))
def get (w width i : ℕ) := (w >>> (width*i)) % (2^width)
def coord (w i : ℕ) := Fin.ofNat 4 (get w 2 i)
def height (w i : ℕ) := get w 3 i
def parent (w i : ℕ) := coord (w >>> 24) i
def pattern : ℕ → List ℕ
  | 2 => [1,3,5,14]
  | 3 => [1,3,6,13]
  | 4 => [1,6,10,12]
  | 5 => [1,6,10,13]
  | 6 => [3,5,6,9]
  | 7 => [3,5,9,14]
  | 8 => [3,5,10,12]
  | _ => []
def permcode : Array (List ℕ) := #[[0,1,2,3],[0,1,3,2],[0,2,1,3],[0,2,3,1],[0,3,1,2],[0,3,2,1],[1,0,2,3],[1,0,3,2],[1,2,0,3],[1,2,3,0],[1,3,0,2],[1,3,2,0],[2,0,1,3],[2,0,3,1],[2,1,0,3],[2,1,3,0],[2,3,0,1],[2,3,1,0],[3,0,1,2],[3,0,2,1],[3,1,0,2],[3,1,2,0],[3,2,0,1],[3,2,1,0]]
def perm (i : Fin 24) (p : V) : V := Fin.ofNat 4 ((permcode[i.val]?.getD []).getD p.val 0)
theorem onto : ∀ i : Fin 24, Function.Surjective (perm i) := by decide +kernel
def pmap (w : ℕ) := perm (Fin.ofNat 24 (w % 24))
def lmap (w : ℕ) := perm (Fin.ofNat 24 (w / 24))
def Cert (a b c d : R) (code : ℕ) : Prop :=
  let w := code/16
  if code % 16=0 then
    let p := coord w 0
    let q := coord w 1
    let l := coord w 2
    let k := coord w 3
    p≠q ∧ l≠k ∧ B a b c d p l ∧ B a b c d p k ∧ B a b c d q l ∧ B a b c d q k
  else if code % 16=1 then
    ∀ p l, B a b c d p l →
      (height w p.val < height w (4+l.val) ∧ parent w (4+l.val) = p) ∨
      (height w (4+l.val) < height w p.val ∧ parent w p.val = l)
  else
    code % 16 ≤ 8 ∧ ∀ p l, B a b c d p l ↔ raw (pattern (code % 16)) (pmap w p) (lmap w l)
instance (a b c d : R) (w : ℕ) : Decidable (Cert a b c d w) := by
  unfold Cert
  dsimp only
  split <;> first | infer_instance | split <;> infer_instance

def tables (a b : R) : Array ℕ :=
  match a.val,b.val with
  | 0,0 => #[15668079034369,15668146159617,15685326028801,16218976764417,15702505897985,16776256114689,16793435983873,17327086719489,15668087425025,15668154550273,15685334419457,16218985155073,15702581413889,2224,16253413067521,2224,15672382392321,15672449517569,15689629386753,16223288513025,15706876381185,17052209861377,2480,2480,15944040122881,15944107248129,15961354242561,1200,15978534111745,2224,2480,1200,11321572147201,15681047842817,15698227712001,16231878447617,3760,3760,3760,3760,11321647663105,3248,11872479316737,3248,3760,2224,3760,2224,11325942630401,15957001589505,3504,3504,3760,3760,2480,2480,11597600360961,3248,3504,1200,3760,2224,2480,1200]
  | 0,1 => #[15668080083201,15668147208449,15685394202881,1136,15702506946817,16776257163521,16793512548609,1136,15668088473857,15668155599105,15685402593537,1136,15702582462721,2224,2,1136,15672391831809,15672458957057,15689705951489,1136,15706952945921,3,2480,1136,1120,1120,1120,1120,1120,1120,1120,1120,11321573196033,15681048891649,15698304276737,1136,3760,3760,3760,1136,11321648711937,3248,403,1136,3760,2224,3760,1136,11326019195137,402,3504,1136,3760,3760,2480,1136,1120,1120,1120,1120,1120,1120,1120,1120]
  | 0,2 => #[14577157343233,14577224468481,14594404337665,15128071854593,14611584206849,16778405696001,2416,2416,15670237006337,15670304131585,15687618251265,803,15704730995201,2224,2416,2416,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,10230717581313,15683198472961,772,773,3760,3760,2416,2416,11323797244417,3248,21,3248,3760,2224,2416,2416,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400]
  | 0,3 => #[14577166782721,14577233907969,14594480902401,1136,14611660771585,2160,2416,1136,2144,2144,2144,2144,2144,2144,2144,2144,2400,2400,2400,2400,2400,2400,2400,2400,1120,1120,1120,1120,1120,1120,1120,1120,10230794146049,2003,1989,1136,3760,2160,2416,1136,2144,2144,2144,2144,2144,2144,2144,2144,2400,2400,2400,2400,2400,2400,2400,2400,1120,1120,1120,1120,1120,1120,1120,1120]
  | 0,4 => #[6923525636097,15671369482753,3440,3440,8031635591169,16779479437825,3440,3440,6923534026753,15671377873409,3440,3440,15705805785857,2224,3440,3440,6927828994049,15675689622017,3440,3440,388,389,3440,3440,7199620975105,1203,3440,3440,1173,2224,3440,3440,6936418928641,15684271165953,3440,3440,3760,3760,3440,3440,11324870986241,3248,3440,3440,3760,2224,3440,3440,3424,3424,3424,3424,3424,3424,3424,3424,3424,3424,3424,3424,3424,3424,3424,3424]
  | 0,5 => #[6923593810177,3184,3440,1136,8031712155905,3184,3440,1136,6923602200833,3184,3440,1136,1603,3184,3440,1136,6927905558785,3184,3440,1136,837,3184,3440,1136,1120,1120,1120,1120,1120,1120,1120,1120,6936495493377,3184,3440,1136,3760,3184,3440,1136,3168,3168,3168,3168,3168,3168,3168,3168,3424,3424,3424,3424,3424,3424,3424,3424,1120,1120,1120,1120,1120,1120,1120,1120]
  | 0,6 => #[5832603944961,14580464572929,3440,3440,3696,3696,2416,2416,6925817858561,1602,3440,3440,3696,3696,2416,2416,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400]
  | 0,7 => #[5832680509697,3184,3440,1136,3696,2160,2416,1136,2144,2144,2144,2144,2144,2144,2144,2144,2400,2400,2400,2400,2400,2400,2400,2400,1120,1120,1120,1120,1120,1120,1120,1120,3680,3680,3680,3680,3680,3680,3680,3680,2144,2144,2144,2144,2144,2144,2144,2144,2400,2400,2400,2400,2400,2400,2400,2400,1120,1120,1120,1120,1120,1120,1120,1120]
  | 1,0 => #[15394274869505,15394341994753,15411521863937,1072,15428701733121,16502451949825,16519631819009,1072,15394283260161,15394350385409,15411530254593,1072,15428777249025,2224,2403,1072,15398578227457,15398645352705,15415825221889,1072,15433072216321,2402,2480,1072,1056,1056,1056,1056,1056,1056,1056,1056,11047767982337,15407243677953,15424423547137,1072,3760,3760,3760,1072,11047843498241,3248,2802,1072,3760,2224,3760,1072,11052138465537,2803,3504,1072,3760,3760,2480,1072,1056,1056,1056,1056,1056,1056,1056,1056]
  | 1,1 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 1,2 => #[14303361569025,14303428694273,14320608563457,1072,14337855557889,5603,2416,1072,5908,38,2310,1072,5574,2224,2416,1072,2400,2400,2400,2400,2400,2400,2400,2400,1056,1056,1056,1056,1056,1056,1056,1056,9956988932353,2328,7222,1072,3760,3760,2416,1072,5909,3248,2327,1072,3760,2224,2416,1072,2400,2400,2400,2400,2400,2400,2400,2400,1056,1056,1056,1056,1056,1056,1056,1056]
  | 1,3 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 1,4 => #[6649788596481,5508,3440,1072,7757906942209,5509,3440,1072,6649796987137,438,3440,1072,2696,2224,3440,1072,6654091954433,2710,3440,1072,7590,2695,3440,1072,1056,1056,1056,1056,1056,1056,1056,1056,6662690279681,5974,3440,1072,3760,3760,3440,1072,6003,3248,3440,1072,3760,2224,3440,1072,3424,3424,3424,3424,3424,3424,3424,3424,1056,1056,1056,1056,1056,1056,1056,1056]
  | 1,5 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 1,6 => #[5558875296001,3237,3440,1072,3696,3696,2416,1072,3637,71,3440,1072,3696,3696,2416,1072,2400,2400,2400,2400,2400,2400,2400,2400,1056,1056,1056,1056,1056,1056,1056,1056,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,3680,2400,2400,2400,2400,2400,2400,2400,2400,1056,1056,1056,1056,1056,1056,1056,1056]
  | 1,7 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 2,0 => #[13477645715457,13477712840705,13494892709889,14028543445505,13512072579073,2096,14062903183873,2096,2080,2080,2080,2080,2080,2080,2080,2080,13753598413313,13753665538561,13770912532993,4803,13788025276929,2096,2480,2096,2080,2080,2080,2080,2080,2080,2080,2080,9131205953537,4708,9682037607169,4709,3760,2096,3760,2096,2080,2080,2080,2080,2080,2080,2080,2080,9407158651393,2421,3504,3504,3760,2096,2480,2096,2080,2080,2080,2080,2080,2080,2080,2080]
  | 2,1 => #[13477646764289,13477713889537,13494960883969,1136,13512073627905,2096,3203,2096,2080,2080,2080,2080,2080,2080,2080,2080,4372,774,2502,1136,3110,2096,2480,2096,2080,2080,2080,2080,2080,2080,2080,2080,9131207002369,1622,776,1136,3760,2096,3760,2096,2080,2080,2080,2080,2080,2080,2080,2080,4373,791,3504,1136,3760,2096,2480,2096,2080,2080,2080,2080,2080,2080,2080,2080]
  | 2,2 => #[13479794247937,13479861373185,13497108367617,3202,13514221111553,2096,2416,2096,2080,2080,2080,2080,2080,2080,2080,2080,2400,2400,2400,2400,2400,2400,2400,2400,2080,2080,2080,2080,2080,2080,2080,2080,9133354486017,3910,7974,3079,3760,2096,2416,2096,2080,2080,2080,2080,2080,2080,2080,2080,2400,2400,2400,2400,2400,2400,2400,2400,2080,2080,2080,2080,2080,2080,2080,2080]
  | 2,3 => #[2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064]
  | 2,4 => #[4733092317185,13480936163841,3440,3440,13515295902209,2096,3440,2096,2080,2080,2080,2080,2080,2080,2080,2080,5009179265537,3144,3440,3440,8038,2096,3440,2096,2080,2080,2080,2080,2080,2080,2080,2080,9134429276673,6790,3440,3440,3760,2096,3440,2096,2080,2080,2080,2080,2080,2080,2080,2080,3424,3424,3424,3424,3424,3424,3424,3424,2080,2080,2080,2080,2080,2080,2080,2080]
  | 2,5 => #[4733160491265,3184,3440,1136,4002,2096,3440,2096,2080,2080,2080,2080,2080,2080,2080,2080,6709,3184,3440,1136,3143,2096,3440,2096,2080,2080,2080,2080,2080,2080,2080,2080,6803,3184,3440,1136,3760,2096,3440,2096,2080,2080,2080,2080,2080,2080,2080,2080,3424,3424,3424,3424,3424,3424,3424,3424,2080,2080,2080,2080,2080,2080,2080,2080]
  | 2,6 => #[4735307974913,4003,3440,3440,3696,2096,2416,2096,2080,2080,2080,2080,2080,2080,2080,2080,2400,2400,2400,2400,2400,2400,2400,2400,2080,2080,2080,2080,2080,2080,2080,2080,3680,3680,3680,3680,3680,3680,3680,3680,2080,2080,2080,2080,2080,2080,2080,2080,2400,2400,2400,2400,2400,2400,2400,2400,2080,2080,2080,2080,2080,2080,2080,2080]
  | 2,7 => #[2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064]
  | 3,0 => #[13203841550593,13203908675841,13221088545025,1072,13238268414209,2096,2352,1072,2080,2080,2080,2080,2080,2080,2080,2080,2336,2336,2336,2336,2336,2336,2336,2336,1056,1056,1056,1056,1056,1056,1056,1056,8857401788673,7589,7603,1072,3760,2096,2352,1072,2080,2080,2080,2080,2080,2080,2080,2080,2336,2336,2336,2336,2336,2336,2336,2336,1056,1056,1056,1056,1056,1056,1056,1056]
  | 3,1 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 3,2 => #[2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320]
  | 3,3 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 3,4 => #[4459355277569,8773,3440,1072,8803,2096,2352,1072,2080,2080,2080,2080,2080,2080,2080,2080,2336,2336,2336,2336,2336,2336,2336,2336,1056,1056,1056,1056,1056,1056,1056,1056,8402,8359,3440,1072,3760,2096,2352,1072,2080,2080,2080,2080,2080,2080,2080,2080,2336,2336,2336,2336,2336,2336,2336,2336,1056,1056,1056,1056,1056,1056,1056,1056]
  | 3,5 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 3,6 => #[2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320]
  | 3,7 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 4,0 => #[2525479124993,3120,3076309729793,3120,3633589080065,3120,4184419684865,3120,2525487515649,3120,3076318120449,3120,2788,3120,2789,3120,2529782482945,3120,3080621478401,3120,3909542826753,3120,2480,3120,2801440213505,3120,5203,3120,5109,3120,2480,3120,2538372417537,3120,3089203022337,3120,3760,3120,3760,3120,3104,3104,3104,3104,3104,3104,3104,3104,2814325115393,3120,3504,3120,3760,3120,2480,3120,3104,3104,3104,3104,3104,3104,3104,3104]
  | 4,1 => #[2525480173825,3120,3972,3120,3633590128897,3120,3973,3120,2525488564481,3120,1174,3120,1990,3120,1159,3120,2529791922433,3120,2902,3120,1176,3120,2480,3120,1120,1120,1120,1120,1120,1120,1120,1120,2538373466369,3120,3510,3120,3760,3120,3760,3120,3104,3104,3104,3104,3104,3104,3104,3104,3603,3120,3504,3120,3760,3120,2480,3120,3104,3104,3104,3104,3104,3104,3104,3104]
  | 4,2 => #[1434557433857,3120,1985404819969,3120,3635738661377,3120,2416,3120,2527637096961,3120,1992,3120,4102,3120,2416,3120,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2540521998849,3120,9190,3120,3760,3120,2416,3120,3104,3104,3104,3104,3104,3104,3104,3104,2400,2400,2400,2400,2400,2400,2400,2400,3104,3104,3104,3104,3104,3104,3104,3104]
  | 4,3 => #[1434566873345,3120,6309,3120,6403,3120,2416,3120,2144,2144,2144,2144,2144,2144,2144,2144,2400,2400,2400,2400,2400,2400,2400,2400,1120,1120,1120,1120,1120,1120,1120,1120,4402,3120,4295,3120,3760,3120,2416,3120,3104,3104,3104,3104,3104,3104,3104,3104,2400,2400,2400,2400,2400,2400,2400,2400,3104,3104,3104,3104,3104,3104,3104,3104]
  | 4,4 => #[2528701399297,3120,3440,3120,3636811354369,3120,3440,3120,2528709789953,3120,3440,3120,4310,3120,3440,3120,2533013147905,3120,3440,3120,8374,3120,3440,3120,3602,3120,3440,3120,3479,3120,3440,3120,2541594691841,3120,3440,3120,3760,3120,3440,3120,3104,3104,3104,3104,3104,3104,3104,3104,3424,3424,3424,3424,3424,3424,3424,3424,3104,3104,3104,3104,3104,3104,3104,3104]
  | 4,5 => #[3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088]
  | 4,6 => #[1437788098817,3120,3440,3120,3696,3120,2416,3120,4403,3120,3440,3120,3696,3120,2416,3120,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,2400,3680,3680,3680,3680,3680,3680,3680,3680,3104,3104,3104,3104,3104,3104,3104,3104,2400,2400,2400,2400,2400,2400,2400,2400,3104,3104,3104,3104,3104,3104,3104,3104]
  | 4,7 => #[3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088]
  | 5,0 => #[2251674960129,3120,3376,1072,3359784915201,3120,3376,1072,2251683350785,3120,3376,1072,4901,3120,3376,1072,2255978318081,3120,3376,1072,7203,3120,3376,1072,1056,1056,1056,1056,1056,1056,1056,1056,2264568252673,3120,3376,1072,3760,3120,3376,1072,3104,3104,3104,3104,3104,3104,3104,3104,3360,3360,3360,3360,3360,3360,3360,3360,1056,1056,1056,1056,1056,1056,1056,1056]
  | 5,1 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 5,2 => #[1160761659649,3120,3376,1072,8002,3120,3376,1072,9173,3120,3376,1072,5671,3120,3376,1072,2400,2400,2400,2400,2400,2400,2400,2400,1056,1056,1056,1056,1056,1056,1056,1056,9203,3120,3376,1072,3760,3120,3376,1072,3104,3104,3104,3104,3104,3104,3104,3104,3360,3360,3360,3360,3360,3360,3360,3360,1056,1056,1056,1056,1056,1056,1056,1056]
  | 5,3 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 5,4 => #[3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344]
  | 5,5 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 5,6 => #[3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344]
  | 5,7 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 6,0 => #[335045806081,3120,885876410881,3120,3632,2096,3632,2096,2080,2080,2080,2080,2080,2080,2080,2080,610998503937,3120,7202,3120,3632,2096,3632,2096,2080,2080,2080,2080,2080,2080,2080,2080,3616,3616,3616,3616,3616,3616,3616,3616,2080,2080,2080,2080,2080,2080,2080,2080,3616,3616,3616,3616,3616,3616,3616,3616,2080,2080,2080,2080,2080,2080,2080,2080]
  | 6,1 => #[335046854913,3120,5701,3120,3632,2096,3632,2096,2080,2080,2080,2080,2080,2080,2080,2080,6101,3120,2599,3120,3632,2096,3632,2096,2080,2080,2080,2080,2080,2080,2080,2080,3616,3616,3616,3616,3616,3616,3616,3616,2080,2080,2080,2080,2080,2080,2080,2080,3616,3616,3616,3616,3616,3616,3616,3616,2080,2080,2080,2080,2080,2080,2080,2080]
  | 6,2 => #[337194338561,3120,8003,3120,3632,2096,3632,2096,2080,2080,2080,2080,2080,2080,2080,2080,2400,2400,2400,2400,2400,2400,2400,2400,2080,2080,2080,2080,2080,2080,2080,2080,3616,3616,3616,3616,3616,3616,3616,3616,2080,2080,2080,2080,2080,2080,2080,2080,3616,3616,3616,3616,3616,3616,3616,3616,2080,2080,2080,2080,2080,2080,2080,2080]
  | 6,3 => #[2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064]
  | 6,4 => #[338268080385,3120,3440,3120,3632,2096,3632,2096,2080,2080,2080,2080,2080,2080,2080,2080,8403,3120,3440,3120,3632,2096,3632,2096,2080,2080,2080,2080,2080,2080,2080,2080,3616,3616,3616,3616,3616,3616,3616,3616,2080,2080,2080,2080,2080,2080,2080,2080,3616,3616,3616,3616,3616,3616,3616,3616,2080,2080,2080,2080,2080,2080,2080,2080]
  | 6,5 => #[3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088,3088]
  | 6,6 => #[3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600,3600]
  | 6,7 => #[2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064,2064]
  | 7,0 => #[61241641217,3120,3376,1072,3632,2096,2352,1072,2080,2080,2080,2080,2080,2080,2080,2080,2336,2336,2336,2336,2336,2336,2336,2336,1056,1056,1056,1056,1056,1056,1056,1056,3616,3616,3616,3616,3616,3616,3616,3616,2080,2080,2080,2080,2080,2080,2080,2080,2336,2336,2336,2336,2336,2336,2336,2336,1056,1056,1056,1056,1056,1056,1056,1056]
  | 7,1 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 7,2 => #[2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320]
  | 7,3 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 7,4 => #[3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344,3344]
  | 7,5 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | 7,6 => #[2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320,2320]
  | 7,7 => #[1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040,1040]
  | _,_ => #[]
def lookup (a b c d : R) := (tables a b)[8*c.val+d.val]?.getD 0
end FiniteFour

namespace Pin
open PEqualNP.CircuitLowerBounds
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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end Pin

namespace Pin
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

end Pin

namespace Pin
open PEqualNP.CircuitLowerBounds
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

end Pin

namespace Pin
open PEqualNP.CircuitLowerBounds
theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

end Pin

namespace Pin.PermInputs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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

end Pin.PermInputs

namespace Pin.Forest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Pin.PermInputs
end Pin.Forest

namespace ColumnPeel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {n m : ℕ}
def F (I : Fin n → Fin m → Prop) [DecidableRel I] (x : Fin (n+m) → Bool) : Bool :=
  decide (∃ p l, I p l ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)
def strip (I : Fin n → Fin m → Prop) (S : Finset (Fin m)) (p : Fin n) (l : Fin m) := I p l ∧ l ∉ S
instance (I : Fin n → Fin m → Prop) [DecidableRel I] (S : Finset (Fin m)) : DecidableRel (strip I S) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
theorem sep (p : Fin n) (l : Fin m) : Fin.castAdd m p ≠ Fin.natAdd n l := by
  intro h
  have e := congrArg Fin.val h
  change p.val = n + l.val at e
  omega
theorem injL (l q : Fin m) : Fin.natAdd n l = Fin.natAdd n q ↔ l=q := by
  constructor
  · intro h; exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
  · exact congrArg _
def pt (p : Fin n) (k : Fin (n+m)) := decide (k=Fin.castAdd m p)
def pair (p : Fin n) (l : Fin m) (k : Fin (n+m)) := decide (k=Fin.castAdd m p ∨ k=Fin.natAdd n l)
theorem pt_no (I : Fin n → Fin m → Prop) [DecidableRel I] (p : Fin n) : F I (pt p) = false := by
  simp only [F,pt,decide_eq_false_iff_not,decide_eq_true_iff]
  rintro ⟨a,b,_,_,e⟩
  exact sep p b e.symm
theorem pair_yes (I : Fin n → Fin m → Prop) [DecidableRel I] (p : Fin n) (l : Fin m) (h : I p l) :
    F I (pair p l) = true := by
  apply decide_eq_true
  exact ⟨p,l,h,decide_eq_true (Or.inl rfl),decide_eq_true (Or.inr rfl)⟩
theorem update_point (p : Fin n) (l : Fin m) :
    Function.update (pt p) (Fin.natAdd n l) (!(pt p (Fin.natAdd n l))) = pair p l := by
  funext k
  by_cases hk : k = Fin.natAdd n l
  · subst k
    simpa [pt,pair,Function.update,Ne.symm (sep p l)]
  · simp [Function.update_of_ne hk,hk,pair,pt]
theorem on_iff (I : Fin n → Fin m → Prop) [DecidableRel I] (x : Fin (n+m) → Bool) : F I x = true ↔ ∃ p l, I p l ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true := decide_eq_true_iff
theorem off (I : Fin n → Fin m → Prop) [DecidableRel I] (S : Finset (Fin m)) (l : Fin m) :
    (fun x => F (strip I S) (Function.update x (Fin.natAdd n l) false)) = F (strip I (insert l S)) := by
  funext x
  apply Bool.eq_iff_iff.mpr
  change (F (strip I S) (Function.update x (Fin.natAdd n l) false) = true) ↔ F (strip I (insert l S)) x = true
  rw [on_iff,on_iff]
  simp only [strip,Finset.mem_insert,not_or]
  constructor
  · rintro ⟨p,q,⟨hi,hn⟩,x1,x2⟩
    have ne : q≠l := by rintro rfl; simp at x2
    exact ⟨p,q,⟨hi,ne,hn⟩,by simpa only [Function.update_of_ne (sep p l)] using x1,
      by simpa only [Function.update_of_ne (fun h => ne ((injL q l).mp h))] using x2⟩
  · rintro ⟨p,q,⟨hi,ne,hn⟩,x1,x2⟩
    exact ⟨p,q,⟨hi,hn⟩,by simpa only [Function.update_of_ne (sep p l)] using x1,
      by simpa only [Function.update_of_ne (fun h => ne ((injL q l).mp h))] using x2⟩

def Lower {d : ℕ} (f : (Fin d → Bool) → Bool) (k : ℕ) := ∀ s, HasCircuitSize d f s → k ≤ s

end ColumnPeel

namespace Pin.Forest
open SimpleGraph
end Pin.Forest

namespace Pin.Forest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Pin.PermInputs
open SimpleGraph
noncomputable def F {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)

def Cov {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T

end Pin.Forest

namespace ColumnGraph
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm SimpleGraph
theorem split_ne {n m} (p : Fin n) (l : Fin m) : Fin.castAdd m p ≠ Fin.natAdd n l := by
  intro h
  have e := congrArg Fin.val h
  change p.val = n+l.val at e
  have := p.isLt
  omega

def graph {n m : ℕ} (I : Fin n → Fin m → Prop) : SimpleGraph (Fin (n+m)) where
  Adj a b := ∃ p l, I p l ∧ ((a=Fin.castAdd m p ∧ b=Fin.natAdd n l) ∨
    (b=Fin.castAdd m p ∧ a=Fin.natAdd n l))
  symm := ⟨by rintro a b ⟨p,l,h,h'|h'⟩ <;> exact ⟨p,l,h,by tauto⟩⟩
  loopless := ⟨by rintro v ⟨p,l,_,⟨h,k⟩|⟨h,k⟩⟩ <;> exact split_ne _ _ (h.symm.trans k)⟩

def Free {n m} (I : Fin n → Fin m → Prop) :=
  ∀ p q l k, p≠q → l≠k → ¬ (I p l ∧ I p k ∧ I q l ∧ I q k)

end ColumnGraph

namespace ColumnGraph
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm SimpleGraph
def inc {n m : ℕ} (E : Finset (Fin n × Fin m)) (p : Fin n) (l : Fin m) := (p,l) ∈ E
instance {n m : ℕ} (E : Finset (Fin n × Fin m)) : DecidableRel (inc E) :=
  fun p l => inferInstanceAs (Decidable ((p,l) ∈ E))

instance {n m} (I : Fin n → Fin m → Prop) [DecidableRel I] : DecidableRel (graph I).Adj :=
  fun a b => inferInstanceAs (Decidable (∃ p l, I p l ∧ ((a=Fin.castAdd m p ∧ b=Fin.natAdd n l) ∨
    (b=Fin.castAdd m p ∧ a=Fin.natAdd n l))))

end ColumnGraph

namespace ColumnGraph
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
end ColumnGraph

namespace SupportThree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Pin.PermInputs
open ColumnPeel
abbrev Edges (n m : ℕ) := Finset (Fin n × Fin m)
abbrev ef {n m} (E : Edges n m) := F (fun i j => (i,j) ∈ E)
def C4 {n m} (E : Edges n m) := ∀ p q l s, p ≠ q → l ≠ s →
  ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)
def Rows {n m} (M : Edges n m) := ∀ a ∈ M, ∀ b ∈ M, a.1 = b.1 → a=b
def Cols {n m} (M : Edges n m) := ∀ a ∈ M, ∀ b ∈ M, a.2 = b.2 → a=b
variable {n m h : ℕ}
def Rmap (a : Fin n → Fin h) (e : Fin n × Fin m) : Fin h × Fin m := (a e.1,e.2)
def ren (a : Fin n → Fin h) (E : Edges n m) : Edges h m := E.image (Rmap a)
def sigma (a : Fin n → Fin h) : Fin (n+m) → Fin (h+m) :=
  Fin.addCases (fun p => Fin.castAdd m (a p)) (fun l => Fin.natAdd h l)

theorem rmem {a : Fin n → Fin h} {E : Edges n m} {p l} :
    (p,l) ∈ ren a E ↔ ∃ q, (q,l) ∈ E ∧ a q = p := by
  constructor
  · rintro hz
    obtain ⟨⟨q,t⟩,hqt,eq⟩ := Finset.mem_image.mp hz
    change (a q,t) = (p,l) at eq
    cases eq
    exact ⟨q,hqt,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    exact Finset.mem_image.mpr ⟨(_, _),hq,rfl⟩

theorem efa (a : Fin n → Fin h) (E : Edges n m) (x : Fin (h+m) → Bool) :
    ef E (x ∘ sigma a) = ef (ren a E) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [ef,F,decide_eq_true_iff,Function.comp_apply,sigma,Fin.addCases_left,Fin.addCases_right]
  constructor
  · rintro ⟨p,l,hl,hx,hy⟩; exact ⟨a p,l,rmem.mpr ⟨p,hl,rfl⟩,hx,hy⟩
  · rintro ⟨_,l,hp,hx,hy⟩
    obtain ⟨p,original,rfl⟩ := rmem.mp hp
    exact ⟨p,l,original,hx,hy⟩

theorem rowmem {E : Edges n m} {e} (he : e∈E) : e.1 ∈ E.image Prod.fst :=
  Finset.mem_image_of_mem Prod.fst he
theorem ren_inj {a : Fin n → Fin h} {E S : Edges n m} (sub : S⊆E)
    (hinj : Set.InjOn a (↑(E.image Prod.fst) : Set (Fin n))) : Set.InjOn (Rmap (m := m) a) (↑S : Set (Fin n × Fin m)) := by
  intro i hi j hj eq
  exact Prod.ext (hinj (rowmem (sub hi)) (rowmem (sub hj)) (congrArg Prod.fst eq)) (congrArg (fun v : Fin h × Fin m => v.2) eq)

theorem rfree {a : Fin n → Fin h} {E : Edges n m} (free : C4 E)
    (hinj : Set.InjOn a (↑(E.image Prod.fst) : Set (Fin n))) : C4 (ren a E) := by
  intro p q l s hpq hls
  rintro ⟨pl,ps,ql,qs⟩
  obtain ⟨u,ul,rfl⟩ := rmem.mp pl
  obtain ⟨v,vl,rfl⟩ := rmem.mp ql
  obtain ⟨u',us,hu'⟩ := rmem.mp ps
  obtain ⟨v',vs,hv'⟩ := rmem.mp qs
  have hu : u' = u := hinj (rowmem us) (rowmem ul) hu'
  have hv : v' = v := hinj (rowmem vs) (rowmem vl) hv'
  exact free u v l s (fun e => hpq (congrArg a e)) hls ⟨ul,hu ▸ us,vl,hv ▸ vs⟩

theorem rrows {a : Fin n → Fin h} {E M : Edges n m} (hm : Rows M) (sub : M⊆E)
    (hinj : Set.InjOn a (↑(E.image Prod.fst) : Set (Fin n))) : Rows (ren a M) := by
  rintro i hi j hj eq
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
  exact congrArg (Rmap a) (hm u hu v hv (hinj (rowmem (sub hu)) (rowmem (sub hv)) eq))

theorem rcols {a : Fin n → Fin h} {M : Edges n m} (hm : Cols M) : Cols (ren a M) := by
  rintro i hi j hj eq
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
  exact congrArg (Rmap a) (hm u hu v hv eq)

def sw (E : Edges n m) : Edges m n := E.image Prod.swap
theorem smem {E : Edges n m} {a b} : (b,a) ∈ sw E ↔ (a,b) ∈ E := by simp [sw]
theorem sfree {E : Edges n m} (hf : C4 E) : C4 (sw E) := by
  intro a b c d ne nf
  rintro ⟨ac,ad,bc,bd⟩
  exact hf c d a b nf ne ⟨smem.mp ac,smem.mp bc,smem.mp ad,smem.mp bd⟩
theorem srow {E : Edges n m} (hc : Cols E) : Rows (sw E) := by
  rintro x hx y hy e
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  exact congrArg Prod.swap (hc a ha b hb e)
theorem scol {E : Edges n m} (hr : Rows E) : Cols (sw E) := by
  rintro x hx y hy e
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  exact congrArg Prod.swap (hr a ha b hb e)
theorem scard (E : Edges n m) : (sw E).card = E.card :=
  Finset.card_image_of_injOn (fun _ _ _ _ h => Prod.swap_injective h)

def tau : Fin (n+m) → Fin (m+n) :=
  Fin.addCases (fun p => Fin.natAdd m p) (fun l => Fin.castAdd n l)
theorem efsw (E : Edges n m) (x : Fin (m+n) → Bool) : ef E (x ∘ tau) = ef (sw E) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [ef,F,decide_eq_true_iff,Function.comp_apply,tau,Fin.addCases_left,Fin.addCases_right]
  constructor
  · rintro ⟨p,l,h,px,lx⟩; exact ⟨l,p,smem.mpr h,lx,px⟩
  · rintro ⟨l,p,h,lx,px⟩; exact ⟨p,l,smem.mp h,px,lx⟩

end SupportThree

namespace LocalNormalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
abbrev Edges (n m : ℕ) := Finset (Fin n × Fin m)
def indexed {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I] : Edges n m :=
  Finset.univ.filter (fun e => I e.1 e.2)

theorem mem_indexed {n m} (I : Fin n → Fin m → Prop) [DecidableRel I] (p l) :
    (p,l) ∈ indexed I ↔ I p l := by simp [indexed]

end LocalNormalize

namespace LocalNormalize
open ColumnGraph
def Rising {n m : ℕ} (I : Fin n → Fin m → Prop) (p : Fin n → ℕ) (l : Fin m → ℕ) :=
  ∀ a b c, b ≠ c → I a b → I a c → p a < l b ∨ p a < l c

end LocalNormalize

namespace FiniteFour
open ColumnGraph LocalNormalize ColumnPeel PEqualNP.MetaComplexity
def D : Edges 4 4 := Finset.univ.map ⟨fun p : V => (p,p),fun _ _ h => congrArg Prod.fst h⟩

end FiniteFour

namespace FiniteFour
def rel (masks : List ℕ) (p l : Fin 4) : Prop := (masks.getD p.val 0).testBit l.val = true
instance (masks : List ℕ) : DecidableRel (rel masks) := fun p l => inferInstanceAs (Decidable (_ = true))
end FiniteFour

namespace Partial9840
open PEqualNP.MetaComplexity Pin.PermInputs
open ColumnPeel
theorem feq {n m} (I J : Fin n → Fin m → Prop) [DecidableRel I] [DecidableRel J]
    (h : ∀ p l, I p l ↔ J p l) : F I = F J := by
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [on_iff,on_iff]
  simp_rw [h]

end Partial9840

namespace IncidenceFour
open Finset
variable {P L : Type*} [DecidableEq P] [DecidableEq L]
def Linear (A : L → Finset P) := ∀ ⦃l k⦄, l ≠ k → ∀ ⦃p q⦄, p ≠ q →
  p ∈ A l → q ∈ A l → p ∈ A k → q ∈ A k → False

theorem pair_budget (A : L → Finset P) (lin : Linear A) (S : Finset L) :
    (∑ l ∈ S, (A l).card.choose 2) ≤ (S.biUnion A).card.choose 2 := by
  classical
  let B := fun l => (A l).powersetCard 2
  have dis : (S : Set L).PairwiseDisjoint B := by
    intro l hl k hk diff
    apply Finset.disjoint_left.mpr
    intro K hK hK'
    obtain ⟨h₁,hc⟩ := Finset.mem_powersetCard.mp hK
    obtain ⟨h₂,_⟩ := Finset.mem_powersetCard.mp hK'
    obtain ⟨p,q,pq,rfl⟩ := Finset.card_eq_two.mp hc
    exact lin diff pq (h₁ (by simp)) (h₁ (by simp)) (h₂ (by simp)) (h₂ (by simp))
  have sub : S.biUnion B ⊆ (S.biUnion A).powersetCard 2 := by
    intro K hK
    obtain ⟨l,hl,h⟩ := Finset.mem_biUnion.mp hK
    obtain ⟨h₁,h₂⟩ := Finset.mem_powersetCard.mp h
    exact Finset.mem_powersetCard.mpr ⟨fun p hp => Finset.mem_biUnion.mpr ⟨l,hl,h₁ hp⟩,h₂⟩
  have h := Finset.card_le_card sub
  rw [Finset.card_biUnion dis,Finset.card_powersetCard] at h
  simpa only [B,Finset.card_powersetCard] using h

theorem hall_four (A : L → Finset P) (lin : Linear A) (S : Finset L)
    (hc : S.card ≤ 4) (heavy : ∀ l ∈ S, 2 ≤ (A l).card) :
    ∃ f : S → P, Function.Injective f ∧ ∀ l : S, f l ∈ A l := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' (fun l : S => A l)).mp
  intro U
  let T := U.map (Function.Embedding.subtype _)
  have eq : U.biUnion (fun l : S => A l) = T.biUnion A := by ext p; simp [T]
  rw [eq]
  have small := Finset.card_le_card (show T ⊆ S by intro l h; obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp h;exact x.prop)
  have card : T.card = U.card := Finset.card_map _
  have ones : T.card ≤ ∑ l ∈ T, (A l).card.choose 2 := by
    calc T.card = ∑ _l ∈ T, 1 := by simp
         _ ≤ _ := Finset.sum_le_sum (fun l hl => by
           have hs : l ∈ S := by obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp hl;exact x.prop
           exact Nat.choose_le_choose 2 (heavy l hs))
  have bound := ones.trans (pair_budget A lin T)
  by_cases h : 4 ≤ (T.biUnion A).card
  · omega
  · let u := (T.biUnion A).card
    have hu : u ≤ 3 := by dsimp [u];omega
    have smallChoose : u.choose 2 ≤ u := by interval_cases u <;> decide
    exact card ▸ bound.trans smallChoose

theorem classify_four (A : L → Finset (Fin 4)) (lin : Linear A) (S : Finset L)
    (heavy : ∀ l ∈ S, 2 ≤ (A l).card) (many : 5 ≤ S.card) :
    (S.card = 5 ∨ S.card = 6) ∧ (∀ l ∈ S, (A l).card = 2) ∧
    Set.InjOn A (S : Set L) := by
  classical
  have total := pair_budget A lin S
  have all : (S.biUnion A).card ≤ 4 := by simpa using (Finset.card_le_univ (S.biUnion A))
  have cap := total.trans (Nat.choose_le_choose 2 all)
  have weigh (T : Finset L) (sub : T ⊆ S) : T.card ≤ ∑ l ∈ T, (A l).card.choose 2 := by
    calc T.card = ∑ _l ∈ T, 1 := by simp
         _ ≤ _ := Finset.sum_le_sum (fun l hl => Nat.choose_le_choose 2 (heavy l (sub hl)))
  have max := (weigh S (fun _ h => h)).trans cap
  change S.card ≤ 6 at max
  have deg (l : L) (hl : l ∈ S) : (A l).card = 2 := by
    have h₂ := heavy l hl
    by_contra! no
    have big := Nat.choose_le_choose 2 (show 3 ≤ (A l).card by omega)
    change 3 ≤ _ at big
    have rest := weigh (S.erase l) (Finset.erase_subset _ _)
    have cr := Finset.card_erase_of_mem hl
    have su := Finset.sum_erase_add S (fun x => (A x).card.choose 2) hl
    change _ ≤ 6 at cap
    omega
  refine ⟨by omega,deg,?_⟩
  intro l hl k hk eq
  by_contra diff
  obtain ⟨p,q,pq,h⟩ := Finset.card_eq_two.mp (deg l hl)
  have hp : p ∈ A l := by rw [h];simp
  have hq : q ∈ A l := by rw [h];simp
  exact lin diff pq hp hq (eq ▸ hp) (eq ▸ hq)

end IncidenceFour

namespace IncidenceFour
open Finset
variable {P L : Type} [DecidableEq P] [DecidableEq L] [Fintype L]
def Matchable (A : L → Finset P) (S : Finset L) :=
  ∃ f : S → P, Function.Injective f ∧ ∀ l : S, f l ∈ A l

theorem extend_matching (A : L → Finset P) (H K : Finset L)
    (hh : Matchable A H) (hk : Matchable A K) :
    ∃ J, H ⊆ J ∧ K.card ≤ J.card ∧ Matchable A J := by
  classical
  obtain ⟨h,hi,hm⟩ := hh
  obtain ⟨k,ki,km⟩ := hk
  let D := (↑(Kᶜ) : Type _)
  let B (l : L) : Finset (P ⊕ D) := (A l).disjSum (if l ∈ H then ∅ else univ)
  let fallback (l : L) : P ⊕ D := if lk : l ∈ K then .inl (k ⟨l,lk⟩) else .inr ⟨l,Finset.mem_compl.mpr lk⟩
  have fi : Function.Injective fallback := by
    intro l j eq
    by_cases lk : l ∈ K <;> by_cases jk : j ∈ K
    · exact congrArg Subtype.val (ki (Sum.inl.inj (by simpa only [fallback,dif_pos lk,dif_pos jk] using eq)))
    · simp [fallback,lk,jk] at eq
    · simp [fallback,lk,jk] at eq
    · simp only [fallback,dif_neg lk,dif_neg jk,Sum.inr.injEq] at eq
      exact congrArg Subtype.val eq
  have hall (S : Finset L) : S.card ≤ (S.biUnion B).card := by
    by_cases sub : S ⊆ H
    · let map (l : S) : P ⊕ D := .inl (h ⟨l.val,sub l.prop⟩)
      have inj : Function.Injective map := fun i j e => Subtype.ext (congrArg (fun a : H => a.val) (hi (Sum.inl.inj e)))
      have sits (l : S) : map l ∈ S.biUnion B := Finset.mem_biUnion.mpr ⟨l.val,l.prop, Finset.inl_mem_disjSum.mpr (hm _)⟩
      have b := Fintype.card_le_of_injective (fun l : S => (⟨map l,sits l⟩ : ↑(S.biUnion B))) (fun _ _ e => inj (congrArg Subtype.val e))
      simpa using b
    · obtain ⟨off,mem,free⟩ := Finset.not_subset.mp sub
      apply Finset.card_le_card_of_injOn fallback _ fi.injOn
      intro l ls
      by_cases lk : l ∈ K
      · exact Finset.mem_biUnion.mpr ⟨l,ls,by simpa [fallback,lk,B] using km ⟨l,lk⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨off,mem,by simp [fallback,lk,B,free]⟩
  obtain ⟨g,gi,gm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' B).mp hall
  let J := Finset.univ.filter fun l => (g l).isLeft = true
  have hJ (l : L) : l ∈ J ↔ (g l).isLeft = true := by simp [J]
  have heavy : H ⊆ J := by
    intro l lh
    apply (hJ _).mpr
    have mem := gm l
    cases eq : g l with
    | inl x => rfl
    | inr d => simp [B,lh,eq] at mem
  let val (l : J) : P := (g l.val).getLeft ((hJ _).mp l.prop)
  have gl (l : J) : g l.val = Sum.inl (val l) := by
    have hh := (hJ _).mp l.prop
    cases eq : g l.val with
    | inl p => simp [val,eq]
    | inr d => simp [eq] at hh
  have cj (l : ↑(Jᶜ)) : (g l.val).isRight = true := by
    have hn := Finset.mem_compl.mp l.prop
    cases eq : g l.val with
    | inl x => exact False.elim (hn ((hJ _).mpr (by simp [eq])))
    | inr d => rfl
  let dummy (l : ↑(Jᶜ)) := (g l.val).getRight (cj l)
  have gr (l : ↑(Jᶜ)) : g l.val = Sum.inr (dummy l) := by
    have hh := cj l
    cases eq : g l.val with
    | inl p => simp [eq] at hh
    | inr d => simp [dummy,eq]
  have b := Fintype.card_le_of_injective dummy (fun i j e => Subtype.ext (gi ((gr i).trans ((congrArg Sum.inr e).trans (gr j).symm))))
  change Fintype.card (↑(Jᶜ)) ≤ Fintype.card (↑(Kᶜ)) at b
  simp only [Fintype.card_coe] at b
  have cJ := Finset.card_compl_add_card J
  have cK := Finset.card_compl_add_card K
  refine ⟨J,heavy,by omega,val,?_,?_⟩
  · intro i j e
    exact Subtype.ext (gi ((gl i).trans ((congrArg Sum.inl e).trans (gl j).symm)))
  · intro l
    have mem := gm l.val
    rw [gl l] at mem
    exact Finset.inl_mem_disjSum.mp mem

end IncidenceFour

namespace IncidenceFour
open Finset SupportThree ColumnPeel
variable {m : ℕ}
abbrev E4 (m : ℕ) := Edges 4 m
def neighbors {n : ℕ} (E : Edges n m) (l : Fin m) := univ.filter fun p => (p,l)∈E
def heavy {n : ℕ} (E : Edges n m) := univ.filter fun l => 2 ≤ (neighbors E l).card

theorem graph_linear (E : E4 m) (free : C4 E) : Linear (neighbors E) := by
  intro l k ne p q diff p₁ q₁ p₂ q₂
  exact free p q l k diff ne ⟨(mem_filter.mp p₁).2,(mem_filter.mp p₂).2,(mem_filter.mp q₁).2,(mem_filter.mp q₂).2⟩

theorem matchedColumns {E M : E4 m} (sub : M ⊆ E) (row : Rows M) :
    Matchable (neighbors E) (M.image Prod.snd) := by
  classical
  let K := M.image Prod.snd
  have hit (j : K) : ∃ p, (p,j.val)∈M := by
    obtain ⟨⟨p,l⟩,he,eq⟩ := mem_image.mp j.prop
    exact ⟨p,eq ▸ he⟩
  choose f hf using hit
  refine ⟨f,?_,fun l => mem_filter.mpr ⟨mem_univ _,sub (hf l)⟩⟩
  intro i j eq
  exact Subtype.ext (congrArg Prod.snd (row _ (hf i) _ (hf j) eq))

end IncidenceFour

namespace GridCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
def Good (base : ℕ) (gs : List Gate) := ∀ j (hj : j<gs.length),
  (gs[j].op = .and ∨ gs[j].op = .or) ∧ gs[j].inputs.length = 2 ∧ ∀ i ∈ gs[j].inputs, i < base+j
theorem good_iff (n) (C : Circuit) : Good n C.gates ↔ IsAO2 n C := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro g hg; obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg; exact (h j hj).1
    · intro j hj k hk
      have eq : gateAt C j = C.gates[j] := by simp [gateAt,List.getD,hj]
      exact (h j hj).2.2 k (eq ▸ hk)
    · intro g hg; obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg; exact (h j hj).2.1
  · rintro ⟨hm,hb,ha⟩ j hj
    have eq : gateAt C j = C.gates[j] := by simp [gateAt,List.getD,hj]
    exact ⟨hm _ (List.getElem_mem hj),ha _ (List.getElem_mem hj),fun k hk => hb j hj k (eq ▸ hk)⟩

theorem good_append {n} {a b : List Gate} (ha : Good n a) (hb : Good (n+a.length) b) : Good n (a++b) := by
  intro j hj
  by_cases h : j<a.length
  · simpa only [List.getElem_append_left h] using ha j h
  · have hy : j-a.length < b.length := by simp at hj; omega
    have h1 := hb (j-a.length) hy
    rw [show n+a.length+(j-a.length)=n+j by omega] at h1
    simpa only [List.getElem_append_right (by omega : a.length≤j)] using h1

def name {n m} (f : Fin n → Fin m) (base i : ℕ) :=
  if hi : i<n then (f ⟨i,hi⟩).val else base+(i-n)
def renameG {n m} (f : Fin n → Fin m) (base : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (name f base)⟩
theorem name_lt {n m} (f : Fin n → Fin m) {base j i : ℕ} (hb : m≤base) (hi : i<n+j) :
    name f base i < base+j := by
  unfold name
  split
  next h => have := (f ⟨i,h⟩).isLt; omega
  next => omega

theorem good_rename {n m base gs} (f : Fin n → Fin m) (hb : m≤base) (h : Good n gs) :
    Good base (gs.map (renameG f base)) := by
  intro j hj
  have hj' : j<gs.length := by simpa using hj
  simp only [List.getElem_map,renameG,List.length_map]
  obtain ⟨ho,hl,hi⟩ := h j hj'
  refine ⟨ho,hl,?_⟩
  intro k hk
  obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hk
  exact name_lt f hb (hi i hi')

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]; simp [step]; omega
theorem old (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k<w.length) : (run gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD k false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hk

theorem lookup {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m ≤ W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (z : List Bool) (i : Nat) :
    (W++z).getD (name f W.length i) false = (List.ofFn x++z).getD i false := by
  unfold name
  split
  next hi =>
    rw [List.getD_append _ _ _ _ (by have := (f ⟨i,hi⟩).isLt; omega),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD,hi] using ag ⟨i,hi⟩
  next hi =>
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : W.length ≤ W.length+(i-n)),
      List.getElem?_append_right (by simp;omega : (List.ofFn x).length ≤ i),List.length_ofFn,Nat.add_sub_cancel_left]

theorem sim {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m≤W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (gs : List Gate) (z : List Bool) :
    ∃ endBits, run gs (List.ofFn x ++ z) = List.ofFn x ++ endBits ∧
      run (gs.map (renameG f W.length)) (W++z) = W++endBits := by
  induction gs generalizing z with
  | nil => exact ⟨z,rfl,rfl⟩
  | cons g gs ih =>
    let bit := g.op.eval (g.inputs.map fun i => (List.ofFn x ++ z).getD i false)
    obtain ⟨t,h1,h2⟩ := ih (z++[bit])
    refine ⟨t,?_,?_⟩
    · simpa [run,step,bit,List.append_assoc] using h1
    · have hstep : step (W++z) (renameG f W.length g) = W++(z++[bit]) := by
        simp only [step,renameG,List.map_map,Function.comp_def,lookup f W hw x ag,List.append_assoc,bit]
      change run _ (step (W++z) (renameG f W.length g)) = _
      rw [hstep];exact h2

theorem copy_val {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m≤W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (C : Circuit) :
    (run (C.gates.map (renameG f W.length)) W).getD (name f W.length C.output) false = circuitFun n C x := by
  obtain ⟨z,h1,h2⟩ := sim f W hw x ag C.gates []
  simp only [List.append_nil] at h1 h2
  change _ = (run C.gates (List.ofFn x)).getD C.output false
  rw [h1,h2,lookup _ _ hw x ag]

def Gadget {n} (f : (Fin n → Bool) → Bool) (k : ℕ) := ∃ C : Circuit, IsAO2 n C ∧
  C.output < n + C.gates.length ∧ C.size = k ∧ circuitFun n C = f

theorem output_valid {n} (C : Circuit) (yes : ∃ x, circuitFun n C x = true) :
    C.output<n+C.gates.length := by
  by_contra! h
  obtain ⟨x,hx⟩ := yes
  change (run C.gates (List.ofFn x)).getD C.output false = true at hx
  rw [List.getD_eq_default _ _ (by simpa [len] using h)] at hx;contradiction

theorem relabel {n m} (C : Circuit) (ok : IsAO2 n C) (valid : C.output<n+C.gates.length)
    (f : Fin n → Fin m) :
    Gadget (fun x => circuitFun n C (x ∘ f)) C.size := by
  let D : Circuit := ⟨C.gates.map (renameG f m),name f m C.output⟩
  refine ⟨D,(good_iff m D).mp (good_rename f le_rfl ((good_iff n C).mpr ok)),?_,?_,?_⟩
  · simpa only [D,List.length_map] using name_lt f le_rfl valid
  · simp [Circuit.size,D]
  · funext x
    have h := copy_val f (List.ofFn x) (by simp) (x ∘ f) (fun i => by simp [List.getD]) C
    change (run (C.gates.map (renameG f m)) (List.ofFn x)).getD (name f m C.output) false = _
    simpa only [List.length_ofFn] using h

def op (b : Bool) : GateOp := if b then .and else .or
def bop (b p q : Bool) : Bool := if b then p && q else p || q

theorem last_ok (base i j) (b : Bool) (hi : i<base) (hj : j<base) :
    Good base [⟨op b,[i,j]⟩] := by
  intro k hk
  have eq : k=0 := by simp at hk;omega
  subst k; cases b <;> simp [op,hi,hj]

theorem last_eval (g : Gate) (W : List Bool) : (run [g] W).getD W.length false =
    g.op.eval (g.inputs.map fun i => W.getD i false) := by simp [run,step,List.getD]

theorem append_run (a b : List Gate) (w : List Bool) : run (a++b) w = run b (run a w) := List.foldl_append

theorem join {n k l} {f g : (Fin n → Bool) → Bool} (b : Bool)
    (hA : Gadget f k) (hB : Gadget g l) : Gadget (fun x => bop b (f x) (g x)) (k+l+1) := by
  obtain ⟨A,ao,ab,asz,ae⟩ := hA
  obtain ⟨B,bo,bb,bsz,be⟩ := hB
  let base := n+A.gates.length
  let bs := B.gates.map (renameG (id : Fin n → Fin n) base)
  let bi := name (id : Fin n → Fin n) base B.output
  let ov := base+bs.length
  let newGate : Gate := ⟨op b,[A.output,bi]⟩
  let D : Circuit := ⟨A.gates ++ bs ++ [newGate],ov⟩
  have bl : bs.length = B.gates.length := by simp [bs]
  have bn : n≤base := by simp [base]
  have blo : bi<ov := by unfold ov; rw [bl]; exact name_lt id bn bb
  have alo : A.output<ov := Nat.lt_of_lt_of_le ab (Nat.le_add_right _ _)
  have og : Good base bs := good_rename id bn ((good_iff n B).mpr bo)
  have wa : n+(A.gates++bs).length=ov := by simp [ov,base,Nat.add_assoc]
  refine ⟨D,(good_iff n D).mp (good_append (good_append ((good_iff _ _).mpr ao) og)
    (wa ▸ last_ok ov A.output bi b alo blo)),?_,?_,?_⟩
  · simp [D,ov,base,List.length_append]; omega
  · change A.gates.length=k at asz
    change B.gates.length=l at bsz
    simp [Circuit.size,D,bl,asz,bsz,Nat.add_assoc]
  · funext x
    let W := run A.gates (List.ofFn x)
    let Y := run bs W
    have wl : W.length=base := by simp [W,len,base]
    have yl : Y.length=ov := by simp [Y,len,wl,ov]
    have ah : Y.getD A.output false = f x := by
      rw [show Y.getD A.output false = W.getD A.output false from old bs W A.output (wl ▸ ab)]
      exact congrFun ae x
    have inh (p : Fin n) : W.getD ((id : Fin n → Fin n) p).val false = x p := by
      change (run A.gates (List.ofFn x)).getD p.val false = x p
      rw [old A.gates _ _ (by simp)]
      simp [List.getD]
    have bv := copy_val (id : Fin n → Fin n) W (wl ▸ bn) x inh B
    have bh : Y.getD bi false = g x := by
      change (run (B.gates.map (renameG id base)) W).getD (name id base B.output) false = _
      rw [←wl]
      exact bv.trans (congrFun be x)
    change (run (A.gates++bs++[newGate]) (List.ofFn x)).getD ov false = _
    rw [append_run,append_run]
    change (run [newGate] Y).getD ov false = _
    rw [←yl,last_eval]
    simp only [newGate,List.map_cons,List.map_nil,ah,bh]
    cases b <;> simp [op,bop,GateOp.eval]

theorem atom {n} (u : Fin n) : Gadget (fun x => x u) 0 := by
  let C : Circuit := ⟨[],u.val⟩
  refine ⟨C,(good_iff _ _).mp (by intro j hj; simp [C] at hj),by simpa [C] using u.isLt,rfl,?_⟩
  funext x
  simp [circuitFun,Circuit.eval,Circuit.wires,C,List.getD]

theorem gather {n} {α : Type} (val : α → (Fin n → Bool) → Bool) (cost : α → ℕ) (l : List α)
    (exist : l≠[]) (ok : ∀ a∈l, Gadget (val a) (cost a)) :
    Gadget (fun x => l.any (fun a => val a x)) ((l.map cost).sum+(l.length-1)) := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    have head := ok a List.mem_cons_self
    by_cases hz : l=[]
    · subst l; simpa using head
    have tail := ih hz (fun u hu => ok u (List.mem_cons_of_mem _ hu))
    have both := join false head tail
    have hl : 0<l.length := List.length_pos_iff.mpr hz
    have cnt : cost a+((l.map cost).sum+(l.length-1))+1 =
        ((a::l).map cost).sum+((a::l).length-1) := by simp;omega
    rw [←cnt]
    simpa [bop] using both

def star {n} (st : Fin n × List (Fin n)) (x : Fin n → Bool) := x st.1 && st.2.any x
theorem star_ok {n} (st : Fin n × List (Fin n)) (nonempty : st.2≠[]) : Gadget (star st) st.2.length := by
  have hl : 0<st.2.length := List.length_pos_iff.mpr nonempty
  have g := gather (fun (i : Fin n) (x : Fin n → Bool) => x i) (fun _ => 0)
    st.2 nonempty (fun i _ => atom i)
  have gz : (st.2.map fun _ => (0 : ℕ)).sum=0 := by simp
  rw [gz,Nat.zero_add] at g
  have h := join true (atom st.1) g
  have cnt : 0 + (st.2.length - 1) + 1 = st.2.length := by omega
  rw [cnt] at h
  exact h

theorem sum_constant {α} (l : List α) (k : Nat) : (l.map fun _ => k).sum = l.length*k := by
  induction l with
  | nil => simp
  | cons h t ih => simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,ih];omega

theorem assemble {n m : ℕ} (C : Circuit) (ok : IsAO2 n C) (valid : C.output < n+C.gates.length)
    (copies : List (Fin n → Fin m)) (hc : copies ≠ []) (stars : List (Fin m × List (Fin m)))
    (hs : ∀ st ∈ stars, st.2 ≠ []) :
    ∃ D : Circuit, IsAO2 m D ∧ D.output < m+D.gates.length ∧
      D.size ≤ copies.length*C.size+(copies.length-1)+(stars.map (fun st => st.2.length)).sum+stars.length ∧
      ∀ x, circuitFun m D x = true ↔
        (∃ f ∈ copies, circuitFun n C (x ∘ f) = true) ∨
        ∃ st ∈ stars, x st.1=true ∧ ∃ leaf ∈ st.2, x leaf=true := by
  let A : List (((Fin m → Bool) → Bool) × ℕ) :=
    copies.map (fun f => (fun x => circuitFun n C (x ∘ f),C.size))
  let B : List (((Fin m → Bool) → Bool) × ℕ) := stars.map (fun st => (star st,st.2.length))
  have nne : A++B ≠ [] := by simpa [A,B] using (show ¬(copies=[] ∧ stars=[]) from fun h => hc h.1)
  have hg (q) (hq : q ∈ A++B) : Gadget q.1 q.2 := by
    rcases List.mem_append.mp hq with hh|hh
    · obtain ⟨f,_,rfl⟩ := List.mem_map.mp hh
      exact relabel C ok valid f
    · obtain ⟨st,hst,rfl⟩ := List.mem_map.mp hh
      exact star_ok st (hs st hst)
  obtain ⟨D,hd,hb,sz,eval⟩ := gather (fun q => q.1) (fun q => q.2) (A++B) nne hg
  refine ⟨D,hd,hb,?_,?_⟩
  · rw [sz]
    have hl := List.length_pos_iff.mpr hc
    simp only [A,B,List.map_append,List.map_map,Function.comp_def,List.sum_append,
      List.length_append,List.length_map,sum_constant]
    omega
  · intro x
    rw [eval]
    simp [A,B,star,List.any_eq_true]

end GridCircuit

namespace MonoGraph
open ColumnGraph LocalNormalize ColumnPeel FiniteFour SupportThree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open Pin.PermInputs PEqualNP.MetaComplexity.NestedCover
def LB {n : ℕ} (f : (Fin n → Bool) → Bool) (k : ℕ) :=
  ∀ C : Circuit, IsAO2 n C → (∀ x, circuitFun n C x=f x) → k ≤ C.size

def Sharp {n m : ℕ} (E : SupportThree.Edges n m) :=
  ∀ M ⊆ E, Rows M → Cols M → LB (ef E) (E.card+M.card-1)

theorem pull {n m : ℕ} (π : Fin n → Fin m) (f : (Fin n → Bool) → Bool)
    {k} (known : LB (fun x => f (x ∘ π)) k) : LB f k := by
  intro C ao spec
  let C' := relabel n m π C
  have cs : C'.size=C.size := by
    change (C.gates.map (relGate n m π)).length = C.gates.length
    exact List.length_map _
  have ao' : IsAO2 m C' := by
    obtain ⟨ops,back,fan⟩ := ao
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
      exact ops v hv
    · intro j hj t ht
      have sj : j<C.gates.length := by simpa [C',relabel] using hj
      have get : gateAt C' j = relGate n m π (gateAt C j) := by
        change (C.gates.map (relGate n m π)).getD j _ =
          relGate n m π (C.gates.getD j _)
        simp [sj]
      rw [get] at ht
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
      have h := back j sj z hz
      dsimp only [wmap]
      split
      · have hπ := (π ⟨z,by assumption⟩).isLt;omega
      · omega
    · intro g hg
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
      simpa [relGate] using fan v hv
  rw [←cs]
  apply known C' ao'
  intro x
  have trans := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
  exact trans.trans (spec (x ∘ π))

end MonoGraph

namespace MonoGraph
open Finset ColumnPeel SupportThree FiniteFour
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
abbrev Diagonal := ∀ (I : Fin 4 → Fin 4 → Prop) [DecidableRel I], ColumnGraph.Free I →
  (∀ i,I i i) → LB (F I) ((LocalNormalize.indexed I).card+4-1)

theorem padded {m} (known : Diagonal) (E : Edges 4 m) (free : C4 E)
    (J : Finset (Fin m)) (ne : J.Nonempty) (active : ∀ e∈E, e.2∈J)
    (f : J → Fin 4) (inj : Function.Injective f) (hit : ∀ j : J,(f j,j.val)∈E) :
    LB (ef E) (E.card+J.card-1) := by
  classical
  let b (l : Fin m) := if hl : l∈J then f ⟨l,hl⟩ else 0
  have bval (j : J) : b j.val = f j := by simp [b,j.prop]
  let W := J.attach.image f
  let K := univ \ W
  let g := fun e : Fin 4 × Fin m => (e.1,b e.2)
  let A := E.image g
  let G := A ∪ K.image (fun i : Fin 4 => (i,i))
  have wval (j : J) : f j ∈ W := mem_image.mpr ⟨j,Finset.mem_attach _ _,rfl⟩
  have used {p l : Fin 4} (e : (p,l)∈A) : l∈W := by
    obtain ⟨⟨u,v⟩,hv,eq⟩ := mem_image.mp e
    have t := active _ hv
    obtain ⟨_,rfl⟩ : u=p ∧ b v=l := ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
    exact (bval ⟨v,t⟩).symm ▸ wval ⟨v,t⟩
  have lookup (p : Fin 4) (j : J) : (p,f j)∈A ↔ (p,j.val)∈E := by
    constructor
    · rintro h
      obtain ⟨⟨u,v⟩,he,eq⟩ := mem_image.mp h
      have va := active _ he
      let t : J := ⟨v,va⟩
      have eqt : t=j := inj ((bval t).symm.trans (congrArg Prod.snd eq))
      have rp : u=p := congrArg Prod.fst eq
      exact rp ▸ (congrArg Subtype.val eqt) ▸ he
    · intro h
      exact mem_image.mpr ⟨(p,j.val),h,Prod.ext rfl (bval j)⟩
  have km (i : Fin 4) : i∈K ↔ i∉W := by simp [K]
  have edge (p l : Fin 4) : (p,l)∈G ↔ (p,l)∈A ∨ (l∈K ∧ p=l) := by
    simp only [G,mem_union,mem_image]
    constructor
    · rintro (h|⟨i,hi,eq⟩)
      · exact Or.inl h
      · cases eq;exact Or.inr ⟨hi,rfl⟩
    · rintro (h|⟨hl,rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p,hl,rfl⟩
  have only (p l : Fin 4) (hw : l∈W) (h : (p,l)∈G) : (p,l)∈A :=
    ((edge p l).mp h).elim id (fun t => False.elim ((km l).mp t.1 hw))
  have twice (p q l : Fin 4) (ne : p≠q) (x : (p,l)∈G) (y : (q,l)∈G) : l∈W := by
    by_contra h
    have u := ((edge p l).mp x).resolve_left (fun e => h (used e))
    have v := ((edge q l).mp y).resolve_left (fun e => h (used e))
    exact ne (u.2.trans v.2.symm)
  have no4 : C4 G := by
    intro p q l s pq ls ⟨a,c,d,e⟩
    have wl := twice p q l pq a d
    have ws := twice p q s pq c e
    obtain ⟨j,_,rfl⟩ := mem_image.mp wl
    obtain ⟨t,_,rfl⟩ := mem_image.mp ws
    exact free p q j.val t.val pq (fun eq => ls (congrArg f (Subtype.ext eq)))
      ⟨(lookup p j).mp (only _ _ (wval j) a),(lookup p t).mp (only _ _ (wval t) c),
       (lookup q j).mp (only _ _ (wval j) d),(lookup q t).mp (only _ _ (wval t) e)⟩
  have dia (i : Fin 4) : (i,i)∈G := by
    by_cases hw : i∈W
    · obtain ⟨j,_,rfl⟩ := mem_image.mp hw
      exact (edge _ _).mpr (Or.inl ((lookup _ j).mpr (hit j)))
    · exact (edge _ _).mpr (Or.inr ⟨(km i).mpr hw,rfl⟩)
  have cA : A.card = E.card := by
    apply card_image_of_injOn
    intro e he d hd eq
    let u : J := ⟨e.2,active e he⟩
    let v : J := ⟨d.2,active d hd⟩
    have uv : u=v := inj ((bval u).symm.trans ((congrArg Prod.snd eq).trans (bval v)))
    exact Prod.ext (congrArg (fun x : Fin 4 × Fin 4 => x.1) eq) (congrArg Subtype.val uv)
  have cs : G.card=E.card+K.card := by
    apply Eq.trans (card_union_of_disjoint ?_) ?_
    · apply disjoint_left.mpr
      rintro ⟨p,l⟩ h1 h2
      obtain ⟨i,hi,h⟩ := mem_image.mp h2
      cases h
      exact (km _).mp hi (used h1)
    · rw [cA,card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq)]
  have wsize : W.card=J.card := by simp [W,card_image_of_injective _ inj]
  have ksize : K.card + J.card = 4 := by
    simpa only [wsize,card_univ,Fintype.card_fin] using
      (card_sdiff_add_card_eq_card (Finset.subset_univ W))
  obtain ⟨j,hj⟩ := ne
  let w : J := ⟨j,hj⟩
  intro C ao spec
  let enc : Fin (4+m) → Fin 8 := Fin.addCases (m:=4) (n:=m) (motive:=fun _ => Fin 8)
    (Fin.castAdd 4) (fun l => Fin.natAdd 4 (b l))
  let star (i : Fin 4) : Fin 8 × List (Fin 8) := (Fin.castAdd 4 i,[Fin.natAdd 4 i])
  have valid := GridCircuit.output_valid C ⟨pair (f w) j,(spec _).trans (pair_yes _ _ _ (hit w))⟩
  obtain ⟨D,aoD,_,size,eval⟩ := GridCircuit.assemble C ao valid [enc] (by simp) (K.toList.map star)
    (by intro st h;obtain ⟨i,_,rfl⟩ := List.mem_map.mp h;simp [star])
  have pay : D.size≤C.size+K.card+K.card := by
    simpa [List.map_map,Function.comp_def,star,GridCircuit.sum_constant] using size
  have eqA (x : Fin 8 → Bool) : ef E (x∘enc)=true ↔ ef A x=true := by
    rw [ef,ef,on_iff,on_iff]
    constructor
    · rintro ⟨p,l,e,u,v⟩
      exact ⟨p,b l,mem_image_of_mem g e,by simpa [enc] using u,by simpa [enc] using v⟩
    · rintro ⟨p,l,h,u,v⟩
      obtain ⟨⟨q,t⟩,e,eq⟩ := mem_image.mp h
      change (q,b t)=(p,l) at eq
      cases eq
      exact ⟨p,t,e,by simpa [enc] using u,by simpa [enc] using v⟩
  have output (x : Fin 8 → Bool) : circuitFun 8 D x=ef G x := by
    apply Bool.eq_iff_iff.mpr
    rw [eval,ef,on_iff]
    simp only [List.mem_singleton,exists_eq_left,List.mem_map,Finset.mem_toList]
    constructor
    · rintro (hold|⟨st,⟨i,hi,rfl⟩,u,z,hz,v⟩)
      · obtain ⟨p,l,h,u,v⟩ := (on_iff _ _).mp ((eqA x).mp ((spec _).symm ▸ hold))
        exact ⟨p,l,(edge p l).mpr (Or.inl h),u,v⟩
      · obtain rfl : z=Fin.natAdd 4 i := List.mem_singleton.mp hz
        exact ⟨i,i,(edge i i).mpr (Or.inr ⟨hi,rfl⟩),u,v⟩
    · rintro ⟨p,l,h,u,v⟩
      rcases (edge p l).mp h with he|⟨hl,rfl⟩
      · left
        rw [spec]
        exact (eqA x).mpr ((on_iff _ _).mpr ⟨p,l,he,u,v⟩)
      · right
        exact ⟨star p,⟨p,hl,rfl⟩,u,Fin.natAdd 4 p,by simp [star],v⟩
  have index : LocalNormalize.indexed (fun p l => (p,l)∈G) = G := by
    ext e
    exact LocalNormalize.mem_indexed _ e.1 e.2
  have lb := known (fun p l => (p,l)∈G) no4 dia D aoD output
  rw [index,cs] at lb
  omega
end MonoGraph

namespace ForcedZero
open PEqualNP.MetaComplexity Pin PEqualNP.CircuitLowerBounds PEqualNP.TopForm
def initial {n : ℕ} (v : Fin n) : List Stat :=
  List.ofFn (fun i : Fin n => if i=v then .const false else .wire i)

theorem inv_initial {n : ℕ} (v : Fin n) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (Function.update x v false)) (initial v,[]) := by
  refine ⟨by simp [initial],?_⟩
  intro j
  by_cases hj : j<n
  · let i : Fin n := ⟨j,hj⟩
    by_cases eq : i=v
    · subst v
      simp [initial,hj,i,wiresFrom,Stat.val,Stat.Valid]
    · simp [initial,hj,i,show (⟨j,hj⟩ : Fin n)≠v from eq,Function.update_of_ne eq,Stat.val,Stat.Valid,wiresFrom]
  · simp [initial,List.getD_eq_default,show n≤j by omega,Stat.val,Stat.Valid,List.length_ofFn]

end ForcedZero

namespace MonoCut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Pin
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
private def Legal (n : ℕ) (gs : List Gate) := IsAO2 n ⟨gs,0⟩

private theorem appendGate {n} {gs : List Gate} (old : Legal n gs) (g : Gate)
    (op : g.op=.and ∨ g.op=.or) (arity : g.inputs.length=2)
    (refs : ∀ i∈g.inputs, i<n+gs.length) : Legal n (gs++[g]) := by
  obtain ⟨ops,before,two⟩ := old
  refine ⟨?_,?_,?_⟩
  · intro h hh
    change h∈gs++[g] at hh
    rcases List.mem_append.mp hh with prev|last
    · exact ops h prev
    · simpa only [List.mem_singleton.mp last] using op
  · intro j hj i hi
    change j<(gs++[g]).length at hj
    change i∈((gs++[g]).getD j _).inputs at hi
    by_cases hj' : j<gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact before j hj' i hi
    · have eq : j=gs.length := by simp at hj;omega
      subst j
      rw [getD_snoc_eq] at hi
      exact refs i hi
  · intro h hh
    change h∈gs++[g] at hh
    rcases List.mem_append.mp hh with prev|last
    · exact two h prev
    · simpa only [List.mem_singleton.mp last] using arity

private theorem preserveStep (n : ℕ) (acc : List Stat × List Gate) (old : Legal n acc.2)
    (valid : ∀ i, (acc.1.getD i (Stat.const false)).Valid (n+acc.2.length))
    (g : Gate) (op : g.op=.and ∨ g.op=.or) (arity : g.inputs.length=2) :
    Legal n (elimStep n acc g).2 := by
  have hh : ∃ a b, g.inputs = [a,b] := by
    rcases ha : g.inputs with _|⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩ <;> simp_all
  obtain ⟨a,b,ab⟩ := hh
  have va := valid a
  have vb := valid b
  rcases op with eq|eq <;>
    cases ea : acc.1.getD a (Stat.const false) <;> cases eb : acc.1.getD b (Stat.const false) <;>
    simp only [elimStep,ab,List.map_cons,List.map_nil,ea,eb,eq,simplify,simpAnd,simpOr,
      Option.toList_none,Option.toList_some,List.append_nil] <;> try exact old
  all_goals
    rw [ea] at va
    rw [eb] at vb
    refine appendGate old _ (by simp) rfl ?_
    simpa [Stat.Valid] using And.intro va vb

private theorem preserve (n : ℕ) (gs : List Gate)
    (good : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2)
    (y w : List Bool) (len : y.length=n) (acc : List Stat × List Gate)
    (inv : Inv n y w acc) (old : Legal n acc.2) : Legal n (elim n gs acc).2 := by
  induction gs generalizing w acc with
  | nil => exact old
  | cons g gs ih =>
    rw [elim_cons]
    have h := good g List.mem_cons_self
    apply ih (fun q hq => good q (List.mem_cons_of_mem _ hq)) _ _
    · exact inv_elim n y len [g] w acc (by
        intro q mem
        obtain rfl := List.mem_singleton.mp mem
        exact ⟨by tauto,h.2.le⟩) inv
    · exact preserveStep n acc old (fun i => (inv.2 i).1) g h.1 h.2

private theorem noRead {k : ℕ} (gs : List Gate) (miss : ∀g∈gs, k∉g.inputs)
    (w u : List Bool) (len : w.length=u.length) (same : ∀ i≠k, w.getD i false=u.getD i false) :
    ∀ i≠k, (wiresFrom gs w).getD i false=(wiresFrom gs u).getD i false := by
  induction gs generalizing w u with
  | nil => exact same
  | cons g gs ih =>
    apply ih (fun q hq => miss q (by simp [hq])) (w++[_]) (u++[_]) (by simp [len])
    intro i hi
    by_cases eq : i=w.length
    · subst i
      rw [getD_snoc_eq,len,getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      exact fun i hm => same i (fun eq => miss g (by simp) (eq ▸ hm))
    · rw [getD_snoc_ne _ _ _ _ eq,getD_snoc_ne _ _ _ _ (by omega)]
      exact same i hi

theorem restrict_zero {n : ℕ} (v : Fin n) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (ao : IsAO2 n C) (spec : ∀ x, circuitFun n C x = f x)
    (dep : ∃ x, f (Function.update x v (!x v)) ≠ f x)
    (nc : ∃ x y, f (Function.update x v false) ≠ f (Function.update y v false)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size+1 ≤ C.size ∧
      ∀ x, circuitFun n D x=f (Function.update x v false) := by
  let A := elim n C.gates (ForcedZero.initial v,[])
  have good (g : Gate) (hg : g∈C.gates) := And.intro (ao.1 g hg) (ao.2.2 g hg)
  have ok (g : Gate) (hg : g∈C.gates) : NOk g := by
    obtain ⟨op,sz⟩ := good g hg
    exact ⟨⟨by tauto,sz.le⟩,by rintro h;rcases op with t|t <;> rw [t] at h <;> contradiction⟩
  have ev (x : Fin n → Bool) : (A.1.getD C.output (Stat.const false)).val
      (wiresFrom A.2 (List.ofFn x)) = f (Function.update x v false) := by
    have h := inv_elim n (List.ofFn x) (by simp) C.gates _ _ (fun g hg => (ok g hg).1) (ForcedZero.inv_initial v x)
    exact ((h.2 C.output).2).trans (spec _)
  cases hs : A.1.getD C.output (Stat.const false) with
  | const c =>
    obtain ⟨x,y,h⟩ := nc
    exact False.elim (h (by rw [←ev x,←ev y,hs];rfl))
  | wire j =>
    have iv : (ForcedZero.initial v).getD v.val (.const false) = .const false := by simp [ForcedZero.initial,v.isLt]
    have read : ∃g∈C.gates, v.val∈g.inputs := by
      by_contra! none
      have out : C.output≠v.val := by
        intro eq
        change (elim n C.gates (ForcedZero.initial v,[])).1.getD C.output _ = _ at hs
        rw [eq,elim_getD n v.val _ C.gates _ (by simp [ForcedZero.initial])] at hs
        change (ForcedZero.initial v).getD v.val _ = _ at hs
        rw [iv] at hs;contradiction
      obtain ⟨x,diff⟩ := dep
      apply diff
      rw [←spec _,←spec _]
      apply noRead C.gates none _ _ (by simp) _ C.output out
      intro i ne
      by_cases lt : i<n
      · have h : (⟨i,lt⟩ : Fin n)≠v := fun eq => ne (congrArg Fin.val eq)
        simp [lt,h]
      · simp [lt]
    have save := elim_len_lt n v.val C.gates (ForcedZero.initial v,[]) ok
      (by simp [ForcedZero.initial]) ⟨false,iv⟩ read
    refine ⟨⟨A.2,j⟩,?_,by change A.2.length + 1 ≤ C.gates.length;simpa only [List.length_nil,Nat.zero_add] using save,?_⟩
    · let x : Fin n → Bool := fun _ => false
      have h := preserve n C.gates good _ _ (by simp) _ (ForcedZero.inv_initial v x) (by
        refine ⟨by simp [PEqualNP.EdgeOwnership.AndOrOnly],?_,by simp⟩
        intro j hj
        exact False.elim (Nat.not_lt_zero _ hj))
      exact h
    · intro x
      change (wiresFrom A.2 (List.ofFn x)).getD j false=_
      simpa only [hs,Stat.val] using ev x

open ForcedZero
open ColumnPeel
variable {n m : ℕ}
def Lower {d : ℕ} (f : (Fin d → Bool) → Bool) (k : ℕ) := ∀ (C : Circuit), IsAO2 d C → (∀ x, circuitFun d C x=f x) → k≤C.size
theorem step_lower (I : Fin n → Fin m → Prop) [DecidableRel I] (S : Finset (Fin m)) (l : Fin m)
    (hl : l ∉ S) (ha : ∃ p, I p l) (hr : ∃ p q, strip I (insert l S) p q) {k : ℕ} (_hk : 0 < k)
    (bound : Lower (F (strip I (insert l S))) k) : Lower (F (strip I S)) (k+1) := by
  intro C ao spec
  obtain ⟨p,hp⟩ := ha
  obtain ⟨a,b,hab⟩ := hr
  obtain ⟨D,hD,sz,ev⟩ := restrict_zero (Fin.natAdd n l) _ C ao spec (by
    refine ⟨pt p,?_⟩
    rw [update_point,pt_no,pair_yes _ _ _ ⟨hp,hl⟩]
    decide) (by
    refine ⟨pair a b,pt a,?_⟩
    change (fun x => F _ (Function.update x _ false)) _ ≠ (fun x => F _ (Function.update x _ false)) _
    rw [off,pt_no,pair_yes _ _ _ hab]
    decide)
  have hb := bound D hD (fun x => (ev x).trans (congrFun (off I S l) x))
  omega

theorem delete_many (I : Fin n → Fin m → Prop) [DecidableRel I] (S T : Finset (Fin m))
    (disj : Disjoint S T) (ha : ∀ l ∈ T, ∃ p, I p l) (rem : ∃ p q, strip I (S ∪ T) p q)
    {k : ℕ} (_hk : 0 < k) (bound : Lower (F (strip I (S ∪ T))) k) :
    Lower (F (strip I S)) (k+T.card) := by
  induction T using Finset.induction_on generalizing S with
  | empty =>
    have eq : F (strip I (S ∪ ∅)) = F (strip I S) := by
      funext x
      apply Bool.eq_iff_iff.mpr
      rw [on_iff,on_iff]
      simp only [strip,Finset.union_empty]
    rw [eq] at bound
    simpa using bound
  | @insert l T hlt ih =>
    have eq : insert l S ∪ T = S ∪ insert l T := by ext q; simp
    have hls : l ∉ S := fun e => Finset.disjoint_left.mp disj e (Finset.mem_insert_self _ _)
    have dj : Disjoint (insert l S) T := by
      rw [Finset.disjoint_left]
      intro q hq hT
      rcases Finset.mem_insert.mp hq with rfl|hs
      · exact hlt hT
      · exact Finset.disjoint_left.mp disj hs (Finset.mem_insert_of_mem hT)
    have hrec := ih (insert l S) dj (fun q hq => ha q (Finset.mem_insert_of_mem hq)) (eq ▸ rem) (eq ▸ bound)
    obtain ⟨a,b,hab,hb⟩ := rem
    have hr : strip I (insert l S) a b := ⟨hab,fun h => hb (by
      rcases Finset.mem_insert.mp h with rfl|hs
      · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      · exact Finset.mem_union_left _ hs)⟩
    have next := step_lower I S l hls (ha _ (Finset.mem_insert_self _ _)) ⟨a,b,hr⟩ (by omega) hrec
    simpa [Finset.card_insert_of_notMem hlt,Nat.add_assoc] using next

end MonoCut

namespace MonoGraph
open Finset IncidenceFour SupportThree ColumnPeel
variable {m : ℕ}
theorem retained (known : Diagonal) (E : E4 m) (free : C4 E) (J : Finset (Fin m)) (ne : J.Nonempty)
    (keep : heavy E ⊆ J) (sat : Matchable (neighbors E) J) :
    LB (ef E) (E.card+J.card-1) := by
  classical
  obtain ⟨f,inj,adj⟩ := sat
  let B := E.filter fun e => e.2∈J
  let X := E.filter fun e => e.2∉J
  let T := X.image Prod.snd
  have bc4 : C4 B := fun p q l s hp hl ⟨a,b,c,d⟩ => free p q l s hp hl
    ⟨(mem_filter.mp a).1,(mem_filter.mp b).1,(mem_filter.mp c).1,(mem_filter.mp d).1⟩
  have base := padded known B bc4 J ne (fun _ h => (mem_filter.mp h).2) f inj
    (fun j => mem_filter.mpr ⟨(mem_filter.mp (adj j)).2,j.prop⟩)
  have em (p l) : (p,l)∈B ↔ (p,l)∈E ∧ l∉T := by
    constructor
    · intro h
      obtain ⟨a,b⟩ := mem_filter.mp h
      refine ⟨a,?_⟩
      intro ht
      obtain ⟨e,he,eq⟩ := mem_image.mp ht
      exact (mem_filter.mp he).2 (eq ▸ b)
    · rintro ⟨a,b⟩
      apply mem_filter.mpr;refine ⟨a,?_⟩
      by_contra h;exact b (mem_image.mpr ⟨(p,l),mem_filter.mpr ⟨a,h⟩,rfl⟩)
  let I := fun p l => (p,l)∈E
  have ebase : F (strip I (∅ ∪ T)) = ef B := Partial9840.feq _ _ (by intro p l;simp only [Finset.empty_union,strip,I];exact (em p l).symm)
  have eall : F (strip I ∅) = ef E := Partial9840.feq _ _ (by intro p l;simp [strip,I])
  obtain ⟨j,hj⟩ := ne
  let j' : J := ⟨j,hj⟩
  have memB : (f j',j)∈B := mem_filter.mpr ⟨(mem_filter.mp (adj j')).2,hj⟩
  have bpos := card_pos.mpr (show B.Nonempty from ⟨_,memB⟩)
  have jpos := card_pos.mpr (show J.Nonempty from ⟨j,hj⟩)
  have paid  := MonoCut.delete_many I ∅ T (by simp) (by
    intro l ht;obtain ⟨⟨p,k⟩,he,eq⟩ := mem_image.mp ht;exact ⟨p,eq ▸ (mem_filter.mp he).1⟩)
    (by refine ⟨f j',j,?_⟩; simpa only [Finset.empty_union,strip,I] using (em _ _).mp memB)
    (k:=B.card+J.card-1) (by omega) (ebase ▸ base)
  rw [eall] at paid
  have xc : T.card = X.card := by
    apply card_image_of_injOn
    rintro ⟨p,l⟩ h ⟨q,k⟩ h' eq
    change l=k at eq;subst k
    have small : (neighbors E l).card ≤ 1 := by
      by_contra! large
      exact (mem_filter.mp h).2 (keep (mem_filter.mpr ⟨mem_univ _,large⟩))
    have memP : p ∈ neighbors E l := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).1⟩
    have memQ : q ∈ neighbors E l := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h').1⟩
    exact Prod.ext ((card_le_one.mp small) p memP q memQ) rfl
  have add := card_filter_add_card_filter_not (s:=E) (fun e => e.2∈J)
  change B.card+X.card=E.card at add
  intro C ao spec;have := paid C ao spec;omega

theorem light (known : Diagonal) (E : E4 m) (free : C4 E) (light : (heavy E).card ≤ 4) : Sharp E := by
  classical
  have hm := hall_four (neighbors E) (graph_linear E free) (heavy E) light (fun _ h => (mem_filter.mp h).2)
  have all (M : E4 m) (sub : M ⊆ E) (row : Rows M) (col : Cols M) (non : M.Nonempty) :
      LB (ef E) (E.card+M.card-1) := by
    obtain ⟨J,keep,card,matchJ⟩ := extend_matching (neighbors E) (heavy E) (M.image Prod.snd) hm (matchedColumns sub row)
    have same : (M.image Prod.snd).card=M.card := card_image_of_injOn col
    have pos := card_pos.mpr non
    have res  := retained known E free J (card_pos.mp (by omega)) keep matchJ
    intro C ao spec;have := res C ao spec;omega
  intro M sub row col
  by_cases non : M.Nonempty
  · exact all M sub row col non
  by_cases has : E.Nonempty
  · obtain ⟨e,he⟩ := has
    have bound := all {e} (singleton_subset_iff.mpr he) (by simp [Rows]) (by simp [Cols]) (singleton_nonempty _)
    have emp := Finset.not_nonempty_iff_eq_empty.mp non
    intro C ao spec;have := bound C ao spec;simp [emp] at *;omega
  · have emp := Finset.not_nonempty_iff_eq_empty.mp has
    have emp' := Finset.not_nonempty_iff_eq_empty.mp non
    simp [emp,emp',LB]

end MonoGraph

namespace IncidenceFour
open SupportThree
def pattern (m : ℕ) : Edges 4 m :=
  Finset.univ.filter fun e => (([3,5,6,9,10,12] : List ℕ).getD e.2.val 0).testBit e.1.val = true

end IncidenceFour

namespace IncidenceFour.First
open SupportThree PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Pin PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
abbrev f := ef (pattern 5)
abbrev v (p : Fin 5) := 4+p.val
def col (i : ℕ) := 4 ≤ i ∧ i<9
def value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
abbrev W (pre : List Gate) (x : Fin 9 → Bool) := wiresFrom pre (List.ofFn x)
def Aside (hide : Nat → Prop) (w u : List Bool) := ∀ i, ¬ hide i → w.getD i false = u.getD i false

def toggle (p : Fin 5) (base : Fin 9 → Bool) (b : Bool) (i : Fin 9) : Bool :=
  if i.val=v p then b else base i
def rows (i : Fin 9) := decide (i.val<4)
def pairSeed (r : Fin 4) (q : Fin 5) (i : Fin 9) := decide (i.val=r.val ∨ i.val=v q)
def vn (p : Fin 5) : Fin 9 := ⟨v p,by have := p.isLt;dsimp [v];omega⟩
end IncidenceFour.First
namespace IncidenceFour
open SupportThree PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm First
end IncidenceFour

namespace IncidenceFour
open ColumnPeel SupportThree PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
def dropColumn (j : Fin 5) := (pattern 5).filter fun e => e.2≠j
def dropMatch (j : Fin 5) : Edges 4 5 :=
  match j with
  | 0 => ([(0,1),(1,4),(2,2),(3,3)] : List (Fin 4 × Fin 5)).toFinset
  | 1 => ([(0,0),(1,4),(2,2),(3,3)] : List (Fin 4 × Fin 5)).toFinset
  | 2 => ([(0,0),(1,4),(2,1),(3,3)] : List (Fin 4 × Fin 5)).toFinset
  | 3 => ([(0,0),(1,2),(2,1),(3,4)] : List (Fin 4 × Fin 5)).toFinset
  | 4 => ([(0,0),(1,2),(2,1),(3,3)] : List (Fin 4 × Fin 5)).toFinset
instance (E : Edges 4 5) : Decidable (C4 E) := by unfold C4;infer_instance
instance (E : Edges 4 5) : Decidable (Rows E) := by unfold Rows;infer_instance
instance (E : Edges 4 5) : Decidable (Cols E) := by unfold Cols;infer_instance
end IncidenceFour

namespace MonoGraph
open IncidenceFour ColumnPeel SupportThree PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
end MonoGraph

namespace IncidenceFour
open Finset
private def renumber : Fin 6 → Fin 4 → Fin 4 :=
  ![![2,3,0,1], ![2,0,3,1], ![2,0,1,3], ![0,2,3,1], ![0,2,1,3], ![0,1,2,3]]

private def symmCheck (k : ℕ) : Prop :=
  ∀ T ∈ ((univ : Finset (Fin 4)).powersetCard 2).powersetCard k,
    ∃ j : Fin 6, Function.Injective (renumber j) ∧
      T.image (fun s => s.image (renumber j)) = univ.image (neighbors (pattern k))

private instance (k : ℕ) : Decidable (symmCheck k) := Finset.decidableDforallFinset

set_option maxRecDepth 8192 in
set_option maxHeartbeats 600000 in
private theorem symmFive : symmCheck 5 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 600000 in
private theorem symmSix : symmCheck 6 := by decide +kernel

set_option maxRecDepth 8192 in
theorem canonical_columns {k : ℕ} (hk : k = 5 ∨ k = 6)
    (T : Finset (Finset (Fin 4))) (card : T.card = k)
    (two : ∀ s ∈ T, s.card = 2) :
    ∃ a : Fin 4 → Fin 4, Function.Injective a ∧
      T.image (fun s => s.image a) = univ.image (neighbors (pattern k)) := by
  have sc : symmCheck k := hk.elim (fun h => h ▸ symmFive) (fun h => h ▸ symmSix)
  obtain ⟨j, inj, im⟩ := sc T (mem_powersetCard.mpr
    ⟨fun s hs => mem_powersetCard.mpr ⟨subset_univ _,two s hs⟩,card⟩)
  exact ⟨renumber j,inj,im⟩

set_option maxRecDepth 8192 in
theorem pattern_distinct {k} (hk : k = 5 ∨ k = 6) : Function.Injective (neighbors (pattern k)) := by
  rcases hk with rfl | rfl <;> decide +kernel

set_option maxRecDepth 8192 in
theorem pattern_card {k} (hk : k = 5 ∨ k = 6) : (pattern k).card = 2*k := by
  rcases hk with rfl | rfl <;> decide +kernel

end IncidenceFour

namespace IncidenceFour
open Finset SupportThree ColumnPeel
variable {n m : ℕ}
def retainedEdges (E : Edges n m) (J : Finset (Fin m)) := E.filter fun e => e.2 ∈ J

end IncidenceFour


end PEqualNP.Outside.L_meta_8181.Support

namespace PEqualNP.Outside.L_meta_8181.Subdivision

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def unitsOn (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => u.1 ∈ K)

def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

theorem tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

theorem wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

theorem wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

theorem wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

theorem wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

theorem wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

theorem wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

theorem val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

theorem val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]

abbrev Ref := Bool ⊕ ℕ

def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

def na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r

theorem na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

theorem na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

theorem na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

theorem na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

theorem na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b) := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [na_comb] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h
      subst h; subst hij
      cases t <;> simp [refVal]

theorem na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
    (h : na_comb t a b = Sum.inl r) : na_ok B r := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h; split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h; split_ifs
      · exact ha
      · trivial
    · simp only [na_comb] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h
      subst h; exact ha

theorem na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

theorem na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

theorem na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

theorem na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

theorem na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

theorem na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i ≠ j) :
    Strict n (D ++ [(t, i, j)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA, opB, na_getD_append_lt D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length := by omega
    subst hkD
    simp only [opA, opB, na_getD_snoc]
    exact ⟨hi, hj, hij⟩

theorem na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

theorem na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : na_Good n st) :
    na_Good n (na_step n st g) ∧ (na_step n st g).2.length ≤ st.2.length + 1 ∧
    ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
      (na_step n st g).1.map (refVal (wl (na_step n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨m, D⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨hS, hok⟩ := h
  dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, na_eval0 op hop]
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact na_look_ok _ m hok a
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, na_eval1 op hop,
        na_look_val]
  · have hla := na_look_ok _ m hok a
    have hlb := na_look_ok _ m hok b
    rcases hc : na_comb (na_isAnd op) (na_look m a) (na_look m b) with r | p
    · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact na_comb_ok _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, na_eval2 op hop,
          na_comb_inl _ (wl D (List.ofFn x)) _ _ _ hc, na_look_val]
    · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
      rw [ea] at hla
      rw [eb] at hlb
      have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact na_ok_mono (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length := by
          rw [wl_length, List.length_ofFn]
        have hW' : wl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
            wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
          rw [wl_append]; rfl
        have h1 : m.map (refVal (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
            m.map (refVal (wl D (List.ofFn x))) :=
          List.map_congr_left (fun r hr => na_refVal_wstep _ _ r (by rw [hWlen]; exact hok r hr))
        have h2 : (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (n + D.length) false =
            gop (na_isAnd op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false) := by
          rw [← hWlen, wstep_getD_last, ← na_look_val, ← na_look_val, ea, eb]; rfl
        simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
          h2, na_eval2 op hop]
  · simp at hlen

theorem na_fold_spec (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ st : List Ref × Dag, na_Good n st →
      na_Good n (gs.foldl (na_step n) st) ∧
      (gs.foldl (na_step n) st).2.length ≤ st.2.length + gs.length ∧
      ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
        (gs.foldl (na_step n) st).1.map
            (refVal (wl (gs.foldl (na_step n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro st h; exact ⟨h, by simp, fun x w hw => hw⟩
  | cons g gs ih =>
    intro st h
    obtain ⟨h1, h2, h3⟩ := na_step_spec n st g (hgs g (by simp)) h
    obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
    refine ⟨i1, ?_, fun x w hw => ?_⟩
    · simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)

theorem na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]

theorem exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hmono _ h0
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m, D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val, hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b, fun x => by rw [hev x, hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k, hkn⟩, fun x => by rw [hev x, hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1 := by
        rw [List.length_take]; omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil, Nat.zero_add] at hlen
        unfold Circuit.size
        omega
      · have ho : outW n (D.take (k - n + 1)) = k := by unfold outW; rw [hl]; omega
        rw [ho, val_take D x (k - n + 1) k (by omega) (by omega), hev x, hr]
        rfl

theorem na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

theorem na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

theorem na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
    tag (na_del n j D) k = tag D (na_up j k) ∧
    opA (na_del n j D) k = na_sh (n + j) (opA D (na_up j k)) ∧
    opB (na_del n j D) k = na_sh (n + j) (opB D (na_up j k)) := by
  have e : (na_del n j D).getD k (false, 0, 0) =
      ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
        na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
    simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
    unfold na_up at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

theorem na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) : Strict n (na_del n j D) := by
  intro k hk
  rw [na_del_length n j D hj] at hk
  have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
  have hk2 : (k < j ∧ na_up j k = k) ∨ (j ≤ k ∧ na_up j k = k + 1) := by
    unfold na_up; split_ifs <;> omega
  obtain ⟨ha, hb, hab⟩ := hS _ hk'
  obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
  obtain ⟨-, ea, eb⟩ := na_del_ops n j D k hk'
  rw [ea, eb]
  generalize na_up j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_, ?_, ?_⟩ <;> unfold na_sh <;> split_ifs <;> omega

theorem na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) (x : Fin n → Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (na_del n j D) x w = val D x (na_up (n + j) w) := by
  refine val_unique (na_del_strict hS j hj hf) x (fun u => val D x (na_up (n + j) u))
    (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length n j D hj]; exact hw)
  · have e : na_up (n + j) i = i := by unfold na_up; split_ifs <;> omega
    show val D x (na_up (n + j) i) = x ⟨i, hi⟩
    rw [e]; exact val_input D x i hi
  · rw [na_del_length n j D hj] at hk
    have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
    obtain ⟨et, ea, eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
    have e1 : na_up (n + j) (n + k) = n + na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n + j → na_up (n + j) (na_sh (n + j) a) = a := by
      intro a ha; unfold na_up na_sh; split_ifs <;> omega
    show val D x (na_up (n + j) (n + k)) = gop (tag (na_del n j D) k)
      (val D x (na_up (n + j) (opA (na_del n j D) k)))
      (val D x (na_up (n + j) (opB (na_del n j D) k)))
    rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
    exact val_gate hS x _ hk'

theorem na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        obtain ⟨D', h1, h2, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, h3⟩

theorem exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

theorem normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x) := by
  rcases exists_strict_of_monotone2 (n := n) C hmono with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, hne, hlen, hD⟩
  · obtain ⟨x, hx⟩ := hnc b
    exact absurd (hb x) hx
  · obtain ⟨x, hx⟩ := hnp i
    exact absurd (hi x) hx
  · obtain ⟨D', h1, h2, h3⟩ :=
      exists_strictLive_of_strict (fun x => C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D', h1, by omega, h3⟩

section SurplusFlow

variable {n : ℕ} {D : Dag}

theorem sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

theorem sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

theorem sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

theorem fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

theorem lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

theorem sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

theorem sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

theorem sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

theorem sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

theorem sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
    ∑ w ∈ K, fanout D w = ((arcs D).filter (fun e => src D e ∈ K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := src D)
    (s := (arcs D).filter (fun e => src D e ∈ K)) (t := K)
    (fun e he => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [sb_fanout_arcs hS, Finset.filter_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, rfl⟩; exact ⟨he, hw, rfl⟩
  · rintro ⟨he, -, h⟩; exact ⟨he, h⟩

theorem sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

theorem surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
  obtain ⟨hS, hL, hne⟩ := h
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have h1 : surplusOn D (inner n D) + (inner n D).card = ∑ w ∈ inner n D, fanout D w :=
    sb_surplus_add_card (fun w hw => hL w (sb_mem_inner.mp hw))
  have h2 : ∑ w ∈ inner n D, fanout D w = 2 * D.length := by
    rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
    intro e he
    exact sb_mem_inner.mpr (sb_src_lt hS e he)
  have h3 : (inner n D).card = n + D.length - 1 := Finset.card_range _
  unfold totalSurplus
  omega

theorem totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem Bplus_le_total (n : ℕ) (D : Dag) : Bplus n D ≤ totalSurplus n D := by
  rw [totalSurplus_split]; omega

theorem mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

theorem val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp

theorem supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

theorem supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

theorem supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

theorem carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    (hpred : ∀ j, j < D.length → n + j ∈ K → opA D j ∈ K ∨ opB D j ∈ K) :
    (exitArcs n D K).card + (merges n D K).card = (sources n K).card + surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := hpred j (Finset.mem_range.mp hj)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

theorem sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

theorem sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
    (sources n (carrierT n D T)).card = T.card := by
  have himg : sources n (carrierT n D T) = T.image (fun v : Fin n => v.val) := by
    ext w
    simp only [sources, carrierT, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨-, v, hv⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_inter, Finset.mem_singleton] at hv
      exact ⟨v, hv.2, by rw [hv.1]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨by have := v.isLt; omega, v, ?_⟩, v.isLt⟩
      rw [supp_input]; simp [hv]
  rw [himg, Finset.card_image_of_injective _ Fin.val_injective]

theorem carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card =
      T.card + surplusOn D (carrierT n D T) := by
  rw [← sb_sources_carrierT D T]
  refine carrier_flow h _ (sb_carrierT_sub T hout) (fun j hj hK => ?_)
  obtain ⟨ha, hb, -⟩ := h.1 j hj
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hK ⊢
  obtain ⟨v, hv⟩ := hK.2
  rw [Finset.mem_inter, supp_gate h.1 j hj] at hv
  split_ifs at hv with ht
  · rw [Finset.mem_inter] at hv
    exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩
  · rw [Finset.mem_union] at hv
    rcases hv.1 with h1 | h1
    · exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩
    · exact Or.inr ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩

theorem mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

theorem card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

theorem mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

theorem mem_ineligSet {v : Fin n} :
    v ∈ ineligSet n D ↔ ∀ w, v ∈ supp n D w → fanout D w ≤ 1 := by
  rw [ineligSet, Finset.mem_sdiff, mem_eligSet]
  constructor
  · rintro ⟨-, h⟩ w hw
    by_contra hc
    exact h ⟨w, by omega, hw⟩
  · intro h
    refine ⟨Finset.mem_univ v, ?_⟩
    rintro ⟨w, hw, hv⟩
    have := h w hv
    omega

theorem sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

theorem sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

theorem reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    reservedUnits n D b ⊆ unitsPlus n D := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨h2, hs⟩ := hb v hv
  have h1 : 1 ≤ fanout D (b v) := by omega
  rw [unitsPlus, Finset.mem_filter, mem_units]
  refine ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS h1), ?_⟩, ?_⟩
  · show 0 + 1 < fanout D (b v)
    omega
  · show (supp n D (b v)).Nonempty
    rw [hs]; exact Finset.singleton_nonempty v

theorem card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

theorem elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

theorem card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

theorem surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) = (T ∩ eligSet n D).card +
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
  have h1 : surplusOn D (carrierT n D T) =
      ((units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
    rw [sb_card_units_filter n D (fun w => (supp n D w ∩ T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      have := sb_mem_inner.mp hw.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hw.2⟩
    · rw [carrierT, Finset.mem_filter] at hw
      have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, hw.2⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) ∪
        (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · exact Or.inl ⟨hr, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1, hu.2.mono Finset.inter_subset_left⟩, hr⟩, hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(Finset.mem_filter.mp (hsub hu.1)).1, hu.2⟩
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : Disjoint ((reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty))
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (T ∩ eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) := by
    rw [reservedUnits, Finset.filter_image]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hv, hne⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty] at hne
      exact ⟨hne, hv⟩
    · rintro ⟨hT, hv⟩
      refine ⟨hv, ?_⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty]
      exact hT
  rw [h1, h2, Finset.card_union_of_disjoint h3, h4,
    Finset.card_image_of_injOn ((sb_reserved_inj b hb).mono
      (Finset.coe_subset.mpr Finset.inter_subset_right))]

theorem surplus_carrierT_le (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) + (eligSet n D).card ≤
      (T ∩ eligSet n D).card + Bplus n D := by
  have h1 := surplus_carrierT_eq hS b hb T
  have h2 := card_residual hS b hb
  have h3 := Finset.card_filter_le (residualUnits n D b)
    (fun u => (supp n D u.1 ∩ T).Nonempty)
  omega

end SurplusFlow

def liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))

theorem tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

theorem tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

theorem tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

theorem liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

theorem tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

theorem tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

theorem relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

theorem tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

theorem tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

theorem tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

theorem relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

theorem relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (w : ℕ) :
    val (relabel σ D) x (liftP σ w) = val D (fun i => x (σ i)) w := by
  by_cases hw : w < n + D.length
  · refine (val_unique (relabel_strict σ hS) x
      (fun w' => val D (fun i => x (σ i)) (liftP σ⁻¹ w')) ?_ ?_ (liftP σ w) ?_).trans ?_
    · intro i hi
      show val D (fun i => x (σ i)) (liftP σ⁻¹ i) = x ⟨i, hi⟩
      rw [tr_liftP_lt σ⁻¹ hi, val_input D _ _ (σ⁻¹ ⟨i, hi⟩).isLt]
      simp
    · intro j hj
      rw [relabel_length] at hj
      show val D (fun i => x (σ i)) (liftP σ⁻¹ (n + j)) =
        gop (tag (relabel σ D) j) (val D (fun i => x (σ i)) (liftP σ⁻¹ (opA (relabel σ D) j)))
          (val D (fun i => x (σ i)) (liftP σ⁻¹ (opB (relabel σ D) j)))
      rw [tr_liftP_ge σ⁻¹ (Nat.le_add_right n j), tr_tag σ D j hj, tr_opA σ D j hj,
        tr_opB σ D j hj, liftP_inv, liftP_inv, val_gate hS _ j hj]
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · show val D (fun i => x (σ i)) (liftP σ⁻¹ (liftP σ w)) = _
      rw [liftP_inv]
  · have hw' := Nat.not_lt.mp hw
    rw [tr_liftP_ge σ (le_trans (Nat.le_add_right _ _) hw'),
      val_ge _ _ _ (by rw [relabel_length]; exact hw'), val_ge _ _ _ hw']

theorem relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

theorem relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
    Live n (relabel σ D) := by
  rcases eq_or_ne D [] with rfl | hne
  · exact hL
  · intro w' hw'
    rw [relabel_length] at hw'
    have hpos := List.length_pos_iff.mpr hne
    rw [← tr_liftP_inv' σ w', relabel_fanout]
    apply hL
    by_cases h : w' < n
    · have := (tr_liftP_lt_iff σ⁻¹ le_rfl w').mpr h
      omega
    · rw [tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]; exact hw'

theorem relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

theorem relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]

theorem tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

theorem relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

theorem tr_sum_liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (P : ℕ → Prop)
    [DecidablePred P] (g : ℕ → ℕ) :
    ∑ w ∈ (Finset.range m).filter (fun w => P (liftP σ w)), g (liftP σ w) =
      ∑ w ∈ (Finset.range m).filter P, g w := by
  refine Finset.sum_nbij' (liftP σ) (liftP σ⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ hm a).mpr ha.1, ha.2⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ⁻¹ hm a).mpr ha.1, by rw [tr_liftP_inv']; exact ha.2⟩
  · intro a _; exact liftP_inv σ a
  · intro a _; exact tr_liftP_inv' σ a
  · intro a _; rfl

theorem tr_surplus_filter {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ w, Q (liftP σ w) ↔ P w) :
    surplusOn (relabel σ D) ((inner n (relabel σ D)).filter Q) =
      surplusOn D ((inner n D).filter P) := by
  rcases eq_or_ne D [] with rfl | hne
  · simp [surplusOn, relabel, fanout, readers]
  · have hpos := List.length_pos_iff.mpr hne
    have hm : n ≤ n + D.length - 1 := by omega
    unfold surplusOn inner
    rw [relabel_length]
    exact (tr_sum_liftP σ hm Q (fun w => fanout (relabel σ D) w - 1)).symm.trans
      (Finset.sum_congr (Finset.filter_congr fun w _ => hPQ w)
        fun w _ => by rw [relabel_fanout])

theorem relabel_Bplus {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Bplus n (relabel σ D) = Bplus n D :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)

def edgeList : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11),
    (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def HeawoodEdge (x : Fin 14 → Bool) : Prop :=
  ∃ u v : Fin 14, (u.val, v.val) ∈ edgeList ∧ x u = true ∧ x v = true

abbrev Adj (u v : Fin 14) : Prop := (u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList

def inc (p l : Fin 7) : Bool :=
  (([11, 69, 98, 49, 88, 44, 22] : List ℕ).getD l.val 0).testBit p.val

def hc_adjB (u v : Fin 14) : Bool :=
  (([1408, 8832, 12544, 6272, 11264, 5632, 2816, 11, 69, 98, 49, 88, 44, 22] : List ℕ).getD
    u.val 0).testBit v.val

def IsCover (S : Finset (Fin 14)) : Prop := ∀ u v : Fin 14, Adj u v → u ∈ S ∨ v ∈ S

def IsIndep (I : Finset (Fin 14)) : Prop := ∀ u ∈ I, ∀ v ∈ I, ¬ Adj u v

def matching : List (Fin 14 × Fin 14) :=
  [(0, 7), (1, 13), (2, 8), (3, 12), (4, 11), (5, 10), (6, 9)]

def hc_mate (v : Fin 14) : Fin 14 :=
  Fin.ofNat 14 (([7, 13, 8, 12, 11, 10, 9, 0, 2, 6, 5, 4, 3, 1] : List ℕ).getD v.val 0)

def IsAut (σ : Equiv.Perm (Fin 14)) : Prop := ∀ u v : Fin 14, Adj (σ u) (σ v) ↔ Adj u v

def hc_ofList (l : List ℕ) (v : Fin 14) : Fin 14 := Fin.ofNat 14 (l.getD v.val 0)

def dualPerm : Equiv.Perm (Fin 14) :=
  ⟨hc_ofList [13, 8, 7, 12, 10, 11, 9, 2, 1, 6, 4, 5, 3, 0],
    hc_ofList [13, 8, 7, 12, 10, 11, 9, 2, 1, 6, 4, 5, 3, 0],
    by intro x; revert x; decide +kernel, by intro x; revert x; decide +kernel⟩

def collPerm : Equiv.Perm (Fin 14) :=
  ⟨hc_ofList [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12],
    hc_ofList [6, 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 7],
    by intro x; revert x; decide +kernel, by intro x; revert x; decide +kernel⟩

def canonI : List (Finset (Fin 14)) :=
  [{0, 1, 2, 3, 4, 5, 6}, {0, 1, 2, 3, 4, 5}, {0, 1, 2, 3, 4}, {0, 1, 2, 5, 11}, {0, 1, 2, 3},
    {0, 1, 2, 5}, {0, 1, 2, 11}, {0, 1, 11, 12}, {0, 1, 2}, {0, 1, 3}, {0, 1, 11}, {0, 1},
    {0, 9}, {0}]

def hc_rep (n : Fin 15) : Finset (Fin 14) := ((∅ : Finset (Fin 14)) :: canonI).getD n.val ∅

abbrev hc_ind (I : Finset (Fin 14)) : Prop := ∀ u ∈ I, ∀ v ∈ I, hc_adjB u v = false

def hc_tab : List (List ℕ) :=
  [[0,1,2,3,4,5,6,7,8,9,10,11,12,13], [1,0,4,3,5,6,2,7,13,8,9,12,11,10],
    [0,3,2,1,5,4,6,7,8,11,10,9,13,12], [0,1,5,3,6,2,4,7,10,13,8,11,12,9],
    [0,2,1,6,4,5,3,8,7,12,10,11,9,13], [0,2,4,6,1,3,5,8,10,12,7,9,11,13],
    [0,2,3,6,5,4,1,8,7,13,10,9,11,12], [1,3,5,0,2,4,6,7,9,11,13,8,10,12],
    [1,2,5,4,3,0,6,13,9,8,7,11,10,12], [1,6,0,5,2,4,3,9,7,11,13,12,10,8],
    [1,6,2,5,0,3,4,9,13,11,7,10,12,8], [11,13,8,10,12,7,9,4,6,1,3,5,0,2],
    [11,13,12,10,8,9,7,4,3,1,6,0,5,2], [11,7,13,12,9,8,10,3,4,0,6,5,2,1],
    [1,2,3,4,5,6,0,13,7,8,9,10,11,12], [2,0,1,6,3,5,4,8,13,10,12,11,9,7],
    [13,8,7,12,10,11,9,2,1,6,4,5,3,0], [8,13,7,12,9,11,10,2,0,4,6,5,3,1],
    [8,13,9,12,7,10,11,2,6,4,0,3,5,1], [8,7,13,10,9,11,12,0,2,3,6,5,4,1]]

def hc_fn (k : Fin 20) : Fin 14 → Fin 14 := hc_ofList (hc_tab.getD k.val [])

def hc_witTab : List (List ℕ) :=
  [[0,1,9,7,10,8,14,19,17,13,18,12,11,16], [], [], [0,0,0,0,0,0,1], [], [0,0,0,0,0,2,1],
    [0,0,0,2,5,0,6], [], [], [0,0,0,0,15,0,4], [0,0,0,0,7,3,1], [0,0,0,0,0,3],
    [0,0,0,0,5,3,1,0,0,0,0,0,1], [0,0,9,2,10,0,0,0,0,0,0,12,11,13],
    [0,0,4,2,5,8,6,0,0,0,0,2,4,3]]

def hc_wit (n : Fin 15) (w : Fin 14) : Fin 20 :=
  Fin.ofNat 20 ((hc_witTab.getD n.val []).getD w.val 0)

def Correct (D : Dag) : Prop :=
  ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ HeawoodEdge x

theorem inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

def sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

def sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

def sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

def sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

def sem_ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ A)

theorem sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

theorem sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

theorem sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

theorem sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

theorem sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

theorem sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

theorem sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

theorem sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

theorem sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

theorem sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

theorem sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

theorem sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (w : ℕ) (hw : val D x w ≠ val D y w) :
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) v.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn] at hw
      have hwv : (⟨w, hn⟩ : Fin n) = v := by
        by_contra hc; exact hw (hxy _ hc)
      rw [← hwv]
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        have hg := hw
        rw [val_gate hS x j hj, val_gate hS y j hj] at hg
        by_cases h1 : val D x (opA D j) = val D y (opA D j)
        · have h2 : val D x (opB D j) ≠ val D y (opB D j) := by
            intro h2; apply hg; rw [h1, h2]
          exact Relation.ReflTransGen.tail (ih _ hb h2)
            ⟨⟨hlt, by omega, Or.inr (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
        · exact Relation.ReflTransGen.tail (ih _ ha h1)
            ⟨⟨hlt, by omega, Or.inl (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
      · exfalso; apply hw; rw [val_ge D x w (by omega), val_ge D y w (by omega)]

def sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

theorem sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (hb : val D x b = val D y b) : val D x (outW n D) = val D y (outW n D) := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

def sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

theorem sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
    sem_Dom n D b v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep _ ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest⟩
      · have h0 := fanout_eq_zero_of_ge hS a (by rw [heq]; unfold outW; omega)
        have h1 := hstep.2
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest

theorem sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
    (∀ u, u < w → v ∈ supp n D u → fanout D u ≤ 1) → sem_Chain n D v.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hlow
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
      rw [hs, Finset.mem_singleton] at hv
      rw [hv]; exact Relation.ReflTransGen.refl
    · have hlt := sem_supp_lt hv
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have key : ∀ s : Bool, v ∈ supp n D (src D (j, s)) → sem_Chain n D v.val (n + j) := by
        intro s hva
        have hstep : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
        have hlt' := sem_src_lt hS hj s
        have h1 := sem_step_fanout hstep
        have h2 := hlow _ hlt' hva
        exact Relation.ReflTransGen.tail (ih _ hlt' hva (fun u hu => hlow u (by omega)))
          ⟨hstep, by omega⟩
      rw [supp_gate hS j hj] at hv
      split_ifs at hv with ht
      · exact key false (by rw [sb_src_false]; exact (Finset.mem_inter.mp hv).1)
      · rcases Finset.mem_union.mp hv with h1 | h1
        · exact key false (by rw [sb_src_false]; exact h1)
        · exact key true (by rw [sb_src_true]; exact h1)

theorem sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac

theorem sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩

theorem sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

theorem sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v} := by
  intro u hu
  rw [Finset.mem_singleton]
  by_contra huv
  obtain ⟨hsym, hirr, hsep, -⟩ := hG
  obtain ⟨z, hvz, huz⟩ := hsep v u (Ne.symm huv)
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge G (sem_two u z) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : sem_Edge G (sem_ins v (sem_two u z)) :=
    ⟨v, z, hvz, sem_ins_self v _, by simp [sem_ins, sem_two]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact h1 ((hC _).mp h3)

theorem sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (hv : v ∈ eligSet n D) :
    ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
  classical
  have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hch : sem_Chain n D v.val (Nat.find hex) :=
    sem_carrier_chain hS v _ h2 (fun u hu huv => by
      have := Nat.find_min hex hu
      by_contra hc
      exact this ⟨by omega, huv⟩)
  exact ⟨Nat.find hex, h1, Finset.Subset.antisymm
    (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2), hch⟩

def sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)

theorem sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_FirstBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · obtain ⟨b, hb⟩ := sem_first_branch hG hS hC v hv
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

theorem sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

theorem sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

theorem sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

theorem sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

theorem sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

theorem sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

theorem sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

theorem sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

theorem sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), by rw [sem_supp_out hG hC]; simp,
      by rw [sem_supp_out hG hC]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, Finset.mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [Finset.mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩

theorem sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {v : Fin n} (hv : v ∈ ineligSet n D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {v} ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G v a → a ∈ supp n D (src D (e.1, !e.2))) ∧
      exitArcs n D (carrierT n D {v}) = {e} ∧ merges n D (carrierT n D {v}) = ∅ := by
  have hS := h.1
  have hfl := carrier_flow_union h {v} (by rw [sem_supp_out hG hC]; simp)
  rw [sem_inelig_surplus hv, Finset.card_singleton] at hfl
  have hmeet : ∀ a, G v a → ∃ j s, j < D.length ∧ tag D j = true ∧
      (j, s) ∈ exitArcs n D (carrierT n D {v}) ∧ a ∈ supp n D (src D (j, !s)) := by
    intro a hva
    obtain ⟨j, hj, ht, -, hju, -, s, h1, -, h3, -⟩ := sem_joint_meeting hG hS hC hva
    exact ⟨j, s, hj, ht, sem_mem_exit1.mpr ⟨hj, h1, hju⟩, h3⟩
  obtain ⟨a0, ha0, -⟩ := hG.2.2.2 v v
  obtain ⟨j0, s0, hj0, ht0, hm0, -⟩ := hmeet a0 ha0
  have hcard : (exitArcs n D (carrierT n D {v})).card = 1 := by
    have := Finset.card_pos.mpr ⟨_, hm0⟩
    omega
  have hmer : merges n D (carrierT n D {v}) = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  rw [he, Finset.mem_singleton] at hm0
  subst hm0
  have hsrc : supp n D (src D (j0, s0)) = {v} :=
    sem_inelig_pure hG hS hC hv
      (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.1
  have hnot : v ∉ supp n D (n + j0) :=
    (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.2
  refine ⟨(j0, s0), hj0, ht0, hsrc, ?_, ?_, he, hmer⟩
  · refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
    have hx2 := sem_supp_and_sub hS hj0 ht0 s0 hx
    rw [hsrc, Finset.mem_singleton] at hx2
    exact hnot (hx2 ▸ hx)
  · intro a hva
    obtain ⟨j, s, -, -, hm, ha⟩ := hmeet a hva
    rw [he, Finset.mem_singleton] at hm
    rw [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ha

theorem sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) : u ∈ eligSet n D ∨ v ∈ eligSet n D := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨eu, -, -, -, -, hnu, hxu, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.1)
  obtain ⟨ev, -, -, hsv, -, -, hxv, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.2)
  obtain ⟨j, hj, -, -, hju, hjv, s, h1, -, h3, -⟩ := sem_joint_meeting hG h.1 hC huv
  have m1 : (j, s) ∈ exitArcs n D (carrierT n D {u}) := sem_mem_exit1.mpr ⟨hj, h1, hju⟩
  have m2 : (j, !s) ∈ exitArcs n D (carrierT n D {v}) := sem_mem_exit1.mpr ⟨hj, h3, hjv⟩
  rw [hxu, Finset.mem_singleton] at m1
  rw [hxv, Finset.mem_singleton] at m2
  subst m1
  subst m2
  obtain ⟨a, hua, hav⟩ := hG.2.2.2 u v
  have h5 : a ∈ supp n D (src D (j, !s)) := hnu a hua
  rw [hsv, Finset.mem_singleton] at h5
  exact hav h5

theorem sem_first_mask (hS : Strict n D) (T M : Finset (Fin n)) (hM : 2 ≤ M.card) (w : ℕ)
    (hw : supp n D w ∩ T = M) :
    ∃ j, j < D.length ∧ n + j ≤ w ∧ supp n D (n + j) ∩ T = M ∧
      j ∈ merges n D (carrierT n D T) ∧ (∀ u, u < n + j → supp n D u ∩ T ≠ M) ∧
      ((tag D j = true ∧ M ⊂ supp n D (opA D j) ∩ T ∧ M ⊂ supp n D (opB D j) ∩ T) ∨
        (tag D j = false ∧ supp n D (opA D j) ∩ T ⊂ M ∧ supp n D (opB D j) ∩ T ⊂ M ∧
          (supp n D (opA D j) ∩ T) ∪ (supp n D (opB D j) ∩ T) = M ∧
          (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty)) := by
  classical
  have hex : ∃ u, supp n D u ∩ T = M := ⟨w, hw⟩
  have hle : Nat.find hex ≤ w := Nat.find_min' hex hw
  have hmin : ∀ u, u < Nat.find hex → supp n D u ∩ T ≠ M := fun u hu => Nat.find_min hex hu
  have hspec := Nat.find_spec hex
  generalize Nat.find hex = f at hle hmin hspec
  have hMne : M.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : ∀ {u : ℕ}, (supp n D u ∩ T).Nonempty → u ∈ carrierT n D T := by
    intro u hu
    obtain ⟨v, hv⟩ := hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (sem_supp_lt (Finset.mem_inter.mp hv).1), v, hv⟩
  have hflt : f < n + D.length := by
    obtain ⟨v, hv⟩ := hMne
    rw [← hspec] at hv
    exact sem_supp_lt (Finset.mem_inter.mp hv).1
  have hfn : n ≤ f := by
    by_contra hc
    have hc' : f < n := by omega
    have hs : supp n D f = {⟨f, hc'⟩} := supp_input D ⟨f, hc'⟩
    have h1 : M.card ≤ 1 := by
      rw [← hspec, hs]
      exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  refine ⟨j, hj, hle, hspec, ?_, hmin, ?_⟩
  · have hAB : (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty := by
      cases ht : tag D j
      · rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
        constructor
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.empty_union] at hspec
          exact hnb hspec
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.union_empty] at hspec
          exact hna hspec
      · rw [sem_supp_and hS hj ht] at hspec
        obtain ⟨v, hv⟩ := hMne
        rw [← hspec] at hv
        simp only [Finset.mem_inter] at hv
        exact ⟨⟨v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩, ⟨v, Finset.mem_inter.mpr ⟨hv.1.2, hv.2⟩⟩⟩
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hmem (by rw [hspec]; exact hMne), hmem hAB.1, hmem hAB.2⟩
  · cases ht : tag D j
    · right
      rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
      have hsa : supp n D (opA D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_left
      have hsb : supp n D (opB D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_right
      refine ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, hnb⟩, hspec, ?_, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.empty_union] at hspec
        exact hnb hspec
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.union_empty] at hspec
        exact hna hspec
    · left
      rw [sem_supp_and hS hj ht] at hspec
      have hsa : M ⊆ supp n D (opA D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.1, hv.2⟩
      have hsb : M ⊆ supp n D (opB D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.2, hv.2⟩
      exact ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, Ne.symm hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, Ne.symm hnb⟩⟩

end SemCore

def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemCodes

def sem_MinBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v) ∧
    ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b v ≤ w

def sem_Arm (n : ℕ) (D : Dag) (X : Finset (Fin n)) (a b : ℕ) : Prop :=
  sem_step n D a b ∧ fanout D a = 1 ∧ ∀ x ∈ X, x ∈ supp n D a ∧ x ∈ supp n D b

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemArms

section SemPaths

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemPaths

def sem_hw_opp (i : Fin 14) : Finset (Fin 14) :=
  Finset.univ.filter (fun a => decide (a.val < 7) ≠ decide (i.val < 7))

def sem_hw_nb (i : Fin 14) : Finset (Fin 14) := Finset.univ.filter (fun a => Adj i a)

section SemDiff

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

end SemDiff

def sup_Occ (n : ℕ) (D : Dag) (P M : Finset (Fin n)) : Prop := ∃ w, supp n D w ∩ P = M

def sup_big (n : ℕ) (D : Dag) (P : Finset (Fin n)) : Finset ℕ :=
  (merges n D (carrierT n D P)).filter (fun j => 2 ≤ (supp n D (n + j) ∩ P).card)

def sup_Wit (n : ℕ) (D : Dag) (P U : Finset (Fin n)) (f : Fin n) (e : ℕ × Bool) : Prop :=
  e.1 < D.length ∧ tag D e.1 = true ∧ f ∈ P ∧ f ∈ supp n D (src D e) ∧
    f ∉ supp n D (n + e.1) ∧ supp n D (src D e) ∩ P ⊆ U ∧ (supp n D (src D e) ∩ P).card ≤ 2

def sup_cost (n : ℕ) (D : Dag) (P : Finset (Fin n)) (e : ℕ × Bool) : (ℕ × Bool) ⊕ ℕ :=
  if supp n D (n + e.1) ∩ P = ∅ then Sum.inl e else Sum.inr e.1

def sup_CostOK (n : ℕ) (D : Dag) (P : Finset (Fin n)) (c : (ℕ × Bool) ⊕ ℕ) : Prop :=
  Sum.elim (fun e => e ∈ exitArcs n D (carrierT n D P) ∧ (supp n D (src D e) ∩ P).card ≤ 2)
    (fun j => j ∈ merges n D (carrierT n D P) ∧ (supp n D (n + j) ∩ P).card = 1) c

section SupMask

variable {n : ℕ} {D : Dag}

end SupMask

def k4_adjB (u v : Fin 10) : Bool :=
  (([112, 400, 672, 832, 3, 5, 9, 6, 10, 12] : List ℕ).getD u.val 0).testBit v.val

abbrev k4_Adj (u v : Fin 10) : Prop := k4_adjB u v = true

theorem k4_gr : sem_Gr k4_Adj :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

section K4Generic

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem k4_mem_carrier {T : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D T ↔ (supp n D w ∩ T).Nonempty := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  rintro ⟨v, hv⟩
  exact sem_supp_lt (Finset.mem_inter.mp hv).1

theorem k4_mem_exit {T : Finset (Fin n)} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D T) ↔
    e.1 < D.length ∧ (supp n D (src D e) ∩ T).Nonempty ∧
      ¬ (supp n D (n + e.1) ∩ T).Nonempty := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, k4_mem_carrier]

def k4_Pos (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) (pos : Fin n → ℕ × Bool) : Prop :=
  (∀ i ∈ ineligSet n D, (pos i).1 < D.length ∧ supp n D (n + (pos i).1) = ∅ ∧
    (∀ a, G i a → a ∈ supp n D (src D (pos i))) ∧
    supp n D (src D ((pos i).1, !(pos i).2)) = {i}) ∧
  ∀ i ∈ ineligSet n D, ∀ i' ∈ ineligSet n D, pos i = pos i' → i = i'

theorem k4_assigned (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) :
    ∃ pos : Fin n → ℕ × Bool, k4_Pos n G D pos := by
  classical
  have hex : ∀ i : Fin n, ∃ e : ℕ × Bool, i ∈ ineligSet n D → (e.1 < D.length ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G i a → a ∈ supp n D (src D e)) ∧
      supp n D (src D (e.1, !e.2)) = {i}) := by
    intro i
    by_cases hi : i ∈ ineligSet n D
    · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ := sem_inelig_consumer hG h hC hi
      exact ⟨(e.1, !e.2), fun _ => ⟨h1, h4, h5, by simpa using h3⟩⟩
    · exact ⟨(0, false), fun hc => absurd hc hi⟩
  choose pos hpos using hex
  refine ⟨pos, hpos, fun i hi i' hi' he => ?_⟩
  have h1 := (hpos i hi).2.2.2
  rw [he, (hpos i' hi').2.2.2] at h1
  exact (Finset.singleton_injective h1).symm

theorem k4_pos_exit {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) {i a : Fin n}
    {T : Finset (Fin n)} (hi : i ∈ ineligSet n D) (hia : G i a) (haT : a ∈ T) :
    pos i ∈ exitArcs n D (carrierT n D T) := by
  obtain ⟨h1, h2, h3, -⟩ := hpos.1 i hi
  rw [k4_mem_exit]
  refine ⟨h1, ⟨a, Finset.mem_inter.mpr ⟨h3 a hia, haT⟩⟩, ?_⟩
  rw [h2, Finset.empty_inter]
  exact Finset.not_nonempty_empty

theorem k4_exits_ge {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J : Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ ∃ a ∈ T, G i a) :
    J.image pos ⊆ exitArcs n D (carrierT n D T) ∧ (J.image pos).card = J.card := by
  constructor
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hi1, a, haT, hia⟩ := hJ i hi
    exact k4_pos_exit hpos hi1 hia haT
  · exact Finset.card_image_of_injOn
      (fun i hi i' hi' he => hpos.2 i (hJ i hi).1 i' (hJ i' hi').1 he)

theorem k4_budget (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) (T : Finset (Fin n)) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card +
      (eligSet n D).card ≤ 2 * T.card + Bplus n D := by
  have h1 := carrier_flow_union h T (by rw [sem_supp_out hG hC, Finset.empty_inter])
  have h2 := surplus_carrierT_le h.1 b hb T
  have h3 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  omega

theorem k4_mask_gate (hS : Strict n D) (T : Finset (Fin n)) (w : ℕ)
    (h2 : 2 ≤ (supp n D w ∩ T).card) :
    ∃ j ∈ merges n D (carrierT n D T), supp n D (n + j) ∩ T = supp n D w ∩ T := by
  obtain ⟨j, -, -, h3, h4, -, -⟩ := sem_first_mask hS T _ h2 w rfl
  exact ⟨j, h4, h3⟩

theorem k4_pair_merges (hS : Strict n D) {T : Finset (Fin n)} (hT : T.card = 3)
    {a b c : Fin n} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {w1 w2 : ℕ} (h1a : a ∈ supp n D w1) (h1b : b ∈ supp n D w1)
    (h2a : a ∈ supp n D w2) (h2c : c ∈ supp n D w2) :
    2 ≤ (merges n D (carrierT n D T)).card := by
  have m1a : a ∈ supp n D w1 ∩ T := Finset.mem_inter.mpr ⟨h1a, ha⟩
  have m1b : b ∈ supp n D w1 ∩ T := Finset.mem_inter.mpr ⟨h1b, hb⟩
  have m2a : a ∈ supp n D w2 ∩ T := Finset.mem_inter.mpr ⟨h2a, ha⟩
  have m2c : c ∈ supp n D w2 ∩ T := Finset.mem_inter.mpr ⟨h2c, hc⟩
  have c1 : 2 ≤ (supp n D w1 ∩ T).card := Finset.one_lt_card.mpr ⟨a, m1a, b, m1b, hab⟩
  have c2 : 2 ≤ (supp n D w2 ∩ T).card := Finset.one_lt_card.mpr ⟨a, m2a, c, m2c, hac⟩
  obtain ⟨j1, hj1, e1⟩ := k4_mask_gate hS T w1 c1
  by_cases heq : supp n D w1 ∩ T = supp n D w2 ∩ T
  · have hfull : supp n D w1 ∩ T = T := by
      refine Finset.eq_of_subset_of_card_le Finset.inter_subset_right ?_
      rw [hT]
      exact Finset.two_lt_card.mpr
        ⟨a, m1a, b, m1b, c, by rw [heq]; exact m2c, hab, hac, hbc⟩
    obtain ⟨j, -, -, h3, h4, -, hcase⟩ := sem_first_mask hS T T (by omega) w1 hfull
    rcases hcase with ⟨-, hA, -⟩ | ⟨-, hA, hB, hU, -, -⟩
    · exact absurd rfl (Finset.ssubset_of_ssubset_of_subset hA Finset.inter_subset_right).ne
    · have hcard : 3 ≤ (supp n D (opA D j) ∩ T).card + (supp n D (opB D j) ∩ T).card := by
        have := Finset.card_union_le (supp n D (opA D j) ∩ T) (supp n D (opB D j) ∩ T)
        rw [hU, hT] at this
        exact this
      have key : ∀ w, supp n D w ∩ T ⊂ T → 2 ≤ (supp n D w ∩ T).card →
          2 ≤ (merges n D (carrierT n D T)).card := by
        intro w hss hc2
        obtain ⟨j', hj', e'⟩ := k4_mask_gate hS T w hc2
        refine Finset.one_lt_card.mpr ⟨j, h4, j', hj', fun hjj => ?_⟩
        rw [hjj, e'] at h3
        exact hss.ne h3
      by_cases hc2 : 2 ≤ (supp n D (opA D j) ∩ T).card
      · exact key _ hA hc2
      · exact key _ hB (by omega)
  · obtain ⟨j2, hj2, e2⟩ := k4_mask_gate hS T w2 c2
    exact Finset.one_lt_card.mpr ⟨j1, hj1, j2, hj2, fun hjj => heq (by rw [← e1, ← e2, hjj])⟩

def k4_joint (n : ℕ) (D : Dag) (u t : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => u ∈ supp n D w ∧ t ∈ supp n D w)

end K4Generic

theorem k4_indep_facts : ∀ I : Finset (Fin 10), (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) →
    5 ≤ I.card → (∀ q ∈ I, 4 ≤ q.val) ∧
      ((4 ∈ I ∧ 5 ∈ I) ∨ (4 ∈ I ∧ 7 ∈ I) ∨ (5 ∈ I ∧ 7 ∈ I)) := by decide +kernel

theorem k4_meets012 : ∀ i : Fin 10, 4 ≤ i.val →
    ∃ a ∈ ({0, 1, 2} : Finset (Fin 10)), k4_Adj i a := by decide +kernel

theorem k4_inelig_indep {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 k4_Adj D) :
    ∀ u ∈ ineligSet 10 D, ∀ v ∈ ineligSet 10 D, k4_adjB u v = false := by
  intro u hu v hv
  by_contra hc
  rw [Bool.not_eq_false] at hc
  rcases sem_elig_cover k4_gr h hC (u := u) (v := v) hc with h1 | h1
  · exact sem_mem_inelig.mp hu h1
  · exact sem_mem_inelig.mp hv h1

theorem k4_surplus_six {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 k4_Adj D) :
    6 ≤ Bplus 10 D := by
  by_contra hlt
  obtain ⟨b, hb⟩ := sem_exists_pureBranch k4_gr h.1 hC
  have hp := elig_le_Bplus h.1 b hb
  have hcard := inelig_card_add 10 D
  obtain ⟨hI4, hpairs⟩ := k4_indep_facts _ (k4_inelig_indep h hC) (by omega)
  obtain ⟨pos, hpos⟩ := k4_assigned k4_gr h hC
  have hbud := k4_budget k4_gr h hC b hb ({0, 1, 2} : Finset (Fin 10))
  obtain ⟨hsub, hcd⟩ := k4_exits_ge hpos ({0, 1, 2} : Finset (Fin 10)) (ineligSet 10 D)
    (fun i hi => ⟨hi, k4_meets012 i (hI4 i hi)⟩)
  have hex := Finset.card_le_card hsub
  have hT : ({0, 1, 2} : Finset (Fin 10)).card = 3 := by decide
  have q : ∀ i ∈ ineligSet 10 D, ∀ a, k4_Adj i a → a ∈ supp 10 D (src D (pos i)) :=
    fun i hi => (hpos.1 i hi).2.2.1
  have hmer : 2 ≤ (merges 10 D (carrierT 10 D ({0, 1, 2} : Finset (Fin 10)))).card := by
    rcases hpairs with ⟨i4, i5⟩ | ⟨i4, i7⟩ | ⟨i5, i7⟩
    · exact k4_pair_merges h.1 hT (a := 0) (b := 1) (c := 2) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (q 4 i4 0 (by decide))
        (q 4 i4 1 (by decide)) (q 5 i5 0 (by decide)) (q 5 i5 2 (by decide))
    · exact k4_pair_merges h.1 hT (a := 1) (b := 0) (c := 2) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (q 4 i4 1 (by decide))
        (q 4 i4 0 (by decide)) (q 7 i7 1 (by decide)) (q 7 i7 2 (by decide))
    · exact k4_pair_merges h.1 hT (a := 2) (b := 0) (c := 1) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (q 5 i5 2 (by decide))
        (q 5 i5 0 (by decide)) (q 7 i7 2 (by decide)) (q 7 i7 1 (by decide))
  omega

theorem k4_relabel_comp {G : Fin 10 → Fin 10 → Prop} (σ : Equiv.Perm (Fin 10))
    (hσ : ∀ u v, G u v ↔ k4_Adj (σ u) (σ v)) {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 G D) : sem_Comp 10 k4_Adj (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2 x, hC]
  unfold sem_Edge
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨σ u, σ v, (hσ u v).mp huv, hu, hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨σ.symm u, σ.symm v, (hσ _ _).mpr (by simpa using huv), by simpa using hu,
      by simpa using hv⟩

theorem k4_surplus_six_iso {G : Fin 10 → Fin 10 → Prop} (σ : Equiv.Perm (Fin 10))
    (hσ : ∀ u v, G u v ↔ k4_Adj (σ u) (σ v)) {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 G D) : 6 ≤ Bplus 10 D := by
  rw [← relabel_Bplus σ h.1]
  exact k4_surplus_six (relabel_strictLive σ h) (k4_relabel_comp σ hσ h hC)


end PEqualNP.Outside.L_meta_8181.Subdivision

namespace PEqualNP.Outside.L_meta_8181.Four
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_8181.Support
open SupportThree IncidenceFour MonoGraph ColumnPeel Finset
open PEqualNP.Outside.L_meta_8181.Subdivision

private abbrev target := ef (pattern 6)
private abbrev sigma : Equiv.Perm (Fin 10) := Equiv.swap 6 7
private abbrev R (u v : Fin 10) := k4_Adj (sigma u) (sigma v)
private def mate : Fin 10→Fin 10 := ![4,4,5,7,0,0,1,0,1,2]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem six : LB (ef (pattern 6)) 15 := by
  intro C ao spec
  have eval (x : Fin 10 → Bool) : C.eval (List.ofFn x)=target x := spec x
  have mono : Monotone2 C := fun g hg=>⟨ao.1 g hg,(ao.2.2 g hg).le⟩
  have tr : ∀ x, target x=true ↔ sem_Edge R x := by
    unfold sem_Edge R
    decide +kernel
  have singles : ∀ i : Fin 10,target (fun k=>decide (k=i)) = false := by decide +kernel
  have yes : ∀ i : Fin 10,target (fun k=>decide (k=mate i) || decide (k=i))=true := by decide +kernel
  have off : target (fun _=>false)=false := by decide +kernel
  have on : target (fun _=>true)=true := by decide +kernel
  obtain ⟨D,l,s,v⟩ := normalize_strictLive (n:=10) C mono
    (by intro b; cases b
        · exact ⟨fun _=>true,by rw [eval,on];decide⟩
        · exact ⟨fun _=>false,by rw [eval,off];decide⟩)
    (by intro i;exact ⟨fun k=>decide (k=i),by rw [eval,singles];simp⟩)
    (by intro i
        refine ⟨fun k=>decide (k=mate i),fun k=>decide (k=mate i) || decide (k=i),fun k ne=>by simp [ne],?_⟩
        rw [eval,eval,singles,yes]
        decide)
  have h := k4_surplus_six_iso sigma (fun _ _=>Iff.rfl) l
    (show sem_Comp 10 R D from fun x=>by rw [v,eval];exact tr x)
  have a := Bplus_le_total 10 D
  have b := surplus_identity l
  omega

private theorem pull_image {n m h k} (E : Edges n m) (a : Fin n → Fin h) (b : Fin m → Fin k)
    (z : ℕ) (hL : LB (ef (E.image (fun e => (a e.1,b e.2)))) z) : LB (ef E) z := by
  let σ : Fin (n+m) → Fin (h+k) := Fin.addCases (fun p => Fin.castAdd k (a p)) (fun l => Fin.natAdd h (b l))
  have eq (x : Fin (h+k) → Bool) : ef E (x ∘ σ) = ef (E.image (fun e => (a e.1,b e.2))) x := by
    apply Bool.eq_iff_iff.mpr
    simp only [ef, F, decide_eq_true_iff, Function.comp_apply, σ, Fin.addCases_left, Fin.addCases_right]
    constructor
    · rintro ⟨p,l,hp,xx,yy⟩
      exact ⟨a p,b l,Finset.mem_image_of_mem _ hp,xx,yy⟩
    · rintro ⟨i,j,hij,xx,yy⟩
      obtain ⟨⟨p,l⟩,hp,mapped⟩ := mem_image.mp hij
      cases mapped
      exact ⟨p,l,hp,xx,yy⟩
  apply pull σ (ef E)
  simpa only [eq] using hL

private theorem pull_pattern {m k} (E : E4 m) (H : Finset (Fin m))
    (hk : k = 5 ∨ k = 6) (size : H.card = k)
    (two : ∀ l ∈ H, (neighbors E l).card = 2)
    (uniq : Set.InjOn (neighbors E) (↑H : Set (Fin m)))
    (hL : LB (ef (pattern k)) (2*k+3)) :
    LB (ef (retainedEdges E H)) ((retainedEdges E H).card+3) ∧ (retainedEdges E H).card=2*k := by
  classical
  let T := H.image (neighbors E)
  have tcard : T.card = k := (card_image_of_injOn uniq).trans size
  obtain ⟨a,ainj,columns⟩ := canonical_columns hk T tcard (by
    intro s hs
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hs
    exact two l hl)
  have choiceCol (l : Fin m) (hl : l∈H) :
      ∃ j, neighbors (pattern k) j = (neighbors E l).image a := by
    have hn := Finset.mem_image_of_mem (fun s : Finset (Fin 4) => s.image a)
      (show neighbors E l ∈ T from mem_image_of_mem _ hl)
    rw [columns] at hn
    obtain ⟨j,_,hj⟩ := mem_image.mp hn
    exact ⟨j,hj⟩
  let b : Fin m → Fin k := fun l => if hl : l ∈ H then (choiceCol l hl).choose else ⟨0,by omega⟩
  have bs (l) (hl : l ∈ H) : neighbors (pattern k) (b l) = (neighbors E l).image a := by
    simpa [b,hl] using (choiceCol l hl).choose_spec
  have bi : Set.InjOn b (↑H : Set (Fin m)) := by
    intro l hl j hj h
    exact uniq hl hj (Finset.image_injective ainj
      ((bs l hl).symm.trans ((congrArg (neighbors (pattern k)) h).trans (bs j hj))))
  have onto (j : Fin k) : ∃ l ∈ H, b l = j := by
    have hn := mem_image_of_mem (neighbors (pattern k)) (mem_univ j)
    rw [← columns] at hn
    obtain ⟨s,hs,he⟩ := mem_image.mp hn
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hs
    exact ⟨l,hl,pattern_distinct hk ((bs l hl).trans he)⟩
  let B := retainedEdges E H
  let emb := fun e : Fin 4 × Fin m => (a e.1,b e.2)
  have im : B.image emb = pattern k := by
    ext ⟨i,j⟩
    constructor
    · intro h
      obtain ⟨⟨p,l⟩,he,hpair⟩ := mem_image.mp h
      change (a p,b l) = (i,j) at hpair
      cases hpair
      obtain ⟨edge,hl⟩ := mem_filter.mp he
      have hp : p ∈ neighbors E l := mem_filter.mpr ⟨mem_univ _,edge⟩
      have incl := mem_image_of_mem a hp
      rw [← bs l hl] at incl
      exact (mem_filter.mp incl).2
    · intro h
      obtain ⟨l,hl,rfl⟩ := onto j
      have hi : i ∈ neighbors (pattern k) (b l) := mem_filter.mpr ⟨mem_univ _,h⟩
      rw [bs l hl] at hi
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
      exact mem_image.mpr ⟨(p,l),mem_filter.mpr ⟨(mem_filter.mp hp).2,hl⟩,rfl⟩
  have inj : Set.InjOn emb (↑B : Set (Fin 4 × Fin m)) := by
    intro e he z hz hz'
    apply Prod.ext (ainj (congrArg Prod.fst hz'))
    exact bi (mem_filter.mp he).2 (mem_filter.mp hz).2 (congrArg Prod.snd hz')
  have c : B.card = 2*k := (card_image_of_injOn inj).symm.trans
    ((congrArg Finset.card im).trans (pattern_card hk))
  refine ⟨?_,c⟩
  change LB (ef B) (B.card+3)
  rw [c]
  exact pull_image B a b _ (by change LB (ef (B.image emb)) _; rw [im]; exact hL)

private theorem smallCode (E : Edges n m) (size : (E.image Prod.fst).card≤4) :
    ∃ a : Fin n → Fin 4, Set.InjOn a (↑(E.image Prod.fst) : Set (Fin n)) := by
  classical
  let S := E.image Prod.fst
  have hh : Fintype.card (↑S : Type) ≤ 4 := by rw [Fintype.card_coe];exact size
  let b : (↑S : Type) → Fin 4 := fun p => Fin.castLE hh (Fintype.equivFin (↑S : Type) p)
  let a : Fin n → Fin 4 := fun p => if hp : p ∈ S then b ⟨p,hp⟩ else 0
  refine ⟨a,?_⟩
  intro p hp q hq eq
  have ep : p∈S := hp
  have eq' : q∈S := hq
  have ee : b ⟨p,ep⟩ = b ⟨q,eq'⟩ := by simpa [a,ep,eq'] using eq
  exact congrArg Subtype.val ((Fintype.equivFin (↑S : Type)).injective (Fin.ext (congrArg (fun z : Fin 4 => z.val) ee)))


private theorem extension {m : ℕ} (E : E4 m) (J : Finset (Fin m))
    (keep : heavy E ⊆ J) (bne : (retainedEdges E J).Nonempty)
    (base : LB (ef (retainedEdges E J)) ((retainedEdges E J).card+3)) : LB (ef E) (E.card+3) := by
  classical
  let B := E.filter fun e => e.2∈J
  let X := E.filter fun e => e.2∉J
  let T := X.image Prod.snd
  have em (p l) : (p,l)∈B ↔ (p,l)∈E ∧ l∉T := by
    constructor
    · intro h
      obtain ⟨a,b⟩ := mem_filter.mp h
      refine ⟨a,?_⟩
      intro ht
      obtain ⟨e,he,eq⟩ := mem_image.mp ht
      exact (mem_filter.mp he).2 (eq ▸ b)
    · rintro ⟨a,b⟩
      apply mem_filter.mpr;refine ⟨a,?_⟩
      by_contra h;exact b (mem_image.mpr ⟨(p,l),mem_filter.mpr ⟨a,h⟩,rfl⟩)
  let I := fun p l => (p,l)∈E
  have ebase : F (strip I (∅ ∪ T)) = ef B := Partial9840.feq _ _ (by intro p l;simp only [Finset.empty_union,strip,I];exact (em p l).symm)
  have eall : F (strip I ∅) = ef E := Partial9840.feq _ _ (by intro p l;simp [strip,I])
  obtain ⟨⟨p,j⟩,memB⟩ := bne
  have paid  := MonoCut.delete_many I ∅ T (by simp) (by
    intro l ht;obtain ⟨⟨p,k⟩,he,eq⟩ := mem_image.mp ht;exact ⟨p,eq ▸ (mem_filter.mp he).1⟩)
    (by refine ⟨p,j,?_⟩; simpa only [Finset.empty_union,strip,I] using (em _ _).mp memB)
    (k:=B.card+3) (by omega) (ebase ▸ base)
  rw [eall] at paid
  have xc : T.card = X.card := by
    apply card_image_of_injOn
    rintro ⟨p,l⟩ h ⟨q,k⟩ h' eq
    change l=k at eq;subst k
    have small : (neighbors E l).card ≤ 1 := by
      by_contra! large
      exact (mem_filter.mp h).2 (keep (mem_filter.mpr ⟨mem_univ _,large⟩))
    have memP : p ∈ neighbors E l := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).1⟩
    have memQ : q ∈ neighbors E l := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h').1⟩
    exact Prod.ext ((card_le_one.mp small) p memP q memQ) rfl
  have add := card_filter_add_card_filter_not (s:=E) (fun e => e.2∈J)
  change B.card+X.card=E.card at add
  intro C ao spec;have := paid C ao spec;omega


theorem subdivisions_with_leaves {m : Nat} (E : E4 m) (free : C4 E)
    (rich : 6 ≤ (heavy E).card) : LB (ef E) (E.card+3) := by
  classical
  have deg (l) (hl : l∈heavy E) : 2≤(neighbors E l).card := (mem_filter.mp hl).2
  obtain ⟨size,all,uniq⟩ := classify_four (neighbors E) (graph_linear E free) (heavy E) deg (by omega)
  have equal : (heavy E).card = 6 := by omega
  obtain ⟨core,num⟩ := pull_pattern E (heavy E) (k:=6) (Or.inr rfl) equal all uniq six
  have pos : (retainedEdges E (heavy E)).Nonempty := card_pos.mp (by rw [num]; decide)
  exact extension E (heavy E) (fun _ h => h) pos core
end PEqualNP.Outside.L_meta_8181.Four


namespace PEqualNP.Outside.L_meta_8181.Four
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_8181.Support
open SupportThree IncidenceFour MonoGraph ColumnPeel Finset
private theorem transferRows {n m h} (a : Fin n → Fin h) (E : Edges n m) (inj : Set.InjOn a (↑(E.image Prod.fst) : Set (Fin n)))
    (known : Sharp (ren a E)) : Sharp E := by
  intro M sub row col
  have hc := known (ren a M) (Finset.image_subset_image sub) (rrows row sub inj) (rcols col)
  have e1 : (ren a E).card = E.card := Finset.card_image_of_injOn (ren_inj (fun _ v => v) inj)
  have e2 : (ren a M).card = M.card := Finset.card_image_of_injOn (ren_inj sub inj)
  rw [e1,e2] at hc
  apply pull (SupportThree.sigma a) (ef E)
  simpa only [efa] using hc

private theorem transferSides {n m} {E : Edges n m} (h : Sharp E) : Sharp (sw E) := by
  intro M sub row col
  have eq : sw (sw E) = E := by ext ⟨i,j⟩;simp only [smem]
  have sub' : sw M ⊆ E := eq ▸ Finset.image_subset_image sub
  have base := h (sw M) sub' (srow col) (scol row)
  apply pull tau (ef (sw E))
  simpa only [efsw,eq,scard] using base

theorem four_from_light (light : PEqualNP.Outside.L_meta_8181.LightPrice)
    {n m : Nat} (E : Edges n m) (free : C4 E)
    (small : (E.image Prod.fst).card ≤ 4 ∨ (E.image Prod.snd).card ≤ 4) : Sharp E := by
  have fixed {k : Nat} (D : E4 k) (lin : C4 D) : Sharp D := by
    by_cases little : (heavy D).card ≤ 5
    · exact light k D lin little
    · have rich := subdivisions_with_leaves D lin (by omega)
      intro T sub row col C ao spec
      have sz := card_le_card_of_injOn Prod.fst (t:=univ) (fun _ _ => mem_univ _) row
      change T.card ≤ 4 at sz
      have paid := rich C ao spec
      omega
  have rows {n m : Nat} (D : Edges n m) (free : C4 D) (sm : (D.image Prod.fst).card ≤ 4) : Sharp D := by
    obtain ⟨f,inj⟩ := smallCode D sm
    exact transferRows f D inj (fixed _ (rfree free inj))
  rcases small with h | h
  · exact rows E free h
  · have sm : ((sw E).image Prod.fst).card ≤ 4 := by
      simpa only [sw,Finset.image_image,Function.comp_def,Prod.fst_swap] using h
    have res := transferSides (rows (sw E) (sfree free) sm)
    have eq : sw (sw E)=E := by ext ⟨i,j⟩;simp only [smem]
    exact eq ▸ res
end PEqualNP.Outside.L_meta_8181.Four

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

set_option maxHeartbeats 900000 in
theorem PEqualNP.Outside.L_meta_8181.Puncture.matchingCircuit : ∀ (n m : ℕ) (F : Finset (Fin n × Fin m)),
      ∃ (T : Finset (Fin n × Fin m)) (D : Circuit),
        T ⊆ F ∧ Set.InjOn Prod.fst (T : Set (Fin n × Fin m)) ∧
        Set.InjOn Prod.snd (T : Set (Fin n × Fin m)) ∧
        D.size ≤ F.card + T.card - 1 ∧ IsAO2 (n+m) D ∧
        ∀ x : Fin (n+m) → Bool, circuitFun (n+m) D x = decide
          (∃ p l, (p,l) ∈ F ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true) := by
  classical
  have saturate {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (r : α → β → Prop) (A : Finset α) (B : Finset β)
      (cov : ∀ a b, r a b → a ∈ A ∨ b ∈ B)
      (minimal : ∀ (X : Finset α) (Y : Finset β),
        (∀ a b, r a b → a ∈ X ∨ b ∈ Y) → A.card+B.card ≤ X.card+Y.card) :
      ∃ f : A → β, Function.Injective f ∧ ∀ a : A, r a (f a) ∧ f a ∉ B := by
    classical
    let adj (a : A) := Finset.univ.filter fun b => r a b ∧ b ∉ B
    have hall (s : Finset A) : s.card ≤ (s.biUnion adj).card := by
      let X : Finset α := s.map (Function.Embedding.subtype _)
      let Y := s.biUnion adj
      have Xsub : X ⊆ A := by
        intro a ha
        obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
        exact i.property
      have replacement : ∀ a b, r a b → a ∈ A \ X ∨ b ∈ B ∪ Y := by
        intro a b h
        by_cases hb : b ∈ B
        · exact Or.inr (Finset.mem_union_left _ hb)
        have ha := (cov a b h).resolve_right hb
        by_cases hx : a ∈ X
        · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
          exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,hb⟩⟩))
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨ha,hx⟩)
      have bound := minimal _ _ replacement
      have card := Finset.card_sdiff_add_card_eq_card Xsub
      have union := Finset.card_union_le B Y
      have sizeX : X.card = s.card := Finset.card_map _
      change s.card ≤ Y.card
      omega
    obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
    exact ⟨f,inj,fun a => (Finset.mem_filter.mp (mem a)).2⟩

  have matchingCover (n m : ℕ) (E : Finset (Fin n × Fin m)) :
      ∃ (M : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)),
        M ⊆ E ∧ Set.InjOn Prod.fst (M : Set (Fin n × Fin m)) ∧
        Set.InjOn Prod.snd (M : Set (Fin n × Fin m)) ∧
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ A.card+B.card ≤ M.card := by
    classical
    let cover (A : Finset (Fin n)) (B : Finset (Fin m)) :=
      ∀ a b, (a,b) ∈ E → a ∈ A ∨ b ∈ B
    have has : ∃ k, ∃ A B, cover A B ∧ A.card+B.card = k :=
      ⟨_,Finset.univ,∅,fun a _ _ => Or.inl (Finset.mem_univ a),rfl⟩
    obtain ⟨A,B,cov,least⟩ := Nat.find_spec has
    have minAB (X Y) (h : cover X Y) : A.card+B.card ≤ X.card+Y.card := by
      rw [least]
      exact Nat.find_min' has ⟨X,Y,h,rfl⟩
    obtain ⟨f,fi,hf⟩ := saturate (fun (a : Fin n) (b : Fin m) => (a,b) ∈ E) A B cov minAB
    obtain ⟨g,gi,hg⟩ := saturate (fun (b : Fin m) (a : Fin n) => (a,b) ∈ E) B A
      (fun b a h => (cov a b h).symm) (fun Y X h => by
        simpa only [Nat.add_comm] using minAB X Y (fun a b he => (h b a he).symm))
    let pair : A ⊕ B → Fin n × Fin m := Sum.elim (fun a => (a.val,f a)) (fun b => (g b,b.val))
    have first : Function.Injective (Prod.fst ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (Subtype.ext eq)
        | inr b => exact False.elim ((hg b).2 ((show a.val = g b from eq) ▸ a.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hg b).2 ((show a.val = g b from eq.symm) ▸ a.property))
        | inr b' => exact congrArg Sum.inr (gi eq)
    have second : Function.Injective (Prod.snd ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (fi eq)
        | inr b => exact False.elim ((hf a).2 ((show b.val = f a from eq.symm) ▸ b.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hf a).2 ((show b.val = f a from eq) ▸ b.property))
        | inr b' => exact congrArg Sum.inr (Subtype.ext eq)
    let M := Finset.univ.image pair
    refine ⟨M,A,B,?_,?_,?_,fun e he => cov _ _ he,?_⟩
    · intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      cases i with
      | inl a => exact (hf a).1
      | inr b => exact (hg b).1
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (first eq)
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (second eq)
    · simp [M,Finset.card_image_of_injective _ (Function.Injective.of_comp first)]

  intro n m F
  obtain ⟨T,A,B,ss,hr,hc,cover,count⟩ := matchingCover n m F
  obtain ⟨D,_,dAO,db,de,_⟩ := PEqualNP.Outside.L_meta_8181.Puncture.stars n m F A B cover
  exact ⟨T,D,ss,hr,hc,by omega,dAO,de⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.L_meta_8181.Puncture.matchingCircuitExplicit : ∀ (n m : ℕ) (F : Finset (Fin n × Fin m)),
      ∃ (T : Finset (Fin n × Fin m)) (D : Circuit),
        T ⊆ F ∧ (∀ e ∈ T, ∀ f ∈ T, e.1 = f.1 → e = f) ∧
        (∀ e ∈ T, ∀ f ∈ T, e.2 = f.2 → e = f) ∧
        D.size ≤ F.card + T.card - 1 ∧ IsAO2 (n+m) D ∧
        ∀ x : Fin (n+m) → Bool, circuitFun (n+m) D x = decide
          (∃ p l, (p,l) ∈ F ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true) := by
  intro n m F
  obtain ⟨T,D,ss,hr,hc,hd,ha,hf⟩ := PEqualNP.Outside.L_meta_8181.Puncture.matchingCircuit n m F
  exact ⟨T,D,ss,fun e he f h eq => hr he h eq,fun e he f h eq => hc he h eq,hd,ha,hf⟩



namespace PEqualNP.Outside.L_meta_8181
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem pure_four : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), ((x3.image Prod.fst).card ≤ 4 ∨ (x3.image Prod.snd).card ≤ 4) → have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);   have x8 : Prop :=     ∃ (x8 : Fin (x1 + x2)),       have x9 : ℕ := (x6.neighborSet x8).ncard;       have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;       (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);   (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) → ¬x6.IsAcyclic → x7 x3 x5 → (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 → x12 = x14) → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.2 = x15.2 → x13 = x15) → x4 ⊆ x3 → (∀ (x15 x16 : Fin x1) (x17 x18 : Fin x2), x15 ≠ x16 → x17 ≠ x18 → ¬((x15, x17) ∈ x3 ∧ (x15, x18) ∈ x3 ∧ (x16, x17) ∈ x3 ∧ (x16, x18) ∈ x3)) → (∀ x16 ∈ x3, ((∀ x18 ∈ x3, x18.1 = x16.1 → x18 = x16) ∨ ∀ x18 ∈ x3, x18.2 = x16.2 → x18 = x16) → (x3.erase x16).Nonempty → x16 ∈ x4) → ¬x8 → ∃ x18 ∈ x3, x18 ∉ x4 ∧ ∃ (x19 : PEqualNP.CircuitLowerBounds.Circuit), x19.size < x5.size ∧ x7 (x3.erase x18) x19 := by
  classical
  intro n m E M C G sm fit hi adj cyc rep pp qq sub square pend quiet
  have lb := Four.four_from_light light_price E square sm
  have ge := girth n m E G adj cyc square
  obtain ⟨e,he,ex⟩ := unmatched n m E M G adj cyc pp qq
  obtain ⟨T,D,st,ml,mr,sz,ao,ev⟩ := Puncture.matchingCircuitExplicit n m (E.erase e)
  have bound := lb T (fun _ h => Finset.mem_of_mem_erase (st h)) ml mr C rep.1 rep.2
  rw [Finset.card_erase_of_mem he] at sz
  exact ⟨e,he,ex,D,by omega,ao,ev⟩
end PEqualNP.Outside.L_meta_8181

namespace PEqualNP.Outside.L_meta_8181
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem covered_by_four : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∃ (P : Finset (Fin x1)) (Q : Finset (Fin x2)), P.card+Q.card ≤ 4 ∧ ∀ e∈x3, e.1∈P ∨ e.2∈Q) → have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);   have x8 : Prop :=     ∃ (x8 : Fin (x1 + x2)),       have x9 : ℕ := (x6.neighborSet x8).ncard;       have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;       (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);   (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) → ¬x6.IsAcyclic → x7 x3 x5 → (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 → x12 = x14) → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.2 = x15.2 → x13 = x15) → x4 ⊆ x3 → (∀ (x15 x16 : Fin x1) (x17 x18 : Fin x2), x15 ≠ x16 → x17 ≠ x18 → ¬((x15, x17) ∈ x3 ∧ (x15, x18) ∈ x3 ∧ (x16, x17) ∈ x3 ∧ (x16, x18) ∈ x3)) → (∀ x16 ∈ x3, ((∀ x18 ∈ x3, x18.1 = x16.1 → x18 = x16) ∨ ∀ x18 ∈ x3, x18.2 = x16.2 → x18 = x16) → (x3.erase x16).Nonempty → x16 ∈ x4) → ¬x8 → ∃ x18 ∈ x3, x18 ∉ x4 ∧ ∃ (x19 : PEqualNP.CircuitLowerBounds.Circuit), x19.size < x5.size ∧ x7 (x3.erase x18) x19 := by
  classical
  intro n m E M C G cv fit hi adj cyc rep pp qq sub square pend quiet
  obtain ⟨P,Q,sz,cover⟩ := cv
  by_cases hp : 0 < P.card
  · by_cases hq : 0 < Q.card
    · exact posted_on_matrix_core n m E M C G (from_mixed E square ⟨P,Q,hp,hq,sz,cover⟩)
        adj cyc rep pp qq sub square pend quiet
    · have empty : Q=∅ := Finset.card_eq_zero.mp (by omega)
      have inc : E.image Prod.fst ⊆ P := by
        rintro _ hi
        obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
        simpa [empty] using cover e he
      exact pure_four n m E M C G (Or.inl ((Finset.card_le_card inc).trans (by omega)))
        adj cyc rep pp qq sub square pend quiet
  · have empty : P=∅ := Finset.card_eq_zero.mp (by omega)
    have inc : E.image Prod.snd ⊆ Q := by
      rintro _ hi
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
      simpa [empty] using cover e he
    exact pure_four n m E M C G (Or.inr ((Finset.card_le_card inc).trans (by omega)))
      adj cyc rep pp qq sub square pend quiet
end PEqualNP.Outside.L_meta_8181
