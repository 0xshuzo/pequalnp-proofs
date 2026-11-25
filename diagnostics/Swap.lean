import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2440
import PEqualNP.Outside.L_meta_2442
import PEqualNP.Outside.L_meta_2444
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2440

namespace Orbit4643
def alter (a : Fin 12) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rl (AUT a)),piT (AUT a) C.output⟩

theorem legal (a : Fin 12) (C : Circuit) (fan : FanInTwo C) : FanInTwo (alter a C) := by
  intro g hg
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
  exact ⟨(fan _ ht).1,by simpa [rl] using (fan _ ht).2⟩

theorem length (a : Fin 12) (C : Circuit) : (alter a C).size=C.size := by simp [alter,Circuit.size]

theorem exactF (a : Fin 12) (C : Circuit) (eq : circuitFun 9 C=fP) : circuitFun 9 (alter a C)=fP := by
  funext x
  change ((C.gates.map (rl (AUT a))).foldl F (List.ofFn x)).getD (piT (AUT a) C.output) false=_
  rw [permw]
  exact (congrFun eq (x ∘ AUT a)).trans (aut a x)

theorem first (a : Fin 12) (C : Circuit) (x : Fin 9 → Bool) :
    ((alter a C).wires (List.ofFn x)).getD 9 false=(C.wires (List.ofFn (x ∘ AUT a))).getD 9 false := by
  have h := permw C.gates (AUT a) x 9
  rw [show piT (AUT a) 9=9 by simp [piT]] at h
  exact h

theorem and_lower (C : Circuit) (fan : FanInTwo C) (ok : circuitFun 9 C=fP)
    (u v : Fin 9) (ne : u≠v) (head : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false=(x u && x v)) :
    16≤C.size := by
  obtain ⟨a,orientation⟩ := cov2 u v ne
  rw [← length a C]
  rcases orientation with pair|pair
  · apply PEqualNP.Outside.L_meta_2444 (AUT a u,AUT a v) pair _ (legal a C fan) _ (exactF a C ok)
    intro x
    exact (first a C x).trans (head _)
  · apply PEqualNP.Outside.L_meta_2444 (AUT a v,AUT a u) pair _ (legal a C fan) _ (exactF a C ok)
    intro x
    rw [first,head]
    exact Bool.and_comm _ _

theorem not_lower (C : Circuit) (fan : FanInTwo C) (ok : circuitFun 9 C=fP)
    (u : Fin 9) (head : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false=(!x u)) :
    16≤C.size := by
  obtain ⟨a,choice⟩ := cov1 u
  have pick : AUT a u ∈ ([0,4] : List (Fin 9)) := by simpa using choice
  rw [← length a C]
  apply PEqualNP.Outside.L_meta_2442 _ pick _ (legal a C fan) _ (exactF a C ok)
  intro x
  exact (first a C x).trans (head _)

end Orbit4643
namespace Swap4643
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2440 Orbit4643

def swap (i : ℕ) := if i=9 then 10 else if i=10 then 9 else i
def rename (g : Gate) : Gate := ⟨g.op,g.inputs.map swap⟩
def inv (w z : List Bool) := w.length=z.length ∧ 11≤z.length ∧ ∀ i, w.getD (swap i) false=z.getD i false

theorem start (x : Fin 9 → Bool) (h b : Bool) : inv (List.ofFn x ++ [h,b]) (List.ofFn x ++ [b,h]) := by
  refine ⟨by simp,by simp,?_⟩
  intro i
  by_cases low : i<9
  · have rem : swap i=i := by simp [swap,show i≠9 by omega,show i≠10 by omega]
    rw [rem,List.getD_append _ _ _ _ (by simpa using low),List.getD_append _ _ _ _ (by simpa using low)]
  by_cases a : i=9
  · subst i
    rw [show swap 9=10 from rfl,List.getD_append_right _ _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)]
    simp
  by_cases bnd : i=10
  · subst i
    rw [show swap 10=9 from rfl,List.getD_append_right _ _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)]
    simp
  have rem : swap i=i := by simp [swap,a,bnd]
  rw [rem,List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]

theorem push (g : Gate) (w z : List Bool) (h : inv w z) : inv (F w (rename g)) (F z g) := by
  obtain ⟨len,high,read⟩ := h
  have value : (rename g).op.eval ((rename g).inputs.map fun i => w.getD i false)=
      g.op.eval (g.inputs.map fun i => z.getD i false) := by
    apply congrArg g.op.eval
    simp only [rename,List.map_map]
    exact List.map_congr_left (fun i _ => read i)
  refine ⟨by simp [F,len],by simp [F];omega,?_⟩
  intro i
  unfold F
  rw [getD_snoc,getD_snoc,value,len]
  by_cases lo : i<11
  · have index : swap i<11 := by unfold swap;split_ifs <;> omega
    rw [if_pos (by omega),if_pos (by omega)]
    exact read i
  · have index : swap i=i := by simp [swap,show i≠9 by omega,show i≠10 by omega]
    have ri := read i
    rw [index] at ri ⊢
    split_ifs <;> first | exact ri | rfl

theorem normalize (D : Circuit) (fan : FanInTwo D) (len : 0<D.size)
    (g : Gate) (headLegal : g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (H : (Fin 9 → Bool) → Bool)
    (one : ∀ x : Fin 9 → Bool, F (List.ofFn x) g=List.ofFn x ++[H x])
    (two : ∀ x : Fin 9 → Bool, (D.wires (List.ofFn x ++[x 0 || x 6])).getD 10 false=H x)
    (ok : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++[x 0 || x 6])=fP x) :
    ∃ C : Circuit, FanInTwo C ∧ C.size=D.size+1 ∧ circuitFun 9 C=fP ∧
      ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false=H x := by
  obtain ⟨gs,o⟩ := D
  cases gs with
  | nil => exact False.elim (Nat.not_lt_zero _ len)
  | cons first rest =>
    let seed : Gate := ⟨.or,[0,6]⟩
    let C : Circuit := ⟨g::seed::rest.map rename,swap o⟩
    have legal : FanInTwo C := by
      intro a ha
      change a∈g::seed::rest.map rename at ha
      simp only [List.mem_cons,List.mem_map] at ha
      rcases ha with rfl|rfl|⟨r,hr,rfl⟩
      · exact headLegal
      · simp [seed]
      · obtain ⟨op,arity⟩ := fan r (List.mem_cons_of_mem _ hr)
        exact ⟨op,by simpa [rename] using arity⟩
    have hsize : C.size=(⟨first::rest,o⟩ : Circuit).size+1 := by simp [C,Circuit.size]
    refine ⟨C,legal,hsize,?_,?_⟩
    · funext x
      let a := List.ofFn x
      let s := x 0 || x 6
      have seedR : F (a++[H x]) seed=a++[H x,s] := by
        have raw (i : Fin 9) : (a++[H x]).getD i.val false=x i := by
          rw [List.getD_append _ _ _ _ (by simpa [a] using i.isLt),getD_ofFn,dif_pos i.isLt]
        simp [F,seed,GateOp.eval,raw (0:Fin 9),raw (6:Fin 9),s]
      let value := first.op.eval (first.inputs.map fun i => (a++[s]).getD i false)
      have initial (z : Bool) : (a++[s,z]).getD 10 false=z := by
        rw [List.getD_append_right _ _ _ _ (by simp [a])];simp [a]
      have before : value=H x := by
        have t := two x
        change (rest.foldl F ((a++[s])++[value])).getD 10 false=H x at t
        rw [fold_pre _ _ _ (by simp [a]),List.append_assoc] at t
        exact (initial value).symm.trans t
      have start2 : F (a++[s]) first=a++[s,H x] := by
        change (a++[s])++[value]=a++[s,H x]
        rw [before,List.append_assoc]
        rfl
      have sim := fold_sim inv rename rest (a++[H x,s]) (a++[s,H x]) (start x _ _) (fun t _ w z h => push t w z h)
      have goal := ok x
      change (rest.foldl F (F (a++[s]) first)).getD o false=fP x at goal
      change ((rest.map rename).foldl F (F (F a g) seed)).getD (swap o) false=fP x
      rw [one,seedR]
      rw [start2] at goal
      exact (sim.2.2 o).trans goal
    · intro x
      change ((seed::rest.map rename).foldl F (F (List.ofFn x) g)).getD 9 false=H x
      rw [one,fold_pre _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)]
      simp

end Swap4643
