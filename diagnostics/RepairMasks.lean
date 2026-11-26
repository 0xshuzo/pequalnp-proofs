import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2585.Tight870
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def C : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.or,[0,3]⟩,⟨.or,[12,5]⟩,⟨.or,[4,14]⟩,⟨.or,[1,3]⟩,⟨.or,[13,4]⟩,⟨.or,[7,8]⟩,⟨.or,[6,18]⟩,⟨.and,[0,19]⟩,⟨.and,[16,9]⟩,⟨.and,[17,10]⟩,⟨.and,[1,7]⟩,⟨.and,[2,8]⟩,⟨.or,[24,11]⟩,⟨.or,[23,25]⟩,⟨.and,[15,26]⟩,⟨.or,[21,22]⟩,⟨.or,[20,27]⟩,⟨.or,[28,29]⟩],30⟩
def row (i : Fin 6) : Nat := ![23,42,36,24,48,32] i
private def Related (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

private def advance (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem step {a b : List Bool} (h : Related a b) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) :
    Related (advance a g) (advance b g) := by
  rcases h with ⟨hlen, hmono⟩
  have evalMono :
      g.op.eval (g.inputs.map fun i => a.getD i false) = true →
        g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
    rcases hop with hop | hop
    · simpa only [hop, GateOp.eval, List.all_map, Function.comp_apply, id_eq, List.all_eq_true] using
        (fun (had : ∀ i ∈ g.inputs, a.getD i false = true) i hi =>
          hmono i (had i hi))
    · simp only [hop, GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true]
      rintro ⟨i, hi, had⟩
      exact ⟨i, hi, hmono i had⟩
  refine ⟨by simp [advance, hlen], ?_⟩
  intro i
  by_cases hm : i < a.length
  · rw [advance, advance, List.getD_append _ _ _ _ hm,
      List.getD_append _ _ _ _ (by omega)]
    exact hmono i
  · rw [advance, advance, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), ← hlen]
    cases i - a.length with
    | zero => simpa only [List.getD_cons_zero] using evalMono
    | succ j => simp

private theorem run (gs : List Gate) (a b : List Bool) (h : Related a b)
    (good : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    Related (gs.foldl advance a) (gs.foldl advance b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have hg := good g (List.mem_cons_self)
    exact ih _ _ (step h g hg) (fun q hq => good q (List.mem_cons_of_mem _ hq))


private def Below (x y : Fin 12 → Bool) : Prop := ∀ j, x j = true → y j = true

private instance (x y : Fin 12 → Bool) : Decidable (Below x y) := by
  unfold Below
  infer_instance

private theorem evalMono (C : Circuit) (hC : Monotone2 C) {x y : Fin 12 → Bool}
    (hle : Below x y) : C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have init : Related (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro k
    by_cases h : k < 12
    · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h)]
      simp only [List.getElem_ofFn]
      exact hle ⟨k, h⟩
    · rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_lt h)]
      simp
  exact (run C.gates _ _ init (fun g hg => by simpa using (hC g hg).1)).2 C.output

theorem typed : IsAO2 12 C ∧ C.size=19 := by decide +kernel
private abbrev raw (m : Nat) (i : Fin 12) := m.testBit i.val
private def pos : List Nat := [65,129,130,257,260,514,520,1025,1032,1040,2050,2052,2064,2080]
private def neg : List Nat := [63,126,252,378,504,565,756,1008,1126,1378,1764,2016,2057,2504,2561,4032]
private def graph (x : Fin 12 → Bool) := decide (∃ a b : Fin 6, (row a).testBit b.val=true ∧ x (Fin.castAdd 6 a)=true ∧ x (Fin.natAdd 6 b)=true)

private theorem extrema : ∀ x : Fin 12 → Bool, (graph x=true → ∃m∈pos, Below (raw m) x) ∧
    (graph x=false → ∃m∈neg, Below x (raw m)) := by decide +kernel

private theorem allRows (K : Circuit) (ao : IsAO2 12 K) (yes : ∀m∈pos, circuitFun 12 K (raw m)=true)
    (no : ∀m∈neg, circuitFun 12 K (raw m)=false) (x : Fin 12 → Bool) : circuitFun 12 K x=graph x := by
  have mono : Monotone2 K := fun g hg => ⟨ao.1 g hg,(ao.2.2 g hg).le⟩
  cases e : graph x with
  | true =>
    obtain ⟨m,hm,lower⟩ := (extrema x).1 e
    exact evalMono K mono lower (yes m hm)
  | false =>
    apply Bool.eq_false_iff.mpr
    intro bad
    obtain ⟨m,hm,upper⟩ := (extrema x).2 e
    exact Bool.noConfusion ((evalMono K mono upper bad).symm.trans (no m hm))

theorem right : ∀ x : Fin 12 → Bool, circuitFun 12 C x = decide (∃ a b : Fin 6, (row a).testBit b.val=true ∧ x (Fin.castAdd 6 a)=true ∧ x (Fin.natAdd 6 b)=true) := allRows C typed.1 (by decide +kernel) (by decide +kernel)
theorem fails : ¬ IsReadK 12 C 1 := by
  intro h
  have prime : IsPrimeImplicant 12 C ({1,7} : Finset (Fin 12)) := by decide +kernel
  have bad := h _ prime
  have no : readsAtMost C 12 (setList ({1,7} : Finset (Fin 12))) 1 = false := by decide +kernel
  exact Bool.noConfusion (bad.symm.trans no)
def D : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.or,[0,3]⟩,⟨.or,[12,5]⟩,⟨.or,[4,14]⟩,⟨.or,[1,3]⟩,⟨.or,[13,4]⟩,⟨.or,[7,8]⟩,⟨.or,[6,18]⟩,⟨.and,[0,19]⟩,⟨.and,[16,9]⟩,⟨.and,[17,10]⟩,⟨.and,[1,7]⟩,⟨.and,[2,8]⟩,⟨.and,[15,11]⟩,⟨.or,[23,24]⟩,⟨.or,[25,26]⟩,⟨.or,[21,22]⟩,⟨.or,[20,27]⟩,⟨.or,[28,29]⟩],30⟩
theorem repaired_shape : IsAO2 12 D ∧ D.size=C.size := by decide +kernel

theorem repaired_eval : ∀ x : Fin 12 → Bool, circuitFun 12 D x=circuitFun 12 C x := fun x => (allRows D repaired_shape.1 (by decide +kernel) (by decide +kernel) x).trans (right x).symm

theorem repaired_read : IsReadK 12 D 1 := by
  classical
  have er : ∀ a b : Fin 6, (row a).testBit b.val=true →
      readsAtMost D 12 (setList ({Fin.castAdd 6 a,Fin.natAdd 6 b} : Finset (Fin 12))) 1=true := by decide +kernel
  intro S prime
  have on := (right (setInput S)).symm.trans ((repaired_eval (setInput S)).symm.trans prime.1)
  obtain ⟨a,b,hit,aa,bb⟩ := of_decide_eq_true on
  let T : Finset (Fin 12) := {Fin.castAdd 6 a,Fin.natAdd 6 b}
  have sub : T ⊆ S := by
    intro i hi
    have m : i=Fin.castAdd 6 a ∨ i=Fin.natAdd 6 b := by simpa [T] using hi
    rcases m with rfl|rfl
    · exact of_decide_eq_true aa
    · exact of_decide_eq_true bb
  by_cases eq : T=S
  · rw [←eq]
    exact er a b hit
  · have neg := prime.2 T (Finset.mem_ssubsets.mpr (lt_of_le_of_ne sub eq))
    have pos : circuitFun 12 D (setInput T)=true := by
      rw [repaired_eval,right]
      exact decide_eq_true ⟨a,b,hit,by simp [T,setInput],by simp [T,setInput]⟩
    exact False.elim (Bool.noConfusion (pos.symm.trans neg))

end PEqualNP.Outside.L_meta_2585.Tight870
