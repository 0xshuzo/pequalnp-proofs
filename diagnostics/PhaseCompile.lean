import Mathlib
import PEqualNP.Defs

namespace Phase4727
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

abbrev Fn (E : Type) := E → Bool

def base {E : Type} (xs F : List (Fn E)) (h : Fn E) : Prop :=
  h = (fun _ => false) ∨ h = (fun _ => true) ∨ h ∈ xs ∨ h ∈ F

def can {E : Type} (xs M F : List (Fn E)) (h : Fn E) : Prop :=
  base xs F h ∨ ∃ a ∈ M, base xs F a ∧ h = (fun x => !(a x))

def valid {E : Type} (xs M F : List (Fn E)) : Prop :=
  ∀ h ∈ F, ∃ A B : List (Fn E), F = A ++ h :: B ∧
    ∃ a b, can xs M A a ∧ can xs M A b ∧
      (h = (fun x => a x && b x) ∨ h = (fun x => a x || b x))

lemma base_mono {E : Type} {xs F F' : List (Fn E)} (hf : F ⊆ F') {h : Fn E} :
    base xs F h → base xs F' h := by
  rintro (h|h|h|h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (hf h)))

lemma mono {E : Type} {xs M F M' F' : List (Fn E)}
    (hm : M ⊆ M') (hf : F ⊆ F') {h : Fn E} :
    can xs M F h → can xs M' F' h := by
  rintro (hh|⟨a,ha,ab,rfl⟩)
  · exact Or.inl (base_mono hf hh)
  · exact Or.inr ⟨a,hm ha,base_mono hf ab,rfl⟩

lemma valid_mono {E : Type} {xs M M' F : List (Fn E)}
    (hm : M ⊆ M') (hv : valid xs M F) : valid xs M' F := by
  intro h hh
  obtain ⟨A,B,eq,a,b,ha,hb,op⟩ := hv h hh
  exact ⟨A,B,eq,a,b,mono hm (fun _ z => z) ha,mono hm (fun _ z => z) hb,op⟩

def vfun {E : Type} (ws : List (Fn E)) (g : Gate) : Fn E :=
  fun x => g.op.eval (g.inputs.map (fun i => (ws.getD i (fun _ => false)) x))

def step {E : Type} (ws : List (Fn E)) (g : Gate) := ws ++ [vfun ws g]

def sem {E : Type} (xs : List (Fn E)) (gs : List Gate) := gs.foldl step xs

lemma eval_map {E : Type} (xs : List (Fn E)) (gs : List Gate) (x : E) :
    (sem xs gs).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (xs.map fun f => f x) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (sem (step xs g) gs).map _ = gs.foldl _ _
    rw [ih]
    have hm : (g.inputs.map fun i => (xs.getD i (fun _ => false)) x) =
        (g.inputs.map fun i => (xs.map fun f => f x).getD i false) := by
      apply List.map_congr_left
      intro i _
      exact (List.getD_map xs (fun _ => false) (fun f => f x)).symm
    simp [step,vfun,hm]

lemma readyD {E : Type} (xs M F w : List (Fn E))
    (ready : ∀ h ∈ w, can xs M F h) (i : ℕ) :
    can xs M F (w.getD i (fun _ => false)) := by
  unfold List.getD
  cases eq : w[i]? with
  | none => exact Or.inl (Or.inl rfl)
  | some f => exact ready f (List.mem_of_getElem? eq)

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

lemma binary {E : Type} (xs M F w : List (Fn E)) (g : Gate)
    (ready : ∀ h ∈ w, can xs M F h)
    (op : g.op = GateOp.and ∨ g.op = GateOp.or) (arity : g.inputs.length ≤ 2) :
    ∃ a b, can xs M F a ∧ can xs M F b ∧
      (vfun w g = (fun x => a x && b x) ∨ vfun w g = (fun x => a x || b x)) := by
  obtain ⟨opg,ins⟩ := g
  change opg = _ ∨ opg = _ at op
  change ins.length ≤ 2 at arity
  have f0 : can xs M F (fun _ => false) := Or.inl (Or.inl rfl)
  have f1 : can xs M F (fun _ => true) := Or.inl (Or.inr (Or.inl rfl))
  cases ins with
  | nil =>
    rcases op with rfl|rfl
    · exact ⟨_,_,f1,f1,Or.inl rfl⟩
    · exact ⟨_,_,f0,f0,Or.inr rfl⟩
  | cons i tail =>
    have ai := readyD xs M F w ready i
    cases tail with
    | nil =>
      rcases op with rfl|rfl
      · exact ⟨_,_,ai,f1,Or.inl (by funext x; simp [vfun,GateOp.eval])⟩
      · exact ⟨_,_,ai,f0,Or.inr (by funext x; simp [vfun,GateOp.eval])⟩
    | cons j tail =>
      have aj := readyD xs M F w ready j
      have empty : tail = [] := List.length_eq_zero_iff.mp (by simp at arity; omega)
      subst tail
      rcases op with rfl|rfl
      · exact ⟨_,_,ai,aj,Or.inl (by funext x; simp [vfun,GateOp.eval])⟩
      · exact ⟨_,_,ai,aj,Or.inr (by funext x; simp [vfun,GateOp.eval])⟩

lemma build {E : Type} (xs : List (Fn E)) (gs : List Gate)
    (fan : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ M F : List (Fn E), M.length ≤ (gs.filter isNot).length ∧
      F.length + (gs.filter isNot).length ≤ gs.length ∧ F.Nodup ∧ valid xs M F ∧
      ∀ h ∈ sem xs gs, can xs M F h := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[],[],by simp,by simp,by simp,by simp [valid],?_⟩
    intro h hh
    exact Or.inl (Or.inr (Or.inr (Or.inl hh)))
  | append_singleton gs g ih =>
    obtain ⟨M,F,hm,hf,nd,good,ready⟩ := ih (fun t ht => fan t (List.mem_append_left _ ht))
    obtain ⟨ok,arity⟩ := fan g (by simp)
    let w := sem xs gs
    let f := vfun w g
    have running : sem xs (gs ++ [g]) = w ++ [f] := by simp [sem,w,f,step]
    have after {M' F' : List (Fn E)} (km : M ⊆ M') (kf : F ⊆ F')
        (nf : can xs M' F' f) : ∀ h ∈ sem xs (gs ++ [g]), can xs M' F' h := by
      rw [running]
      intro h hh
      rcases List.mem_append.mp hh with ho|hn
      · exact mono km kf (ready h ho)
      · exact (List.mem_singleton.mp hn).symm ▸ nf
    by_cases inv : g.op = GateOp.not
    · have delta : ((gs ++ [g]).filter isNot).length = (gs.filter isNot).length + 1 := by
        simp [isNot, inv, List.filter_append]
      let a := (g.inputs.head?).elim (fun _ : E => false) (fun i => w.getD i (fun _ => false))
      have ha : can xs M F a := by
        cases h : g.inputs.head? with
        | none => simpa [a,h] using (show can xs M F (fun _ => false) from Or.inl (Or.inl rfl))
        | some i => simpa [a,h] using readyD xs M F w ready i
      have equiv : f = (fun x => !(a x)) := by
        obtain ⟨opg,inputs⟩ := g
        change opg = GateOp.not at inv
        subst opg
        cases inputs <;> rfl
      rcases ha with ba | ⟨b,bm,bb,eq⟩
      · refine ⟨a::M,F,by simp [delta] <;> omega,by simp [delta] <;> omega,nd,?_,?_⟩
        · exact valid_mono (List.subset_cons_self ..) good
        · exact after (List.subset_cons_self ..) (fun _ z => z)
            (Or.inr ⟨a,by simp,ba,equiv⟩)
      · refine ⟨M,F,by simp [delta] <;> omega,by simp [delta] <;> omega,nd,good,?_⟩
        have fb : f = b := by rw [equiv,eq]; funext x; simp
        exact after (fun _ z => z) (fun _ z => z) (fb.symm ▸ Or.inl bb)
    · have delta : ((gs ++ [g]).filter isNot).length = (gs.filter isNot).length := by
        have h : isNot g = false := by cases hg : g.op <;> simp_all [isNot]
        simp [List.filter_append,h]
      have kind : g.op = GateOp.and ∨ g.op = GateOp.or := by
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ok
        tauto
      obtain ⟨a,b,ha,hb,hop⟩ := binary xs M F w g ready kind arity
      by_cases seenF : f ∈ F
      · refine ⟨M,F,by simpa [delta] using hm,by simp [delta] <;> omega,nd,good,?_⟩
        exact after (fun _ z => z) (fun _ z => z) (Or.inl (Or.inr (Or.inr (Or.inr seenF))))
      · refine ⟨M,F ++ [f],by simpa [delta] using hm,by simp [delta] <;> omega,?_,?_,?_⟩
        · simpa [List.nodup_append,nd,seenF]
        · intro h hh
          rcases List.mem_append.mp hh with ho|hn
          · obtain ⟨A,B,eq,a',b',ha',hb',op'⟩ := good h ho
            exact ⟨A,B++[f],by rw [eq, List.append_assoc]; rfl,a',b',ha',hb',op'⟩
          · obtain rfl := List.mem_singleton.mp hn
            exact ⟨F,[],rfl,a,b,ha,hb,hop⟩
        · exact after (fun _ z => z) (fun _ z => List.mem_append_left _ z)
            (Or.inl (Or.inr (Or.inr (Or.inr (by simp)))))

theorem compile : ∀ (E : Type) (xs : List (E → Bool)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C →
      ∃ M F : List (E → Bool), M.length ≤ PEqualNP.NotBracket.notCount C ∧
        F.length + PEqualNP.NotBracket.notCount C ≤ C.size ∧ F.Nodup ∧
        let base := fun (P : List (E → Bool)) (h : E → Bool) =>
          h = (fun _ => false) ∨ h = (fun _ => true) ∨ h ∈ xs ∨ h ∈ P
        let can := fun (P : List (E → Bool)) (h : E → Bool) =>
          base P h ∨ ∃ a ∈ M, base P a ∧ h = (fun x => !(a x))
        (∀ h ∈ F, ∃ A B : List (E → Bool), F = A ++ h :: B ∧
            ∃ a b, can A a ∧ can A b ∧
              (h = (fun x => a x && b x) ∨ h = (fun x => a x || b x))) ∧ can F (fun x => C.eval (xs.map (fun h => h x))) := by
  intro E xs C fan
  obtain ⟨M,F,hm,hf,nd,valid,ready⟩ := build xs C.gates fan
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  have inv : isNot = fun g : Gate => decide (g.op = GateOp.not) := by
    funext g
    rcases g with ⟨op,ins⟩
    cases op <;> rfl
  have nk : (C.gates.filter isNot).length = notCount C := by rw [inv]; rfl
  rw [nk] at hm hf
  refine ⟨M,F,hm,hf,nd,valid,?_⟩
  have canout := readyD xs M F _ ready C.output
  have eq : (sem xs C.gates).getD C.output (fun _ => false) =
      fun x => C.eval (xs.map (fun h => h x)) := by
    funext x
    have h := List.getD_map (sem xs C.gates) (fun _ => false) (n := C.output) (fun f => f x)
    rw [eval_map] at h
    exact h.symm
  rw [← eq]
  exact canout

end Phase4727
