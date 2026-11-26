import PEqualNP.Defs

namespace Search9820
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

deriving instance DecidableEq for GateOp

def value (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)
def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl (fun s g => s++[value g s]) w

def LE (a b : List Bool) := ∀i,a.getD i false=true → b.getD i false=true

theorem stepLE {a b : List Bool} {u v : Bool} (hl : a.length=b.length) (h : LE a b) (s : u=true→v=true) :
    LE (a++[u]) (b++[v]) := by
  intro i on
  by_cases lt : i<a.length
  · rw [List.getD_append _ _ _ _ lt] at on
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i on
  · by_cases e : i=a.length
    · subst i
      rw [hl]
      simpa using s (by simpa using on)
    · rw [List.getD_eq_default _ _ (by simp;omega)] at on
      contradiction

theorem valueLE {a b : List Bool} (g : Gate) (op : g.op=.and ∨ g.op=.or) (h : LE a b) :
    value g a=true → value g b=true := by
  rcases op with eq|eq
  · simpa [value,eq,GateOp.eval,List.all_eq_true] using
      (show (∀i∈g.inputs,a.getD i false=true) → ∀i∈g.inputs,b.getD i false=true from fun s i hi=>h i (s i hi))
  · simpa [value,eq,GateOp.eval,List.any_eq_true] using
      (show (∃i∈g.inputs,a.getD i false=true) → ∃i∈g.inputs,b.getD i false=true from fun ⟨i,mem,on⟩=>⟨i,mem,h i on⟩)


def trace : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w =>
    let u := value g w
    let t := trace gs (w ++ [u])
    if g.op = .not then u :: t else t

theorem ordered_run (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (a b : List Bool) (len : a.length = b.length) (h : LE a b)
    (tr : trace gs a = trace gs b) :
    LE (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have rest : ∀ t ∈ gs, t.op = .and ∨ t.op = .or ∨ t.op = .not :=
      fun t ht => ops t (List.mem_cons_of_mem _ ht)
    change LE (run gs (a ++ [value g a])) (run gs (b ++ [value g b]))
    apply ih rest _ _ (by simp [len])
    · apply stepLE len h
      rcases ops g List.mem_cons_self with e | e | e
      · exact valueLE g (Or.inl e) h
      · exact valueLE g (Or.inr e) h
      · simp only [trace, e, ite_true, List.cons.injEq] at tr
        exact fun ha => tr.1.symm.trans ha
    · by_cases e : g.op = .not
      · simp only [trace, e, ite_true, List.cons.injEq] at tr
        exact tr.2
      · simpa only [trace, e, ite_false] using tr

def bits {n : ℕ} (A : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ A)

def signature {n : ℕ} (C : Circuit) (A : Finset (Fin n)) : List Bool :=
  trace C.gates (List.ofFn (bits A))

theorem on_fiber {n : ℕ} (C : Circuit) (legal : FanInTwo C)
    {A B : Finset (Fin n)} (sub : A ⊆ B) (sig : signature C A = signature C B) :
    C.eval (List.ofFn (bits A)) = true → C.eval (List.ofFn (bits B)) = true := by
  apply ordered_run C.gates (fun g hg => by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (legal g hg).1)
    _ _ (by simp) _ sig C.output
  intro j on
  by_cases small : j < n
  · have a : (⟨j,small⟩ : Fin n) ∈ A := by
      simpa [bits, List.getD_eq_getElem?_getD, small] using on
    simpa [bits, List.getD_eq_getElem?_getD, small] using sub a
  · simp [List.getD_eq_getElem?_getD, small] at on

def boundary {n : ℕ} {T : Type} (tag : Finset (Fin n) → T)
    (F : Finset (Fin n) → Bool) (s : Finset (Fin n)) : Prop :=
  (F s = true ∧ ∀ t, t ⊂ s → tag t = tag s → F t = false) ∨
  (F s = false ∧ ∀ t, s ⊂ t → tag t = tag s → F t = true)

theorem check_boundary {n : ℕ} {T : Type} (tag : Finset (Fin n) → T)
    (F V : Finset (Fin n) → Bool)
    (order : ∀ a b, a ⊆ b → tag a = tag b → V a = true → V b = true)
    (tests : ∀ s, boundary tag F s → V s = F s) (s : Finset (Fin n)) : V s = F s := by
  classical
  cases hs : F s with
  | true =>
    let good := s.powerset.filter (fun t => tag t = tag s ∧ F t = true)
    have ok : s ∈ good := by simp [good,hs]
    obtain ⟨m, hm, hmin⟩ := good.exists_min_image Finset.card ⟨s,ok⟩
    obtain ⟨ms,mt,mf⟩ : m ⊆ s ∧ tag m = tag s ∧ F m = true := by simpa [good] using hm
    have bd : boundary tag F m := by
      refine Or.inl ⟨mf,fun t lt eq => ?_⟩
      cases ht : F t with
      | false => rfl
      | true =>
        have inc : t ∈ good := Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (lt.le.trans ms),eq.trans mt,ht⟩
        exact False.elim ((Nat.not_lt_of_ge (hmin t inc)) (Finset.card_lt_card lt))
    exact order m s ms mt ((tests m bd).trans mf)
  | false =>
    let good := (Finset.univ : Finset (Finset (Fin n))).filter (fun t => s ⊆ t ∧ tag t = tag s ∧ F t = false)
    have ok : s ∈ good := by simp [good,hs]
    obtain ⟨m, hm, hmax⟩ := good.exists_max_image Finset.card ⟨s,ok⟩
    obtain ⟨sm,mt,mf⟩ : s ⊆ m ∧ tag m = tag s ∧ F m = false := by simpa [good] using hm
    have bd : boundary tag F m := by
      refine Or.inr ⟨mf,fun t lt eq => ?_⟩
      cases ht : F t with
      | true => rfl
      | false =>
        have inc : t ∈ good := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,sm.trans lt.le,eq.trans mt,ht⟩
        exact False.elim ((Nat.not_lt_of_ge (hmax t inc)) (Finset.card_lt_card lt))
    cases hv : V s with
    | false => rfl
    | true =>
      have vm := order s m sm mt.symm hv
      have z := (tests m bd).trans mf
      simp [vm] at z

theorem accept_from_tests {n : ℕ} (C : Circuit) (legal : FanInTwo C)
    (F : (Fin n → Bool) → Bool) (s : ℕ) (size : C.size ≤ s)
    (checks : ∀ A, boundary (signature C) (fun B => F (bits B)) A →
      C.eval (List.ofFn (bits A)) = F (bits A)) : HasCircuitSize n F s := by
  refine ⟨C, legal, size, fun x => ?_⟩
  let A : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)
  have eq : bits A = x := by
    funext i
    cases h : x i <;> simp [bits,A,h]
  have all := check_boundary (signature C) (fun B => F (bits B))
    (fun B => C.eval (List.ofFn (bits B))) (fun _ _ => on_fiber C legal) checks A
  simpa only [eq] using all

def control : Circuit := ⟨[
  ⟨.or,[1,9]⟩,
  ⟨.or,[8,10]⟩,
  ⟨.and,[6,11]⟩,
  ⟨.or,[7,1]⟩,
  ⟨.and,[2,13]⟩,
  ⟨.or,[0,3]⟩,
  ⟨.or,[9,15]⟩,
  ⟨.and,[4,16]⟩,
  ⟨.or,[5,3]⟩,
  ⟨.and,[8,18]⟩,
  ⟨.or,[5,9]⟩,
  ⟨.and,[7,20]⟩,
  ⟨.and,[0,5]⟩,
  ⟨.or,[19,12]⟩,
  ⟨.or,[21,23]⟩,
  ⟨.or,[22,14]⟩,
  ⟨.or,[17,24]⟩,
  ⟨.or,[26,25]⟩],27⟩

def legal (g : Gate) : Bool :=
  decide (g.op = .and ∨ g.op = .or ∨ g.op = .not) && decide (g.inputs.length ≤ 2)

theorem fanin : FanInTwo control := by
  have hall : control.gates.all legal = true := by decide +kernel
  intro g hg
  have h := (List.all_eq_true.1 hall) g hg
  simpa only [legal, Bool.and_eq_true, decide_eq_true_eq, Set.mem_insert_iff, Set.mem_singleton_iff] using h


def target (x : Fin 10 → Bool) : Bool := (x 1 && x 2) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem control_correct : HasCircuitSize 10 target 18 := by
  refine ⟨control, fanin, by decide +kernel, fun x => ?_⟩
  change (((x 4 && ((x 9 || ((x 0 || (x 3 || false)) || false)) && true)) || (((x 7 && ((x 5 || (x 9 || false)) && true)) || (((x 8 && ((x 5 || (x 3 || false)) && true)) || ((x 6 && ((x 8 || ((x 1 || (x 9 || false)) || false)) && true)) || false)) || false)) || false)) || (((x 0 && (x 5 && true)) || ((x 2 && ((x 7 || (x 1 || false)) && true)) || false)) || false)) = _
  simp only [target, Bool.or_false, Bool.and_true, Bool.and_or_distrib_left, Bool.and_or_distrib_right]
  ac_rfl

theorem witness_from_tests (C : Circuit) (h : FanInTwo C) (k : C.size ≤ 17)
    (check : ∀ s, boundary (signature C) (fun t => target (bits t)) s →
      C.eval (List.ofFn (bits s)) = target (bits s)) : HasCircuitSize 10 target 17 :=
  accept_from_tests C h target 17 k check

theorem trace_join (a b : List Gate) (w : List Bool) :
    trace (a ++ b) w = trace a w ++ trace b (run a w) := by
  induction a generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (if g.op = .not then value g w :: trace (gs ++ b) (w ++ [value g w])
      else trace (gs ++ b) (w ++ [value g w])) = _
    by_cases e : g.op = .not
    · simp [trace, e, run, ih]
    · simp [trace, e, run, ih]

theorem no_trace (gs : List Gate) (w : List Bool) (free : ∀ g ∈ gs, g.op ≠ .not) :
    trace gs w = [] := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [trace, if_neg (free _ List.mem_cons_self)]
    exact ih _ (fun t ht => free _ (List.mem_cons_of_mem _ ht))

def withGuard (before : List Gate) (j : ℕ) (after : List Gate) (out : ℕ) : Circuit :=
  ⟨before ++ ⟨.not,[j]⟩ :: after, out⟩

def guardValue {n : ℕ} (before : List Gate) (j : ℕ) (A : Finset (Fin n)) : Bool :=
  (run before (List.ofFn (bits A))).getD j false

theorem guard_trace {n : ℕ} (before after : List Gate) (j out : ℕ)
    (prev : ∀ g ∈ before, g.op ≠ .not) (post : ∀ g ∈ after, g.op ≠ .not) (A : Finset (Fin n)) :
    signature (withGuard before j after out) A = [!(guardValue before j A)] := by
  change trace (before ++ ⟨GateOp.not,[j]⟩ :: after) (List.ofFn (bits A)) = _
  rw [trace_join, no_trace _ _ prev]
  simp [trace, no_trace after _ post, guardValue, value, GateOp.eval]

theorem fixed_guard_witness (before after : List Gate) (j out : ℕ)
    (prev : ∀ g ∈ before, g.op ≠ .not) (post : ∀ g ∈ after, g.op ≠ .not)
    (legal : FanInTwo (withGuard before j after out))
    (size : (withGuard before j after out).size ≤ 17)
    (tests : ∀ A, boundary (guardValue before j) (fun B => target (bits B)) A →
      (withGuard before j after out).eval (List.ofFn (bits A)) = target (bits A)) :
    HasCircuitSize 10 target 17 := by
  apply witness_from_tests _ legal size
  intro A test
  apply tests
  rcases test with ⟨trueA,minA⟩ | ⟨falseA,maxA⟩
  · exact Or.inl ⟨trueA, fun t lt eq => minA t lt (by
      rw [guard_trace _ _ _ _ prev post, guard_trace _ _ _ _ prev post, eq])⟩
  · exact Or.inr ⟨falseA, fun t lt eq => maxA t lt (by
      rw [guard_trace _ _ _ _ prev post, guard_trace _ _ _ _ prev post, eq])⟩

end Search9820
