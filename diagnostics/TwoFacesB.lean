import PEqualNP.Outside.L_meta_670
namespace Research9755.Trace
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Fn (n : Nat) := (Fin n → Bool) → Bool
def z : Fn n := fun _ => false
def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def stage (w : List Bool) (g : Gate) := w ++ [val g w]
def wires (s : List Gate) (x : Fin n → Bool) := s.foldl stage (List.ofFn x)
def fn (w : List (Fn n)) (g : Gate) : Fn n :=
  fun x => g.op.eval (g.inputs.map fun i => (w.getD i z) x)
def advance (w : List (Fn n)) (g : Gate) := w ++ [fn w g]
def run (w : List (Fn n)) (gs : List Gate) := gs.foldl advance w
noncomputable def fee (w : List (Fn n)) (gs : List Gate) : Nat := by
  classical
  exact match gs with
  | [] => 0
  | g :: tail => (if fn w g = z ∨ fn w g ∈ w then 0 else 1) + fee (advance w g) tail

def allowed (g : Gate) : Prop :=
  (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) ∧ g.inputs.length ≤ 2
def avail (s : List Gate) (v : Fn n) : Prop :=
  v = z ∨ ∃ i, i < n+s.length ∧ ∀ x, (wires s x).getD i false = v x
theorem length_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl stage w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons,List.length_cons,ih,stage,List.length_append,List.length_singleton,List.length_nil]; omega
theorem length_wires (s : List Gate) (x : Fin n → Bool) :
    (wires s x).length = n+s.length := by simp [wires,length_fold]
theorem indexed {v : Fn n} {s : List Gate} (h : avail s v) :
    ∃ i, ∀ x, (wires s x).getD i false = v x := by
  rcases h with rfl | ⟨i,_,a⟩
  · refine ⟨n+s.length,fun x => ?_⟩
    have le : (wires s x).length ≤ n+s.length := (length_wires s x).le
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none le,z]
  · exact ⟨i,a⟩
theorem append_wires (s : List Gate) (g : Gate) (x : Fin n → Bool) :
    wires (s++[g]) x = wires s x ++ [val g (wires s x)] := by
  simp [wires,List.foldl_append,stage]
theorem keep {s : List Gate} {v : Fn n} (g : Gate) (h : avail s v) : avail (s++[g]) v := by
  rcases h with h | ⟨i,hi,ev⟩
  · exact Or.inl h
  refine Or.inr ⟨i,by simp; omega,fun x => ?_⟩
  rw [append_wires]
  have lt : i < (wires s x).length := (length_wires s x).symm ▸ hi
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt] using ev x
theorem availableAt {w : List (Fn n)} {s : List Gate} (h : ∀ v∈w, avail s v) (i : Nat) :
    avail s (w.getD i z) := by
  by_cases hi : i<w.length
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] using h w[i] (List.getElem_mem hi)
  · have le := Nat.le_of_not_gt hi
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none le,avail]

theorem extend {w : List (Fn n)} {s : List Gate} (h : ∀ v∈w, avail s v) (g : Gate) (ok : allowed g) :
    ∃ q : Gate, allowed q ∧ avail (s++[q]) (fn w g) := by
  classical
  have which (i : Nat) := indexed (availableAt h i)
  let ix (i : Nat) := (which i).choose
  have eq (i : Nat) (x : Fin n → Bool) : (wires s x).getD (ix i) false = (w.getD i z) x :=
    (which i).choose_spec x
  let q : Gate := ⟨g.op,g.inputs.map ix⟩
  refine ⟨q,⟨ok.1,by simpa [q] using ok.2⟩,Or.inr ⟨n+s.length,by simp,fun x => ?_⟩⟩
  have v : val q (wires s x) = fn w g x := by
    change g.op.eval ((g.inputs.map ix).map (fun j => (wires s x).getD j false)) = _
    rw [List.map_map]
    apply congrArg g.op.eval
    exact List.map_congr_left fun i _ => eq i x
  rw [append_wires,← length_wires s x]
  simpa [List.getD_eq_getElem?_getD] using v

theorem compile (gs : List Gate) (w : List (Fn n)) (s : List Gate)
    (legal : ∀ g∈gs,allowed g) (prior : ∀ g∈s,allowed g) (rep : ∀ v∈w,avail s v) :
    ∃ t : List Gate, (∀ g∈t,allowed g) ∧ t.length ≤ s.length + fee w gs ∧ ∀ v∈run w gs, avail t v := by
  classical
  induction gs generalizing w s with
  | nil => exact ⟨s,prior,by simp [fee],rep⟩
  | cons g tail ih =>
    have rest : ∀ j∈tail,allowed j := fun j hj => legal j (by simp [hj])
    by_cases seen : fn w g = z ∨ fn w g ∈ w
    · have h : avail s (fn w g) := seen.elim Or.inl (fun hv => rep _ hv)
      have next : ∀ v∈advance w g,avail s v := by
        intro v hv
        rcases List.mem_append.mp hv with a | b
        · exact rep _ a
        · obtain rfl := List.mem_singleton.mp b
          exact h
      obtain ⟨t,good,cost,holds⟩ := ih (advance w g) s rest prior next
      exact ⟨t,good,by simpa [fee,seen] using cost,holds⟩
    · obtain ⟨q,ok,h⟩ := extend rep g (legal _ (by simp))
      have next : ∀ v∈advance w g,avail (s++[q]) v := by
        intro v hv
        rcases List.mem_append.mp hv with a | b
        · exact keep q (rep _ a)
        · obtain rfl := List.mem_singleton.mp b
          exact h
      have good : ∀ j∈s++[q],allowed j := by
        intro j hj
        rcases List.mem_append.mp hj with a | b
        · exact prior _ a
        · obtain rfl := List.mem_singleton.mp b
          exact ok
      obtain ⟨t,fit,cost,holds⟩ := ih (advance w g) (s++[q]) rest good next
      refine ⟨t,fit,?_,holds⟩
      simp only [fee,if_neg seen,List.length_append,List.length_singleton] at *
      omega
end Research9755.Trace

namespace Research9755.Trace
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def read (w : List (Fn n)) (x : Fin n → Bool) := w.map (fun f => f x)
theorem read_at (w : List (Fn n)) (x : Fin n → Bool) (i : Nat) :
    (read w x).getD i false = (w.getD i z) x := by
  induction w generalizing i with
  | nil => simp [read,List.getD_eq_getElem?_getD,z]
  | cons a w ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i
theorem read_adv (w : List (Fn n)) (x : Fin n → Bool) (g : Gate) :
    read (advance w g) x = stage (read w x) g := by
  change (w++[fn w g]).map (fun f => f x) = read w x ++ [val g (read w x)]
  rw [List.map_append]
  apply congrArg (fun a : List Bool => read w x ++ a)
  change [fn w g x] = [val g (read w x)]
  apply congrArg (fun a : Bool => [a])
  exact congrArg g.op.eval (List.map_congr_left fun i _ => (read_at w x i).symm)
theorem read_run (w : List (Fn n)) (gs : List Gate) (x : Fin n → Bool) :
    read (run w gs) x = gs.foldl stage (read w x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change read (run (advance w g) gs) x = gs.foldl stage (stage (read w x) g)
    rw [ih,read_adv]
theorem raw_avail (k : Fin n) : avail ([] : List Gate) (fun x : Fin n → Bool => x k) := by
  refine Or.inr ⟨k.val,by simpa using k.isLt,fun x => ?_⟩
  simp [wires,List.getD_eq_getElem?_getD,k.isLt]

theorem fee_bound (C : Circuit) (w : List (Fn n)) (fit : FanInTwo C)
    (raw : ∀ v∈w,avail ([] : List Gate) v) :
    HasCircuitSize n ((run w C.gates).getD C.output z) (fee w C.gates) := by
  obtain ⟨t,good,sz,rep⟩ := compile C.gates w [] fit (by simp) raw
  obtain ⟨i,hi⟩ := indexed (availableAt rep C.output)
  exact ⟨⟨t,i⟩,good,by simpa [Circuit.size] using sz,hi⟩

def target (x : Fin 10 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def h (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def eraser (side : Bool) : Fin 10 → Option (Fin 9) :=
  if side then ![some 4,none,some 7,some 5,some 0,some 3,some 6,some 2,some 8,some 1]
  else ![none,some 4,some 0,some 1,some 6,some 7,some 3,some 5,some 2,some 8]
def pull (s : Bool) (x : Fin 9 → Bool) (j : Fin 10) := (eraser s j).elim false x
def lowerBank (s : Bool) : List (Fn 9) := List.ofFn fun i : Fin 10 => fun x => pull s x i
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem equals_minor : ∀ s x, target (pull s x) = h x := by decide +kernel
theorem projected_bank (s : Bool) (x : Fin 9 → Bool) :
    read (lowerBank s) x = List.ofFn (pull s x) := by
  simp [read,lowerBank,List.map_ofFn]
theorem endpoint_fee (C : Circuit) (fit : FanInTwo C) (ev : ∀ x, C.eval (List.ofFn x) = target x)
    (s : Bool) : 16 ≤ fee (lowerBank s) C.gates := by
  have raw : ∀ v∈lowerBank s,avail ([] : List Gate) v := by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    cases eq : eraser s i with
    | none => exact Or.inl (by funext y; simp [pull,eq,z])
    | some k => simpa [pull,eq] using raw_avail k
  have got := fee_bound C (lowerBank s) fit raw
  have hx : (run (lowerBank s) C.gates).getD C.output z = h := by
    funext x
    rw [← read_at,read_run,projected_bank]
    exact (ev (pull s x)).trans (equals_minor s x)
  rw [hx] at got
  by_contra! low
  obtain ⟨c,fitc,cost,valc⟩ := got
  exact PEqualNP.Outside.L_meta_670 ⟨c,fitc,by omega,valc⟩
end Research9755.Trace
