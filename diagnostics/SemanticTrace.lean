import PEqualNP.Defs
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
  | cons g gs ih => simp only [List.foldl_cons,List.length_cons,ih,stage,List.length_append,List.length_singleton]; omega
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
    simp [val,fn,q,List.map_map,Function.comp_def,eq]
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
