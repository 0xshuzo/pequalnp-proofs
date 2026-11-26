import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18723
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def graphFn {n : ℕ} (E : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  E.any fun e => x e.1 && x e.2


def adj (E : List (Fin n × Fin n)) (a b : Fin n) : Prop :=
  (a,b) ∈ E ∨ (b,a) ∈ E

theorem adjSymm (E : List (Fin n × Fin n)) (a b : Fin n) : adj E a b ↔ adj E b a := or_comm

theorem freeNeighbor (E : List (Fin n × Fin n)) (v u w z : Fin n)
    (noFour : ∀ a b c d, a ≠ c → b ≠ d → adj E a b → adj E b c → adj E c d → adj E d a → False)
    (uw : u ≠ w) (vz : v ≠ z) (vu : adj E v u) (vw : adj E v w) :
    ∃ t, (t=u ∨ t=w) ∧ adj E v t ∧ ¬ adj E z t := by
  classical
  by_cases zu : adj E z u
  · refine ⟨w,Or.inr rfl,vw,fun zw => ?_⟩
    exact noFour v u z w vz uw vu ((adjSymm E z u).mp zu) zw ((adjSymm E v w).mp vw)
  · exact ⟨u,Or.inl rfl,vu,zu⟩

def pairBits (z t : Fin n) (i : Fin n) : Bool := decide (i=z ∨ i=t)

theorem pairOff (E : List (Fin n × Fin n)) (z t : Fin n)
    (loops : ∀ e ∈ E, e.1 ≠ e.2) (indep : ¬ adj E z t) :
    graphFn E (pairBits z t) = false := by
  classical
  cases h : graphFn E (pairBits z t) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨⟨a,b⟩,he,hbits⟩ := (List.any_eq_true.mp h)
    change (pairBits z t a && pairBits z t b) = true at hbits
    simp only [pairBits,Bool.and_eq_true,decide_eq_true_eq] at hbits
    rcases hbits with ⟨az | at',bz | bt⟩
    · exact loops _ he (az.trans bz.symm)
    · exact indep (Or.inl (by simpa [az,bt] using he))
    · exact indep (Or.inr (by simpa [at',bz] using he))
    · exact loops _ he (at'.trans bt.symm)

theorem togglesPair (E : List (Fin n × Fin n)) (v u w z : Fin n)
    (loops : ∀ e ∈ E, e.1 ≠ e.2)
    (noFour : ∀ a b c d, a ≠ c → b ≠ d → adj E a b → adj E b c → adj E c d → adj E d a → False)
    (uw : u ≠ w) (vz : v ≠ z) (vu : adj E v u) (vw : adj E v w) :
    ∃ x : Fin n → Bool, x z = true ∧ x v = false ∧ graphFn E x = false ∧
      graphFn E (Function.update x v true) = true := by
  classical
  obtain ⟨t,_,vt,zt⟩ := freeNeighbor E v u w z noFour uw vz vu vw
  have tv : t ≠ v := by
    intro eq; subst t
    rcases vt with he|he <;> exact loops _ he rfl
  refine ⟨pairBits z t, by simp [pairBits], by simp [pairBits,vz,tv.symm], pairOff E z t loops zt, ?_⟩
  apply List.any_eq_true.mpr
  rcases vt with he|he
  · exact ⟨(v,t),he,by simp [Function.update_of_ne tv,pairBits]⟩
  · exact ⟨(t,v),he,by simp [Function.update_of_ne tv,pairBits]⟩


def evalGate (g : Gate) (a : List Bool) := g.op.eval (g.inputs.map fun k => a.getD k false)
def advance (a : List Bool) (g : Gate) := a ++ [evalGate g a]
def near (v : ℕ) (a b : List Bool) := a.length=b.length ∧ ∀ j, j ≠ v → a.getD j false = b.getD j false

theorem nearStep (v : ℕ) (a b : List Bool) (g : Gate) (h : near v a b)
    (same : evalGate g a = evalGate g b) : near v (advance a g) (advance b g) := by
  obtain ⟨len,eq⟩ := h
  refine ⟨by simp [advance,len], ?_⟩
  intro j hj
  by_cases small : j < b.length
  · simpa only [advance, List.getD_append _ _ _ _ small,
      List.getD_append _ _ _ _ (by omega : j < a.length)] using eq j hj
  · simp only [advance,List.getD_append_right _ _ _ _ (by omega : a.length ≤ j),
      List.getD_append_right _ _ _ _ (by omega : b.length ≤ j),len,same]

theorem foldMask (v z : ℕ) (gs : List Gate) (a b : List Bool) (h : near v a b)
    (za : z < a.length) (ha : a.getD z false = true) (hb : b.getD z false = true)
    (sem : ∀ g ∈ gs, v ∈ g.inputs → g.op = .or ∧ z ∈ g.inputs) :
    near v (gs.foldl advance a) (gs.foldl advance b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have l := h.1
    have zb : z < b.length := by omega
    have val : evalGate g a = evalGate g b := by
      by_cases read : v ∈ g.inputs
      · obtain ⟨op,member⟩ := sem g (by simp) read
        have on (s : List Bool) (hs : s.getD z false=true) : evalGate g s=true := by
          simp only [evalGate,op,GateOp.eval,List.any_map,Function.comp_def,List.any_eq_true]
          exact ⟨z,member,hs⟩
        exact (on a ha).trans (on b hb).symm
      · apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        exact h.2 j (fun eq => read (eq ▸ hj))
    apply ih (advance a g) (advance b g) (nearStep v a b g h val)
    · simp [advance]; omega
    · simpa only [advance,List.getD_append _ _ _ _ za] using ha
    · simpa only [advance,List.getD_append _ _ _ _ zb] using hb
    · intro k hk; exact sem k (by simp [hk])

theorem rawPin {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    (C.gates.foldl advance (List.ofFn x)).getD i.val false = x i := by
  have aux (gs : List Gate) (s : List Bool) (hi : i.val < s.length) :
      (gs.foldl advance s).getD i.val false = s.getD i.val false := by
    induction gs generalizing s with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl advance (advance s g)).getD i.val false = _
      rw [ih _ (by simp [advance]; omega)]
      exact List.getD_append _ _ _ _ hi
  rw [aux C.gates _ (by simpa using i.isLt)]
  simp

theorem noRawMask (E : List (Fin n × Fin n)) (v u w z : Fin n) (C : Circuit)
    (loops : ∀ e ∈ E, e.1 ≠ e.2)
    (noFour : ∀ a b c d, a ≠ c → b ≠ d → adj E a b → adj E b c → adj E c d → adj E d a → False)
    (uw : u ≠ w) (vz : v ≠ z) (vu : adj E v u) (vw : adj E v w)
    (comp : ∀ x, C.eval (List.ofFn x) = graphFn E x) :
    ¬ (∀ g ∈ C.gates, v.val ∈ g.inputs → g.op = .or ∧ z.val ∈ g.inputs) := by
  classical
  intro sem
  obtain ⟨x,xz,xv,off,on⟩ := togglesPair E v u w z loops noFour uw vz vu vw
  let y := Function.update x v true
  have yz : y z = true := by simpa [y,Function.update_of_ne vz.symm] using xz
  have raw : near v.val (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro j ne
    by_cases lt : j < n
    · let k : Fin n := ⟨j,lt⟩
      have kv : k ≠ v := by intro e; exact ne (congrArg Fin.val e)
      change (List.ofFn x).getD k.val false = (List.ofFn y).getD k.val false
      simp [y,Function.update_of_ne kv]
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt lt),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt lt)]
  have folded := foldMask v.val z.val C.gates (List.ofFn x) (List.ofFn y) raw
    (by simpa using z.isLt) (by simpa using xz) (by simpa using yz) sem
  have out : C.output ≠ v.val := by
    intro e
    have nloop : ¬ adj E v v := by rintro (a|a) <;> exact loops _ a rfl
    have bad := (comp (pairBits v v)).trans (pairOff E v v loops nloop)
    change (C.gates.foldl advance (List.ofFn (pairBits v v))).getD C.output false = false at bad
    rw [e,rawPin] at bad
    simp [pairBits] at bad
  have same : C.eval (List.ofFn x) = C.eval (List.ofFn y) := folded.2 C.output out
  have ff := comp x
  have tt := comp y
  change graphFn E y = true at on
  simp_all

end PEqualNP.Outside.L_meta_18723
