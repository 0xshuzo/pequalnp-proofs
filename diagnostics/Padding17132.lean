import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_17132
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)


open PEqualNP.MetaComplexity
def flag (g : Gate) := g.op.eval [true,false]
def ors (C : Circuit) := (C.gates.filter flag).length
def ands (C : Circuit) := (C.gates.filter (fun g => !(flag g))).length
def dummy : Gate := ⟨.or,[]⟩
def pad (C : Circuit) (k : Nat) : Circuit := ⟨C.gates ++ List.replicate k dummy,C.output⟩
theorem dummyOn : flag dummy=true := rfl
theorem isPad (C : Circuit) (k : Nat) (hc : Monotone2 C) : Monotone2 (pad C k) := by
  intro g hg
  change g ∈ C.gates ++ List.replicate k dummy at hg
  rcases List.mem_append.mp hg with old | new
  · exact hc g old
  · have eq : g=dummy := (List.mem_replicate.mp new).2
    subst g
    exact ⟨Or.inr rfl,by decide⟩

theorem dummyCounts (C : Circuit) (k : Nat) :
    ors (pad C k) = ors C+k ∧ ands (pad C k)=ands C := by
  have h1 : (List.replicate k dummy).filter flag=List.replicate k dummy := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, List.filter_cons,dummyOn,ih]
  have h2 : (List.replicate k dummy).filter (fun g => !(flag g))=[] := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ,List.filter_cons,dummyOn,ih]
  simp [ors,ands,pad,List.filter_append,h1,h2]

theorem output_valid {n} (C : Circuit) (x : Fin n → Bool) (h : circuitFun n C x=true) :
    C.output < n+C.gates.length := by
  by_contra! bad
  change (wf C.gates (List.ofFn x)).getD C.output false=true at h
  have hlen : (wf C.gates (List.ofFn x)).length≤ C.output := by simpa [wf_len] using bad
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none hlen] at h
  contradiction

theorem pad_fun {n} (C : Circuit) (k : Nat) (ok : C.output<n+C.gates.length) :
    circuitFun n (pad C k)=circuitFun n C := by
  funext x
  exact wf_prefix _ _ _ _ (by simpa using ok)
abbrev Posted := ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (200 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →               (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →                 have x13 : ℕ := (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length;                 (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ x13 → (100 : ℕ) * x13 < x2 * x1 → ¬x1 % (2 : ℕ) = (0 : ℕ) → x2 * x1 - (100 : ℕ) * x13 ≤ (100 : ℕ) * (List.filter (fun (x17 : PEqualNP.CircuitLowerBounds.Gate) => !x17.op.eval [Bool.true, Bool.false]) x5.gates).length
abbrev Padded := ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (200 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →               (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →                  ¬x1 % 2 = 0 → x2 * x1 ≤ 100 * (ands x5 + max (ors x5) (2*x1^2+1))

theorem padding_equivalence : Posted ↔ Padded := by
  constructor
  · intro claim q N I inst C hq ord lines unique mon hit off odd
    let k := 2*q^2+1-ors C
    have npos : 0<N := by omega
    let l : Fin N := ⟨0,npos⟩
    have pos : 0 < Fintype.card {p : Fin N // I p l} := by rw [lines]; omega
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp pos
    have ok := output_valid C _ (hit v.1 l v.2)
    have law := pad_fun C k ok
    obtain ⟨ho,ha⟩ := dummyCounts C k
    have cost : ors (pad C k)=max (ors C) (2*q^2+1) := by rw [ho]; dsimp [k]; omega
    have H := claim q N I (pad C k) hq ord lines unique (isPad _ _ mon)
      (by rw [law]; exact hit) (by rw [law]; exact off)
    change 2*q^2+1≤ors (pad C k) → 100*ors (pad C k)<N*q →
      ¬q%2=0 → N*q-100*ors (pad C k)≤100*ands (pad C k) at H
    rw [cost,ha] at H
    by_cases small : 100*max (ors C) (2*q^2+1)<N*q
    · have H' := H (Nat.le_max_right _ _) small odd
      omega
    · omega
  · intro claim q N I inst C hq ord lines unique mon hit off
    change 2*q^2+1≤ors C → 100*ors C<N*q → ¬q%2=0 → N*q-100*ors C≤100*ands C
    intro floor _ odd
    have H := claim q N I C hq ord lines unique mon hit off odd
    rw [max_eq_left floor] at H
    omega
end PEqualNP.Outside.L_meta_17132
