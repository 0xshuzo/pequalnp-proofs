import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace FerrersLower

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
  PEqualNP.MetaComplexity.Helpers.PermInputs

abbrev Input (n : ℕ) := Fin n → Bool
abbrev Func (n : ℕ) := Input n → Bool

def prefix {n : ℕ} (x : Input (n+2)) : Input n :=
  fun i => x i.castSucc.castSucc

def extend {n : ℕ} (f mark : Func n) (x : Input (n+2)) : Bool :=
  f (prefix x) || ((mark (prefix x) || x (Fin.last (n+1))) && x (Fin.last n).castSucc)

def extendMark {n : ℕ} (mark : Func n) (x : Input (n+2)) : Bool :=
  mark (prefix x) || x (Fin.last (n+1))

@[simp] lemma prefix_snoc {n : ℕ} (u : Input n) (y x : Bool) :
    prefix (Fin.snoc (Fin.snoc u y) x) = u := by
  funext i
  simp [prefix]

@[simp] lemma extend_snoc {n : ℕ} (f mark : Func n) (u : Input n) (y x : Bool) :
    extend f mark (Fin.snoc (Fin.snoc u y) x) = (f u || ((mark u || x) && y)) := by
  simp [extend]

@[simp] lemma mark_snoc {n : ℕ} (mark : Func n) (u : Input n) (y x : Bool) :
    extendMark mark (Fin.snoc (Fin.snoc u y) x) = (mark u || x) := by
  simp [extendMark]

lemma flipLast {n : ℕ} (f : Func (n+1)) (u : Input n)
    (h : f (Fin.snoc u true) ≠ f (Fin.snoc u false)) :
    ∃ x : Input (n+1), f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x := by
  refine ⟨Fin.snoc u false, ?_⟩
  have eq : Function.update (Fin.snoc u false) (Fin.last n)
      (!(Fin.snoc u false (Fin.last n))) = Fin.snoc u true := by
    funext i
    induction i using Fin.lastCases <;> simp [Function.update_of_ne]
  rwa [eq]

def witnesses {n : ℕ} (f mark : Func n) : Prop :=
  ∃ zero row edge : Input n, f zero = false ∧ mark zero = false ∧
    f row = false ∧ mark row = true ∧ f edge = true

lemma extend_witnesses {n : ℕ} {f mark : Func n} (hw : witnesses f mark) :
    witnesses (extend f mark) (extendMark mark) := by
  obtain ⟨z,_,e,hz,hm,_,_,he⟩ := hw
  refine ⟨Fin.snoc (Fin.snoc z false) false, Fin.snoc (Fin.snoc z false) true,
    Fin.snoc (Fin.snoc e false) false, ?_⟩
  simp [hz,hm,he]

lemma extend_lower {n r : ℕ} {f mark : Func n} (hw : witnesses f mark) (hr : 0 < r)
    (lb : ∀ s, HasCircuitSize n f s → r ≤ s) :
    ∀ s, HasCircuitSize (n+2) (extend f mark) s → r + 3 ≤ s := by
  intro s hs
  obtain ⟨z,row,e,hz,hm,hrow,hmark,he⟩ := hw
  have hd := flipLast (extend f mark) (Fin.snoc z true) (by simp [hz,hm])
  have nc (b : Bool) : ∃ u v : Input (n+1),
      extend f mark (Fin.snoc u b) ≠ extend f mark (Fin.snoc v b) :=
    ⟨Fin.snoc z false, Fin.snoc e false, by simp [hz,he]⟩
  obtain ⟨b,t,ht,hcof⟩ := gate_elim_two (n+1) _ s hd nc hs
  let cof : Func (n+1) := fun u => extend f mark (Fin.snoc u b)
  have hd' := flipLast cof row (by simp [cof,hrow,hmark])
  have nc' : ∃ u v : Input n, cof (Fin.snoc u false) ≠ cof (Fin.snoc v false) :=
    ⟨z,e,by simp [cof,hz,he]⟩
  have lower (q : ℕ) (hq : HasCircuitSize (n+1) cof (q+1)) : r ≤ q := by
    apply lb
    have hminor := gate_elim n cof false q hd' nc' hq
    simpa [cof] using hminor
  cases t with
  | zero =>
    have hone : HasCircuitSize (n+1) cof 1 := by
      obtain ⟨C,hC,hlen,hev⟩ := hcof
      exact ⟨C,hC,by omega,hev⟩
    have := lower 0 hone
    omega
  | succ t =>
    have := lower t hcof
    omega

def dim : ℕ → ℕ
  | 0 => 2
  | k+1 => dim k + 2

def staircase : (k : ℕ) → Func (dim k) × Func (dim k)
  | 0 => (fun x => x 0 && x 1, fun x => x 0)
  | k+1 => (extend (staircase k).1 (staircase k).2, extendMark (staircase k).2)

lemma staircase_witnesses (k : ℕ) : witnesses (staircase k).1 (staircase k).2 := by
  induction k with
  | zero =>
    refine ⟨fun _ => false, fun i => decide (i = 0), fun _ => true, ?_⟩
    decide
  | succ k ih => exact extend_witnesses ih

theorem staircase_lower (k : ℕ) : ∀ s, HasCircuitSize (dim k) (staircase k).1 s → 3*k+1 ≤ s := by
  induction k with
  | zero =>
    intro s hs
    have dep (i : Fin 2) (hi : i ∈ (Finset.univ : Finset (Fin 2))) :
        ∃ x : Input 2, (staircase 0).1 (Function.update x i (!x i)) ≠ (staircase 0).1 x := by
      refine ⟨fun _ => true, ?_⟩
      fin_cases i <;> decide
    have hb := dep_lower_set 2 (staircase 0).1 Finset.univ dep s hs
    have hcard : (Finset.univ : Finset (Fin 2)).card = 2 := by decide
    rw [hcard] at hb
    omega
  | succ k ih =>
    intro s hs
    have hb := extend_lower (staircase_witnesses k) (by omega : 0 < 3*k+1) ih s hs
    omega

end FerrersLower
