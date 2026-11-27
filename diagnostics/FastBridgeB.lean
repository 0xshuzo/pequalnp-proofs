import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9929.FastBridge
abbrev Sig := BitVec 64
def zero : Sig := 0
def one : Sig := BitVec.allOnes 64
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def bit (i : Fin 64) (a : Sig) : Bool := a.getLsbD i.val
abbrev Row := Fin 64
def target : Sig := 0x80c0e0f0f8fcfe
def reserve (S : Finset Sig) (a b : Sig) (ka kb : Bool) : Finset Sig :=
  S.filter (fun v => (v≠a ∨ ka=true) ∧ (v≠b ∨ kb=true))
abbrev ProofCut := Nat → Nat → Finset Sig → Bool
def nextCut (check : ProofCut) (k n : Nat) (S : Finset Sig) (z : Sig) (U : Finset Sig) :=
  if z∈S ∨ z=zero ∨ z=one ∨ k+1 < (insert z U).card then true else check k n (insert z U)
def allSet (S : Finset Sig) (p : Sig → Bool) := (S.filter (fun v => p v = false)).card == 0
theorem allSet_iff {S : Finset Sig} {p : Sig → Bool} :
    allSet S p=true ↔ ∀a∈S,p a=true := by
  simp only [allSet,beq_iff_eq,Finset.card_eq_zero]
  constructor
  · intro h a ha
    cases e : p a with
    | true => rfl
    | false =>
      have m : a∈S.filter (fun v => p v=false) := Finset.mem_filter.mpr ⟨ha,e⟩
      rw [h] at m
      simp at m
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a m
    obtain ⟨ha,he⟩ := Finset.mem_filter.mp m
    exact Bool.noConfusion ((h a ha).symm.trans he)
abbrev Small := BitVec 8
def flat (v : Small) : Bool := v==0 || v==BitVec.allOnes 8
def charge (v : Small) : Nat := (flat v).toNat
def mass8 (f : Sig → Small) (S : Finset Sig) := ∑ a∈S, charge (f a)
def domain8 (bank : List Small) := (0 : Small) :: (BitVec.allOnes 8) :: (bank ++ bank.map (fun a => ~~~a))
def base8 : List Small := [170,204,240]
def maj8 : Small := 232
def project8 (rs : Fin 8 → Row) (a : Sig) : Small :=
  (BitVec.ofBoolListLE (List.ofFn fun i => bit (rs i) a)).cast List.length_ofFn
structure Chart where
  rows : Fin 8 → Row
  targetOK : project8 rows target=maj8
def faceCut (c : Chart) (K : Nat) (S : Finset Sig) : Bool :=
  allSet S (fun a => decide (project8 c.rows a ∈ domain8 base8)) && decide (K < 4+mass8 (project8 c.rows) S)
theorem project_at (rs : Fin 8 → Row) (a : Sig) (i : Fin 8) :
    (project8 rs a).getLsbD i.val=bit (rs i) a := by
  simp only [project8,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
structure FastChart extends Chart where
  mask : Sig
  vectors : List Sig
  covers : ∀i : Fin 8, bit (rows i) mask=true
  labels : ∀x ∈ vectors, project8 rows x ∈ domain8 base8

theorem projMask (c : FastChart) (a : Sig) :
    project8 c.rows (a &&& c.mask)=project8 c.rows a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  calc
    _ = bit (c.rows ⟨j,hj⟩) (a &&& c.mask) := project_at _ _ _
    _ = (bit (c.rows ⟨j,hj⟩) a && bit (c.rows ⟨j,hj⟩) c.mask) := by
      simp only [bit,BitVec.getLsbD_and]
    _ = bit (c.rows ⟨j,hj⟩) a := by rw [c.covers]; simp
    _ = _ := (project_at c.rows a ⟨j,hj⟩).symm

def quickFlat (c : FastChart) (a : Sig) := ((a &&& c.mask)==0) || ((a &&& c.mask)==c.mask)
theorem quickCharge (c : FastChart) (a : Sig) :
    (quickFlat c a).toNat ≤ charge (project8 c.rows a) := by
  cases he : quickFlat c a with
  | false => exact Nat.zero_le _
  | true =>
    have h0 : project8 c.rows (0 : Sig)=0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simpa [bit] using project_at c.rows (0 : Sig) ⟨i,hi⟩
    have h1 : project8 c.rows c.mask=BitVec.allOnes 8 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      calc
        _ = true := (project_at c.rows c.mask ⟨i,hi⟩).trans (c.covers ⟨i,hi⟩)
        _ = _ := by rw [BitVec.getLsbD_allOnes]; simp [hi]
    rcases (by simpa [quickFlat] using he : a &&& c.mask = 0 ∨ a &&& c.mask = c.mask) with h|h
    · rw [←projMask c a,h,h0]; decide
    · rw [←projMask c a,h,h1]; decide
def quickFace (c : FastChart) (K : Nat) (S : Finset Sig) :=
  allSet S (fun a => decide (a &&& c.mask ∈ c.vectors)) &&
  decide (K < 4+∑a∈S,(quickFlat c a).toNat)
theorem quickPass {c K S} (h : quickFace c K S=true) : faceCut c.toChart K S=true := by
  simp only [quickFace,faceCut,Bool.and_eq_true,allSet_iff,decide_eq_true_eq] at h ⊢
  constructor
  · intro a ha
    rw [←projMask c a]
    exact c.labels _ (h.1 a ha)
  · have le : (∑a∈S,(quickFlat c a).toNat) ≤ mass8 (project8 c.rows) S :=
      Finset.sum_le_sum fun a _ => quickCharge c a
    exact lt_of_lt_of_le h.2 (by omega)
end PEqualNP.Outside.L_meta_9929.FastBridge
