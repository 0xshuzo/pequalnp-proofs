import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19367.Controls

abbrev Q := Fin 25
def pairTable : Q → Fin 5 × Fin 5 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]
def value (C : Circuit) (q : Q) : Bool :=
  let p := pairTable q
  C.eval (PEqualNP.Represents.oneEach p.1 p.2)
def target (q : Q) : Bool := (7577150 : ℕ).testBit q.val
def requiredRows : Finset Q := {0,8,9}
def otherRows : Finset Q := {1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24}
def omissionControl : Fin 3 → Circuit := ![⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [11, 9]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [11, 9]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩, ⟨[⟨.or, [0, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [11, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [15, 14]⟩], 16⟩, ⟨[⟨.or, [0, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [11, 12]⟩, ⟨.not, [14]⟩, ⟨.and, [13, 15]⟩], 16⟩]
def omitRow : Fin 3 → Q := ![0, 8, 9]
def family : Fin 30 → Circuit := ![⟨[⟨.or, [0, 9]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [12, 11]⟩, ⟨.not, [13]⟩, ⟨.or, [14, 15]⟩], 16⟩, ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [12, 9]⟩, ⟨.and, [10, 9]⟩, ⟨.not, [13]⟩, ⟨.or, [14, 15]⟩], 16⟩, ⟨[⟨.not, [0]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [12, 13]⟩, ⟨.not, [14]⟩, ⟨.or, [9, 15]⟩], 16⟩, ⟨[⟨.or, [0, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [12, 11]⟩, ⟨.not, [14]⟩, ⟨.and, [13, 15]⟩], 16⟩, ⟨[⟨.or, [0, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [12, 11]⟩, ⟨.not, [14]⟩, ⟨.and, [13, 15]⟩], 16⟩, ⟨[⟨.or, [5, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [11, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [14, 15]⟩], 16⟩, ⟨[⟨.or, [0, 6]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [12, 5]⟩, ⟨.not, [13]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [15, 14]⟩], 16⟩, ⟨[⟨.or, [0, 7]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [12, 5]⟩, ⟨.not, [13]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [15, 14]⟩], 16⟩, ⟨[⟨.or, [5, 1]⟩, ⟨.or, [0, 10]⟩, ⟨.not, [10]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [14, 15]⟩], 16⟩, ⟨[⟨.and, [0, 5]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [12, 9]⟩, ⟨.or, [12, 9]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩, ⟨[⟨.not, [0]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [13, 14]⟩, ⟨.not, [15]⟩], 16⟩, ⟨[⟨.or, [0, 1]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [11, 9]⟩, ⟨.or, [11, 9]⟩, ⟨.not, [13]⟩, ⟨.or, [12, 14]⟩], 15⟩, ⟨[⟨.and, [0, 5]⟩, ⟨.or, [10, 9]⟩, ⟨.not, [8]⟩, ⟨.or, [0, 12]⟩, ⟨.not, [11]⟩, ⟨.or, [1, 14]⟩, ⟨.and, [15, 13]⟩], 16⟩, ⟨[⟨.not, [0]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [1, 12]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩, ⟨[⟨.not, [1]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [0, 12]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩, ⟨[⟨.not, [0]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [12, 10]⟩, ⟨.or, [12, 10]⟩, ⟨.not, [14]⟩, ⟨.or, [15, 13]⟩], 16⟩, ⟨[⟨.or, [0, 1]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [1, 12]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩, ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [13, 9]⟩, ⟨.not, [12]⟩, ⟨.or, [14, 15]⟩], 16⟩, ⟨[⟨.or, [0, 1]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [10, 12]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩, ⟨[⟨.or, [0, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [14, 13]⟩, ⟨.not, [15]⟩], 16⟩, ⟨[⟨.or, [0, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [14, 13]⟩, ⟨.not, [15]⟩], 16⟩, ⟨[⟨.or, [0, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [14, 13]⟩, ⟨.not, [15]⟩], 16⟩, ⟨[⟨.and, [0, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [12, 11]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [13, 14]⟩, ⟨.not, [15]⟩], 16⟩, ⟨[⟨.and, [0, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [12, 11]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [13, 14]⟩, ⟨.not, [15]⟩], 16⟩, ⟨[⟨.and, [0, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [12, 11]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [13, 14]⟩, ⟨.not, [15]⟩], 16⟩, ⟨[⟨.and, [0, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [12, 11]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [13, 14]⟩, ⟨.not, [15]⟩], 16⟩, ⟨[⟨.and, [0, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [12, 11]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [13, 14]⟩, ⟨.not, [15]⟩], 16⟩, ⟨[⟨.and, [0, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [12, 11]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [13, 14]⟩, ⟨.not, [15]⟩], 16⟩, ⟨[⟨.or, [0, 7]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [1, 12]⟩, ⟨.not, [11]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, ⟨[⟨.or, [0, 6]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [1, 12]⟩, ⟨.not, [11]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩]
def misses : Fin 30 → Finset Q := ![{1,2,4}, {5,13,18,23}, {5,14,19,24}, {6,11,16,21}, {7,12,17,22}, {4,10,15,20}, {6,12,17,22}, {7,11,16,21}, {5,10,15,20}, {3,4,5}, {6,7,14,24}, {1,2,3,5}, {4,6,7}, {10,13,15,18,20,23}, {1,2,6,7}, {11,12,16,17,21,22}, {4,13,18,23}, {1,2,14,19,24}, {1,2,3,13,18,23}, {3,14,19,20,21,22}, {3,10,11,12,19,24}, {3,14,15,16,17,24}, {3,6,14,24}, {3,6,14,19}, {3,6,19,24}, {3,7,14,24}, {3,7,19,24}, {3,7,14,19}, {10,11,15,16,20,21}, {10,12,15,17,20,22}]
def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

def legal (C : Circuit) := C.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2))

theorem sound (C : Circuit) (h : legal C = true) : FanInTwo C := by
  intro g hg
  have passed := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem legalO : ∀ i : Fin 3, legal (omissionControl i) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem legalF : ∀ i : Fin 30, legal (family i) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sizeO : ∀ i : Fin 3, (omissionControl i).size ≤ 7 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sizeF : ∀ i : Fin 30, (family i).size ≤ 7 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem exactO : ∀ (i : Fin 3) (q : Q), q ≠ omitRow i → value (omissionControl i) q = target q := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem exactF : ∀ (i : Fin 30) (q : Q), q ∉ misses i → value (family i) q = target q := by decide +kernel
theorem omitAll : ∀ q ∈ requiredRows, ∃ i : Fin 3, omitRow i = q := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem avoidsRequired : ∀ (i : Fin 30) (q : Q), q ∈ requiredRows → q ∉ misses i := by decide +kernel
theorem positiveOf : ∀ q : Q, q ∉ requiredRows → q ∈ otherRows := by decide +kernel
theorem requiredCount : requiredRows.card = 3 := by decide +kernel

def blocks : Nat → List (Finset Q) → Bool
  | _, [] => false
  | 0, _ :: _ => true
  | k+1, e :: es => ((List.finRange 25).filter fun a => decide (a ∈ e)).all fun a => blocks k ((e::es).filter fun h => decide (a ∉ h))

theorem blocks_sound : ∀ k (E : List (Finset Q)), blocks k E = true →
    ∀ T : Finset Q, T.card ≤ k → ∃ e ∈ E, Disjoint T e := by
  intro k
  induction k with
  | zero =>
    intro E h T ht
    cases E with
    | nil => simp [blocks] at h
    | cons e es =>
      have emp : T = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨e,by simp,by simp [emp]⟩
  | succ k ih =>
    intro E h T ht
    cases E with
    | nil => simp [blocks] at h
    | cons e es =>
      by_cases dis : Disjoint T e
      · exact ⟨e,by simp,dis⟩
      · obtain ⟨a,haT,hae⟩ := Finset.not_disjoint_iff.mp dis
        have hstep := List.all_eq_true.mp h a (by simp [hae])
        have hsize : (T.erase a).card ≤ k := by rw [Finset.card_erase_of_mem haT]; omega
        obtain ⟨z,hz,hzd⟩ := ih _ hstep _ hsize
        have hz' := List.mem_filter.mp hz
        have hn : a ∉ z := of_decide_eq_true hz'.2
        refine ⟨z,hz'.1,Finset.disjoint_left.mpr ?_⟩
        intro q hq hqz
        by_cases eq : q = a
        · exact hn (eq ▸ hqz)
        · exact Finset.disjoint_left.mp hzd (Finset.mem_erase.mpr ⟨eq,hq⟩) hqz

def errors := List.ofFn misses
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionDepth : blocks 7 errors = true := by decide +kernel

theorem projectionCover (T : Finset Q) (ht : T.card ≤ 7) : ∃ i, Disjoint T (misses i) := by
  obtain ⟨e,h,hd⟩ := blocks_sound 7 errors obstructionDepth T ht
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
  exact ⟨i,hi.symm ▸ hd⟩

theorem allTen (S : Finset Q) (hs : S.card ≤ 10) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ r ∈ S, value C r = target r := by
  classical
  by_cases included : requiredRows ⊆ S
  · let T := S \ requiredRows
    have small : T.card ≤ 7 := by
      dsimp [T]
      rw [Finset.card_sdiff_of_subset included, requiredCount]
      omega
    obtain ⟨i,good⟩ := projectionCover T small
    refine ⟨family i,sound _ (legalF i),sizeF i,?_⟩
    intro q hq
    apply exactF
    by_cases h : q ∈ requiredRows
    · exact avoidsRequired i q h
    · exact Finset.disjoint_left.mp good (Finset.mem_sdiff.mpr ⟨hq,h⟩)
  · obtain ⟨q,hq,hn⟩ := Finset.not_subset.mp included
    obtain ⟨i,hi⟩ := omitAll q hq
    refine ⟨omissionControl i,sound _ (legalO i),sizeO i,?_⟩
    intro r hr
    apply exactO
    intro eq
    exact hn ((eq.trans hi) ▸ hr)

end PEqualNP.Outside.L_meta_19367.Controls

open PEqualNP.Outside.L_meta_19367.Controls in
theorem PEqualNP.Outside.L_meta_19367 (S : Finset Q) (hs : S.card ≤ 10) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ r ∈ S, value C r = target r :=
  allTen S hs
