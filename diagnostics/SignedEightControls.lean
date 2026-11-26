import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22975.SignedEightControls

abbrev Q := Fin 21

def pairTable : Q → Fin 6 × Fin 6 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]
def value (C : Circuit) (q : Q) : Bool :=
  let p := pairTable q
  C.eval (List.ofFn fun k : Fin 6 => decide (k = p.1 ∨ k = p.2))
def target (q : Q) : Bool :=
  let p := pairTable q
  (33584 : ℕ).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)
def critical : Finset Q := {4, 5, 7, 8, 12}
def otherRows : Finset Q := {0, 1, 2, 3, 6, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20}
def omissionControl : Fin 5 → Circuit := ![⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [8, 10]⟩], 11⟩, ⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [8, 10]⟩], 11⟩, ⟨[⟨.or, [1, 2]⟩, ⟨.and, [6, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 7]⟩], 10⟩, ⟨[⟨.or, [1, 3]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 7]⟩], 10⟩, ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 7]⟩], 10⟩]
def omitRow : Fin 5 → Q := ![4, 5, 7, 8, 12]
def family : Fin 15 → Circuit := ![⟨[⟨.not, [0]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [7, 6]⟩, ⟨.not, [8]⟩, ⟨.or, [7, 6]⟩, ⟨.and, [9, 10]⟩], 11⟩, ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [7, 9]⟩], 10⟩, ⟨[⟨.or, [4, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [8, 10]⟩], 11⟩, ⟨[⟨.not, [0]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [8, 10]⟩], 11⟩, ⟨[⟨.not, [0]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [8, 10]⟩], 11⟩, ⟨[⟨.not, [0]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [8, 10]⟩], 11⟩, ⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 7]⟩, ⟨.not, [7]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩, ⟨[⟨.not, [1]⟩, ⟨.and, [6, 2]⟩, ⟨.not, [7]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [10, 3]⟩], 11⟩, ⟨[⟨.not, [1]⟩, ⟨.and, [6, 3]⟩, ⟨.not, [7]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [10, 2]⟩], 11⟩, ⟨[⟨.not, [1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [10, 7]⟩], 11⟩, ⟨[⟨.and, [0, 1]⟩, ⟨.not, [6]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [8, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [9, 10]⟩], 11⟩, ⟨[⟨.and, [0, 2]⟩, ⟨.not, [6]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [10, 7]⟩], 11⟩, ⟨[⟨.and, [0, 3]⟩, ⟨.not, [6]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [10, 7]⟩], 11⟩, ⟨[⟨.or, [4, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [9, 10]⟩], 11⟩, ⟨[⟨.or, [4, 5]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [9, 10]⟩], 11⟩]
def misses : Fin 15 → Finset Q := ![{6, 11, 15}, {0, 1, 2, 3}, {9, 10, 13, 14, 16, 17, 18, 19, 20}, {6, 9, 10, 15, 16, 17}, {6, 9, 10, 11, 13, 14}, {11, 13, 14, 15, 16, 17}, {1, 2, 6, 11}, {0, 3, 15, 16, 17, 18, 19, 20}, {0, 2, 11, 13, 14, 18, 19, 20}, {0, 1, 6, 9, 10, 18, 19, 20}, {0, 2, 3, 6, 9, 10}, {0, 1, 3, 11, 13, 14}, {0, 1, 2, 15, 16, 17}, {2, 3, 9, 10, 11, 15, 18, 19, 20}, {1, 3, 6, 13, 14, 15, 18, 19, 20}]
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
theorem legalO : ∀ i : Fin 5, legal (omissionControl i) = true := by decide +kernel
theorem legalF : ∀ i : Fin 15, legal (family i) = true := by decide +kernel
theorem sizeO : ∀ i : Fin 5, (omissionControl i).size ≤ 6 := by decide +kernel
theorem sizeF : ∀ i : Fin 15, (family i).size ≤ 6 := by decide +kernel
theorem exactO : ∀ (i : Fin 5) (q : Q), q ≠ omitRow i → value (omissionControl i) q = target q := by decide +kernel
theorem exactF : ∀ (i : Fin 15) (q : Q), q ∉ misses i → value (family i) q = target q := by decide +kernel
theorem omitAll : ∀ q ∈ critical, ∃ i : Fin 5, omitRow i = q := by decide +kernel
theorem noneNeg : ∀ (i : Fin 15) (q : Q), q ∈ critical → q ∉ misses i := by decide +kernel
theorem positiveOf : ∀ q : Q, q ∉ critical → q ∈ otherRows := by decide +kernel
theorem criticalCount : critical.card = 5 := by decide +kernel

def blocks : Nat → List (Finset Q) → Bool
  | _, [] => false
  | 0, _ :: _ => true
  | k+1, e :: es => ((List.finRange 21).filter fun a => decide (a ∈ e)).all fun a => blocks k ((e::es).filter fun h => decide (a ∉ h))

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
theorem obstructionDepth : blocks 3 errors = true := by decide +kernel

theorem projectionCover (T : Finset Q) (ht : T.card ≤ 3) : ∃ i, Disjoint T (misses i) := by
  obtain ⟨e,h,hd⟩ := blocks_sound 3 errors obstructionDepth T ht
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
  exact ⟨i,hi.symm ▸ hd⟩

theorem allSamples (S : Finset Q) (hs : S.card ≤ 8) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ ∀ r ∈ S, value C r = target r := by
  classical
  by_cases included : critical ⊆ S
  · let T := S \ critical
    have small : T.card ≤ 3 := by
      dsimp [T]
      rw [Finset.card_sdiff_of_subset included, criticalCount]
      omega
    obtain ⟨i,good⟩ := projectionCover T small
    refine ⟨family i,sound _ (legalF i),sizeF i,?_⟩
    intro q hq
    apply exactF
    by_cases h : q ∈ critical
    · exact noneNeg i q h
    · exact Finset.disjoint_left.mp good (Finset.mem_sdiff.mpr ⟨hq,h⟩)
  · obtain ⟨q,hq,hn⟩ := Finset.not_subset.mp included
    obtain ⟨i,hi⟩ := omitAll q hq
    refine ⟨omissionControl i,sound _ (legalO i),sizeO i,?_⟩
    intro r hr
    apply exactO
    intro eq
    exact hn ((eq.trans hi) ▸ hr)

end PEqualNP.Outside.L_meta_22975.SignedEightControls

open PEqualNP.Outside.L_meta_22975.SignedEightControls in
theorem PEqualNP.Outside.L_meta_22975 (S : Finset Q) (hs : S.card ≤ 8) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ ∀ r ∈ S, value C r = target r :=
  allSamples S hs
