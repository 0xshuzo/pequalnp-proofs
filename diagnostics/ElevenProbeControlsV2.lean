import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_24685.Controls

abbrev Q := Fin 21

def pairTable : Q → Fin 6 × Fin 6 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]
def value (C : Circuit) (q : Q) : Bool :=
  let p := pairTable q
  C.eval (List.ofFn fun k : Fin 6 => decide (k = p.1 ∨ k = p.2))
def target (q : Q) : Bool :=
  let p := pairTable q
  (34630389437 : ℕ).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)
def negRows : Finset Q := {1,7,14,16,17,19}
def posRows : Finset Q := {0,2,3,4,5,6,8,9,10,11,12,13,15,18,20}
def omit : Fin 6 → Circuit := ![⟨[⟨.and,[1, 2]⟩, ⟨.or,[6, 5]⟩, ⟨.or,[2, 3]⟩, ⟨.and,[3, 4]⟩, ⟨.or,[9, 7]⟩, ⟨.or,[8, 4]⟩, ⟨.and,[11, 10]⟩, ⟨.not,[12]⟩], 13⟩, ⟨[⟨.and,[0, 1]⟩, ⟨.or,[2, 3]⟩, ⟨.and,[3, 4]⟩, ⟨.or,[6, 8]⟩, ⟨.or,[7, 4]⟩, ⟨.and,[10, 5]⟩, ⟨.or,[9, 11]⟩, ⟨.not,[12]⟩], 13⟩, ⟨[⟨.or,[0, 2]⟩, ⟨.and,[1, 6]⟩, ⟨.and,[3, 4]⟩, ⟨.or,[7, 8]⟩, ⟨.or,[3, 4]⟩, ⟨.and,[10, 5]⟩, ⟨.or,[9, 11]⟩, ⟨.not,[12]⟩], 13⟩, ⟨[⟨.or,[0, 2]⟩, ⟨.and,[1, 6]⟩, ⟨.or,[2, 3]⟩, ⟨.or,[8, 4]⟩, ⟨.and,[9, 5]⟩, ⟨.or,[7, 10]⟩, ⟨.not,[11]⟩], 12⟩, ⟨[⟨.and,[0, 1]⟩, ⟨.or,[6, 2]⟩, ⟨.or,[1, 5]⟩, ⟨.and,[7, 8]⟩, ⟨.or,[3, 5]⟩, ⟨.and,[4, 10]⟩, ⟨.or,[9, 11]⟩, ⟨.not,[12]⟩], 13⟩, ⟨[⟨.and,[0, 1]⟩, ⟨.or,[6, 2]⟩, ⟨.or,[1, 5]⟩, ⟨.and,[7, 8]⟩, ⟨.or,[4, 5]⟩, ⟨.and,[3, 10]⟩, ⟨.or,[9, 11]⟩, ⟨.not,[12]⟩], 13⟩]
def omitRow : Fin 6 → Q := ![1, 7, 14, 16, 17, 19]
def family : Fin 19 → Circuit := ![⟨[⟨.or,[0, 2]⟩, ⟨.or,[1, 5]⟩, ⟨.or,[6, 3]⟩, ⟨.or,[3, 5]⟩, ⟨.and,[8, 7]⟩, ⟨.and,[4, 9]⟩, ⟨.or,[10, 11]⟩, ⟨.not,[12]⟩], 13⟩, ⟨[⟨.not,[0]⟩, ⟨.or,[0, 2]⟩, ⟨.and,[1, 7]⟩, ⟨.and,[3, 4]⟩, ⟨.or,[8, 9]⟩, ⟨.and,[5, 6]⟩, ⟨.or,[10, 11]⟩, ⟨.not,[12]⟩], 13⟩, ⟨[⟨.or,[0, 2]⟩, ⟨.or,[1, 5]⟩, ⟨.or,[6, 4]⟩, ⟨.or,[4, 5]⟩, ⟨.and,[3, 9]⟩, ⟨.and,[8, 7]⟩, ⟨.or,[10, 11]⟩, ⟨.not,[12]⟩], 13⟩, ⟨[⟨.or,[2, 3]⟩, ⟨.or,[3, 5]⟩, ⟨.and,[6, 5]⟩, ⟨.or,[8, 4]⟩, ⟨.and,[9, 7]⟩, ⟨.not,[10]⟩, ⟨.or,[9, 7]⟩, ⟨.and,[11, 12]⟩], 13⟩, ⟨[⟨.or,[0, 2]⟩, ⟨.and,[1, 6]⟩, ⟨.or,[7, 4]⟩, ⟨.or,[2, 3]⟩, ⟨.and,[9, 5]⟩, ⟨.or,[10, 8]⟩, ⟨.not,[11]⟩], 12⟩, ⟨[⟨.or,[0, 2]⟩, ⟨.and,[1, 6]⟩, ⟨.or,[7, 3]⟩, ⟨.or,[2, 4]⟩, ⟨.and,[9, 5]⟩, ⟨.or,[8, 10]⟩, ⟨.not,[11]⟩], 12⟩, ⟨[⟨.not,[0]⟩, ⟨.not,[2]⟩, ⟨.or,[5, 7]⟩, ⟨.and,[8, 6]⟩, ⟨.and,[1, 9]⟩, ⟨.or,[1, 9]⟩, ⟨.not,[11]⟩, ⟨.or,[10, 12]⟩], 13⟩, ⟨[⟨.and,[0, 1]⟩, ⟨.or,[6, 2]⟩, ⟨.and,[3, 4]⟩, ⟨.or,[7, 8]⟩, ⟨.or,[3, 4]⟩, ⟨.and,[10, 5]⟩, ⟨.or,[9, 11]⟩, ⟨.not,[12]⟩], 13⟩, ⟨[⟨.not,[1]⟩, ⟨.or,[2, 3]⟩, ⟨.and,[3, 4]⟩, ⟨.or,[8, 5]⟩, ⟨.or,[7, 4]⟩, ⟨.and,[10, 9]⟩, ⟨.not,[11]⟩, ⟨.and,[12, 6]⟩], 13⟩, ⟨[⟨.or,[1, 4]⟩, ⟨.or,[2, 3]⟩, ⟨.or,[3, 4]⟩, ⟨.and,[1, 8]⟩, ⟨.and,[7, 5]⟩, ⟨.or,[10, 6]⟩, ⟨.not,[11]⟩, ⟨.or,[9, 12]⟩], 13⟩, ⟨[⟨.or,[1, 3]⟩, ⟨.or,[2, 4]⟩, ⟨.or,[3, 4]⟩, ⟨.and,[1, 8]⟩, ⟨.and,[7, 5]⟩, ⟨.or,[6, 10]⟩, ⟨.not,[11]⟩, ⟨.or,[9, 12]⟩], 13⟩, ⟨[⟨.not,[0]⟩, ⟨.and,[1, 5]⟩, ⟨.and,[3, 4]⟩, ⟨.or,[1, 8]⟩, ⟨.and,[5, 6]⟩, ⟨.or,[9, 10]⟩, ⟨.not,[11]⟩, ⟨.or,[7, 12]⟩], 13⟩, ⟨[⟨.and,[0, 1]⟩, ⟨.or,[6, 2]⟩, ⟨.or,[1, 7]⟩, ⟨.or,[3, 4]⟩, ⟨.or,[7, 9]⟩, ⟨.and,[8, 9]⟩, ⟨.not,[10]⟩, ⟨.or,[11, 12]⟩], 13⟩, ⟨[⟨.or,[1, 3]⟩, ⟨.and,[6, 4]⟩, ⟨.or,[7, 5]⟩, ⟨.or,[1, 8]⟩, ⟨.or,[3, 8]⟩, ⟨.and,[1, 10]⟩, ⟨.not,[9]⟩, ⟨.or,[11, 12]⟩], 13⟩, ⟨[⟨.or,[0, 2]⟩, ⟨.not,[1]⟩, ⟨.or,[1, 5]⟩, ⟨.and,[6, 8]⟩, ⟨.or,[3, 4]⟩, ⟨.and,[10, 7]⟩, ⟨.or,[9, 11]⟩, ⟨.not,[12]⟩], 13⟩, ⟨[⟨.and,[0, 1]⟩, ⟨.or,[6, 2]⟩, ⟨.and,[7, 4]⟩, ⟨.or,[7, 4]⟩, ⟨.and,[3, 5]⟩, ⟨.or,[10, 9]⟩, ⟨.not,[11]⟩, ⟨.or,[8, 12]⟩], 13⟩, ⟨[⟨.and,[0, 1]⟩, ⟨.or,[6, 2]⟩, ⟨.and,[7, 3]⟩, ⟨.or,[7, 3]⟩, ⟨.and,[5, 4]⟩, ⟨.or,[9, 10]⟩, ⟨.not,[11]⟩, ⟨.or,[8, 12]⟩], 13⟩, ⟨[⟨.or,[0, 1]⟩, ⟨.not,[2]⟩, ⟨.and,[3, 7]⟩, ⟨.or,[8, 5]⟩, ⟨.or,[1, 9]⟩, ⟨.and,[6, 9]⟩, ⟨.not,[10]⟩, ⟨.or,[11, 12]⟩], 13⟩, ⟨[⟨.or,[0, 1]⟩, ⟨.not,[2]⟩, ⟨.and,[4, 7]⟩, ⟨.or,[8, 5]⟩, ⟨.or,[1, 9]⟩, ⟨.and,[6, 9]⟩, ⟨.not,[10]⟩, ⟨.or,[11, 12]⟩], 13⟩]
def misses : Fin 19 → Finset Q := ![{5,8}, {10,20}, {5,9}, {0,2,6,11}, {4,9,13,18}, {3,8,12,15}, {15,18,20}, {2,11,12,13}, {6,8,9,10}, {4,6,10,13,18}, {3,6,10,12,15}, {6,8,9,20}, {2,3,4,11,15,18}, {5,6,20}, {3,4,5,12,13,15,18}, {2,4,9,11,12,18}, {2,3,8,11,13,15}, {6,9,15,20}, {6,8,18,20}]
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
theorem legalO : ∀ i : Fin 6, legal (omit i) = true := by decide +kernel
theorem legalF : ∀ i : Fin 19, legal (family i) = true := by decide +kernel
theorem sizeO : ∀ i : Fin 6, (omit i).size ≤ 8 := by decide +kernel
theorem sizeF : ∀ i : Fin 19, (family i).size ≤ 8 := by decide +kernel
theorem exactO : ∀ (i : Fin 6) (q : Q), q ≠ omitRow i → value (omit i) q = target q := by decide +kernel
theorem exactF : ∀ (i : Fin 19) (q : Q), q ∉ misses i → value (family i) q = target q := by decide +kernel
theorem omitAll : ∀ q ∈ negRows, ∃ i : Fin 6, omitRow i = q := by decide +kernel
theorem noneNeg : ∀ (i : Fin 19) (q : Q), q ∈ negRows → q ∉ misses i := by decide +kernel
theorem positiveOf : ∀ q : Q, q ∉ negRows → q ∈ posRows := by decide +kernel
theorem countNeg : negRows.card = 6 := by decide +kernel

def blocks : Nat → List (Finset Q) → Bool
  | _, [] => false
  | 0, _ :: _ => true
  | k+1, e :: es => e.toList.all fun a => blocks k ((e::es).filter fun h => decide (a ∉ h))

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
        have hstep := List.all_eq_true.mp h a (by simpa using hae)
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
theorem obstructionDepth : blocks 5 errors = true := by decide +kernel

theorem projectionCover (T : Finset Q) (ht : T.card ≤ 5) : ∃ i, Disjoint T (misses i) := by
  obtain ⟨e,h,hd⟩ := blocks_sound 5 errors obstructionDepth T ht
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
  exact ⟨i,hi.symm ▸ hd⟩

theorem allEleven (S : Finset Q) (hs : S.card ≤ 11) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ r ∈ S, value C r = target r := by
  classical
  by_cases included : negRows ⊆ S
  · let T := S \ negRows
    have small : T.card ≤ 5 := by
      dsimp [T]
      rw [Finset.card_sdiff_of_subset included, countNeg]
      omega
    obtain ⟨i,good⟩ := projectionCover T small
    refine ⟨family i,sound _ (legalF i),sizeF i,?_⟩
    intro q hq
    apply exactF
    by_cases h : q ∈ negRows
    · exact noneNeg i q h
    · exact Finset.disjoint_left.mp good (Finset.mem_sdiff.mpr ⟨hq,h⟩)
  · obtain ⟨q,hq,hn⟩ := Finset.not_subset.mp included
    obtain ⟨i,hi⟩ := omitAll q hq
    refine ⟨omit i,sound _ (legalO i),sizeO i,?_⟩
    intro r hr
    apply exactO
    intro eq
    exact hn ((eq.trans hi) ▸ hr)

end PEqualNP.Outside.L_meta_24685.Controls

open PEqualNP.Outside.L_meta_24685.Controls in
theorem PEqualNP.Outside.L_meta_24685 (S : Finset Q) (hs : S.card ≤ 11) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ r ∈ S, value C r = target r :=
  allEleven S hs
