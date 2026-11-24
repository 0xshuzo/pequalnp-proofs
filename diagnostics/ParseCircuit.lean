import Mathlib
import PEqualNP.Outside.L_meta_2613

namespace ParsePath4021

/-- The relation records either order of the two input wires. -/
structure Net where
  disj : ℕ → ℕ → ℕ → Prop
  conj : ℕ → ℕ → ℕ → Prop

/-- Counts occurrences of the marked input in the unfolded accepting tree.
The only other permitted leaf is the baseline input. -/
inductive Reads (G : Net) (b t : ℕ) : ℕ → ℕ → Prop where
  | base : Reads G b t b 0
  | mark : Reads G b t t 1
  | disj {u v w k} : G.disj u v w → Reads G b t u k → Reads G b t w k
  | conj {u v w j k} : G.conj u v w → Reads G b t u j → Reads G b t v k →
      Reads G b t w (j+k)

def Step (G : Net) (b t u w : ℕ) : Prop :=
  (∃ v, G.disj u v w) ∨
  (∃ v, G.conj u v w ∧ Reads G b t v 0) ∨
  (∃ v, G.conj v u w ∧ Reads G b t v 0)

theorem single_iff_path (G : Net) (b t w : ℕ) :
    Reads G b t w 1 ↔ Relation.ReflTransGen (Step G b t) t w := by
  constructor
  · intro h
    generalize hk : 1 = k at h
    induction h with
    | base => omega
    | mark => exact .refl
    | disj hg _ ih => exact (ih hk).tail (Or.inl ⟨_, hg⟩)
    | @conj u v w i j hg hu hv ihu ihv =>
      rcases (show i = 1 ∧ j = 0 ∨ i = 0 ∧ j = 1 by omega) with ⟨hi,hj⟩ | ⟨hi,hj⟩
      · subst i
        subst j
        exact (ihu rfl).tail (Or.inr (Or.inl ⟨_, hg, hv⟩))
      · subst i
        subst j
        exact (ihv rfl).tail (Or.inr (Or.inr ⟨_, hg, hu⟩))
  · intro h
    induction h with
    | refl => exact .mark
    | tail _ step ih =>
      rcases step with ⟨v,hv⟩ | ⟨v,hv,hz⟩ | ⟨v,hv,hz⟩
      · exact .disj hv ih
      · exact Reads.conj hv ih hz
      · exact Reads.conj hv hz ih


open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2613

def gateRel (C : Circuit) (op : GateOp) (u v w : ℕ) : Prop :=
  ∃ j < C.gates.length, w = 26+j ∧ (gateAt C j).op = op ∧
    ((u = opnd0 C j ∧ v = opnd1 C j) ∨ (u = opnd1 C j ∧ v = opnd0 C j))

def fromCircuit (C : Circuit) : Net := ⟨gateRel C .or, gateRel C .and⟩

theorem zero_sound {C : Circuit} (hAO : IsAO2 26 C) (b t : Fin 26) {w k : ℕ}
    (h : Reads (fromCircuit C) b.val t.val w k) (hk : k = 0) :
    wval C (single b) w = true := by
  induction h with
  | base => simp [wval_input, single]
  | mark => omega
  | disj hg _ ih =>
    obtain ⟨j,hj,rfl,ho,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := hg <;>
      simp [wval_or hAO _ hj ho, ih hk]
  | @conj u v w i j hg hu hv ihu ihv =>
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    obtain ⟨l,hl,rfl,ho,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := hg <;>
      simp [wval_and hAO _ hl ho, ihu hi, ihv hj]

theorem zero_complete {C : Circuit} (hAO : IsAO2 26 C) (b t : Fin 26) (w : ℕ)
    (h : wval C (single b) w = true) : Reads (fromCircuit C) b.val t.val w 0 := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < 26
    · let i : Fin 26 := ⟨w,hw⟩
      rw [wval_input C _ i] at h
      have h' : i = b := of_decide_eq_true h
      have hw' : w = b.val := congrArg Fin.val h'
      rw [hw']
      exact .base
    · by_cases hj : w-26 < C.gates.length
      · let j := w-26
        have hw' : w = 26+j := by dsimp [j]; omega
        rw [hw'] at h ⊢
        have ⟨hu,hv⟩ := opnd_lt hAO hj
        have hm : gateAt C j ∈ C.gates := by rw [gateAt_eq hj]; exact List.getElem_mem hj
        rcases hAO.1 _ hm with ho | ho
        · rw [wval_and hAO _ hj ho, Bool.and_eq_true] at h
          apply Reads.conj (j:=0) (k:=0) (u:=opnd0 C j) (v:=opnd1 C j)
          · exact ⟨j,hj,rfl,ho,Or.inl ⟨rfl,rfl⟩⟩
          · exact ih _ (by change opnd0 C j < w; rw [hw']; exact hu) h.1
          · exact ih _ (by change opnd1 C j < w; rw [hw']; exact hv) h.2
        · rw [wval_or hAO _ hj ho, Bool.or_eq_true] at h
          rcases h with h | h
          · exact .disj (v:=opnd1 C j) ⟨j,hj,rfl,ho,Or.inl ⟨rfl,rfl⟩⟩
              (ih _ (by rw [hw']; exact hu) h)
          · exact .disj (v:=opnd0 C j) ⟨j,hj,rfl,ho,Or.inr ⟨rfl,rfl⟩⟩
              (ih _ (by rw [hw']; exact hv) h)
      · rw [wval_beyond C _ w (by omega)] at h
        contradiction

def singletonStep (C : Circuit) (b : Fin 26) (u w : ℕ) : Prop :=
  (∃ v, gateRel C .or u v w) ∨
    (∃ v, gateRel C .and u v w ∧ wval C (single b) v = true) ∨
    (∃ v, gateRel C .and v u w ∧ wval C (single b) v = true)

theorem single_iff_circuit_path {C : Circuit} (hAO : IsAO2 26 C) (b t : Fin 26) (w : ℕ) :
    Reads (fromCircuit C) b.val t.val w 1 ↔
    Relation.ReflTransGen (singletonStep C b) t.val w := by
  rw [single_iff_path]
  have hrel : Step (fromCircuit C) b.val t.val = singletonStep C b := by
    funext u v
    apply propext
    have hzero : ∀ q, Reads (fromCircuit C) b.val t.val q 0 ↔ wval C (single b) q = true :=
      fun q => ⟨fun h => zero_sound hAO b t h rfl, zero_complete hAO b t q⟩
    simp [Step, singletonStep, fromCircuit, hzero]
  rw [hrel]

end ParsePath4021
