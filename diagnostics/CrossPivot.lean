import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_121_join
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]

def par (a : V → Bool) (f : Finset V) : Prop := Odd (f.filter (fun v => a v = true)).card

theorem card_sd (s t : Finset V) : (symmDiff s t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : s ∪ t = (symmDiff s t) ∪ (s ∩ t) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff s t) (s ∩ t) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1; omega

theorem par_sd (a : V → Bool) (s t : Finset V) : par a (symmDiff s t) ↔ ¬ (par a s ↔ par a t) := by
  unfold par
  have hf : (symmDiff s t).filter (fun v => a v = true) =
      symmDiff (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  rw [hf]
  have := card_sd (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true))
  simp only [Nat.odd_iff]; omega


def cross (q r : LinEq V) : LinEq V := (symmDiff q.1 r.1,xor q.2 r.2)
def flip (q : LinEq V) : LinEq V := (q.1,!q.2)

theorem cross_truth {q r : LinEq V} {a : V → Bool} :
    LinEqSat a (cross q r) ↔ (LinEqSat a q ↔ LinEqSat a r) := by
  rcases q with ⟨p,u⟩
  rcases r with ⟨s,v⟩
  change (par a (symmDiff p s) ↔ xor u v = true) ↔
    ((par a p ↔ u=true) ↔ (par a s ↔ v=true))
  rw [par_sd]
  cases u <;> cases v <;> simp only [Bool.xor_false, Bool.xor_true, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, true_iff, iff_true] <;> tauto

theorem flip_truth {q : LinEq V} {a : V → Bool} : LinEqSat a (flip q) ↔ ¬LinEqSat a q := by
  rcases q with ⟨f,b⟩
  cases b <;> simp [LinEqSat, flip]

def side (D : LinClause V) (q r : LinEq V) :=
  insert (flip q) (insert (cross q r) (D.erase r))

theorem sideLegal (D : LinClause V) (q r : LinEq V) (a : V → Bool) :
    LinClauseSat a D → LinClauseSat a (side D q r) := by
  rintro ⟨v,m,h⟩
  by_cases ev : v=r
  · subst v
    by_cases qc : LinEqSat a q
    · exact ⟨cross q r,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
        cross_truth.mpr ⟨fun _=>h,fun _=>qc⟩⟩
    · exact ⟨flip q,Finset.mem_insert_self ..,flip_truth.mpr qc⟩
  · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨ev,m⟩)),h⟩

def combined (C D : LinClause V) (q r : LinEq V) :=
  C.erase q ∪ (side D q r).erase (flip q)

theorem fused {F : Set (LinClause V)} {π : List (LinClause V)}
    (legal : IsLinDerivation F π) {C D : LinClause V} (cm : C∈π) (dm : D∈π)
    (q r : LinEq V) (qm : q∈C) :
    IsLinDerivation F (combined C D q r :: side D q r :: π) := by
  have wk := IsLinDerivation.weak legal dm (sideLegal D q r)
  have dmem : side D q r∈side D q r::π := List.mem_cons_self
  have cmem : C∈side D q r::π := List.mem_cons_of_mem _ cm
  rcases q with ⟨f,b⟩
  cases b
  · exact IsLinDerivation.res wk cmem dmem
      ⟨f,qm,Finset.mem_insert_self ..,rfl⟩
  · apply IsLinDerivation.res wk dmem cmem
    refine ⟨f,Finset.mem_insert_self ..,qm,?_⟩
    exact Finset.union_comm _ _

end PEqualNP.Outside.L_pcx_121_join
