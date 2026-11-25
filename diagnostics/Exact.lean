import Mathlib
import PEqualNP.Outside.L_meta_696
import PEqualNP.Defs.NewLowMerge
namespace Exact606
open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge
open PEqualNP.MetaComplexity.LowMergeProof

variable {P L : Nat} (inc : Fin P→Fin L→Bool) (C : Circuit) (w : Fin L)

theorem labels (t : Nat) : classLabel P L inc C t w=lab inc C w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (List.range (t+1)).foldl _ _=_
    rw [List.range_succ,List.foldl_append]
    change classStep P L inc C w (classLabel P L inc C t w) t=_
    rw [ih]
    rfl

theorem new_iff (t : Nat) : IsNewLowMerge P L inc C t w ↔
    IsLow P L inc C t w ∧ 2≤(labs inc C w t).card := by
  unfold IsNewLowMerge classesMet labs
  rw [labels]

theorem step_exact (mono : IsMonotoneCircuit C) (fan : ∀g∈C.gates,g.inputs.length≤2)
    (t : Nat) : (lineLabs inc C w t).card=(lineLabs inc C w (t+1)).card+
      (if IsNewLowMerge P L inc C t w then 1 else 0) := by
  classical
  rw [new_iff]
  by_cases low : IsLow P L inc C t w
  · simp only [low,true_and]
    let T := labs inc C w t
    let X := lineLabs inc C w t
    let Y := lineLabs inc C w (t+1)
    change X.card=Y.card+(if 2≤T.card then 1 else 0)
    have hl := lineLabs_step inc C w t low
    change X.card+1≤Y.card+T.card ∨ T.card=0 ∧ X.card≤Y.card at hl
    have sub : T⊆X := Finset.image_subset_image (alive_sub_line inc C t w low)
    have bound := labs_bound inc C w mono fan t low
    have bnd : T.card≤2 := by rcases bound with h|h; exact h.trans (by decide); exact h.2
    rcases T.eq_empty_or_nonempty with empty|non
    · have same : lab inc C w (t+1)=lab inc C w t := by
        funext p
        simp only [lab]
        rw [if_neg]
        intro h
        have hh : lab inc C w t p∈T := h.2
        rw [empty] at hh
        exact Finset.notMem_empty _ hh
      have eq : Y=X := by dsimp only [Y,X,lineLabs]; rw [same]
      simp [eq,empty]
    · obtain ⟨d,hd,eqd⟩ := Finset.exists_mem_eq_sup T non id
      have back : Y ⊆ insert (T.sup id) (X \ T) := by
        intro v hv
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
        change (if IsLow P L inc C t w ∧ lab inc C w t p∈T then T.sup id else lab inc C w t p)∈_
        by_cases ht : lab inc C w t p∈T
        · rw [if_pos ⟨low,ht⟩]; exact Finset.mem_insert_self _ _
        · rw [if_neg (fun h=>ht h.2)]
          exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ hp,ht⟩)
      have norm : T.sup id ∉ X \ T := by
        rw [eqd]
        intro h; exact (Finset.mem_sdiff.mp h).2 hd
      have hi := Finset.card_le_card back
      rw [Finset.card_insert_of_notMem norm] at hi
      have bal := Finset.card_sdiff_add_card_eq_card sub
      have pos := Finset.card_pos.mpr non
      split <;> omega
  · have eq : lineLabs inc C w (t+1)=lineLabs inc C w t := by
      unfold lineLabs; rw [lab_succ_of_not_low inc C w t low]
    simp [low,eq]

theorem telescope (mono : IsMonotoneCircuit C) (fan : ∀g∈C.gates,g.inputs.length≤2) (t : Nat) :
    (lineLabs inc C w 0).card=(lineLabs inc C w t).card+
      ((Finset.range t).filter (fun g=>IsNewLowMerge P L inc C g w)).card := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [ih,step_exact inc C w mono fan t,Finset.range_add_one]
    by_cases h : IsNewLowMerge P L inc C t w
    · simp [h,Finset.filter_insert,Finset.mem_filter]; omega
    · simp [h,Finset.filter_insert]

theorem perLine (mono : IsMonotoneCircuit C) (fan : ∀g∈C.gates,g.inputs.length≤2)
    (hout : ∀pts : Fin P→Bool,V C w C.output pts=lineSum P L inc w pts) :
    let S := Finset.univ.filter (fun p : Fin P=>inc p w=true)
    let K := ((Finset.range (P+L+C.gates.length)).filter (fun g=>IsNewLowMerge P L inc C g w)).card
    S.card=K+(if S.Nonempty then 1 else 0) := by
  classical
  let S := Finset.univ.filter (fun p : Fin P=>inc p w=true)
  let N := P+L+C.gates.length
  have base : (lineLabs inc C w 0).card=S.card := Finset.card_image_of_injective _ Fin.val_injective
  have tel := telescope inc C w mono fan N
  rw [base] at tel
  rcases S.eq_empty_or_nonempty with empty|⟨p0,hp⟩
  · have line : lineLabs inc C w N=∅ := by change S.image _=∅; simp [empty]
    rw [line] at tel
    change S.card=_+(if S.Nonempty then 1 else 0)
    simpa [empty,N] using tel
  · have inc0 : inc p0 w=true := (Finset.mem_filter.mp hp).2
    have low : IsLow P L inc C C.output w := fun pts h=>by rw [←hout];exact h
    have lt : C.output<N := by
      by_contra! bad
      have z := hout (ind p0)
      rw [V_big C w _ _ bad,lineSum_ind,inc0] at z
      exact Bool.false_ne_true z
    have sub : S ⊆ aliveSet P L C C.output w := by
      intro p hp;rw [alive_mem,hout,lineSum_ind];exact (Finset.mem_filter.mp hp).2
    have end1 : (lineLabs inc C w N).card≤1 :=
      card_image_le_one inc C w _ S _ sub (const_later inc C w _ _ lt low)
    have end0 : 0<(lineLabs inc C w N).card :=
      Finset.card_pos.mpr ⟨_,Finset.mem_image_of_mem _ hp⟩
    have ne : S.Nonempty := ⟨_,hp⟩
    change S.card=_+(if S.Nonempty then 1 else 0)
    rw [if_pos ne]
    change S.card=((Finset.range N).filter (fun g=>IsNewLowMerge P L inc C g w)).card+1
    omega
end Exact606
