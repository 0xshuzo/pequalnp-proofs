import PEqualNP.Outside.L_meta_4245
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
  have indicator : (if IsNewLowMerge P L inc C t w then 1 else 0) =
      (if IsLow P L inc C t w ∧ 2≤(labs inc C w t).card then 1 else 0) := by
    by_cases h : IsNewLowMerge P L inc C t w
    · rw [if_pos h,if_pos ((new_iff inc C w t).mp h)]
    · rw [if_neg h,if_neg (fun e=>h ((new_iff inc C w t).mpr e))]
  rw [indicator]
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
namespace Star606
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.LowMerge
open PEqualNP.MetaComplexity.LowMergeProof
open PEqualNP.Outside.L_meta_4245_aux

variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def source (v u : Fin n) : Nat := if u=v then n else if G.Adj v u then u.val else n+1

def view (C : Circuit) (v : Fin n) : Circuit :=
  let f := wire (n+2) (source G v)
  ⟨C.gates.map (rewire f),f C.output⟩

def mask (v : Fin n) (x : Fin n→Bool) (u : Fin n) : Bool :=
  if u=v then true else if G.Adj v u then x u else false

def inc (v u : Fin n) (_ : Fin 2) : Bool := decide (G.Adj v u)

theorem viewMono (C : Circuit) (v : Fin n) (h : Monotone2 C) : Monotone2 (view G C v) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  simpa only [rewire,List.length_map] using h a ha

theorem semantics (C : Circuit) (v : Fin n) (x : Fin n→Bool) (g : Nat) :
    wireVal (view G C v) (restrictInput n 2 0 x) (wire (n+2) (source G v) g) =
      wireVal C (List.ofFn (mask G v x)) g := by
  let X := List.ofFn x
  let Y := List.ofFn (fun i : Fin 2=>decide (i=0))
  have bounds (u : Fin n) : source G v u<n+2 := by
    have := u.isLt
    dsimp [source]
    split <;> split_ifs <;> omega
  apply run_rewire bounds C.gates 0 (List.ofFn (mask G v x)) (X++Y) (by simp) (by simp [X,Y])
  intro i
  by_cases h : i<n
  · let u : Fin n := ⟨i,h⟩
    change (X++Y).getD (wire (n+2) (source G v) u.val) false=(List.ofFn (mask G v x)).getD u.val false
    rw [input_value]
    have wr : wire (n+2) (source G v) u.val=source G v u := by simp [wire,u.isLt]
    rw [wr]
    by_cases eq : u=v
    · simp only [source,mask,eq,if_true]
      rw [List.getD_append_right _ _ _ _ (by simp [X])]
      simp [X,Y]
    · by_cases edge : G.Adj v u
      · simp only [source,mask,eq,edge,if_false,if_true]
        rw [List.getD_append _ _ _ _ (by simpa [X] using u.isLt)]
        exact input_value x u
      · simp only [source,mask,eq,edge,if_false]
        rw [List.getD_append_right _ _ _ _ (by simp [X])]
        simp [X,Y]
  · have hnew : n+2≤wire (n+2) (source G v) i := by simp [wire,h]
    rw [List.getD_eq_default _ _ (by simp [X,Y];omega),List.getD_eq_default _ _ (by simp;omega)]

theorem output (C : Circuit)
    (correct : circuitFun n C=fun x=>decide (∃i j,G.Adj i j ∧ x i=true ∧ x j=true))
    (v : Fin n) (x : Fin n→Bool) : V (view G C v) (0 : Fin 2) (view G C v).output x =
      lineSum n 2 (inc G v) 0 x := by
  change wireVal (view G C v) (restrictInput n 2 0 x) (wire (n+2) (source G v) C.output)=_
  rw [semantics]
  change circuitFun n C (mask G v x) = _
  rw [correct]
  unfold lineSum inc
  apply decide_eq_decide.mpr
  have casesOn (i : Fin n) (hi : mask G v x i=true) : i=v ∨ G.Adj v i ∧ x i=true := by
    by_cases e : i=v
    · exact Or.inl e
    · exact Or.inr (by simpa [mask,e] using hi)
  constructor
  · rintro ⟨i,j,edge,hi,hj⟩
    rcases casesOn i hi with rfl|⟨a,b⟩
    · rcases casesOn j hj with rfl|⟨a,b⟩
      · exact (G.loopless.irrefl _ edge).elim
      · exact ⟨j,decide_eq_true a,b⟩
    · exact ⟨i,decide_eq_true a,b⟩
  · rintro ⟨i,hi,hx⟩
    have edge := of_decide_eq_true hi
    have ne : i≠v := fun e=>G.loopless.irrefl v (e ▸ edge)
    exact ⟨v,i,edge,by simp [mask],by simp [mask,ne,edge,hx]⟩

def newAt (C : Circuit) (j : Nat) (v : Fin n) : Prop :=
  IsNewLowMerge n 2 (inc G v) (view G C v) (n+2+j) 0

instance (C : Circuit) (j : Nat) (v : Fin n) : Decidable (newAt G C j v) := by
  unfold newAt;infer_instance

theorem degree (C : Circuit) (mono : Monotone2 C)
    (correct : circuitFun n C=fun x=>decide (∃i j,G.Adj i j ∧ x i=true ∧ x j=true))
    (v : Fin n) : G.degree v=((Finset.range C.gates.length).filter (fun j=>newAt G C j v)).card+
      (if (G.neighborFinset v).Nonempty then 1 else 0) := by
  classical
  let D := view G C v
  let I := inc G v
  have m := viewMono G C v mono
  have andor : IsMonotoneCircuit D := fun g hg=>by simpa using (m g hg).1
  have fan : ∀g∈D.gates,g.inputs.length≤2 := fun g hg=>(m g hg).2
  have h := Exact606.perLine I D (0 : Fin 2) andor fan (output G C correct v)
  dsimp only at h
  have rows : Finset.univ.filter (fun p=>I p 0=true)=G.neighborFinset v := by
    ext i;simp [I,inc]
  rw [rows,G.card_neighborFinset_eq_degree] at h
  have len : D.gates.length=C.gates.length := by simp [D,view]
  rw [len,Finset.card_filter,Finset.sum_range_add] at h
  have raw : ∑i∈Finset.range (n+2),(if IsNewLowMerge n 2 I D i 0 then 1 else 0)=0 := by
    refine Finset.sum_eq_zero fun i hi=>if_neg ?_
    intro hm
    obtain ⟨low,big⟩ := (Exact606.new_iff I D 0 i).mp hm
    rcases labs_bound I D 0 andor fan i low with small|hh
    · omega
    · exact (Nat.not_le_of_gt (Finset.mem_range.mp hi)) hh.1.1
  rw [raw,zero_add] at h
  rw [Finset.card_filter]
  exact h

theorem identity (C : Circuit) (mono : Monotone2 C)
    (correct : circuitFun n C=fun x=>decide (∃i j,G.Adj i j ∧ x i=true ∧ x j=true)) :
    2*G.edgeFinset.card =
      (∑ j∈Finset.range C.gates.length,(Finset.univ.filter (newAt G C j)).card) +
      (Finset.univ.filter (fun v=>(G.neighborFinset v).Nonempty)).card := by
  classical
  rw [←G.sum_degrees_eq_twice_card_edges]
  simp_rw [degree G C mono correct]
  rw [Finset.sum_add_distrib]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
end Star606
