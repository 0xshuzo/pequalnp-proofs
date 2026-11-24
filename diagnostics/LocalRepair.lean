import Mathlib
import PEqualNP.Defs

namespace Ports3451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

deriving instance DecidableEq for GateOp

def value (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)
def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl (fun s g => s++[value g s]) w

theorem keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[value g w])).getD i false = _
    rw [ih _ (by simp;omega),List.getD_append _ _ _ _ hi]

def check (s : List Bool) : List Gate → Prop
  | [] => True
  | g::gs => (g.op=.and → value g s=false) ∧ check (s++[if g.op=.and then false else value g s]) gs

theorem check_iff (w : List Bool) (gs : List Gate) : check w gs ↔
    ∀ j (hj : j < gs.length), gs[j].op=.and → (run gs w).getD (w.length+j) false=false := by
  induction gs generalizing w with
  | nil => simp [check]
  | cons g gs ih =>
    have first : (run (g::gs) w).getD w.length false=value g w := by
      change (run gs (w++[value g w])).getD _ _=_
      rw [keep _ _ _ (by simp)]
      simp
    have alltail (j : ℕ) :
        (run gs (w++[value g w])).getD ((w++[value g w]).length+j) false =
        (run (g::gs) w).getD (w.length+(j+1)) false := by
      change (run gs _).getD _ _ = (run gs _).getD _ _
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    constructor
    · rintro ⟨head,tail⟩
      have eq : (if g.op=.and then false else value g w)=value g w := by split <;> simp_all
      rw [eq] at tail
      intro j hj op
      cases j with
      | zero => simpa only [Nat.add_zero,first] using head op
      | succ j =>
        exact (alltail j) ▸ (ih _).mp tail j (by simpa using hj) op
    · intro all
      have head : g.op=.and → value g w=false := by
        intro op
        have v := all 0 (by simp) op
        simpa only [Nat.add_zero,first] using v
      refine ⟨head,?_⟩
      have eq : (if g.op=.and then false else value g w)=value g w := by split <;> simp_all
      rw [eq]
      apply (ih _).mpr
      intro j hj op
      rw [alltail]
      exact all (j+1) (by simpa using hj) op

def hit {α : Type} [DecidableEq α] (S A : Finset α) : Bool := decide (∃ a ∈ S, a∈A)

def cone {α : Type} [DecidableEq α] (g : Gate) (ss : List (Finset α)) : Finset α :=
  if g.op=.and then ∅ else g.inputs.foldr (fun i v => ss.getD i ∅ ∪ v) ∅

def missing {α : Type} [DecidableEq α] (A : Finset α) (ss : List (Finset α)) : List Gate → Prop
  | [] => True
  | g::gs => (g.op=.and → ∃ i∈g.inputs, hit (ss.getD i ∅) A=false) ∧ missing A (ss++[cone g ss]) gs

theorem hits_default {α : Type} [DecidableEq α] (A : Finset α) (ss : List (Finset α)) (i : ℕ) :
    (ss.map (fun S => hit S A)).getD i false=hit (ss.getD i ∅) A := by
  by_cases h : i < ss.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ h,List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
    simp [hit]

theorem hits_fold {α : Type} [DecidableEq α] (A : Finset α) (ss : List (Finset α)) (ins : List ℕ) :
    hit (ins.foldr (fun i v => ss.getD i ∅ ∪ v) ∅) A = (ins.map fun i => hit (ss.getD i ∅) A).any id := by
  induction ins with
  | nil => simp [hit]
  | cons i t ih =>
    rw [List.foldr_cons,List.map_cons,List.any_cons,←ih]
    apply Bool.eq_iff_iff.mpr
    simp [hit,or_and_right,exists_or]

theorem cone_check {α : Type} [DecidableEq α] (A : Finset α) (gs : List Gate)
    (mono : ∀ g∈gs, g.op=.and ∨ g.op=.or) (ss : List (Finset α)) :
    check (ss.map (fun S => hit S A)) gs ↔ missing A ss gs := by
  induction gs generalizing ss with
  | nil => rfl
  | cons g gs ih =>
    let w := ss.map (fun S => hit S A)
    have vals : value g w = g.op.eval (g.inputs.map fun i => hit (ss.getD i ∅) A) := by
      simp only [value,w,hits_default]
    have cval : hit (cone g ss) A = (if g.op=.and then false else value g w) := by
      rcases mono g List.mem_cons_self with op|op
      · simp [op,cone,hit]
      · rw [if_neg (by simp [op]),vals]
        simp only [cone,op,reduceCtorEq,if_false,GateOp.eval,hits_fold]
    have ts := ih (fun h mem => mono h (List.mem_cons_of_mem _ mem)) (ss++[cone g ss])
    simp only [List.map_append,List.map_cons,List.map_nil,cval] at ts
    change ((g.op=.and → value g w=false) ∧ _) ↔ ((g.op=.and → _) ∧ _)
    apply and_congr _ ts
    apply forall_congr'
    intro op
    rw [vals,op]
    simp [GateOp.eval]

theorem singleton_hit {n : ℕ} (A : Finset (Fin n)) :
    (List.ofFn fun i : Fin n => ({i} : Finset (Fin n))).map (fun S => hit S A)=List.ofFn (fun i => decide (i∈A)) := by
  simp [List.map_ofFn,Function.comp_def,hit]

theorem circuit {n : ℕ} (A : Finset (Fin n)) (C : Circuit) (mono : Monotone2 C) :
    missing A (List.ofFn fun i : Fin n => ({i} : Finset (Fin n))) C.gates ↔
    ∀ j (hj : j < C.gates.length), (gateAt C j).op=.and →
      (C.wires (List.ofFn fun i => decide (i∈A))).getD (n+j) false=false := by
  have ok (g : Gate) (h : g∈C.gates) : g.op=.and ∨ g.op=.or := by simpa using (mono g h).1
  rw [←cone_check A _ ok _,singleton_hit,check_iff]
  have atgate (j : ℕ) (hj : j < C.gates.length) : gateAt C j=C.gates[j] := by simp [gateAt,List.getD_eq_getElem?_getD,hj]
  simp only [List.length_ofFn]
  constructor
  · intro h j hj op
    exact h j hj ((atgate j hj) ▸ op)
  · intro h j hj op
    exact h j hj ((atgate j hj).symm ▸ op)

end Ports3451


namespace LocalCost3451

theorem probe_lower_bound {N k : ℕ} (I : Fin N → Fin N → Bool)
    (P L : Fin k → Fin N → Bool) (combine : (Fin k → Bool) → Bool)
    (distinct : ∀ p q, p≠q → ∃ l, I p l ≠ I q l)
    (spec : ∀ p l, combine (fun t => P t p || L t l)=I p l) : N ≤ 2^k := by
  have inj : Function.Injective (fun p : Fin N => fun t : Fin k => P t p) := by
    intro p q eq
    by_contra ne
    obtain ⟨l,h⟩ := distinct p q ne
    apply h
    rw [←spec p l,←spec q l]
    apply congrArg combine
    funext t
    exact congrArg (fun b => b || L t l) (congrFun eq t)
  simpa using Fintype.card_le_of_injective _ inj

def cyclic (N : ℕ) (p l : Fin N) : Bool :=
  decide (p.val=l.val ∨ (p.val+1)%N=l.val)

theorem cyclic_distinct {N : ℕ} (large : 3 ≤ N) : ∀ p q : Fin N, p≠q → ∃ l, cyclic N p l ≠ cyclic N q l := by
  intro p q diff
  have neq : p.val≠q.val := fun e => diff (Fin.ext e)
  have hp := p.isLt
  have hq := q.isLt
  have step (v : Fin N) : (v.val+1)%N=if v.val+1=N then 0 else v.val+1 := by
    split
    · rename_i h;rw [h,Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by have := v.isLt;omega)]
  by_cases pred : (q.val+1)%N=p.val
  · refine ⟨q,?_⟩
    have no : (p.val+1)%N≠q.val := by
      rw [step] at pred ⊢
      split_ifs at pred ⊢ <;> omega
    simp [cyclic,neq,no]
  · exact ⟨p,by simp [cyclic,Ne.symm neq,pred]⟩

theorem cyclic_free {N : ℕ} (large : 3 ≤ N) : ∀ a b c d : Fin N, a≠b → c≠d → ¬(cyclic N a c=true ∧
    cyclic N a d=true ∧ cyclic N b c=true ∧ cyclic N b d=true) := by
  intro a b c d ab cd edges
  have two (p : Fin N) (hc : cyclic N p c=true) (hd : cyclic N p d=true) (l : Fin N) :
      cyclic N p l=true ↔ c.val=l.val ∨ d.val=l.val := by
    have nc : c.val≠d.val := fun e => cd (Fin.ext e)
    simp only [cyclic,decide_eq_true_eq] at hc hd ⊢
    rcases hc with hc|hc <;> rcases hd with hd|hd <;> omega
  obtain ⟨l,neq⟩ := cyclic_distinct large a b ab
  apply neq
  exact Bool.eq_iff_iff.mpr ((two a edges.1 edges.2.1 l).trans (two b edges.2.2.1 edges.2.2.2 l).symm)

def edge {N : ℕ} (I : Fin N → Fin N → Prop) (P L : Fin N → Bool) : Prop :=
  ∃ p l, I p l ∧ P p=true ∧ L l=true

def both {N : ℕ} (P L : Fin N → Bool) : Prop := (∃ p, P p=true) ∧ ∃ l, L l=true

theorem guard {N : ℕ} (I : Fin N → Fin N → Prop) (P L : Fin N → Bool)
    (rows : ∀ p, ∃ l, I p l) (cols : ∀ l, ∃ p, I p l) :
    ((edge I P L ∨ (∀ p, P p=true) ∨ (∀ l, L l=true)) ∧ both P L) ↔ edge I P L := by
  constructor
  · rintro ⟨yes,⟨p,pp⟩,l,ll⟩
    rcases yes with h|all|all
    · exact h
    · obtain ⟨q,inc⟩ := cols l
      exact ⟨q,l,inc,all q,ll⟩
    · obtain ⟨k,inc⟩ := rows p
      exact ⟨p,k,inc,pp,all k⟩
  · intro h
    rcases h with ⟨p,l,inc,hp,hl⟩
    exact ⟨Or.inl ⟨p,l,inc,hp,hl⟩,⟨p,hp⟩,l,hl⟩

theorem mixed_distinguishes {N k : ℕ} (large : 3 ≤ N)
    (P L : Fin k → Fin N → Bool) (combine : (Fin k → Bool) → Bool)
    (spec : ∀ p l, combine (fun t => P t p || L t l)=cyclic N p l) : N ≤ 2^k :=
  probe_lower_bound _ _ _ _ (cyclic_distinct large) spec

end LocalCost3451

namespace LocalCost3451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ports (gs : List Gate) (out : ℕ) := out :: gs.flatMap Gate.inputs
def run (gs : List Gate) (w : List Bool) := gs.foldl (fun s g => s++[g.op.eval (g.inputs.map fun i => s.getD i false)]) w

theorem needed (gs : List Gate) (out : ℕ) (w v : List Bool) (len : w.length=v.length)
    (raw : ∀ i∈ports gs out, w.getD i false=v.getD i false) :
    (run gs w).getD out false=(run gs v).getD out false := by
  induction gs generalizing w v with
  | nil => exact raw out List.mem_cons_self
  | cons g gs ih =>
    have eq : g.op.eval (g.inputs.map fun i => w.getD i false)=g.op.eval (g.inputs.map fun i => v.getD i false) := by
      apply congrArg g.op.eval
      exact List.map_congr_left (fun i mem => raw i (by simp [ports,mem]))
    change (run gs (w++[_])).getD out false=(run gs (v++[_])).getD out false
    rw [eq]
    apply ih _ _ (by simp [len])
    intro i hi
    by_cases small : i < w.length
    · rw [List.getD_append _ _ _ _ small,List.getD_append _ _ _ _ (by omega)]
      apply raw
      simp only [ports,List.mem_cons,List.flatMap_cons,List.mem_append] at hi ⊢
      tauto
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]

theorem ports_bound (C : Circuit) (arity : ∀ g∈C.gates, g.inputs.length ≤ 2) :
    (ports C.gates C.output).length ≤ 2*C.size+1 := by
  have count (gs : List Gate) (sizes : ∀ g∈gs, g.inputs.length ≤ 2) : (gs.flatMap Gate.inputs).length ≤ 2*gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      have sh := sizes g List.mem_cons_self
      have st := ih (fun h hh => sizes h (List.mem_cons_of_mem _ hh))
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega
  have h := count C.gates arity
  change (C.gates.flatMap Gate.inputs).length+1 ≤ 2*C.gates.length+1
  omega

theorem circuit_probe_lower {N k : ℕ} (I : Fin N → Fin N → Bool)
    (P L : Fin k → Fin N → Bool) (C : Circuit) (arity : ∀ g∈C.gates, g.inputs.length ≤ 2)
    (distinct : ∀ p q, p≠q → ∃ l, I p l ≠ I q l)
    (result : ∀ p l, C.eval (List.ofFn fun t => P t p || L t l)=I p l) :
    N ≤ 2^(2*C.size+1) := by
  let used := ports C.gates C.output
  let sig (p : Fin N) (j : Fin used.length) := if h : used[j] < k then P ⟨used[j],h⟩ p else false
  have inj : Function.Injective sig := by
    intro p q eq
    by_contra ne
    obtain ⟨l,diff⟩ := distinct p q ne
    apply diff
    rw [←result p l,←result q l]
    apply needed C.gates C.output _ _ (by simp)
    intro i hi
    change i∈used at hi
    obtain ⟨j,hj,jval⟩ := List.getElem_of_mem hi
    by_cases small : i < k
    · let t : Fin used.length := ⟨j,hj⟩
      have index : used[t]=i := jval
      have s := congrFun eq t
      change (if h : used[t] < k then P ⟨used[t],h⟩ p else false) = (if h : used[t] < k then P ⟨used[t],h⟩ q else false) at s
      simp only [index,small,dite_true] at s
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,small,dite_true,Option.getD_some,s]
    · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
  have card : N ≤ 2^used.length := by simpa using Fintype.card_le_of_injective _ inj
  exact card.trans (Nat.pow_le_pow_right (by decide) (ports_bound C arity))

end LocalCost3451

namespace Ports3451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem reaches (gs : List Gate) (mono : ∀ g∈gs, g.op=.and ∨ g.op=.or)
    (w a b : List Bool) (wa : w.length=a.length) (wb : w.length=b.length)
    (lift : ∀ i, w.getD i false=true → a.getD i false=true ∨ b.getD i false=true)
    (quiet : check w gs) : ∀ i, (run gs w).getD i false=true →
    (run gs a).getD i false=true ∨ (run gs b).getD i false=true := by
  induction gs generalizing w a b with
  | nil => exact lift
  | cons g gs ih =>
    have next : (if g.op=.and then false else value g w)=value g w := by
      split
      · exact (quiet.1 (by assumption)).symm
      · rfl
    have tail : check (w++[value g w]) gs := by rw [←next];exact quiet.2
    apply ih (fun g' h => mono _ (List.mem_cons_of_mem _ h)) (w++[value g w]) (a++[value g a]) (b++[value g b])
      (by simp [wa]) (by simp [wb]) _ tail
    intro i hi
    by_cases small : i < w.length
    · rw [List.getD_append _ _ _ _ small] at hi
      rw [List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
      exact lift i hi
    · by_cases eq : i=w.length
      · subst i
        have on : value g w=true := by simpa using hi
        have branch : value g a=true ∨ value g b=true := by
          rcases mono g List.mem_cons_self with op|op
          · exact False.elim (Bool.noConfusion ((quiet.1 op).symm.trans on))
          · simp only [value,op,GateOp.eval,List.any_eq_true,List.mem_map,id_eq] at on ⊢
            obtain ⟨_,⟨j,mem,rfl⟩,high⟩ := on
            rcases lift j high with ha|hb
            · exact Or.inl ⟨_,⟨j,mem,rfl⟩,ha⟩
            · exact Or.inr ⟨_,⟨j,mem,rfl⟩,hb⟩
        rcases branch with left|right
        · left;rw [wa];simpa using left
        · right;rw [wb];simpa using right
      · rw [List.getD_eq_default _ _ (by simp;omega)] at hi
        exact Bool.noConfusion hi

end Ports3451

namespace LocalCost3451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem local_repair {N k : ℕ} (I : Fin N → Fin N → Bool)
    (P L : Fin k → Fin N → Bool) (C : Circuit) (mono : Monotone2 C)
    (rows : ∀ p q, p≠q → ∃ l, I p l ≠ I q l)
    (preserve : ∀ p l, I p l=true → C.eval (List.ofFn fun t => P t p || L t l)=true)
    (pfalse : C.eval (List.ofFn fun t => decide (∃ p, P t p=true))=false)
    (lfalse : C.eval (List.ofFn fun t => decide (∃ l, L t l=true))=false)
    (clean : ∀ p l, I p l=false → ∀ j < C.gates.length, (gateAt C j).op=.and →
      (C.wires (List.ofFn fun t => P t p || L t l)).getD (k+j) false=false) :
    N ≤ 2^(2*C.size+1) := by
  apply circuit_probe_lower I P L C (fun g h => (mono g h).2) rows
  intro p l
  cases h : I p l with
  | true => exact preserve _ _ h
  | false =>
    let w := List.ofFn fun t => P t p || L t l
    let a := List.ofFn fun t => decide (∃ p, P t p=true)
    let b := List.ofFn fun t => decide (∃ l, L t l=true)
    have quiet : Ports3451.check w C.gates := by
      apply (Ports3451.check_iff _ _).mpr
      intro j hj op
      have gate : gateAt C j=C.gates[j] := by simp [gateAt,List.getD_eq_getElem?_getD,hj]
      have eq := clean p l h j hj (by rw [gate];exact op)
      change (Ports3451.run C.gates w).getD (k+j) false=false at eq
      simpa only [w,List.length_ofFn] using eq
    have mono' (g : Gate) (m : g∈C.gates) : g.op=.and ∨ g.op=.or := by simpa using (mono g m).1
    have lift (i : ℕ) : w.getD i false=true → a.getD i false=true ∨ b.getD i false=true := by
      intro hi
      by_cases hr : i < k
      · simp only [w,a,b,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hr,dite_true,Option.getD_some,
          Bool.or_eq_true,decide_eq_true_eq] at hi ⊢
        exact hi.elim (fun hp => Or.inl ⟨p,hp⟩) (fun hl => Or.inr ⟨l,hl⟩)
      · simp [w,List.getD_eq_getElem?_getD,hr] at hi
    cases v : C.eval w with
    | false => rfl
    | true =>
      rcases Ports3451.reaches C.gates mono' w a b (by simp [w,a]) (by simp [w,b]) lift quiet C.output v with u|u
      · exact False.elim (Bool.noConfusion (pfalse.symm.trans u))
      · exact False.elim (Bool.noConfusion (lfalse.symm.trans u))

end LocalCost3451
