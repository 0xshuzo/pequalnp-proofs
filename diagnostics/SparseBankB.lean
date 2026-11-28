import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9829.CofactorBank
abbrev Signal (X : Type) := X → Bool

structure Shelf (X : Type) where
  has : Signal X → Prop
  unary : ∀ f, has f → ∀ (u : Bool → Bool), has (fun x => u (f x))

def Shelf.add {X : Type} (B : Shelf X) (g : Signal X) : Shelf X where
  has f := B.has f ∨ ∃ u : Bool → Bool, f = fun x => u (g x)
  unary f hf v := by
    rcases hf with old | ⟨u,rfl⟩
    · exact Or.inl (B.unary _ old _)
    · exact Or.inr ⟨fun b => v (u b),rfl⟩

def Canal (op : Bool → Bool → Bool) : Prop :=
  (∃ a c, ∀ b, op a b = c) ∧ (∃ b c, ∀ a, op a b = c)

inductive Runs {X I : Type} (target : I → Signal X) : Shelf X → Nat → Prop
 | done {B} (ok : ∀ i,B.has (target i)) : Runs target B 0
 | step {B n a b} (ha : B.has a) (hb : B.has b) (op : Bool → Bool → Bool)
     (legal : Canal op) (tail : Runs target (B.add (fun x => op (a x) (b x))) n) :
       Runs target B (n+1)

variable {X Y I : Type} {target : I → Signal X}

def Trans (q : Y → X) (B : Shelf X) (D : Shelf Y) : Prop :=
  ∀ f,B.has f → D.has (fun y => f (q y))

theorem extendCheap {B : Shelf X} {D : Shelf Y} {q : Y → X} {g : Signal X}
    (tr : Trans q B D) (free : D.has (fun y => g (q y))) : Trans q (B.add g) D := by
  intro f h
  rcases h with old | ⟨u,rfl⟩
  · exact tr _ old
  · exact D.unary _ free u

theorem extendPaid {B : Shelf X} {D : Shelf Y} {q : Y → X} {g : Signal X}
    (tr : Trans q B D) : Trans q (B.add g) (D.add (fun y => g (q y))) := by
  intro f h
  rcases h with h | ⟨u,rfl⟩
  · exact Or.inl (tr _ h)
  · exact Or.inr ⟨u,rfl⟩

theorem projection {B : Shelf X} {n} (run : Runs target B n) (q : Y → X)
    {D : Shelf Y} (tr : Trans q B D) : Runs (fun i y => target i (q y)) D n := by
  induction run generalizing D with
  | done ok => exact .done (fun i => tr _ (ok i))
  | step ha hb op legal tail ih =>
    exact .step (tr _ ha) (tr _ hb) op legal (ih (extendPaid tr))

def Constant (v : Signal Y) : Prop := ∃ b,∀ y,v y=b

def Safe (x z : X) (q : Y → X) (f : Signal X) : Prop :=
  f x=f z ∨ Constant (fun y => f (q y))

theorem addSafe {B : Shelf X} {v : Signal X} {x z : X} {q : Y → X}
    (old : ∀ f,B.has f → Safe x z q f) (next : Safe x z q v) :
    ∀ f,(B.add v).has f → Safe x z q f := by
  intro f h
  rcases h with prev | ⟨u,rfl⟩
  · exact old _ prev
  · rcases next with same | ⟨c,hc⟩
    · exact Or.inl (congrArg u same)
    · exact Or.inr ⟨u c,fun y => congrArg u (hc y)⟩

theorem saveReader {B : Shelf X} {n} (run : Runs target B n) (q : Y → X) (x z : X)
    {D : Shelf Y} (tr : Trans q B D) (clean : ∀ f,B.has f → Safe x z q f)
    (bad : ∃ i,¬ Safe x z q (target i)) :
    ∃ m, m+1 ≤ n ∧ Runs (fun i y => target i (q y)) D m := by
  induction run generalizing D with
  | done ok =>
    obtain ⟨i,no⟩ := bad
    exact (no (clean _ (ok i))).elim
  | @step B n a b ha hb op legal tail ih =>
    let g : Signal X := fun s => op (a s) (b s)
    by_cases sg : Safe x z q g
    · obtain ⟨m,hm,r⟩ := ih (extendPaid tr) (addSafe clean sg)
      exact ⟨m+1,by omega,.step (tr _ ha) (tr _ hb) op legal r⟩
    · have free : D.has (fun y => g (q y)) := by
        rcases clean _ ha with la | ⟨c,hc⟩
        · rcases clean _ hb with lb | ⟨d,hd⟩
          · exact (sg (Or.inl (by change op (a x) (b x)=op (a z) (b z);rw [la,lb]))).elim
          · have e : (fun y => g (q y)) = (fun y => op (a (q y)) d) :=
              funext (fun y => congrArg (op (a (q y))) (hd y))
            rw [e]
            exact D.unary _ (tr _ ha) (fun s => op s d)
        · have e : (fun y => g (q y)) = (fun y => op c (b (q y))) :=
            funext (fun y => congrArg (fun t => op t (b (q y))) (hc y))
          rw [e]
          exact D.unary _ (tr _ hb) (op c)
      exact ⟨n,by omega,projection tail q (extendCheap tr free)⟩
open Finset
section Board
variable {P J : Type} [DecidableEq P]
abbrev Board (P : Type) := P → Bool
def raw (P : Type) : Shelf (Board P) where
  has f := Constant f ∨ ∃ p : P,∃ u : Bool→Bool,f=fun x => u (x p)
  unary f hf v := by
    rcases hf with ⟨b,hb⟩ | ⟨p,u,rfl⟩
    · exact Or.inl ⟨v b,fun y => congrArg v (hb y)⟩
    · exact Or.inr ⟨p,fun b => v (u b),rfl⟩

def clamp (p : P) (x : Board P) := Function.update x p false
noncomputable def rowOr (s : Finset P) (x : Board P) : Bool := s.toList.any x

theorem row_on (s : Finset P) (x : Board P) : rowOr s x=true ↔ ∃ i∈s,x i=true := by
  simp [rowOr,List.any_eq_true]

theorem row_clamp (s : Finset P) (p : P) (x : Board P) :
    rowOr s (clamp p x) = rowOr (s.erase p) x := by
  apply Bool.eq_iff_iff.mpr
  rw [row_on,row_on]
  constructor
  · rintro ⟨i,hi,on⟩
    by_cases eq : i=p
    · subst i
      simp [clamp] at on
    · exact ⟨i,mem_erase.mpr ⟨eq,hi⟩,by simpa [clamp,eq] using on⟩
  · rintro ⟨i,hi,on⟩
    obtain ⟨ne,ins⟩ := mem_erase.mp hi
    exact ⟨i,ins,by simpa [clamp,ne] using on⟩

theorem rawMap (p : P) : Trans (clamp p) (raw P) (raw P) := by
  intro f hf
  rcases hf with ⟨b,hb⟩ | ⟨j,u,rfl⟩
  · exact Or.inl ⟨b,fun y => hb _⟩
  · by_cases eq : j=p
    · subst j
      exact Or.inl ⟨u false,fun y => by simp [clamp]⟩
    · exact Or.inr ⟨j,u,funext (fun y => by simp [clamp,eq])⟩

theorem rawSafe (p : P) (v : Board P) : ∀ f,(raw P).has f →
    Safe v (Function.update v p true) (clamp p) f := by
  intro f hf
  rcases hf with ⟨b,hb⟩ | ⟨j,u,rfl⟩
  · exact Or.inl ((hb _).trans (hb _).symm)
  · by_cases eq : j=p
    · subst j
      exact Or.inr ⟨u false,fun y => by simp [clamp]⟩
    · exact Or.inl (by simp [eq])

theorem rowObstruction {s : Finset P} {p j k : P} (hp : p∈s) (hk : k∈s)
    (kp : k≠p) (hj : j∉s) (value : Bool) :
    let v : Board P := fun i => if i=j then value else false
    ¬ Safe v (Function.update v p true) (clamp p) (rowOr s) := by
  let v : Board P := fun i => if i=j then value else false
  change ¬ Safe v (Function.update v p true) (clamp p) (rowOr s)
  have off : rowOr s v=false := by
    cases h : rowOr s v with
    | false => rfl
    | true =>
      obtain ⟨i,hi,yes⟩ := (row_on s v).mp h
      have ne : i≠j := fun e => hj (e ▸ hi)
      simp [v,ne] at yes
  have on : rowOr s (Function.update v p true)=true :=
    (row_on _ _).mpr ⟨p,hp,by simp⟩
  have zero : rowOr (s.erase p) (fun _ => false)=false := by
    cases h : rowOr (s.erase p) (fun _ => false) with
    | false => rfl
    | true => simpa using (row_on _ _).mp h
  have one : rowOr (s.erase p) (fun i => decide (i=k))=true :=
    (row_on _ _).mpr ⟨k,mem_erase.mpr ⟨kp,hk⟩,by simp⟩
  rintro (same | ⟨b,hb⟩)
  · simp [off,on] at same
  · have c := hb (fun _ => false)
    have d := hb (fun i => decide (i=k))
    change rowOr s (clamp p (fun _ => false)) = b at c
    change rowOr s (clamp p (fun i => decide (i=k))) = b at d
    rw [row_clamp,zero] at c
    rw [row_clamp,one] at d
    cases b <;> simp_all

theorem surjUnary {u : Bool→Bool} (diff : u false ≠ u true) (c : Bool) :
    ∃ b,u b=c := by
  cases h : u false <;> cases k : u true <;> cases c <;> first | exact ⟨false,h⟩ | exact ⟨true,k⟩ | simp_all

theorem rowStep {rows : J→Finset P} {p j : P} (pj : p≠j) (u v : Bool→Bool)
    (vd : v false≠v true) (op : Bool→Bool→Bool) (can : Canal op)
    (witness : ∃ t, p∈rows t ∧ j∉rows t ∧ ∃k∈rows t,k≠p)
    {n} (tail : Runs (fun t => rowOr (rows t))
      ((raw P).add (fun x => op (u (x p)) (v (x j)))) n) :
    ∃ m, m+1≤n ∧ Runs (fun t => rowOr ((rows t).erase p)) (raw P) m := by
  obtain ⟨absorber,c,blocks⟩ := can.2
  obtain ⟨value,hval⟩ := surjUnary vd absorber
  let z : Board P := fun i => if i=j then value else false
  let w : Signal (Board P) := fun x => op (u (x p)) (v (x j))
  have eq : w z = w (Function.update z p true) := by
    simp [w,z,pj,Ne.symm pj,hval,blocks]
  have zfree : (raw P).has (fun y => w (clamp p y)) := by
    exact Or.inr ⟨j,fun s => op (u false) (v s),funext (fun y => by simp [w,clamp,Ne.symm pj])⟩
  obtain ⟨t,hp,hj,k,hk,ne⟩ := witness
  have bad : ¬ Safe z (Function.update z p true) (clamp p) (rowOr (rows t)) :=
    rowObstruction hp hk ne hj value
  obtain ⟨m,hm,run⟩ := saveReader tail (clamp p) z (Function.update z p true)
    (extendCheap (rawMap p) zfree) (addSafe (rawSafe p z) (Or.inl eq)) ⟨t,bad⟩
  exact ⟨m,hm,by simpa only [row_clamp] using run⟩
end Board
section Price
open Finset
variable {P J : Type} [DecidableEq P] [DecidableEq J] [Fintype J]
def owners (rows : J → Finset P) (p : P) : Finset J :=
  univ.filter (fun i => p∈rows i ∧ 2≤(rows i).card)
def dropPin (rows : J → Finset P) (p : P) (i : J) := (rows i).erase p
def cost (rows : J → Finset P) := ∑ i,((rows i).card-1)
def Linear (rows : J → Finset P) := ∀ p q : P,p≠q → ∀ a b : J,
    p∈rows a → q∈rows a → p∈rows b → q∈rows b → a=b
def Sparse (rows : J → Finset P) := ∀ p q : P, p≠q →
    (owners rows p).card≤2 ∨ (owners rows q).card≤2

theorem chooseRow {rows : J→Finset P} (lin : Linear rows) {p j : P} (ne : p≠j)
    (two : 2≤(owners rows p).card) : ∃ t, p∈rows t ∧ j∉rows t ∧ ∃k∈rows t,k≠p := by
  classical
  obtain ⟨a,ha,b,hb,diff⟩ := one_lt_card.mp two
  have good {i : J} (hi : i∈owners rows p) (avoid : j∉rows i) :
      p∈rows i ∧ j∉rows i ∧ ∃k∈rows i,k≠p := by
    obtain ⟨hp,large⟩ := (mem_filter.mp hi).2
    obtain ⟨f,hf,g,hg,fg⟩ := one_lt_card.mp large
    refine ⟨hp,avoid,?_⟩
    by_cases e : f=p
    · exact ⟨g,hg,fun eq => fg (e.trans eq.symm)⟩
    · exact ⟨f,hf,e⟩
  by_cases aj : j∈rows a
  · have bj : j∉rows b := fun h => diff (lin p j ne a b (mem_filter.mp ha).2.1 aj (mem_filter.mp hb).2.1 h)
    exact ⟨b,good hb bj⟩
  · exact ⟨a,good ha aj⟩

theorem dropLinear {rows : J→Finset P} (lin : Linear rows) (p : P) :
    Linear (dropPin rows p) := by
  intro i j ne a b h₁ h₂ h₃ h₄
  exact lin i j ne a b (mem_erase.mp h₁).2 (mem_erase.mp h₂).2 (mem_erase.mp h₃).2 (mem_erase.mp h₄).2

theorem dropSparse {rows : J→Finset P} (thin : Sparse rows) (p : P) :
    Sparse (dropPin rows p) := by
  have le (i : P) : (owners (dropPin rows p) i).card ≤ (owners rows i).card := by
    apply card_le_card
    intro j hj
    obtain ⟨hi,large⟩ := (mem_filter.mp hj).2
    exact mem_filter.mpr ⟨mem_univ _,(mem_erase.mp hi).2,large.trans (card_le_card (erase_subset p (rows j)))⟩
  intro i j ne
  rcases thin i j ne with a|b
  · exact Or.inl ((le i).trans a)
  · exact Or.inr ((le j).trans b)

theorem costDrop (rows : J→Finset P) (p : P) :
    cost (dropPin rows p)+(owners rows p).card=cost rows := by
  classical
  unfold cost owners
  rw [card_filter]
  calc
    _ = ∑ i : J, (((dropPin rows p i).card-1) + (if p∈rows i ∧ 2≤(rows i).card then 1 else 0)) := by rw [Finset.sum_add_distrib]
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      unfold dropPin
      by_cases hp : p∈rows i
      · rw [card_erase_of_mem hp]
        by_cases large : 2≤(rows i).card <;> simp [hp,large] <;> omega
      · simp [erase_eq_of_notMem hp,hp]

theorem initialSmall {s : Finset P} (raws : (raw P).has (rowOr s)) : s.card≤1 := by
  by_contra! big
  obtain ⟨p,hp,q,hq,ne⟩ := one_lt_card.mp big
  let z : Board P := fun _ => false
  have off : rowOr s z=false := by
    cases h : rowOr s z with
    | false => rfl
    | true => simpa [z] using (row_on s z).mp h
  have on (i : P) (hi : i∈s) : rowOr s (fun t => decide (t=i))=true :=
    (row_on _ _).mpr ⟨i,hi,by simp⟩
  rcases raws with ⟨c,hc⟩ | ⟨j,u,e⟩
  · have a := hc z
    have b := hc (fun t => decide (t=p))
    rw [off] at a
    rw [on p hp] at b
    cases c <;> simp_all
  · have no (i : P) (hi : i∈s) (ij : j≠i) : False := by
      have a := congrFun e z
      have b := congrFun e (fun t => decide (t=i))
      rw [off] at a
      rw [on i hi] at b
      have uf : u false=false := by simpa only [z] using a.symm
      simpa [ij,uf] using b
    by_cases jp : j=p
    · exact no q hq (fun e => ne (jp.symm.trans e))
    · exact no p hp jp

theorem unaryConst {u : Bool→Bool} (same : u false=u true) (b : Bool) : u b=u false := by
  cases b
  · rfl
  · exact same.symm

theorem stepBound {rows : J→Finset P} (lin : Linear rows) (thin : Sparse rows)
    {p j : P} (ne : p≠j) (cheap : (owners rows p).card≤2) (u v : Bool→Bool)
    (vd : v false≠v true) (op : Bool→Bool→Bool) (can : Canal op)
    {n} (tail : Runs (fun i => rowOr (rows i))
       ((raw P).add (fun x => op (u (x p)) (v (x j)))) n)
    (ih : ∀ m, m<n+1 → ∀ rs : J→Finset P, Linear rs → Sparse rs →
      Runs (fun i => rowOr (rs i)) (raw P) m → cost rs≤m) :
    cost rows ≤ n+1 := by
  have cd := costDrop rows p
  by_cases two : 2≤(owners rows p).card
  · obtain ⟨m,le,r⟩ := rowStep ne u v vd op can (chooseRow lin ne two) tail
    have h := ih m (by omega) (dropPin rows p) (dropLinear lin p) (dropSparse thin p) r
    omega
  · have free : (raw P).has (fun y => op (u ((clamp p y) p)) (v ((clamp p y) j))) :=
      Or.inr ⟨j,fun s => op (u false) (v s),funext (fun y => by simp [clamp,Ne.symm ne])⟩
    have sub := projection tail (clamp p) (extendCheap (rawMap p) free)
    have r : Runs (fun i => rowOr (dropPin rows p i)) (raw P) n := by
      simpa only [row_clamp,dropPin] using sub
    have h := ih n (by omega) (dropPin rows p) (dropLinear lin p) (dropSparse thin p) r
    omega

theorem sparseBankPrice (n : Nat) (rows : J→Finset P) (lin : Linear rows) (thin : Sparse rows)
    (run : Runs (fun i => rowOr (rows i)) (raw P) n) : cost rows≤n := by
  induction n using Nat.strong_induction_on generalizing rows with
  | ind n ih =>
    cases run with
    | done ok =>
      have e : cost rows=0 := by
        apply sum_eq_zero
        intro i hi
        exact Nat.sub_eq_zero_of_le (initialSmall (ok i))
      omega
    | @step _ k a b ha hb op can tail =>
      let g : Signal (Board P) := fun x => op (a x) (b x)
      by_cases free : (raw P).has g
      · have tr : Trans id (raw P) (raw P) := fun _ h => h
        have sub := projection tail id (extendCheap tr free)
        exact Nat.le.step (ih k (by omega) rows lin thin sub)
      · rcases ha with ⟨ca,ha⟩ | ⟨p,u,rfl⟩
        · have e : g=(fun x => op ca (b x)) := funext (fun x => congrArg (fun t => op t (b x)) (ha x))
          apply False.elim
          apply free
          rw [e]
          exact (raw P).unary b hb (op ca)
        rcases hb with ⟨cb,hb⟩ | ⟨j,v,rfl⟩
        · have e : g=(fun x => op (u (x p)) cb) := funext (fun x => congrArg (op (u (x p))) (hb x))
          apply False.elim
          apply free
          rw [e]
          exact Or.inr ⟨p,fun t => op (u t) cb,rfl⟩
        have ne : p≠j := by
          rintro rfl
          exact free (Or.inr ⟨p,fun t => op (u t) (v t),rfl⟩)
        have ud : u false ≠ u true := by
          intro same
          exact free (Or.inr ⟨j,fun t => op (u false) (v t),funext (fun x =>
            congrArg (fun a => op a (v (x j))) (unaryConst same (x p)))⟩)
        have vd : v false ≠ v true := by
          intro same
          exact free (Or.inr ⟨p,fun t => op (u t) (v false),funext (fun x =>
            congrArg (op (u (x p))) (unaryConst same (x j)))⟩)
        rcases thin p j ne with cheap|cheap
        · exact stepBound lin thin ne cheap u v vd op can tail ih
        · exact stepBound lin thin ne.symm cheap v u ud (fun x y => op y x) ⟨can.2,can.1⟩ tail ih
end Price
end PEqualNP.Outside.L_meta_9829.CofactorBank
