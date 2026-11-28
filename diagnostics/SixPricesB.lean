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

theorem pricedStep {rows : J→Finset P}
    {p j : P} (ne : p≠j) (u v : Bool→Bool)
    (vd : v false≠v true) (op : Bool→Bool→Bool) (can : Canal op)
    {n a b : Nat}
    (budget : a≤b+1 ∨ a≤b+2 ∧ 2≤(owners rows p).card)
    (lin : Linear rows)
    (tail : Runs (fun i => rowOr (rows i))
       ((raw P).add (fun x => op (u (x p)) (v (x j)))) n)
    (lower : ∀ m, m<n+1 → Runs (fun i => rowOr (dropPin rows p i)) (raw P) m → b≤m) :
    a ≤ n+1 := by
  rcases budget with small | ⟨big,two⟩
  · have free : (raw P).has (fun y => op (u ((clamp p y) p)) (v ((clamp p y) j))) :=
      Or.inr ⟨j,fun z => op (u false) (v z),funext (fun y => by simp [clamp,Ne.symm ne])⟩
    have sub := projection tail (clamp p) (extendCheap (rawMap p) free)
    have r : Runs (fun i => rowOr (dropPin rows p i)) (raw P) n := by
      simpa only [row_clamp,dropPin] using sub
    have h := lower n (by omega) r
    omega
  · obtain ⟨m,le,r⟩ := rowStep ne u v vd op can (chooseRow lin ne two) tail
    have h := lower m (by omega) r
    omega

theorem frontierPrice {A : Type} (rs : A → J → Finset P) (cut : A → P → A)
    (rank : A → Nat) (exception : A → P)
    (drop : ∀ a p, rs (cut a p) = dropPin (rs a) p)
    (tiny : ∀ a, rank a=0 ∨ ∃ i,2≤(rs a i).card)
    (linear : ∀ a, Linear (rs a))
    (next : ∀ a p, p≠exception a →
      rank a≤rank (cut a p)+1 ∨ rank a≤rank (cut a p)+2 ∧ 2≤(owners (rs a) p).card)
    (n : Nat) (a : A) (run : Runs (fun i => rowOr (rs a i)) (raw P) n) :
    rank a≤n := by
  induction n using Nat.strong_induction_on generalizing a with
  | ind n ih =>
    cases run with
    | done ok =>
      rcases tiny a with e|⟨i,big⟩
      · omega
      · have h := initialSmall (ok i)
        omega
    | @step _ k s t hs ht op can tail =>
      let g : Signal (Board P) := fun x => op (s x) (t x)
      by_cases free : (raw P).has g
      · have tr : Trans id (raw P) (raw P) := fun _ h => h
        have sub := projection tail id (extendCheap tr free)
        exact Nat.le.step (ih k (by omega) a sub)
      · rcases hs with ⟨ca,hs⟩ | ⟨p,u,rfl⟩
        · have e : g=(fun x => op ca (t x)) := funext (fun x => congrArg (fun z => op z (t x)) (hs x))
          apply False.elim
          apply free
          rw [e]
          exact (raw P).unary t ht (op ca)
        rcases ht with ⟨cb,ht⟩ | ⟨j,v,rfl⟩
        · have e : g=(fun x => op (u (x p)) cb) := funext (fun x => congrArg (op (u (x p))) (ht x))
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
            congrArg (fun s => op s (v (x j))) (unaryConst same (x p)))⟩)
        have vd : v false ≠ v true := by
          intro same
          exact free (Or.inr ⟨p,fun t => op (u t) (v false),funext (fun x =>
            congrArg (op (u (x p))) (unaryConst same (x j)))⟩)
        by_cases good : p=exception a
        · have goodj : j≠exception a := fun e => ne (good.trans e.symm)
          apply pricedStep ne.symm v u ud (fun x y => op y x) ⟨can.2,can.1⟩
            (next a j goodj) (linear a) tail
          intro m lt r
          apply ih m lt (cut a j)
          simpa only [drop] using r
        · apply pricedStep ne u v vd op can (next a p good) (linear a) tail
          intro m lt r
          apply ih m lt (cut a p)
          simpa only [drop] using r
end Price
end PEqualNP.Outside.L_meta_9829.CofactorBank

namespace PEqualNP.Outside.L_meta_9829.SixCore
open PEqualNP.Outside.L_meta_9829.CofactorBank
open Finset
abbrev Pin := Fin 9
abbrev Row := Fin 6
abbrev Mask := BitVec 9
def label (i : Row) : Mask := (#[267,149,102,168,304,448] : Array Mask)[i.val]!
def rows (a : Mask) (i : Row) : Finset Pin :=
  univ.filter (fun p => a.getLsbD p.val = true ∧ (label i).getLsbD p.val = true)
def kill (p : Pin) : Mask := ~~~((1 : Mask) <<< p.val)
def cut (a : Mask) (p : Pin) : Mask := a &&& kill p
theorem kill_bit : ∀ p j : Pin,(kill p).getLsbD j.val = decide (j≠p) := by decide +kernel
theorem cutRows (a : Mask) (p : Pin) : rows (cut a p) = dropPin (rows a) p := by
  funext i
  ext x
  have h := kill_bit p x
  simp at h
  simp [rows,cut,dropPin,BitVec.getLsbD_and,h,and_comm,and_left_comm,and_assoc]
theorem labelsLinear : ∀ (p q : Pin), p≠q → ∀ i j : Row,
    (label i).getLsbD p.val=true → (label i).getLsbD q.val=true →
    (label j).getLsbD p.val=true → (label j).getLsbD q.val=true → i=j := by decide +kernel
theorem rowsLinear (a : Mask) : Linear (rows a) := by
  intro p q ne i j h₁ h₂ h₃ h₄
  exact labelsLinear p q ne i j (mem_filter.mp h₁).2.2 (mem_filter.mp h₂).2.2
    (mem_filter.mp h₃).2.2 (mem_filter.mp h₄).2.2
def rank (a : Mask) : Nat := (#[0,0,0,1,0,1,1,3,0,1,1,2,0,2,2,4,0,1,0,2,1,2,2,4,0,2,1,3,1,3,3,5,0,0,1,2,1,2,2,4,1,2,3,4,2,4,4,6,1,2,2,4,3,4,4,6,2,4,4,6,4,6,6,8,0,0,1,2,1,2,2,4,0,1,2,3,1,3,3,5,0,1,1,3,2,3,3,5,0,2,2,4,2,4,4,6,1,1,2,3,2,3,3,5,2,3,4,5,3,5,5,7,2,3,3,5,4,5,5,7,3,5,5,7,5,7,7,9,0,1,0,2,1,2,2,4,1,3,2,4,2,4,4,6,1,2,1,3,2,3,3,5,2,4,3,5,3,5,5,7,1,2,2,4,3,4,4,6,2,4,4,6,4,6,6,8,3,4,4,6,5,6,6,8,4,6,6,8,6,8,8,10,1,2,2,4,3,4,4,6,2,4,4,6,4,6,6,8,2,3,3,5,4,5,5,7,3,5,5,7,5,7,7,9,3,4,4,6,5,6,6,8,4,6,6,8,6,8,8,10,4,5,5,7,6,7,7,9,5,7,7,9,7,9,9,11,0,1,1,2,0,2,2,4,1,2,2,3,1,3,3,5,1,3,2,4,2,4,4,6,2,4,3,5,3,5,5,7,1,2,3,4,2,4,4,6,3,4,5,6,4,6,6,8,2,4,4,6,4,6,6,8,4,6,6,8,6,8,8,10,1,2,3,4,2,4,4,6,2,3,4,5,3,5,5,7,2,4,4,6,4,6,6,8,3,5,5,7,5,7,7,9,3,4,5,6,4,6,6,8,4,5,6,7,5,7,7,9,4,6,6,8,6,8,8,10,5,7,7,9,7,9,9,11,1,3,2,4,2,4,4,6,3,5,4,6,4,6,6,8,3,5,4,6,4,6,6,8,4,6,5,7,5,7,7,9,3,4,4,6,4,6,6,8,5,6,6,8,6,8,8,10,5,6,6,8,6,8,8,10,6,8,8,10,8,10,10,12,2,4,4,6,4,6,6,8,4,6,6,8,6,8,8,10,4,6,6,8,6,8,8,10,5,7,7,9,7,9,9,11,5,6,6,8,6,8,8,10,6,8,8,10,8,10,10,12,6,8,8,10,8,10,10,12,7,9,9,11,9,11,11,13] : Array Nat)[a.toNat]!
def exception (a : Mask) : Pin := (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,0,0,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,7,0,7,7,7,7,7,0,0,0,0,0,0,0,0,7,7,7,7,7,7,7,7,0,7,0,7,7,7,7,7,0,7,0,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,8,8,0,8,8,8,8,8,8,8,8,8,8,8,0,8,8,8,0,8,8,8,0,0,0,0,0,0,0,0,0,8,8,8,0,8,8,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,7,7,7,7,7,0,8,8,8,0,8,8,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,7,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,7,0,7,7,7,7,7,0,8,8,8,0,8,8,8,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,7,0,7,7,7,7,7,0,8,8,8,0,8,8,8,0,0,0,0,0,0,0,0] : Array Pin)[a.toNat]!
def checks (a : Mask) : Prop :=
  (rank a=0 ∨ ∃ i : Row, 2≤(rows a i).card) ∧
  (∀ p : Pin, p≠exception a →
    rank a≤rank (cut a p)+1 ∨ rank a≤rank (cut a p)+2 ∧ 2≤(owners (rows a) p).card)
instance (a : Mask) : Decidable (checks a) := by unfold checks; infer_instance
def chunk (q : Fin 32) (i : Fin 16) : Mask := BitVec.ofNat 9 (q.val*16+i.val)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks0 : ∀ i,checks (chunk 0 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks1 : ∀ i,checks (chunk 1 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks2 : ∀ i,checks (chunk 2 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks3 : ∀ i,checks (chunk 3 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks4 : ∀ i,checks (chunk 4 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks5 : ∀ i,checks (chunk 5 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks6 : ∀ i,checks (chunk 6 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks7 : ∀ i,checks (chunk 7 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks8 : ∀ i,checks (chunk 8 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks9 : ∀ i,checks (chunk 9 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks10 : ∀ i,checks (chunk 10 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks11 : ∀ i,checks (chunk 11 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks12 : ∀ i,checks (chunk 12 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks13 : ∀ i,checks (chunk 13 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks14 : ∀ i,checks (chunk 14 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks15 : ∀ i,checks (chunk 15 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks16 : ∀ i,checks (chunk 16 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks17 : ∀ i,checks (chunk 17 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks18 : ∀ i,checks (chunk 18 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks19 : ∀ i,checks (chunk 19 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks20 : ∀ i,checks (chunk 20 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks21 : ∀ i,checks (chunk 21 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks22 : ∀ i,checks (chunk 22 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks23 : ∀ i,checks (chunk 23 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks24 : ∀ i,checks (chunk 24 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks25 : ∀ i,checks (chunk 25 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks26 : ∀ i,checks (chunk 26 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks27 : ∀ i,checks (chunk 27 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks28 : ∀ i,checks (chunk 28 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks29 : ∀ i,checks (chunk 29 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks30 : ∀ i,checks (chunk 30 i) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checks31 : ∀ i,checks (chunk 31 i) := by decide +kernel
theorem chunks (q : Fin 32) (i : Fin 16) : checks (chunk q i) := by
  fin_cases q
  · exact checks0 i
  · exact checks1 i
  · exact checks2 i
  · exact checks3 i
  · exact checks4 i
  · exact checks5 i
  · exact checks6 i
  · exact checks7 i
  · exact checks8 i
  · exact checks9 i
  · exact checks10 i
  · exact checks11 i
  · exact checks12 i
  · exact checks13 i
  · exact checks14 i
  · exact checks15 i
  · exact checks16 i
  · exact checks17 i
  · exact checks18 i
  · exact checks19 i
  · exact checks20 i
  · exact checks21 i
  · exact checks22 i
  · exact checks23 i
  · exact checks24 i
  · exact checks25 i
  · exact checks26 i
  · exact checks27 i
  · exact checks28 i
  · exact checks29 i
  · exact checks30 i
  · exact checks31 i
theorem checked (a : Mask) : checks a := by
  let q : Fin 32 := ⟨a.toNat/16,by have h := a.isLt; change a.toNat<512 at h; omega⟩
  let i : Fin 16 := ⟨a.toNat%16,Nat.mod_lt _ (by decide)⟩
  have eq : chunk q i=a := by
    apply BitVec.eq_of_toNat_eq
    have h := a.isLt
    change a.toNat < 512 at h
    change (a.toNat/16*16+a.toNat%16)%512=a.toNat
    omega
  exact eq ▸ chunks q i
theorem price (a : Mask) (n : Nat)
    (run : Runs (fun i => rowOr (rows a i)) (raw Pin) n) : rank a≤n :=
  frontierPrice rows cut rank exception cutRows (fun m => (checked m).1)
    rowsLinear (fun m => (checked m).2) n a run
theorem sixPrices :
    rank 511=13 ∧ rank 503=12 ∧ rank 495=12 ∧ rank 447=12 := by decide +kernel
end PEqualNP.Outside.L_meta_9829.SixCore
