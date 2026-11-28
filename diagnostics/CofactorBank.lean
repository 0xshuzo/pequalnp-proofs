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
end PEqualNP.Outside.L_meta_9829.CofactorBank
