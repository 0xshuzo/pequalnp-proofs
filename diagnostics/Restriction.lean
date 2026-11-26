import PEqualNP.Defs

namespace Saturated8321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
abbrev X := Fin 42 → Bool
abbrev F := X → Bool
abbrev Pin := Fin 42
def Ed (u v : Pin) := u.val<21 ∧ (21 : Nat)≤v.val ∧ (v.val+21-u.val)%21∈([0,5,7,17,20]:List Nat)
instance (u v : Pin) : Decidable (Ed u v) := by unfold Ed; infer_instance
abbrev E := {z : Pin × Pin // Ed z.1 z.2}
def flag (e : E) (i : Pin) : Bool := decide (i=e.val.1 ∨ i=e.val.2)
def Hit (x : X) := ∃u v : Pin,Ed u v ∧ x u=true ∧ x v=true
def Top (C : Circuit) := ∀x : X,C.eval (List.ofFn x)=true ↔ Hit x
def paid (g : Gate) := match g.op with | .or => true | _ => false
abbrev Mask := Finset E
abbrev Recipe := Mask × Mask
def supp (f : F) : Mask := Finset.univ.filter fun e => f (flag e)=true
def covers (T : Mask) (f : F) := ∀e∈T,f (flag e)=true
def bot : F := fun _ => false
def input (i : Pin) : F := fun x => x i
def raws := List.ofFn input
def start := bot::raws
def gv (w : List F) (g : Gate) : F := fun x => g.op.eval (g.inputs.map fun i => (w.getD i bot) x)
def step (w : List F) (g : Gate) := w++[gv w g]
theorem arms {g : Gate} (w : List F) (op : g.op=.or) (size : g.inputs.length≤2) :
    ∃f g' : F,(f=bot ∨ ∃i,f=w.getD i bot) ∧ (g'=bot ∨ ∃i,g'=w.getD i bot) ∧
      gv w g=(fun x => f x || g' x) := by
  cases eq : g.inputs with
  | nil => exact ⟨bot,bot,.inl rfl,.inl rfl,by funext x; simp [gv,eq,op,GateOp.eval,bot]⟩
  | cons a t =>
    cases et : t with
    | nil => exact ⟨w.getD a bot,bot,.inr ⟨a,rfl⟩,.inl rfl,by funext x; simp [gv,eq,et,op,GateOp.eval,bot]⟩
    | cons b u =>
      cases eu : u with
      | nil => exact ⟨w.getD a bot,w.getD b bot,.inr ⟨a,rfl⟩,.inr ⟨b,rfl⟩,by
          funext x; simp [gv,eq,et,eu,op,GateOp.eval]⟩
      | cons c t' => simp [eq,et,eu] at size
def project (w : List F) (x : X) := w.map fun f => f x
theorem get_project (w : List F) (x : X) (i : Nat) :
    (project w x).getD i false = (w.getD i bot) x := by
  by_cases hi : i<w.length
  · rw [List.getD_eq_getElem _ _ (by simpa [project] using hi),List.getD_eq_getElem _ _ hi]
    simp [project]
  · rw [List.getD_eq_default _ _ (by simp [project]; omega),List.getD_eq_default _ _ (by omega)]
    rfl
theorem simulation (gs : List Gate) (w : List F) (x : X) :
    project (gs.foldl step w) x = gs.foldl (fun b g => b++[g.op.eval (g.inputs.map fun i => b.getD i false)]) (project w x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    change (w++[gv w g]).map (fun f => f x) =
      project w x ++ [g.op.eval (g.inputs.map fun i => (project w x).getD i false)]
    simp only [List.map_append,List.map_cons,List.map_nil,gv,get_project]
    rfl
theorem project_raw (x : X) : project raws x=List.ofFn x := by
  simp [project,raws,List.map_ofFn,input,Function.comp_def]
theorem hitFlag (e : E) : Hit (flag e) :=
  ⟨e.val.1,e.val.2,e.property,decide_eq_true (.inl rfl),decide_eq_true (.inr rfl)⟩
theorem subset_flag {u v : Pin} (inc : Ed u v) {x : X} (hu : x u=true) (hv : x v=true) :
    flag ⟨(u,v),inc⟩ ≤ x := by
  intro i
  apply Bool.le_iff_imp.mpr
  rintro p
  obtain rfl|rfl := of_decide_eq_true p
  · exact hu
  · exact hv
abbrev Ideal := Mask → Prop
def down (D : Ideal) := ∀{A B : Mask},A⊆B → D B → D A
def orig (x : X) (T : Mask) := T=∅ ∨ ∃v : Pin,x v=false ∧ ∀e∈T,flag e v=true
def advance (r : Recipe) (D : Ideal) (T : Mask) := D T ∨ (T⊆r.1∪r.2 ∧ D r.1 ∧ D r.2)
def replay : List Recipe → Ideal → Ideal
  | [],D => D
  | r::rs,D => replay rs (advance r D)
theorem down_orig (x : X) : down (orig x) := by
  intro A B sub h
  rcases h with rfl|⟨v,off,all⟩
  · exact Or.inl (Finset.subset_empty.mp sub)
  · exact Or.inr ⟨v,off,fun e he => all e (sub he)⟩
theorem down_step {D : Ideal} (h : down D) (r : Recipe) : down (advance r D) :=
  fun sub old => old.elim (fun q => Or.inl (h sub q)) (fun q => Or.inr ⟨sub.trans q.1,q.2⟩)
def records (Ix : X → Ideal) (w : List F) :=
  (∀ x, Ix x ∅) ∧ ∀ f∈w,∀x, f x=false → Ix x (supp f)
theorem supp0 : supp bot=∅ := by ext e; simp [supp,bot]
theorem rec_get {D w} (h : records D w) (i : Nat) (x : X) (off : (w.getD i bot) x=false) :
    D x (supp (w.getD i bot)) := by
  by_cases hi : i<w.length
  · rw [List.getD_eq_getElem _ _ hi] at off ⊢
    exact h.2 _ (List.getElem_mem hi) x off
  · rw [List.getD_eq_default _ _ (by omega),supp0]
    exact h.1 x
theorem rec_raw : records orig raws := by
  refine ⟨fun _ => Or.inl rfl,?_⟩
  intro f hf x no
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
  exact Or.inr ⟨i,no,fun e he => (Finset.mem_filter.mp he).2⟩
theorem rec_gateAnd {w D} (di : ∀ x,down (D x)) (h : records D w)
    {g : Gate} (ha : g.op=.and) : records D (step w g) := by
  refine ⟨h.1,?_⟩
  intro f hf x off
  rcases List.mem_append.mp hf with hf|hf
  · exact h.2 _ hf _ off
  obtain rfl := List.mem_singleton.mp hf
  have fails : ∃ i∈g.inputs, (w.getD i bot) x=false := by
    simpa [gv,ha,GateOp.eval,List.all_eq_false] using off
  obtain ⟨i,hi,ix⟩ := fails
  apply di x _ (rec_get h i x ix)
  intro e he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  have on := (Finset.mem_filter.mp he).2
  have yes : ∀ k∈g.inputs, (w.getD k bot) (flag e)=true := by
    simpa [gv,ha,GateOp.eval,List.all_eq_true] using on
  exact yes i hi
theorem rec_gates (gs : List Gate)
    (leg : ∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    ∀ D w,(∀x,down (D x)) → records D w →
      ∃rs : List Recipe,rs.length=gs.countP paid ∧ records (fun x => replay rs (D x)) (gs.foldl step w) := by
  induction gs with
  | nil => intro D w _ h; exact ⟨[],rfl,h⟩
  | cons g gs ih =>
    intro D w di h
    have tail := ih (fun q hq => leg q (List.mem_cons_of_mem _ hq))
    obtain ⟨op,sz⟩ := leg g List.mem_cons_self
    rcases op with ha|ho
    · obtain ⟨rs,len,hb⟩ := tail D (step w g) di (rec_gateAnd di h ha)
      exact ⟨rs,by simpa [List.countP_cons,paid,ha] using len,hb⟩
    · obtain ⟨u,v,hu,hv,eq⟩ := arms w ho sz
      let r : Recipe := (supp u,supp v)
      have read (z : F) (hz : z=bot ∨ ∃i,z=w.getD i bot) (x : X) (off : z x=false) : D x (supp z) := by
        rcases hz with rfl|⟨i,rfl⟩
        · rw [supp0]; exact h.1 x
        · exact rec_get h _ x off
      have nh : records (fun x => advance r (D x)) (step w g) := by
        refine ⟨fun x => Or.inl (h.1 x),?_⟩
        intro f mem x off
        rcases List.mem_append.mp mem with old|new
        · exact Or.inl (h.2 _ old x off)
        obtain rfl := List.mem_singleton.mp new
        rw [eq] at off ⊢
        have ⟨fu,fv⟩ := Bool.or_eq_false_iff.mp off
        apply Or.inr
        refine ⟨?_,read u hu x fu,read v hv x fv⟩
        intro e he
        have yes := (Finset.mem_filter.mp he).2
        change (u (flag e) || v (flag e))=true at yes
        rw [Bool.or_eq_true] at yes
        exact Finset.mem_union.mpr (yes.imp
          (fun q => Finset.mem_filter.mpr ⟨Finset.mem_univ _,q⟩)
          (fun q => Finset.mem_filter.mpr ⟨Finset.mem_univ _,q⟩))
      obtain ⟨rs,len,hb⟩ := tail _ _ (fun x => down_step (di x) r) nh
      exact ⟨r::rs,by simp [List.countP_cons,paid,ho,len],hb⟩
def Wins (rs : List Recipe) := ∀x : X, ¬Hit x → replay rs (orig x) Finset.univ
theorem of_physical (C : Circuit) (hm : Monotone2 C) (spec : Top C) :
    ∃rs : List Recipe, rs.length=C.gates.countP paid ∧ Wins rs := by
  obtain ⟨rs,len,hrec⟩ := rec_gates C.gates hm orig raws down_orig rec_raw
  let w := C.gates.foldl step raws
  let f := w.getD C.output bot
  have old (x : X) : f x=C.eval (List.ofFn x) := by
    change (C.gates.foldl step raws).getD C.output bot x = _
    rw [←get_project,simulation,project_raw]
    rfl
  have all : supp f=Finset.univ := by
    ext e
    apply iff_of_true _ (Finset.mem_univ _)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(old _) ▸ (spec _).mpr (hitFlag e)⟩
  refine ⟨rs,len,fun x hneg => ?_⟩
  have off : f x=false := Bool.eq_false_iff.mpr fun on => hneg ((spec x).mp ((old x) ▸ on))
  rw [←all]
  exact rec_get hrec C.output x off
namespace Restrict
def clip (M : Mask) (r : Recipe) : Recipe := (r.1∩M,r.2∩M)
def active (M : Mask) (r : Recipe) := (r.1∩M).Nonempty ∧ (r.2∩M).Nonempty
instance (M : Mask) (r : Recipe) : Decidable (active M r) := by unfold active; infer_instance
def project (M : Mask) : List Recipe → List Recipe
  | [] => []
  | r::rs => if active M r then clip M r::project M rs else project M rs
theorem projectedDown (rs : List Recipe) {D : Ideal} (h : down D) : down (replay rs D) := by
  induction rs generalizing D with
  | nil => exact h
  | cons r rs ih => exact ih (down_step h r)
theorem clip_step {M : Mask} {T : Mask} {r : Recipe} (s : T⊆r.1∪r.2) :
    T∩M⊆(clip M r).1∪(clip M r).2 := by
  intro e he
  obtain ⟨he,hm⟩ := Finset.mem_inter.mp he
  rcases Finset.mem_union.mp (s he) with h|h
  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h,hm⟩)
  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h,hm⟩)
theorem transport (M : Mask) (rs : List Recipe) {D P : Ideal} (dp : down P)
    (h : ∀T,D T → P (T∩M)) : ∀T,replay rs D T → replay (project M rs) P (T∩M) := by
  induction rs generalizing D P with
  | nil => exact h
  | cons r rs ih =>
    by_cases act : active M r
    · rw [project,if_pos act]
      apply ih (down_step dp (clip M r))
      intro T ht
      rcases ht with old|⟨sub,a,b⟩
      · exact Or.inl (h T old)
      · exact Or.inr ⟨clip_step sub,h _ a,h _ b⟩
    · rw [project,if_neg act]
      apply ih dp
      intro T ht
      rcases ht with old|⟨sub,a,b⟩
      · exact h T old
      · have cov := clip_step (M:=M) sub
        change T∩M ⊆ (r.1∩M) ∪ (r.2∩M) at cov
        by_cases left : (r.1∩M).Nonempty
        · have emp : r.2∩M=∅ := Finset.not_nonempty_iff_eq_empty.mp (fun right => act ⟨left,right⟩)
          rw [emp,Finset.union_empty] at cov
          exact dp cov (h _ a)
        · rw [Finset.not_nonempty_iff_eq_empty.mp left,Finset.empty_union] at cov
          exact dp cov (h _ b)
theorem won (M : Mask) {rs : List Recipe} (w : Wins rs) (x : X) (neg : ¬Hit x) :
    replay (project M rs) (orig x) M := by
  have h := transport M rs (down_orig x) (D:=orig x)
    (fun T old => down_orig x Finset.inter_subset_left old) Finset.univ (w x neg)
  simpa using h
end Restrict
end Saturated8321
