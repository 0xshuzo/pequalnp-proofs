import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9804.UnionTree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
abbrev X := Fin 40 → Bool
abbrev F := X → Bool
abbrev Pin := Fin 40
def listed : List (Nat × Nat) := [(0, 20), (0, 25), (0, 27), (0, 37), (1, 21), (1, 26), (1, 28), (1, 38), (2, 21), (2, 22), (2, 27), (2, 29), (2, 39), (3, 20), (3, 22), (3, 23), (3, 28), (3, 30), (4, 23), (4, 24), (4, 29), (4, 31), (5, 21), (5, 24), (5, 25), (5, 30), (5, 32), (6, 22), (6, 25), (6, 26), (6, 31), (6, 33), (7, 23), (7, 26), (7, 27), (7, 32), (7, 34), (8, 24), (8, 27), (8, 28), (8, 33), (8, 35), (9, 25), (9, 28), (9, 29), (9, 34), (9, 36), (10, 26), (10, 29), (10, 30), (10, 35), (10, 37), (11, 27), (11, 30), (11, 31), (11, 36), (11, 38), (12, 28), (12, 31), (12, 32), (12, 37), (12, 39), (13, 20), (13, 29), (13, 32), (13, 33), (13, 38), (14, 30), (14, 33), (14, 34), (14, 39), (15, 20), (15, 21), (15, 31), (15, 34), (15, 35), (16, 22), (16, 32), (16, 35), (16, 36), (17, 21), (17, 23), (17, 33), (17, 36), (17, 37), (18, 22), (18, 24), (18, 34), (18, 37), (18, 38), (19, 23), (19, 25), (19, 35), (19, 38), (19, 39)]
def Ed (u v : Pin) := u.val<20 ∧ (20 : Nat)≤v.val ∧ (u.val,v.val)∈listed
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

namespace Tree
def coords (i : Fin 39) : Pin × Pin := (#[(14, 30), (1, 28), (4, 23), (16, 22), (19, 39), (9, 36), (6, 26), (5, 24), (15, 35), (15, 34), (15, 31), (15, 21), (13, 38), (13, 33), (13, 32), (13, 29), (3, 30), (3, 28), (3, 23), (3, 22), (18, 37), (17, 37), (12, 37), (10, 37), (11, 27), (8, 27), (7, 27), (2, 27), (19, 25), (9, 25), (6, 25), (5, 25), (15, 20), (13, 20), (3, 20), (0, 37), (0, 27), (0, 25), (0, 20)] : Array (Pin × Pin))[i.val]!
def anchor (i : Fin 38) : Pin := (#[30, 28, 23, 22, 19, 9, 6, 5, 15, 15, 15, 15, 13, 13, 13, 13, 3, 3, 3, 3, 37, 37, 37, 37, 27, 27, 27, 27, 25, 25, 25, 25, 20, 20, 20, 0, 0, 0] : Array Pin)[i.val]!
theorem geo : ∀i, Ed (coords i).1 (coords i).2 := by decide +kernel
def edge (i : Fin 39) : E := ⟨coords i,geo i⟩
def row (i : Fin 38) (v : Pin) := decide (v=anchor i)
theorem rowNeg (i : Fin 38) : ¬Hit (row i) := by
  rintro ⟨a,b,he,ha,hb⟩
  have ha' : a=anchor i := of_decide_eq_true ha
  have hb' : b=anchor i := of_decide_eq_true hb
  have hp := he.1
  have hl := he.2.1
  rw [ha'] at hp
  rw [hb'] at hl
  omega
theorem leafdata : ∀ (i : Fin 38) (j : Fin 39), i.val<j.val →
    (coords i.castSucc).1=anchor i ∧
      (coords j).1≠(coords i.castSucc).2 ∧ (coords j).2≠(coords i.castSucc).2 ∨
    (coords i.castSucc).2=anchor i ∧
      (coords j).1≠(coords i.castSucc).1 ∧ (coords j).2≠(coords i.castSucc).1 := by decide +kernel
def mixed (i : Fin 38) (T : Mask) :=
  edge i.castSucc∈T ∧ ∃j : Fin 39,i.val<j.val ∧ edge j∈T
def clear (i : Fin 38) (D : Ideal) := ∀T,D T → ¬mixed i T
theorem initialClear (i : Fin 38) : clear i (orig (row i)) := by
  rintro T (rfl|⟨v,off,sub⟩) ⟨a,j,lt,b⟩
  · simpa using a
  · have na : v≠anchor i := of_decide_eq_false off
    have av : v=(coords i.castSucc).1 ∨ v=(coords i.castSucc).2 := of_decide_eq_true (sub _ a)
    have bv : v=(coords j).1 ∨ v=(coords j).2 := of_decide_eq_true (sub _ b)
    rcases leafdata i j lt with h|h <;> rcases av with h'|h' <;> rcases bv with h''|h'' <;> grind
def absent (i : Fin 38) (S : Mask) := ∀j : Fin 39,i.val<j.val → edge j∉S
def later (i : Fin 38) (S : Mask) := ∃j : Fin 39,i.val<j.val ∧ edge j∈S
def separates (i : Fin 38) (r : Recipe) :=
  (edge i.castSucc∈r.1 ∧ absent i r.1 ∧ later i r.2) ∨
  (edge i.castSucc∈r.2 ∧ absent i r.2 ∧ later i r.1)
theorem stepClear {i D r} (cl : clear i D) (bad : ¬separates i r) : clear i (advance r D) := by
  intro T old m
  rcases old with prev|⟨sub,a,b⟩
  · exact cl T prev m
  obtain ⟨first,j,lt,last⟩ := m
  rcases Finset.mem_union.mp (sub first) with left|right
  · have no : absent i r.1 := fun k hk h => cl r.1 a ⟨left,k,hk,h⟩
    exact bad (Or.inl ⟨left,no,j,lt,(Finset.mem_union.mp (sub last)).resolve_left (no j lt)⟩)
  · have no : absent i r.2 := fun k hk h => cl r.2 b ⟨right,k,hk,h⟩
    exact bad (Or.inr ⟨right,no,j,lt,(Finset.mem_union.mp (sub last)).resolve_right (no j lt)⟩)
theorem noCharge {i : Fin 38} (rs : List Recipe) {D : Ideal} (cl : clear i D)
    (none : ∀r∈rs,¬separates i r) : clear i (replay rs D) := by
  induction rs generalizing D with
  | nil => exact cl
  | cons r tail ih =>
    exact ih (stepClear cl (none r (by simp))) (fun s hs => none s (by simp [hs]))
theorem charge {rs : List Recipe} (h : Wins rs) (i : Fin 38) : ∃r∈rs,separates i r := by
  classical
  by_contra! n
  exact (noCharge rs (initialClear i) n) Finset.univ (h _ (rowNeg i))
    ⟨Finset.mem_univ _,Fin.last 38,by exact i.isLt,Finset.mem_univ _⟩
theorem clash {i j : Fin 38} {r : Recipe} (lt : i.val<j.val) (a : separates i r) (b : separates j r) : False := by
  rcases a with ⟨_,no,_⟩|⟨_,no,_⟩
  · rcases b with ⟨l,_,_⟩|⟨_,_,k,hk,hm⟩
    · exact no j.castSucc lt l
    · exact no k (lt_trans lt hk) hm
  · rcases b with ⟨_,_,k,hk,hm⟩|⟨l,_,_⟩
    · exact no k (lt_trans lt hk) hm
    · exact no j.castSucc lt l
theorem thirtyEight {rs : List Recipe} (h : Wins rs) : 38≤rs.length := by
  classical
  choose f mem cut using charge h
  have inj : Function.Injective f := by
    intro i j eq
    rcases lt_trichotomy i j with hij|hij|hij
    · exact (clash hij (eq ▸ cut i) (cut j)).elim
    · exact hij
    · exact (clash hij (eq.symm ▸ cut j) (cut i)).elim
  have sub : Finset.univ.image f ⊆ rs.toFinset := by
    intro r hr
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
    exact List.mem_toFinset.mpr (mem i)
  have bound := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inj] at bound
  simpa using le_trans bound rs.toFinset_card_le
theorem physical_thirtyEight (C : Circuit) (hm : Monotone2 C) (sp : Top C) : 38≤C.gates.countP paid := by
  obtain ⟨rs,l,h⟩ := of_physical C hm sp
  exact l ▸ thirtyEight h
end Tree
end PEqualNP.Outside.L_meta_9804.UnionTree
