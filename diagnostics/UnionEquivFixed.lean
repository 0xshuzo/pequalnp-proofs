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
end Saturated8321

namespace PlaneOrdered
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

end PlaneOrdered


namespace Saturated8321.Build
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wires_eq_run (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

lemma getD_append_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_append_lt _ _ _ (by rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

def rd (gs : List Gate) (i : Nat) (x : X) := (run gs (List.ofFn x)).getD i false
def valid (g : Gate) := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2
def ext (G H : List Gate) (k : Nat) := ∃L,H=G++L ∧ (∀g∈L,valid g) ∧ L.countP paid=k
theorem initialExt (G : List Gate) : ext G G 0 := ⟨[],by simp,by simp,rfl⟩
theorem oneExt (G : List Gate) (g : Gate) (ok : valid g) : ext G (G++[g]) (if paid g then 1 else 0) :=
  ⟨[g],rfl,by simpa using ok,by cases eq : paid g <;> simp [eq]⟩
theorem composeExt {G H J : List Gate} {i j : Nat} (a : ext G H i) (b : ext H J j) : ext G J (i+j) := by
  obtain ⟨L,rfl,ok,q⟩ := a
  obtain ⟨M,rfl,ok',r⟩ := b
  exact ⟨L++M,by simp [List.append_assoc],fun g hg => (List.mem_append.mp hg).elim (ok g) (ok' g),
    by simp [List.countP_append,q,r]⟩
theorem longer {G H : List Gate} {k} (ex : ext G H k) : G.length≤H.length := by
  obtain ⟨L,rfl,-,-⟩ := ex
  simp
theorem keep {G H : List Gate} {k} (ex : ext G H k) {i} (hi : i<42+G.length) (x : X) :
    rd H i x=rd G i x := by
  obtain ⟨L,rfl,-,-⟩ := ex
  exact run_prefix G L _ i (by simpa using hi)
theorem last (G : List Gate) (g : Gate) (x : X) :
    rd (G++[g]) (42+G.length) x=g.op.eval (g.inputs.map fun i => rd G i x) := by
  unfold rd
  rw [run_snoc]
  have L : (run G (List.ofFn x)).length=42+G.length := by simp [run_length]
  rw [←L,getD_append_eq]

theorem conjunction (G : List Gate) (pins : List Nat) (bounds : ∀i∈pins,i<42+G.length) :
    ∃H o,ext G H 0 ∧ o<42+H.length ∧
      ∀x,rd H o x=true ↔ ∀i∈pins,rd G i x=true := by
  induction pins with
  | nil =>
    let g : Gate := ⟨.and,[]⟩
    refine ⟨G++[g],42+G.length,oneExt G g (by simp [valid,g]),by simp,?_⟩
    intro x; rw [last]; simp [g,GateOp.eval]
  | cons a pins ih =>
    obtain ⟨H,o,ex,ho,sem⟩ := ih (fun i hi => bounds i (List.mem_cons_of_mem _ hi))
    let g : Gate := ⟨.and,[a,o]⟩
    have ee : ext H (H++[g]) 0 := oneExt H g (by simp [valid,g])
    refine ⟨H++[g],42+H.length,composeExt ex ee,by simp,?_⟩
    intro x
    rw [last]
    simp only [g,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,
      Bool.and_true,Bool.and_eq_true,List.forall_mem_cons]
    rw [keep ex (bounds a List.mem_cons_self) x,sem x]

def presents (G : List Gate) (D : X → Ideal) := ∀ x T,D x T →
  ∃i, i<42+G.length ∧ covers T (rd G i) ∧ rd G i x=false

theorem carries {G H : List Gate} {D : X → Ideal} {k : Nat} (ex : ext G H k)
    (rep : presents G D) : presents H D := by
  intro x T yes
  obtain ⟨i,hi,cv,off⟩ := rep x T yes
  refine ⟨i,by have := longer ex; omega,fun e he => ?_,?_⟩
  · rw [keep ex hi]; exact cv e he
  · rw [keep ex hi]; exact off

theorem realizeMask (G : List Gate) (D : X → Ideal) (rep : presents G D) (T : Mask) :
    ∃H o,ext G H 0 ∧ o<42+H.length ∧ covers T (rd H o) ∧ ∀x,D x T → rd H o x=false := by
  classical
  let pins := (List.range (42+G.length)).filter fun i => decide (covers T (rd G i))
  have char (i : Nat) : i∈pins ↔ i<42+G.length ∧ covers T (rd G i) := by simp [pins]
  obtain ⟨H,o,ex,ho,sem⟩ := conjunction G pins (fun i hi => ((char i).mp hi).1)
  refine ⟨H,o,ex,ho,fun e he => (sem _).mpr (fun i hi => ((char i).mp hi).2 e he),?_⟩
  intro x yes
  obtain ⟨i,hi,cold,off⟩ := rep x T yes
  apply Bool.eq_false_iff.mpr
  intro lit
  exact Bool.noConfusion (((sem x).mp lit i ((char i).mpr ⟨hi,cold⟩)).symm.trans off)

theorem realizeRule (G : List Gate) (D : X → Ideal) (rep : presents G D) (r : Recipe) :
    ∃H,ext G H 1 ∧ presents H (fun x => advance r (D x)) := by
  obtain ⟨H,a,eh,ha,ca,oa⟩ := realizeMask G D rep r.1
  obtain ⟨J,b,ej,hb,cb,ob⟩ := realizeMask H D (carries eh rep) r.2
  let g : Gate := ⟨.or,[a,b]⟩
  let K := J++[g]
  have ejk : ext J K 1 := oneExt J g (by simp [valid,g])
  have e : ext G K 1 := composeExt (composeExt eh ej) ejk
  refine ⟨K,e,?_⟩
  intro x T ok
  rcases ok with prev|⟨sub,l,r'⟩
  · exact carries e rep x T prev
  have atGate (z : X) : rd K (42+J.length) z=(rd H a z || rd J b z) := by
    rw [show K=J++[g] from rfl,last]
    simp [g,GateOp.eval,keep ej ha]
  refine ⟨42+J.length,by simp [K],?_,?_⟩
  · intro f hf
    rw [atGate,Bool.or_eq_true]
    exact (Finset.mem_union.mp (sub hf)).imp (ca f) (cb f)
  · rw [atGate,oa x l,ob x r']; rfl
theorem materialize (rs : List Recipe) : ∀G D,presents G D →
    ∃H,ext G H rs.length ∧ presents H (fun x => replay rs (D x)) := by
  induction rs with
  | nil => intro G D rep; exact ⟨G,initialExt _,rep⟩
  | cons r rs ih =>
    intro G D rep
    obtain ⟨H,ex,next⟩ := realizeRule G D rep r
    obtain ⟨J,ex',done⟩ := ih H _ next
    exact ⟨J,by simpa [Nat.add_comm] using composeExt ex ex',done⟩
def G0 : List Gate := [⟨.and,[42]⟩]
theorem initial : presents G0 orig := by
  intro x T d
  rcases d with rfl|⟨i,off,sub⟩
  · refine ⟨42,by decide,by simp [covers],?_⟩
    have z := last ([] : List Gate) (⟨.and,[42]⟩ : Gate) x
    change rd G0 42 x=false
    change rd G0 42 x=_ at z
    rw [z]
    have e : rd [] 42 x=false := List.getD_eq_default _ _ (by simp [run])
    simp [GateOp.eval,e]
  · have eq (z : X) : rd G0 i.val z=z i := by
      unfold rd
      rw [run_input _ _ _ (by simp)]
      fin_cases i <;> rfl
    exact ⟨i.val,by have := i.isLt; omega,fun e he => by rw [eq]; exact sub e he,by rw [eq]; exact off⟩
theorem to_physical (rs : List Recipe) (win : Wins rs) :
    ∃ C : Circuit,Monotone2 C ∧ Top C ∧ C.gates.countP paid=rs.length := by
  obtain ⟨H,ex,rep⟩ := materialize rs G0 orig initial
  obtain ⟨J,o,e,_,cv,off⟩ := realizeMask H _ rep Finset.univ
  obtain ⟨L,eq,ok,cost⟩ := composeExt ex e
  let C : Circuit := ⟨J,o⟩
  have hm : Monotone2 C := by
    intro g hg
    change g∈J at hg
    rw [eq] at hg
    rcases List.mem_append.mp hg with old|new
    · have he : g=⟨.and,[42]⟩ := List.mem_singleton.mp old
      subst g
      simp
    · exact ok g new
  refine ⟨C,hm,?_,?_⟩
  · intro x
    constructor
    · intro yes
      by_contra bad
      exact Bool.noConfusion (yes.symm.trans (off _ (win _ bad)))
    · rintro ⟨u,v,ed,hu,hv⟩
      have yes := cv (⟨(u,v),ed⟩ : E) (Finset.mem_univ _)
      exact PlaneOrdered.cmono C hm 42 _ x (subset_flag ed hu hv) yes
  · change J.countP paid=_
    rw [eq,List.countP_append]
    simpa [G0,paid] using cost

theorem exact_optimization (s : Nat) :
    (∃ C : Circuit,Monotone2 C ∧ Top C ∧ C.gates.countP paid≤s) ↔
    ∃ rs : List Recipe, rs.length≤s ∧ Wins rs := by
  constructor
  · rintro ⟨C,hm,h,b⟩
    obtain ⟨p,sz,good⟩ := of_physical C hm h
    exact ⟨p,sz.trans_le b,good⟩
  · rintro ⟨p,b,h⟩
    obtain ⟨C,hm,good,sz⟩ := to_physical p h
    exact ⟨C,hm,good,sz.trans_le b⟩
end Saturated8321.Build
