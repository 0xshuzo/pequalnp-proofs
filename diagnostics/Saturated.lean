import PEqualNP.Defs

namespace Saturated8321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 1000000
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
def stronger (A : List F) (f : F) := ∀x, f x=false → ∃z∈A,z x=false ∧ covers (supp f) z
noncomputable def meet (A : List F) (T : Mask) (x : X) : Bool := by
  classical exact decide (∀z∈A,covers T z → z x=true)
theorem meet_yes (A : List F) (T : Mask) (x : X) :
    meet A T x=true ↔ ∀z∈A,covers T z → z x=true := by classical simp [meet]
theorem supmem (f : F) (e : E) : e∈supp f ↔ f (flag e)=true := by simp [supp]

theorem at_flag {A : List F} {T : Mask} {e : E} (h : e∈T) :
    meet A T (flag e)=true := (meet_yes ..).mpr (fun _ _ cover => cover e h)
theorem below {A : List F} {f : F} (h : stronger A f) (x : X) :
    meet A (supp f) x=true → f x=true := by
  intro hm
  cases hf : f x with
  | true => rfl
  | false =>
    obtain ⟨z,hz,off,ok⟩ := h x hf
    exact Bool.noConfusion (((meet_yes ..).mp hm z hz ok).symm.trans off)
theorem rawStrong {A : List F} {f : F} (mem : f∈A) : stronger A f :=
  fun _ off => ⟨f,mem,off,fun e hy => (supmem f e).mp hy⟩
theorem grow {A : List F} {f z : F} (h : stronger A f) : stronger (z::A) f := by
  intro x off
  obtain ⟨w,hw,old,cover⟩ := h x off
  exact ⟨w,List.mem_cons_of_mem _ hw,old,cover⟩
theorem fullStrong (A : List F) : stronger A (fun _ => true) := by intro x h; contradiction
theorem andStrong {A : List F} {f g : F} (hf : stronger A f) (hg : stronger A g) :
    stronger A (fun x => f x && g x) := by
  intro x h
  rcases Bool.and_eq_false_iff.mp h with fail|fail
  · obtain ⟨w,hw,off,sub⟩ := hf x fail
    refine ⟨w,hw,off,fun e he => sub e ((supmem _ _).mpr ?_)⟩
    exact (Bool.and_eq_true.mp ((supmem _ _).mp he)).1
  · obtain ⟨w,hw,off,sub⟩ := hg x fail
    refine ⟨w,hw,off,fun e he => sub e ((supmem _ _).mpr ?_)⟩
    exact (Bool.and_eq_true.mp ((supmem _ _).mp he)).2
noncomputable def merge (A : List F) (r : Recipe) : F := fun x => meet A r.1 x || meet A r.2 x
theorem orStrong {A : List F} {f g : F} (hf : stronger A f) (hg : stronger A g) :
    stronger (merge A (supp f,supp g)::A) (fun x => f x || g x) := by
  intro x h
  refine ⟨_,List.mem_cons_self,?_,?_⟩
  · apply Bool.eq_false_iff.mpr
    intro yes
    obtain ha|hb := Bool.or_eq_true.mp yes
    · exact Bool.noConfusion ((Bool.or_eq_true.mpr (.inl (below hf x ha))).symm.trans h)
    · exact Bool.noConfusion ((Bool.or_eq_true.mpr (.inr (below hg x hb))).symm.trans h)
  · intro e he
    obtain ha|hb := Bool.or_eq_true.mp ((supmem _ _).mp he)
    · exact Bool.or_eq_true.mpr (.inl (at_flag ((supmem f e).mpr ha)))
    · exact Bool.or_eq_true.mpr (.inr (at_flag ((supmem g e).mpr hb)))
def bot : F := fun _ => false
def input (i : Pin) : F := fun x => x i
def raws := List.ofFn input
def start := bot::raws
noncomputable def run : List Recipe → List F → List F
  | [],A => A
  | r::rs,A => run rs (merge A r::A)
def gv (w : List F) (g : Gate) : F := fun x => g.op.eval (g.inputs.map fun i => (w.getD i bot) x)
def step (w : List F) (g : Gate) := w++[gv w g]
def bank (A w : List F) := stronger A bot ∧ ∀f∈w,stronger A f
theorem getbank {A w : List F} (h : bank A w) (i : Nat) : stronger A (w.getD i bot) := by
  by_cases lt : i<w.length
  · rw [List.getD_eq_getElem _ _ lt]
    exact h.2 _ (List.getElem_mem lt)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact h.1
theorem start_ok : bank start raws := ⟨rawStrong List.mem_cons_self,fun _ mem => rawStrong (List.mem_cons_of_mem _ mem)⟩
theorem andList (A w : List F) (ok : bank A w) (L : List Nat) :
    stronger A (fun x => (L.map (fun i => (w.getD i bot) x)).all id) := by
  induction L with
  | nil => exact fullStrong A
  | cons i t ih => exact andStrong (getbank ok i) ih
theorem gAnd {g : Gate} {w A : List F} (ok : bank A w) (ha : g.op=.and) :
    bank A (step w g) := by
  refine ⟨ok.1,?_⟩
  intro f mem
  rcases List.mem_append.mp mem with old|new
  · exact ok.2 _ old
  obtain rfl := List.mem_singleton.mp new
  simpa only [gv,ha,GateOp.eval] using andList A w ok g.inputs
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
theorem process (gs : List Gate) (leg : ∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    ∀ A w,bank A w → ∃ rs : List Recipe,rs.length=gs.countP paid ∧ bank (run rs A) (gs.foldl step w) := by
  induction gs with
  | nil => intro A w ok; exact ⟨[],rfl,ok⟩
  | cons g gs ih =>
    intro A w ok
    have tail := ih (fun q hq => leg q (List.mem_cons_of_mem _ hq))
    obtain ⟨op,sz⟩ := leg g List.mem_cons_self
    rcases op with ha|ho
    · obtain ⟨rs,len,banked⟩ := tail A (step w g) (gAnd ok ha)
      exact ⟨rs,by simpa [List.countP_cons,paid,ha] using len,banked⟩
    · obtain ⟨f,g',ef,eg,eq⟩ := arms w ho sz
      have available (z : F) (hz : z=bot ∨ ∃i,z=w.getD i bot) : stronger A z := by
        rcases hz with rfl|⟨i,rfl⟩
        · exact ok.1
        · exact getbank ok _
      let r : Recipe := (supp f,supp g')
      have more : bank (merge A r::A) (step w g) := by
        refine ⟨grow ok.1,?_⟩
        intro v hv
        rcases List.mem_append.mp hv with old|new
        · exact grow (ok.2 _ old)
        obtain rfl := List.mem_singleton.mp new
        rw [eq]
        exact orStrong (available _ ef) (available _ eg)
      obtain ⟨rs,len,last⟩ := tail _ _ more
      exact ⟨r::rs,by simp [List.countP_cons,paid,ho,len],last⟩
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
    simp [step,project,gv,get_project]
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
theorem monotone_meet {A : List F} {T : Mask} (h : ∀f∈A,Monotone f) : Monotone (meet A T) := by
  intro x y le
  apply Bool.le_iff_imp.mpr
  intro hx
  exact (meet_yes ..).mpr fun z mem hz => (Bool.le_iff_imp.mp (h z mem le)) ((meet_yes ..).mp hx z mem hz)
theorem monotone_run (rs : List Recipe) : ∀ A, (∀f∈A,Monotone f) → ∀f∈run rs A,Monotone f := by
  induction rs with
  | nil => intro A h; exact h
  | cons r rs ih =>
    intro A h
    apply ih
    intro f hf
    rcases List.mem_cons.mp hf with rfl|mem
    · intro x y le
      apply Bool.le_iff_imp.mpr
      intro yes
      obtain ha|hb := Bool.or_eq_true.mp yes
      · exact Bool.or_eq_true.mpr (.inl (Bool.le_iff_imp.mp (monotone_meet (T:=r.1) h le) ha))
      · exact Bool.or_eq_true.mpr (.inr (Bool.le_iff_imp.mp (monotone_meet (T:=r.2) h le) hb))
    · exact h _ mem
theorem mono_start : ∀ f∈start,Monotone f := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl|mem
  · intro _ _ _; rfl
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
  exact fun _ _ h => h i
theorem saturated_normal_form (C : Circuit) (hm : Monotone2 C) (exactC : Top C) :
    ∃ rs : List Recipe, rs.length=C.gates.countP paid ∧
      ∀x : X, meet (run rs start) Finset.univ x=true ↔ Hit x := by
  obtain ⟨rs,len,banked⟩ := process C.gates hm start raws start_ok
  let f := (C.gates.foldl step raws).getD C.output bot
  have old (x : X) : f x=C.eval (List.ofFn x) := by
    rw [←get_project,simulation,project_raw]
    rfl
  have all : supp f=Finset.univ := by
    ext e
    simp only [supmem,Finset.mem_univ,iff_true]
    rw [old]
    exact (exactC _).mpr (hitFlag e)
  have strong : stronger (run rs start) f := getbank banked C.output
  refine ⟨rs,len,fun x => ⟨?_,?_⟩⟩
  · intro on
    rw [←all] at on
    exact (exactC x).mp ((old x) ▸ below strong x on)
  · rintro ⟨u,v,edge,hu,hv⟩
    have up := monotone_meet (T:=Finset.univ) (monotone_run rs start mono_start) (subset_flag edge hu hv)
    exact Bool.le_iff_imp.mp up (at_flag (Finset.mem_univ _))
end Saturated8321
