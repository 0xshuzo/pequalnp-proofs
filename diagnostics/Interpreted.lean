import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8123.Meet
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-- The ordinary value, the degree-zero part and the degree-one part on one trial. -/
structure V where
  bit : Bool
  z : Bool
  o : Bool
deriving DecidableEq, Fintype
instance : Inhabited V := ⟨⟨false,false,false⟩⟩
def mult (a b : V) : V := ⟨a.bit && b.bit,a.z && b.z,(a.z && b.o)||(a.o && b.z)⟩
def plus (a b : V) : V := ⟨a.bit||b.bit,a.z||b.z,a.o||b.o⟩
def unit : V := ⟨true,true,false⟩
def R (a b : V) : Prop := a.bit=b.bit ∧ a.z=b.z ∧ (a.o=true → b.o=true)
instance (a b : V) : Decidable (R a b) := by unfold R; infer_instance
theorem rr : ∀a,R a a := by decide +kernel
theorem rt : ∀a b c,R a b → R b c → R a c := by decide +kernel
theorem mm : ∀a b c d,R a b → R c d → R (mult a c) (mult b d) := by decide +kernel
theorem pp : ∀a b c d,R a b → R c d → R (plus a c) (plus b d) := by decide +kernel
theorem assoc : ∀a b c,mult (mult a b) c=mult a (mult b c) := by decide +kernel
theorem commute : ∀a b,mult a b=mult b a := by decide +kernel
theorem identity : ∀a,mult unit a=a := by decide +kernel
theorem dup : ∀a b,R (mult a (mult a b)) (mult a b) := by decide +kernel
theorem swap : ∀a b c,mult a (mult b c)=mult b (mult a c) := by decide +kernel

def value (f : Nat → V) : List Nat → V
  | [] => unit
  | a::t => mult (f a) (value f t)

def merge : List Nat → List Nat → List Nat
  | [], b => b
  | i::a,b => let t:=merge a b; if i∈t then t else i::t

theorem factor (f : Nat→V) (i : Nat) (w : List Nat) (mem:i∈w) : ∃v,value f w=mult (f i) v := by
  induction w with
  | nil => simp at mem
  | cons a t ih =>
    rcases List.mem_cons.mp mem with rfl|inside
    · exact ⟨_,rfl⟩
    · obtain ⟨v,hi⟩ := ih inside
      exact ⟨mult (f a) v,by simp only [value,hi,swap (f a) (f i)]⟩

theorem merge_sound (f : Nat→V) (a b : List Nat) :
    R (mult (value f a) (value f b)) (value f (merge a b)) := by
  induction a with
  | nil => simpa only [value,merge,identity] using rr (value f b)
  | cons i a ih =>
    simp only [value,merge,assoc]
    have h:=mm _ _ _ _ (rr (f i)) ih
    by_cases seen : i ∈ merge a b
    · rw [if_pos seen]
      apply rt _ _ _ h
      obtain ⟨v,hv⟩ := factor f i _ seen
      rw [hv]
      exact dup _ _
    · rw [if_neg seen]
      exact h

theorem merge_mem (i : Nat) (a b : List Nat) : i∈merge a b ↔ i∈a ∨ i∈b := by
  induction a with
  | nil => simp [merge]
  | cons j a ih =>
    simp only [merge]
    split_ifs with seen
    · by_cases eq : i=j
      · subst i; simp [seen]
      · simp [ih,eq]
    · simp [ih,or_assoc]

theorem merge_nodup (a b : List Nat) (h:b.Nodup) : (merge a b).Nodup := by
  induction a with
  | nil => exact h
  | cons i a ih => simp only [merge]; split_ifs with e <;> simp_all

abbrev Word := List Nat
abbrev Recipe := Word × Word
structure Plan where
  ops : List Recipe
  keys : List Word

def key (P : Plan) (i : Nat) : Word := P.keys.getD i []
def atoms (w : List V) (u : Word) : V := value (fun i=>w.getD i default) u
def make (r : Recipe) (w : List V) : V := plus (atoms w r.1) (atoms w r.2)
def run (ops : List Recipe) (raw : List V) := ops.foldl (fun w r=>w++[make r w]) raw
theorem rsnoc (ops : List Recipe) (r : Recipe) (raw : List V) :
    run (ops++[r]) raw = run ops raw ++ [make r (run ops raw)] := by simp [run,List.foldl_append]
theorem rlength (ops : List Recipe) (raw : List V) : (run ops raw).length=raw.length+ops.length := by
  induction ops using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton os r ih => rw [rsnoc]; simp [ih,Nat.add_assoc]

def expand (n : Nat) (P : Plan) (g : Gate) : Plan :=
  let a:=key P (g.inputs.getD 0 0)
  let b:=key P (g.inputs.getD 1 0)
  match g.op with
  | .or => ⟨P.ops++[(a,b)],P.keys++[[n+P.ops.length]]⟩
  | _ => ⟨P.ops,P.keys++[merge a b]⟩
def initial (n : Nat) : Plan := ⟨[],(List.range n).map (fun i=>[i])⟩
def compile (n : Nat) (gs : List Gate) : Plan := gs.foldl (expand n) (initial n)

def wordOK (k : Nat) (w : Word) := w.Nodup ∧ ∀v∈w,v<k
def good (n : Nat) (P : Plan) := ∀w∈P.keys,wordOK (n+P.ops.length) w
theorem selected {n P} (ok:good n P) (i : Nat) : wordOK (n+P.ops.length) (key P i) := by
  by_cases h:i<P.keys.length
  · rw [key,List.getD_eq_getElem _ _ h]
    exact ok _ (List.getElem_mem h)
  · rw [key,List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
    simp [wordOK]

theorem expand_good {n P} (ok:good n P) (g : Gate) : good n (expand n P g) := by
  have ia:=selected ok (g.inputs.getD 0 0)
  have ib:=selected ok (g.inputs.getD 1 0)
  intro w hw
  unfold expand at hw ⊢
  cases op:g.op <;> simp only [op,List.mem_append,List.mem_singleton] at hw ⊢ <;>
    rcases hw with h|rfl
  all_goals first
    | exact ok _ h
    | exact ⟨merge_nodup _ _ ib.1,fun _ hv => ((merge_mem _ _ _).mp hv).elim (ia.2 _) (ib.2 _)⟩
    | exact ⟨(ok _ h).1,fun v hv => by have k:=(ok _ h).2 v hv; simp; omega⟩
    | simp [wordOK]

theorem value_congr {f g : Nat→V} (w : Word) (h : ∀i∈w,f i=g i) : value f w=value g w := by
  induction w with
  | nil => rfl
  | cons i t ih => rw [value,value,h i List.mem_cons_self,ih (fun j hj=> h j (List.mem_cons_of_mem _ hj))]

theorem atom_snoc (w : List V) (v : V) (word : Word) (valid : ∀i∈word,i<w.length) :
    atoms (w++[v]) word=atoms w word := by
  apply value_congr
  intro i hi
  exact List.getD_append _ _ _ _ (valid i hi)

theorem singleton (f : Nat→V) (i : Nat) : value f [i]=f i := by
  simp [value,commute (f i) unit,identity]

def readStep (w : List V) (g : Gate) : V :=
  let a:=w.getD (g.inputs.getD 0 0) default
  let b:=w.getD (g.inputs.getD 1 0) default
  match g.op with
  | .or => plus a b
  | _ => mult a b

def oldrun (gs : List Gate) (raw : List V) := gs.foldl (fun w g=>w++[readStep w g]) raw
def tracked (P : Plan) (raw old : List V) := old.length=P.keys.length ∧
  ∀i<old.length,R (old.getD i default) (atoms (run P.ops raw) (key P i))

private theorem atSnoc {α} (s : List α) (v d : α) : (s++[v]).getD s.length d=v := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem expand_tracks (P : Plan) (raw old : List V) (g : Gate) (ok:good raw.length P)
    (back : ∀i∈g.inputs,i<old.length) (two : g.inputs.length=2) (track:tracked P raw old) :
    tracked (expand raw.length P g) raw (old++[readStep old g]) := by
  obtain ⟨size,oldval⟩ := track
  have holder (k : Nat) (hk:k<2) : g.inputs.getD k 0<old.length := by
    have h:k<g.inputs.length := by omega
    rw [List.getD_eq_getElem _ _ h]; exact back _ (List.getElem_mem h)
  have la:=oldval (g.inputs.getD 0 0) (holder 0 (by decide))
  have lb:=oldval (g.inputs.getD 1 0) (holder 1 (by decide))
  let supply:=run P.ops raw
  have price : supply.length=raw.length+P.ops.length := rlength .. 
  have previous (i : Nat) (hi:i<old.length) : key (expand raw.length P g) i=key P i := by
    have hk:i<P.keys.length := by omega
    cases e:g.op <;> simp only [expand,key,e] <;> exact List.getD_append _ _ _ _ hk
  have oldOr (i : Nat) (hi:i<old.length) (r : Recipe) :
      atoms (run (P.ops++[r]) raw) (key P i) = atoms supply (key P i) := by
    rw [rsnoc]
    exact atom_snoc supply _ _ (fun v hv=>price.symm ▸ (selected ok i).2 v hv)
  constructor
  · cases e:g.op <;> simp [expand,e,size]
  intro i hi
  by_cases h:i<old.length
  · rw [previous i h,List.getD_append _ _ _ _ h]
    have use:=oldval i h
    cases e:g.op <;> simp only [expand,e] <;> first | exact use | simpa only [oldOr i h] using use
  have eq:i=old.length := by simp at hi; omega
  subst i
  rw [atSnoc]
  have loc : old.length=P.keys.length := size
  cases e:g.op <;> simp only [expand,readStep,key,loc,e,atSnoc] <;> first
    | exact rt _ _ _ (mm _ _ _ _ la lb) (merge_sound ..)
    | rw [rsnoc]; change R _ (value _ [_]); rw [singleton]
      rw [show raw.length+P.ops.length=(run P.ops raw).length from price.symm,atSnoc]
      exact pp _ _ _ _ la lb

end PEqualNP.Outside.L_meta_8123.Meet
namespace PEqualNP.Outside.L_meta_8123.Meet
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
def legal : Nat → List Gate → Prop
  | _, [] => True
  | k, g::gs => g.inputs.length=2 ∧ (∀v∈g.inputs,v<k) ∧ legal (k+1) gs

theorem iff_legal (k : Nat) (gs : List Gate) :
    (∀ (j : Nat) (hj : j < gs.length), gs[j].inputs.length=2 ∧ ∀v∈gs[j].inputs,v<k+j) → legal k gs := by
  induction gs generalizing k with
  | nil => intro _; trivial
  | cons g gs ih =>
    intro h
    have head:=h 0 (by simp)
    have tail := ih (k+1) (fun j hj => by
      have use:=h (j+1) (by simp; omega)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using use)
    exact ⟨by simpa using head.1,by simpa using head.2,tail⟩

theorem allLegal {n : Nat} {C : Circuit} (ao : IsAO2 n C) : legal n C.gates := by
  apply iff_legal
  intro j hj
  refine ⟨ao.2.2 _ (List.getElem_mem hj),?_⟩
  intro v hv
  apply ao.2.1 j hj
  change v ∈ (C.gates.getD j _).inputs
  rw [List.getD_eq_getElem _ _ hj]
  exact hv

theorem initialGood (n : Nat) : good n (initial n) := by
  intro w hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
  simp [wordOK,initial,List.mem_range.mp hi]

theorem initialTracks (raw : List V) : tracked (initial raw.length) raw raw := by
  refine ⟨by simp [initial],?_⟩
  intro i hi
  have word : key (initial raw.length) i=[i] := by
    unfold key initial
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  rw [word]
  change R _ (value _ [i])
  rw [singleton]
  exact rr _

theorem iterate (n : Nat) (P : Plan) (raw old : List V) (hsize:raw.length=n) (gs : List Gate)
    (lg : legal old.length gs) (ok:good n P) (tr:tracked P raw old) :
    good n (gs.foldl (expand n) P) ∧ tracked (gs.foldl (expand n) P) raw (oldrun gs old) := by
  induction gs generalizing P old with
  | nil => exact ⟨ok,tr⟩
  | cons g gs ih =>
    have key := expand_tracks P raw old g (hsize ▸ ok) lg.2.1 lg.1 tr
    rw [hsize] at key
    apply ih _ _ (by simpa using lg.2.2) (expand_good ok g) key

theorem semantic_normal_form {n : Nat} (C : Circuit) (ao:IsAO2 n C) (raw:List V) (hs:raw.length=n) :
    good n (compile n C.gates) ∧ tracked (compile n C.gates) raw (oldrun C.gates raw) := by
  apply iterate n _ _ _ hs
  · simpa [hs] using allLegal ao
  · exact initialGood n
  · simpa [hs] using initialTracks raw

def orFlag (g : Gate) : Bool := match g.op with | .or => true | _ => false

theorem paid (n : Nat) (gs : List Gate) (P : Plan) :
    (gs.foldl (expand n) P).ops.length=P.ops.length+gs.countP orFlag := by
  induction gs generalizing P with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons,ih,List.countP_cons]
    cases e:g.op <;> simp [expand,orFlag,e,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

theorem exact_or_count (n : Nat) (gs : List Gate) : (compile n gs).ops.length=gs.countP orFlag := by
  simp [compile,paid,initial]

end PEqualNP.Outside.L_meta_8123.Meet
namespace PEqualNP.Outside.L_meta_3568.Slice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl


end PEqualNP.Outside.L_meta_3568.Slice
namespace PEqualNP.Outside.L_meta_8123.Meet
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK
open PEqualNP.Outside.L_meta_3568.Slice
set_option maxHeartbeats 0
def pair (a:V) := (a.z,a.o)

private theorem get_map {α β : Type} (f:α→β) (w:List α) (i:Nat) (d:α) :
    (w.map f).getD i (f d)=f (w.getD i d) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h:w[i]? <;> rfl

private theorem projections (s : List V) (g : Gate) (typed:g.op=.and ∨ g.op=.or) (two:g.inputs.length=2) :
    (readStep s g).bit=boolStep (s.map V.bit) g ∧ pair (readStep s g)=linStep (s.map pair) g := by
  obtain ⟨a,b,inputs⟩ : ∃ a b,g.inputs=[a,b] := by
    cases e:g.inputs with
    | nil => simp [e] at two
    | cons a t =>
      cases t with
      | nil => simp [e] at two
      | cons b t =>
        cases t <;> simp_all
  have bit (i : Nat) : (s.map V.bit).getD i false=(s.getD i default).bit := get_map _ _ _ _
  have both (i : Nat) : (s.map pair).getD i (false,false)=pair (s.getD i default) := get_map _ _ _ _
  rcases typed with e|e <;>
    simp [readStep,boolStep,linStep,e,inputs,bit,both,plus,mult,pair,GateOp.eval]
  
theorem projection_runs (gs : List Gate) (s : List V)
    (typed : ∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) :
    (oldrun gs s).map V.bit=scan boolStep gs (s.map V.bit) ∧
    (oldrun gs s).map pair=scan linStep gs (s.map pair) := by
  induction gs generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons g gs ih =>
    have t:=typed g List.mem_cons_self
    have v:=projections s g t.1 t.2
    have rec:=ih (s++[readStep s g]) (fun a ha=>typed a (List.mem_cons_of_mem _ ha))
    simpa [oldrun,scan,List.foldl_cons,v.1,v.2] using rec

theorem typed_recipe {n : Nat} (K : Circuit) (ao:IsAO2 n K) (s : List V) (len:s.length=n)
    (out:K.output < n+K.gates.length) :
    let P := compile n K.gates
    let v:=atoms (run P.ops s) (key P K.output)
    (scan boolStep K.gates (s.map V.bit)).getD K.output false=v.bit ∧
    ((scan linStep K.gates (s.map pair)).getD K.output (false,false)).1=v.z ∧
    (((scan linStep K.gates (s.map pair)).getD K.output (false,false)).2=true → v.o=true) := by
  have trace:=semantic_normal_form K ao s len
  have used : (oldrun K.gates s).length=n+K.gates.length := by
    change (scan readStep K.gates s).length=_
    rw [scan_length,len]
  have q:=trace.2.2 K.output (used.symm ▸ out)
  have prs:=projection_runs K.gates s (fun g hg=>⟨ao.1 g hg,ao.2.2 g hg⟩)
  rw [←prs.1,←prs.2]
  change ((oldrun K.gates s).map V.bit).getD K.output (V.bit default)=_ ∧
    (((oldrun K.gates s).map pair).getD K.output (pair default)).1=_ ∧
    ((((oldrun K.gates s).map pair).getD K.output (pair default)).2=true → _)
  rw [get_map,get_map]
  exact q

def builtWords (n : Nat) (ops : List Recipe) : Prop := ∀(i:Nat) (h:i<ops.length),
  wordOK (n+i) ops[i].1 ∧ wordOK (n+i) ops[i].2

private theorem word_append {n ops} (ok:builtWords n ops) (a b:Word)
    (ha:wordOK (n+ops.length) a) (hb:wordOK (n+ops.length) b) : builtWords n (ops++[(a,b)]) := by
  intro i hi
  by_cases early:i<ops.length
  · rw [List.getElem_append_left early]
    exact ok i early
  · have eq:i=ops.length := by simp at hi; omega
    subst i
    simpa using And.intro ha hb

theorem growWords (n:Nat) (g:Gate) (P:Plan) (ok:good n P) (valid:builtWords n P.ops) :
    builtWords n (expand n P g).ops := by
  cases e:g.op <;> simp only [expand,e] <;> first | exact valid | apply word_append valid <;> exact selected ok _

theorem allWords (n:Nat) (gs:List Gate) (P:Plan) (ok:good n P) (valid:builtWords n P.ops) :
    builtWords n (gs.foldl (expand n) P).ops := by
  induction gs generalizing P with
  | nil => exact valid
  | cons g gs ih => exact ih _ (expand_good ok g) (growWords n g P ok valid)

theorem recipe_words (n:Nat) (gs:List Gate) : builtWords n (compile n gs).ops :=
  allWords n gs _ (initialGood n) (by intro i hi; simp [initial] at hi)

end PEqualNP.Outside.L_meta_8123.Meet
