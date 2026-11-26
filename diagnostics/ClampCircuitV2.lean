import PEqualNP.Defs
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

theorem ordered (n : ℕ) (D : Circuit) (h : PEqualNP.TopForm.IsAO2 n D) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => (D.wires (List.ofFn x)).getD w false) := by
  let C : Circuit := ⟨D.gates,w⟩
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    exact ⟨h.1 g hg,by have eq := h.2.2 g hg; omega⟩
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  exact cmono C hm n x y hxy

end PlaneOrdered

namespace Helper9450
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
abbrev P := Fin 13
abbrev W := Fin 26
def E (p l : P) := l≠1 ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9)
def F (x : W → Bool) := ∃p l : P,E p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
def read (C : Circuit) (useOr : Bool) (o : List Nat) (x : W → Bool) (h : Bool) :=
  let w := C.wires (List.ofFn x++[h])
  if useOr=true then o.any (fun i => w.getD i false) else o.all (fun i => w.getD i false)
def hint (x : W → Bool) := x 1 || x 2
def Tested (C : Circuit) (b : Bool) (o : List Nat) := ∀x : W→Bool,
  Minimal F x ∨ Maximal (fun y => ¬F y) x → (read C b o x (hint x)=true ↔ F x)
theorem ordered (C : Circuit) (ao : IsAO2 27 C) (b : Bool) (o : List Nat)
    {x y : W → Bool} {h k : Bool} (hx : x≤y) (hk : h≤k) :
    read C b o x h=true → read C b o y k=true := by
  have src : ∀ i, (List.ofFn x++[h]).getD i false=true → (List.ofFn y++[k]).getD i false=true := by
    intro i
    rcases lt_trichotomy i 26 with lt|eq|gt
    · rw [PlaneOrdered.getD_snoc_lt _ _ _ (by simpa using lt),PlaneOrdered.getD_snoc_lt _ _ _ (by simpa using lt)]
      exact PlaneOrdered.ofFn_mono 26 x y (fun v => Bool.le_iff_imp.mp (hx v)) i
    · subst i
      have a := PlaneOrdered.getD_snoc_eq (List.ofFn x) h
      have b := PlaneOrdered.getD_snoc_eq (List.ofFn y) k
      rw [List.length_ofFn] at a b
      rw [a,b]
      exact Bool.le_iff_imp.mp hk
    · rw [PlaneOrdered.getD_snoc_gt _ _ _ (by simpa using gt)]
      simp
  have wire (i : Nat) : (C.wires (List.ofFn x++[h])).getD i false=true →
      (C.wires (List.ofFn y++[k])).getD i false=true :=
    PlaneOrdered.mono2 C.gates (fun g hg => ⟨ao.1 g hg,(ao.2.2 g hg).le⟩) _ _ (by simp) src i
  cases b
  · simp only [read,Bool.false_eq_true,ite_false,List.all_eq_true]
    intro all i hi
    exact wire i (all i hi)
  · simp only [read,ite_true,List.any_eq_true]
    rintro ⟨i,hi,lit⟩
    exact ⟨i,hi,wire i lit⟩
theorem coherent {C : Circuit} {b : Bool} {o : List Nat} (ao : IsAO2 27 C) (t : Tested C b o)
    (x : W → Bool) : read C b o x (hint x)=true ↔ F x := by
  have hm {u v : W→Bool} (le : u≤v) : hint u≤hint v := by
    rw [Bool.le_iff_imp]
    simp only [hint,Bool.or_eq_true]
    exact fun one => one.imp (Bool.le_iff_imp.mp (le 1)) (Bool.le_iff_imp.mp (le 2))
  constructor
  · intro accepted
    by_contra no
    obtain ⟨y,up,top⟩ := Finite.exists_le_maximal (p:=fun z => ¬F z) no
    exact top.1 ((t y (Or.inr top)).mp (ordered C ao b o up (hm up) accepted))
  · intro yes
    obtain ⟨y,low,bot⟩ := Finite.exists_le_minimal (p:=F) yes
    exact ordered C ao b o low (hm low) ((t y (Or.inl bot)).mpr bot.1)
def patch (x : W → Bool) (a b : Bool) (v : W) := if v=1 then a else if v=2 then b else x v
def Other (x : W → Bool) := ∃p l : P,p≠1 ∧ p≠2 ∧ E p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
def Pencil (x : W → Bool) (p : P) := ∃l,E p l ∧ x (Fin.natAdd 13 l)=true
theorem pointIdx : ∀p:P, (Fin.castAdd 13 p=(1:W) ↔ p=1) ∧
    (Fin.castAdd 13 p=(2:W) ↔ p=2) := by decide +kernel
theorem lineIdx : ∀l:P,Fin.natAdd 13 l≠(1:W) ∧ Fin.natAdd 13 l≠(2:W) := by decide +kernel
theorem patchP (x : W→Bool) (a b : Bool) (p : P) : patch x a b (Fin.castAdd 13 p) =
    (if p=1 then a else if p=2 then b else x (Fin.castAdd 13 p)) := by simp only [patch,(pointIdx p).1,(pointIdx p).2]
theorem patchL (x : W→Bool) (a b : Bool) (l : P) : patch x a b (Fin.natAdd 13 l)=x (Fin.natAdd 13 l) := by
  simp only [patch,(lineIdx l).1,(lineIdx l).2,ite_false]
theorem patchHint (x : W→Bool) (a b : Bool) : hint (patch x a b)= (a||b) := by
  have ne : (2:W)≠1 := by decide
  simp [hint,patch,ne]
theorem patched (x : W→Bool) (a b : Bool) : F (patch x a b) ↔ Other x ∨ (a=true ∧ Pencil x 1) ∨ (b=true ∧ Pencil x 2) := by
  constructor
  · rintro ⟨p,l,e,hp,hl⟩
    rw [patchP] at hp
    rw [patchL] at hl
    by_cases p1 : p=1
    · subst p
      exact Or.inr (Or.inl ⟨by simpa using hp,l,e,hl⟩)
    by_cases p2 : p=2
    · subst p
      exact Or.inr (Or.inr ⟨by simpa [p1] using hp,l,e,hl⟩)
    exact Or.inl ⟨p,l,p1,p2,e,by simpa [p1,p2] using hp,hl⟩
  · rintro (⟨p,l,h1,h2,e,hp,hl⟩|⟨ha,l,e,hl⟩|⟨hb,l,e,hl⟩)
    · exact ⟨p,l,e,by simpa only [patchP,h1,h2,ite_false] using hp,by simpa only [patchL] using hl⟩
    · exact ⟨1,l,e,by simpa only [patchP,ite_true] using ha,by simpa only [patchL] using hl⟩
    · have ne : (2:P)≠1 := by decide
      exact ⟨2,l,e,by simpa only [patchP,ne,ite_false,ite_true] using hb,by simpa only [patchL] using hl⟩
def Low (B R S : Prop) (a b h : Bool) := B ∨ h=true ∧ ((a=true ∧ R) ∨ (b=true ∧ S))
def High (B R S : Prop) (a b h : Bool) := B ∨ (a=true ∧ R) ∨ (b=true ∧ S) ∨ (h=true ∧ R ∧ S)
theorem interval (Q : Bool → Bool → Bool → Prop) (B R S : Prop)
    (monoQ : ∀{a b h i j k},a ≤ i → b ≤ j → h ≤ k → Q a b h → Q i j k)
    (known : ∀a b,Q a b (a||b) ↔ B ∨ (a=true ∧ R) ∨ (b=true ∧ S))
    (a b h : Bool) : (Low B R S a b h → Q a b h) ∧ (Q a b h → High B R S a b h) := by
  constructor
  · rintro (base|⟨rfl,⟨ha,hr⟩|⟨hb,hs⟩⟩)
    · exact monoQ (Bool.false_le _) (Bool.false_le _) (Bool.false_le _) ((known false false).mpr (Or.inl base))
    · subst a
      exact (known true b).mpr (Or.inr (Or.inl ⟨rfl,hr⟩))
    · subst b
      have t := (known a true).mpr (Or.inr (Or.inr ⟨rfl,hs⟩))
      simpa using t
  · intro z
    by_cases flip : h≤(a||b)
    · rcases (known a b).mp (monoQ le_rfl le_rfl flip z) with base|p|q
      · exact Or.inl base
      · exact Or.inr (Or.inl p)
      · exact Or.inr (Or.inr (Or.inl q))
    · have vals : h=true ∧ a=false ∧ b=false := by
        cases a <;> cases b <;> cases h <;> simp_all
      obtain ⟨rfl,rfl,rfl⟩ := vals
      have one := (known true false).mp (monoQ (Bool.false_le _) le_rfl le_rfl z)
      have two := (known false true).mp (monoQ le_rfl (Bool.false_le _) le_rfl z)
      simp at one two
      rcases one with bp|r
      · exact Or.inl bp
      rcases two with bq|s
      · exact Or.inl bq
      · exact Or.inr (Or.inr (Or.inr ⟨rfl,r,s⟩))
theorem offPromise {C : Circuit} {useOr : Bool} {o : List Nat} (ao : IsAO2 27 C) (t : Tested C useOr o)
    (x : W→Bool) (a b h : Bool) :
    (Low (Other x) (Pencil x 1) (Pencil x 2) a b h → read C useOr o (patch x a b) h=true) ∧
    (read C useOr o (patch x a b) h=true → High (Other x) (Pencil x 1) (Pencil x 2) a b h) := by
  apply interval _ _ _ _ _ _ a b h
  · intro a b h i j k ai bj hk
    apply ordered C ao useOr o _ hk
    intro v
    by_cases one : v=1
    · simpa only [patch,one,ite_true] using ai
    by_cases two : v=2
    · subst v
      have distinct : (2:W)≠1 := by decide
      simpa only [patch,distinct,ite_false,ite_true] using bj
    simp only [patch,one,two,ite_false,le_refl]
  · intro a b
    rw [←patchHint,coherent ao t,patched]
end Helper9450

namespace Helper9450
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
def point (p : P) : W := Fin.castAdd 13 p
def line (l : P) : W := Fin.natAdd 13 l
def row (p l : P) (v : W) := decide (v=point p ∨ v=line l)
def unit (a v : W) := decide (v=a)
def mate (p : P) : P := if p=1 then 2 else 1
def central (p : P) := p=1 ∨ p=2
instance (p : P) : Decidable (central p) := by unfold central; infer_instance
instance (p l : P) : Decidable (E p l) := by unfold E; infer_instance
instance (x : W→Bool) : Decidable (F x) := by unfold F; infer_instance
theorem plane : (∀p l : P,F (row p l) ↔ E p l) ∧ (∀a : W,¬F (unit a)) ∧
    (∀p l:P,hint (row p l)=decide (central p)) ∧
    (∀p:P,hint (unit (point p))=decide (central p)) ∧
    (∀p:P,central (mate p)) ∧ (∀p l:P,central p → E p l → ¬E (mate p) l) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel
theorem pureRow {p l : P} {x : W → Bool} (hp : x (point p)=true) (hl : x (line l)=true) :
    row p l≤x := by
  intro v
  rw [Bool.le_iff_imp]
  intro on
  rcases of_decide_eq_true on with h|h
  · simpa only [h] using hp
  · simpa only [h] using hl
def Triple (C : Circuit) (b : Bool) (o : List Nat) (p l : P) :=
  read C b o (row p l) true=true ∧ read C b o (row p l) false=false ∧
  read C b o (unit (point p)) true=false ∧ read C b o (unit (line l)) true=false
theorem clampOrTriple {C : Circuit} {b : Bool} {o : List Nat} (ao : IsAO2 27 C) (t : Tested C b o) :
    (∀x, read C b o x false=true ↔ F x) ∨ ∃p l:P,central p ∧ E p l ∧ Triple C b o p l := by
  classical
  obtain ⟨rows,units,hrow,hunit,hmate,mismatch⟩ := plane
  by_cases covers : ∀p l:P,E p l → read C b o (row p l) false=true
  · left
    intro x
    constructor
    · intro lit
      exact (coherent ao t x).mp (ordered C ao b o le_rfl (Bool.false_le _) lit)
    · rintro ⟨p,l,e,hp,hl⟩
      exact ordered C ao b o (pureRow hp hl) le_rfl (covers p l e)
  · right
    push_neg at covers
    obtain ⟨p,l,e,missing⟩ := covers
    have yes := (coherent ao t (row p l)).mpr ((rows p l).mpr e)
    have mid : central p := by
      by_contra no
      rw [hrow,decide_eq_false no] at yes
      simp_all
    have hh := hrow p l
    rw [decide_eq_true mid] at hh
    rw [hh] at yes
    refine ⟨p,l,mid,e,yes,?_,?_,?_⟩
    · simpa using missing
    · have hu := hunit p
      rw [decide_eq_true mid] at hu
      cases q : read C b o (unit (point p)) true with
      | false => rfl
      | true => exact False.elim (units (point p) ((coherent ao t (unit (point p))).mp (by simpa only [hu] using q)))
    · cases q : read C b o (unit (line l)) true with
      | false => rfl
      | true =>
        have subset : unit (line l) ≤ row (mate p) l := by
          intro v
          rw [Bool.le_iff_imp]
          intro lit
          have ev : v=line l := of_decide_eq_true lit
          exact decide_eq_true (Or.inr ev)
        have fire := ordered C ao b o subset le_rfl q
        have main := coherent ao t (row (mate p) l)
        rw [hrow,decide_eq_true (hmate p)] at main
        exact False.elim (mismatch p l mid e ((rows _ _).mp (main.mp fire)))
end Helper9450

namespace PEqualNP.Outside.L_meta_9448_aux

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem gL {V l : List Bool} {i : ℕ} (h : i < V.length) :
    (V ++ l).getD i false = V.getD i false := List.getD_append _ _ _ _ h

def chain (op : GateOp) : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | c, acc, y :: ys => ⟨op, [acc, y]⟩ :: chain op (c + 1) c ys

def fin : ℕ → ℕ → List ℕ → ℕ
  | _, acc, [] => acc
  | c, _, _ :: ys => fin (c + 1) c ys

theorem chain_len (op : GateOp) (ys : List ℕ) : ∀ c acc, (chain op c acc ys).length = ys.length := by
  induction ys with
  | nil => simp [chain]
  | cons y ys ih => intro c acc; simp [chain, ih]

theorem fin_cons (y : ℕ) (ys : List ℕ) : ∀ c acc, fin c acc (y :: ys) = c + ys.length := by
  induction ys generalizing y with
  | nil => intro c acc; simp [fin]
  | cons z zs ih => intro c acc; rw [fin, ih]; simp; omega

theorem chain_op (op : GateOp) (ys : List ℕ) : ∀ c acc, ∀ g ∈ chain op c acc ys,
    g.op = op ∧ g.inputs.length = 2 := by
  induction ys with
  | nil => simp [chain]
  | cons y ys ih =>
    intro c acc g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih _ _ g hg

theorem chain_nd (op : GateOp) (R : ℕ) (ys : List ℕ) : ∀ c acc, R ≤ c → (∀ y ∈ ys, y < R) → acc ∉ ys →
    ∀ g ∈ chain op c acc ys, g.inputs.Nodup := by
  induction ys with
  | nil => simp [chain]
  | cons y ys ih =>
    intro c acc hR hy ha g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [List.mem_cons, not_or] at ha
      simp [ha.1]
    · exact ih (c + 1) c (by omega) (fun z hz => hy z (by simp [hz]))
        (fun hc => by have := hy c (by simp [hc]); omega) g hg

theorem chain_rb (op : GateOp) (ys : List ℕ) : ∀ c acc, acc < c → (∀ y ∈ ys, y < c) →
    ∀ j < (chain op c acc ys).length, ∀ i ∈ ((chain op c acc ys).getD j ⟨GateOp.or, []⟩).inputs, i < c + j := by
  induction ys with
  | nil => simp [chain]
  | cons y ys ih =>
    intro c acc ha hy j hj i hi
    cases j with
    | zero =>
      simp [chain] at hi
      rcases hi with rfl | rfl
      · omega
      · have := hy i (by simp); omega
    | succ j =>
      simp only [chain, List.length_cons] at hj
      simp only [chain, List.getD_cons_succ] at hi
      have := ih (c + 1) c (by omega) (fun z hz => by have := hy z (by simp [hz]); omega) j (by omega) i hi
      omega

theorem chain_val (op : GateOp) (R : ℕ) (f : ℕ → Bool) (ys : List ℕ) (hys : ∀ y ∈ ys, y < R) :
    ∀ c acc (v : Bool) (V : List Bool), V.length = c → R ≤ c → (∀ i < R, V.getD i false = f i) →
      acc < c → V.getD acc false = v →
      ((chain op c acc ys).foldl stp V).getD (fin c acc ys) false =
        ys.foldl (fun b y => op.eval [b, f y]) v := by
  induction ys with
  | nil => intro c acc v V _ _ _ _ h0; simpa [chain, fin] using h0
  | cons y ys ih =>
    intro c acc v V hV hR hf hac h0
    have hy := hys y (by simp)
    simp only [chain, fin, List.foldl_cons]
    set a := op.eval ([acc, y].map fun i => V.getD i false) with ha
    have hs : stp V ⟨op, [acc, y]⟩ = V ++ [a] := rfl
    rw [hs]
    have hav : a = op.eval [v, f y] := by
      rw [ha]; simp only [List.map_cons, List.map_nil]; rw [h0, hf y hy]
    rw [← hav]
    apply ih (fun z hz => hys z (by simp [hz])) (c + 1) c a (V ++ [a]) (by simp [hV]) (by omega)
      (fun i hi => by rw [gL (by omega)]; exact hf i hi) (by omega)
    simp [List.getD_eq_getElem?_getD, hV]

theorem fold_or (g : ℕ → Bool) (l : List ℕ) : ∀ v, l.foldl (fun b y => GateOp.or.eval [b, g y]) v = (v || l.any g) := by
  induction l with
  | nil => simp
  | cons y ys ih => intro v; rw [List.foldl_cons, ih]; simp [GateOp.eval, Bool.or_assoc]

theorem fold_and (g : ℕ → Bool) (l : List ℕ) : ∀ v, l.foldl (fun b y => GateOp.and.eval [b, g y]) v = (v && l.all g) := by
  induction l with
  | nil => simp
  | cons y ys ih => intro v; rw [List.foldl_cons, ih]; simp [GateOp.eval, Bool.and_assoc]

theorem ev (C : Circuit) (x : List Bool) : C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

end PEqualNP.Outside.L_meta_9448_aux

open PEqualNP.Outside.L_meta_9448_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9448 : ∀ (x1 : ℕ) (x2 : Bool) (x3 : Fin x1) (x4 : List (Fin x1)), x4 ≠ [] → (x3 :: x4).Nodup → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), x7.size = x4.length ∧ x7.output = x1 + x7.size - (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x7 ∧ (∀ x8 ∈ x7.gates, x8.inputs.Nodup) ∧ ∀ (x8 : List Bool), x8.length = x1 → x7.eval x8 = if x2 = Bool.true then (x3 :: x4).any fun (x10 : Fin x1) => x8.getD (↑x10) Bool.false else (x3 :: x4).all fun (x10 : Fin x1) => x8.getD (↑x10) Bool.false := by
  intro x1 x2 x3 x4 hne hnd
  let op : GateOp := if x2 = true then GateOp.or else GateOp.and
  let ys : List ℕ := x4.map Fin.val
  have hys : ∀ y ∈ ys, y < x1 := by
    intro y hy; simp only [ys, List.mem_map] at hy; obtain ⟨q, _, rfl⟩ := hy; exact q.isLt
  have hyne : ys ≠ [] := by simpa [ys] using hne
  obtain ⟨y0, ys0, hy0⟩ := List.exists_cons_of_ne_nil hyne
  have hx3 : x3.val ∉ ys := by
    intro h; simp only [ys, List.mem_map] at h; obtain ⟨q, hq, hqe⟩ := h
    have := (List.nodup_cons.mp hnd).1; rw [Fin.ext hqe] at hq; exact this hq
  refine ⟨⟨chain op x1 x3.val ys, fin x1 x3.val ys⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Circuit.size, chain_len, ys]
  · simp only [Circuit.size, chain_len]; rw [hy0, fin_cons]; simp
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg; have := (chain_op op ys _ _ g hg).1; rw [this]; simp only [op]; split_ifs <;> simp
    · intro j hj i hi
      exact chain_rb op ys x1 x3.val x3.isLt (fun y hy => hys y hy) j hj i hi
    · intro g hg; exact (chain_op op ys _ _ g hg).2
  · exact chain_nd op x1 ys x1 x3.val le_rfl hys hx3
  · intro x8 hx8
    rw [ev]
    rw [chain_val op x1 (fun i => x8.getD i false) ys hys x1 x3.val _ x8 hx8 le_rfl (fun i _ => rfl) x3.isLt rfl]
    simp only [op]
    split_ifs with h
    · rw [fold_or]; simp [ys, List.any_map, Function.comp_def]
    · rw [fold_and]; simp [ys, List.all_map, Function.comp_def]
namespace Physical9450
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm Helper9450 PlaneOrdered
def idx (bad j : Nat) := if j=26 then bad else if j<26 then j else j-1
def mapped (bad : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (idx bad)⟩
def clamp (C : Circuit) : Circuit := ⟨C.gates.map (mapped (27+C.size)),idx (27+C.size) C.output⟩
theorem consWF (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g::gs) w=wf gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
theorem sim (B : List Gate) (bad : Nat) :
    ∀ U V : List Bool, U.length=V.length+1 → 27≤U.length → V.length+B.length<bad →
    (∀j,U.getD j false=V.getD (idx bad j) false) → ∀j,
    (wf B U).getD j false=(wf (B.map (mapped bad)) V).getD (idx bad j) false := by
  induction B with
  | nil => intro U V _ _ _ eq j; exact eq j
  | cons g B ih =>
    intro U V len enough bound vals i
    rw [List.map_cons,consWF,consWF]
    have ev : g.op.eval (g.inputs.map fun j => U.getD j false) =
        (mapped bad g).op.eval ((mapped bad g).inputs.map fun j => V.getD j false) := by
      change _=g.op.eval ((g.inputs.map (idx bad)).map fun j => V.getD j false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      exact fun j _ => vals j
    apply ih
    · simp [len]
    · simp; omega
    · simp at bound ⊢; omega
    · intro j
      rw [ev]
      by_cases centre : j=26
      · subst j
        rw [getD_snoc_lt _ _ _ (by omega),vals]
        simp only [idx,ite_true]
        rw [getD_snoc_gt _ _ _ (by simp at bound; omega),List.getD_eq_default _ _ (by simp at bound; omega)]
      · rcases lt_trichotomy j U.length with lt|eq|gt
        · have smaller : idx bad j<V.length := by
            unfold idx
            simp only [centre,ite_false]
            split <;> omega
          rw [getD_snoc_lt _ _ _ lt,getD_snoc_lt _ _ _ smaller,vals]
        · have eq' : idx bad j=V.length := by simp only [idx,centre,show ¬j<26 by omega,ite_false]; omega
          rw [eq,getD_snoc_eq,←eq,eq',getD_snoc_eq]
        · have gt' : V.length<idx bad j := by simp only [idx,centre,show ¬j<26 by omega,ite_false]; omega
          rw [getD_snoc_gt _ _ _ gt,getD_snoc_gt _ _ _ gt']
theorem simulation (C : Circuit) (x : W → Bool) :
    C.eval (List.ofFn x++[false])=(clamp C).eval (List.ofFn x) := by
  change (wf C.gates _).getD _ false=(wf (C.gates.map (mapped _)) _).getD (idx _ _) false
  apply sim
  · simp
  · simp
  · simp [Circuit.size]
  · intro i
    rcases lt_trichotomy i 26 with a|a|a
    · have ne : i≠26 := by omega
      rw [getD_snoc_lt _ _ _ (by simpa using a)]
      simp [idx,ne,a]
    · subst i
      simp only [idx,ite_true]
      have q := getD_snoc_eq (List.ofFn x) false
      rw [List.length_ofFn] at q
      rw [q,List.getD_eq_default _ _ (by simp; omega)]
    · have ne : i≠26 := by omega
      rw [getD_snoc_gt _ _ _ (by simpa using a),List.getD_eq_default _ _ (by simp [idx,ne,show ¬i<26 by omega]; omega)]
theorem clamp_shape {C : Circuit} (ao : Monotone2 C) : (clamp C).size=C.size ∧ Monotone2 (clamp C) := by
  refine ⟨by simp [clamp,Circuit.size],?_⟩
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  exact ⟨(ao a ha).1,by simpa [mapped] using (ao a ha).2⟩
def legal {n : Nat} {C : Circuit} (ao : IsAO2 n C) : Monotone2 C :=
  fun g hg => ⟨ao.1 g hg,(ao.2.2 g hg).le⟩
def WireList (C : Circuit) (o : List (Fin (27+C.size))) := o.map Fin.val
theorem scalar {D : Circuit} (b : Bool) (a : Fin (27+D.size)) (s : List (Fin (27+D.size)))
    (ne : s≠[]) (unique : (a::s).Nodup) (ao : IsAO2 27 D) :
    ∃C : Circuit, C.size = D.size+s.length ∧ Monotone2 C ∧
      ∀x : W→Bool, C.eval (List.ofFn x)=read D b (WireList D (a::s)) x false := by
  obtain ⟨Q,sz,_,leg,_,eq⟩ := PEqualNP.Outside.L_meta_9448 _ b a s ne unique
  let T : Circuit := ⟨D.gates++Q.gates,Q.output⟩
  have tsz : T.size = D.size+s.length := by
    change (D.gates++Q.gates).length=_
    rw [List.length_append]
    change D.size+Q.size=_
    rw [sz]
  have lm : Monotone2 T := by
    intro g hg
    rcases List.mem_append.mp hg with left|right
    · exact legal ao g left
    · exact legal leg g right
  obtain ⟨szC,mc⟩ := clamp_shape lm
  refine ⟨clamp T,szC.trans tsz,mc,?_⟩
  intro x
  rw [←simulation]
  have len : (D.wires (List.ofFn x++[false])).length=27+D.size := by
    change (wf D.gates _).length=_
    simp [wf_len,Circuit.size]
  have merge : T.eval (List.ofFn x++[false])=Q.eval (D.wires (List.ofFn x++[false])) := by
    change ((D.gates++Q.gates).foldl _ _).getD _ _=_
    rw [List.foldl_append]
    rfl
  rw [merge,eq _ len]
  simp only [read,WireList,List.any_map,List.all_map,Function.comp_def]
theorem ordinaryOrTriple {D : Circuit} (b : Bool) (a : Fin (27+D.size)) (s : List (Fin (27+D.size)))
    (ne : s≠[]) (unique : (a::s).Nodup) (ao : IsAO2 27 D) (bound : D.size+s.length ≤ 58)
    (t : Tested D b (WireList D (a::s))) :
    (∃C : Circuit, C.size≤58 ∧ Monotone2 C ∧ ∀x : W→Bool,C.eval (List.ofFn x)=true ↔ F x) ∨
      ∃p l:P,central p ∧ E p l ∧ Triple D b (WireList D (a::s)) p l := by
  rcases clampOrTriple ao t with computes|uses
  · left
    obtain ⟨C,sz,h,eq⟩ := scalar b a s ne unique ao
    exact ⟨C,sz.trans_le bound,h,fun x => by rw [eq,computes]⟩
  · exact Or.inr uses
end Physical9450
