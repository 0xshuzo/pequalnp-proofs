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
namespace Lift9450
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PlaneOrdered Helper9450
def readat (C : Circuit) (x : W→Bool) (i : Nat) := (C.wires (List.ofFn x)).getD i false
def put (C : Circuit) (op : GateOp) (a b : Nat) : Circuit := ⟨C.gates++[⟨op,[a,b]⟩],26+C.size⟩
theorem putSize (C : Circuit) (op : GateOp) (a b : Nat) : (put C op a b).size=C.size+1 := by simp [put,Circuit.size]
theorem putOut (C : Circuit) (op : GateOp) (a b : Nat) : (put C op a b).output=26+C.size := rfl
theorem keep (C : Circuit) (op : GateOp) (a b i : Nat) (x : W→Bool) (lt : i<26+C.size) :
    readat (put C op a b) x i=readat C x i := by
  change (wf (C.gates++[⟨op,[a,b]⟩]) (List.ofFn x)).getD i false=(wf C.gates _).getD i false
  rw [wf_snoc,getD_snoc_lt]
  simpa only [wf_len,List.length_ofFn,Circuit.size] using lt
theorem atOutput (C : Circuit) (x : W→Bool) : readat C x C.output=C.eval (List.ofFn x) := rfl
theorem atRaw (C : Circuit) (x : W→Bool) (v : W) : readat C x v.val = x v := by
  change (wf C.gates (List.ofFn x)).getD v.val false=x v
  rw [wf_keep _ _ _ (by simpa using v.isLt)]
  simp
theorem value (C : Circuit) (op : GateOp) (a b : Nat) (x : W→Bool) :
    (put C op a b).eval (List.ofFn x)=op.eval [readat C x a,readat C x b] := by
  change (wf (C.gates++[⟨op,[a,b]⟩]) (List.ofFn x)).getD (26+C.size) false=_
  rw [wf_snoc]
  let L := wf C.gates (List.ofFn x)
  have sz : L.length=26+C.size := by simp only [L,wf_len,List.length_ofFn,Circuit.size]
  have last := getD_snoc_eq L (op.eval [readat C x a,readat C x b])
  rw [sz] at last
  exact last
theorem putMono {C : Circuit} (hc : Monotone2 C) (o : GateOp) (ok : o=GateOp.and ∨ o=GateOp.or) (a b : Nat) :
    Monotone2 (put C o a b) := by
  intro g hg
  rcases List.mem_append.mp hg with hg|hg
  · exact hc g hg
  · obtain rfl := List.mem_singleton.mp hg
    exact ⟨ok,by decide⟩
def full (x : W→Bool) := ∃p l:P,(p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
  x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
theorem combine (x : W→Bool) : full x ↔ F x ∨
    (((hint x || x 4) || x 10)=true ∧ x 14=true) := by
  have one : ∀p:P,(p=1 ∨ p=1+1 ∨ p=1+3 ∨ p=1+9) ↔ p=1 ∨ p=2 ∨ p=4 ∨ p=10 := by decide +kernel
  constructor
  · rintro ⟨p,l,e,px,lx⟩
    by_cases l1 : l=1
    · subst l
      right
      refine ⟨?_,lx⟩
      simp only [hint,Bool.or_eq_true]
      rcases (one p).mp e with rfl|rfl|rfl|rfl
      · exact Or.inl (Or.inl (Or.inl px))
      · exact Or.inl (Or.inl (Or.inr px))
      · exact Or.inl (Or.inr px)
      · exact Or.inr px
    · exact Or.inl ⟨p,l,⟨l1,e⟩,px,lx⟩
  · rintro (⟨p,l,⟨_,e⟩,px,lx⟩|⟨px,lx⟩)
    · exact ⟨p,l,e,px,lx⟩
    · simp only [hint,Bool.or_eq_true] at px
      rcases px with ((p|p)|p)|p
      · exact ⟨1,1,(one 1).mpr (by simp),p,lx⟩
      · exact ⟨2,1,(one 2).mpr (by simp),p,lx⟩
      · exact ⟨4,1,(one 4).mpr (by simp),p,lx⟩
      · exact ⟨10,1,(one 10).mpr (by simp),p,lx⟩
theorem fill {C : Circuit} (cm : Monotone2 C) (size : C.size ≤ 59) (out : C.output<26+C.size)
    (tap : Nat) (ht : ∀x : W→Bool,readat C x tap=hint x)
    (funC : ∀x : W→Bool,C.eval (List.ofFn x)=true ↔ F x) :
    ∃Z : Circuit,Z.size≤63 ∧ Monotone2 Z ∧ ∀x : W→Bool,Z.eval (List.ofFn x)=true ↔ full x := by
  let A := put C .or tap 4
  let B := put A .or A.output 10
  let L := put B .and B.output 14
  let Z := put L .or C.output L.output
  have sA := putSize C .or tap 4
  have sB := putSize A .or A.output 10
  have sL := putSize B .and B.output 14
  change A.size=_ at sA
  change B.size=_ at sB
  change L.size=_ at sL
  have funA := putMono cm GateOp.or (Or.inr rfl) tap 4
  have funB := putMono funA GateOp.or (Or.inr rfl) A.output 10
  have funL := putMono funB GateOp.and (Or.inl rfl) B.output 14
  refine ⟨Z,?_,putMono funL GateOp.or (Or.inr rfl) C.output L.output,?_⟩
  · change (put L GateOp.or _ _).size≤63
    rw [putSize]
    omega
  · intro x
    have vA : A.eval (List.ofFn x)=(hint x || x 4) := by
      rw [show A=put C .or tap 4 from rfl,value,ht,atRaw C x (4:W)]
      simp [GateOp.eval]
    have vB : B.eval (List.ofFn x)=((hint x || x 4) || x 10) := by
      rw [show B=put A .or A.output 10 from rfl,value,atOutput,vA,atRaw A x (10:W)]
      simp [GateOp.eval]
    have vL : L.eval (List.ofFn x)=(((hint x || x 4) || x 10) && x 14) := by
      rw [show L=put B .and B.output 14 from rfl,value,atOutput,vB,atRaw B x (14:W)]
      simp [GateOp.eval]
    have old : readat L x C.output=C.eval (List.ofFn x) := by
      change readat (put B .and B.output 14) x _=_
      rw [keep _ _ _ _ _ _ (by omega)]
      change readat (put A .or A.output 10) x _=_
      rw [keep _ _ _ _ _ _ (by omega)]
      change readat (put C .or tap 4) x _=_
      rw [keep _ _ _ _ _ _ out,atOutput]
    change (put L .or C.output L.output).eval _=true ↔ _
    rw [value,old,atOutput,vL,combine]
    simp only [GateOp.eval,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true,Bool.and_eq_true,funC]
theorem full63 {D : Circuit} (b : Bool) (a : Fin (27+D.size)) (s : List (Fin (27+D.size)))
    (ne : s≠[]) (unique : (a::s).Nodup) (ao : IsAO2 27 D) (bound : D.size+s.length ≤ 58)
    (t : Tested D b ((a::s).map Fin.val)) :
    ∃Z : Circuit,Z.size≤63 ∧ Monotone2 Z ∧ ∀x : W→Bool,Z.eval (List.ofFn x)=true ↔ full x := by
  obtain ⟨Q,szQ,outQ,lQ,_,eqQ⟩ := PEqualNP.Outside.L_meta_9448 _ b a s ne unique
  let head : Gate := ⟨GateOp.or,[1,2]⟩
  let C : Circuit := ⟨head::(D.gates++Q.gates),Q.output⟩
  have szC : C.size=1+D.size+s.length := by
    change (head::(D.gates++Q.gates)).length=_
    simp only [List.length_cons,List.length_append]
    change D.size+Q.size+1=_
    omega
  have ls : Monotone2 C := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl|h
    · exact ⟨Or.inr rfl,by decide⟩
    rcases List.mem_append.mp h with h|h
    · exact ⟨ao.1 g h,(ao.2.2 g h).le⟩
    · exact ⟨lQ.1 g h,(lQ.2.2 g h).le⟩
  have init (x : W→Bool) : head.op.eval (head.inputs.map fun i => (List.ofFn x).getD i false)=hint x := by
    simp [head,hint,GateOp.eval,List.getD_eq_getElem?_getD]
  apply fill ls (by omega) (by change Q.output<26+C.size; omega) 26
  · intro x
    change (wf (D.gates++Q.gates) (List.ofFn x++[_])).getD 26 false=_
    rw [init,wf_keep _ _ _ (by simp)]
    have last := getD_snoc_eq (List.ofFn x) (hint x)
    simpa only [List.length_ofFn] using last
  · intro x
    have len : (D.wires (List.ofFn x++[hint x])).length=27+D.size := by
      change (wf D.gates _).length=_
      simp [wf_len,Circuit.size]
    have agree : C.eval (List.ofFn x)=Q.eval (D.wires (List.ofFn x++[hint x])) := by
      change ((D.gates++Q.gates).foldl _ (List.ofFn x++[_])).getD _ _=_
      rw [init,List.foldl_append]
      rfl
    rw [agree,eqQ _ len]
    simpa only [read,List.any_map,List.all_map,Function.comp_def] using coherent ao t x
end Lift9450
