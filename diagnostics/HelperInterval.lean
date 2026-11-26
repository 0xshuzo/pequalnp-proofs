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
    (monoQ : ∀{a b h i j k},a≤i → b≤j → h≤k → Q a b h → Q i j k)
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
    · simpa only [patch,one,two,ite_false,ite_true] using bj
    simp only [patch,one,two,ite_false,le_refl]
  · intro a b
    rw [←patchHint,coherent ao t,patched]
end Helper9450
