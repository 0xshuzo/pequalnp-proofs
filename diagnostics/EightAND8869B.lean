import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8869.Matching
open Finset
variable {α β : Type} [DecidableEq α] [DecidableEq β]

def Induced (R : α → β → Prop) (E : Finset (α × β)) (d : Nat) : Prop :=
  ∃ a : Fin d → α, ∃ b : Fin d → β,(∀ i,(a i,b i)∈E) ∧ ∀ i j,R (a i) (b j) → i=j

def Linear (R : α → β → Prop) : Prop := ∀ a a' b b',a≠a' → R a b → R a b' → R a' b → R a' b' → b=b'

theorem other {γ : Type} [DecidableEq γ] (S : Finset γ) (h : 2≤S.card) (g : γ) :
    ∃ x∈S,x≠g := by
  classical
  by_contra! all
  have sub : S⊆{g} := fun x hx => mem_singleton.mpr (all x hx)
  have bound := card_le_card sub
  simp only [card_singleton] at bound
  omega

theorem induced_min (R : α → β → Prop) [DecidableRel R] (E : Finset (α × β))
    (lin : Linear R) (inc : ∀ e∈E,R e.1 e.2) (d : Nat) (P : Finset α) (L : Finset β)
    (alive : 0<d → P.Nonempty)
    (rows : ∀ a∈P,d≤(L.filter (fun b => (a,b)∈E)).card)
    (cols : ∀ b∈L,d≤(P.filter (fun a => (a,b)∈E)).card) :
    ∃ a : Fin d → α, ∃ b : Fin d → β,
      (∀ i,a i∈P ∧ b i∈L ∧ (a i,b i)∈E) ∧ ∀ i j,R (a i) (b j) → i=j := by
  classical
  induction d generalizing P L with
  | zero => exact ⟨Fin.elim0,Fin.elim0,(fun i => i.elim0),(fun i => i.elim0)⟩
  | succ d ih =>
    obtain ⟨u,up⟩ := alive (by omega)
    have rowU := rows u up
    obtain ⟨v,hv⟩ := card_pos.mp (show 0<(L.filter (fun b => (u,b)∈E)).card by omega)
    obtain ⟨vl,uv⟩ := mem_filter.mp hv
    have ur := inc (u,v) uv
    let P' := P.filter (fun p => ¬R p v)
    let L' := L.filter (fun b => ¬R u b)
    have alive' (pos : 0<d) : P'.Nonempty := by
      obtain ⟨t,ht,vt⟩ := other _ (show 2≤(L.filter (fun b => (u,b)∈E)).card by omega) v
      obtain ⟨tl,ut⟩ := mem_filter.mp ht
      have colT := cols t tl
      obtain ⟨p,hp,pu⟩ := other _ (show 2≤(P.filter (fun a => (a,t)∈E)).card by omega) u
      obtain ⟨pp,pt⟩ := mem_filter.mp hp
      exact ⟨p,mem_filter.mpr ⟨pp,fun pv => vt (lin p u t v pu (inc (p,t) pt) pv (inc (u,t) ut) ur)⟩⟩
    have row' (p : α) (hp : p∈P') : d≤(L'.filter (fun b => (p,b)∈E)).card := by
      obtain ⟨pp,pv⟩ := mem_filter.mp hp
      have pu : p≠u := fun eq => pv (eq ▸ ur)
      let A := L.filter (fun b => (p,b)∈E)
      let B := L'.filter (fun b => (p,b)∈E)
      have sub : B⊆A := fun b hb => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hb).1).1,(mem_filter.mp hb).2⟩
      have lose (b : β) (hb : b∈A\B) : R p b ∧ R u b := by
        obtain ⟨ha,hno⟩ := mem_sdiff.mp hb
        obtain ⟨bl,eb⟩ := mem_filter.mp ha
        exact ⟨inc (p,b) eb,by by_contra no; exact hno (mem_filter.mpr ⟨mem_filter.mpr ⟨bl,no⟩,eb⟩)⟩
      have one : (A\B).card≤1 := card_le_one.mpr (fun b hb c hc => lin p u b c pu
        (lose b hb).1 (lose c hc).1 (lose b hb).2 (lose c hc).2)
      have eq := card_sdiff_add_card_eq_card sub
      have low : d+1≤A.card := rows p pp
      change d≤B.card
      omega
    have col' (b : β) (hb : b∈L') : d≤(P'.filter (fun p => (p,b)∈E)).card := by
      obtain ⟨bl,ub⟩ := mem_filter.mp hb
      have bv : b≠v := fun e => ub (e ▸ ur)
      let A := P.filter (fun p => (p,b)∈E)
      let B := P'.filter (fun p => (p,b)∈E)
      have sub : B⊆A := fun p hp => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
      have lose (p : α) (hp : p∈A\B) : R p b ∧ R p v := by
        obtain ⟨ha,hno⟩ := mem_sdiff.mp hp
        obtain ⟨pp,eb⟩ := mem_filter.mp ha
        exact ⟨inc (p,b) eb,by by_contra no; exact hno (mem_filter.mpr ⟨mem_filter.mpr ⟨pp,no⟩,eb⟩)⟩
      have one : (A\B).card≤1 := card_le_one.mpr (fun p hp r hr => by
        by_contra ne
        exact bv (lin p r b v ne (lose p hp).1 (lose p hp).2 (lose r hr).1 (lose r hr).2))
      have eq := card_sdiff_add_card_eq_card sub
      have low : d+1≤A.card := cols b bl
      change d≤B.card
      omega
    obtain ⟨a,b,good,ind⟩ := ih P' L' alive' row' col'
    refine ⟨Fin.cases u a,Fin.cases v b,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨up,vl,uv⟩
      · exact ⟨(mem_filter.mp (good j).1).1,(mem_filter.mp (good j).2.1).1,(good j).2.2⟩
    · intro i j
      refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
      · exact fun _ => rfl
      · exact fun h => False.elim ((mem_filter.mp (good l).2.1).2 h)
      · exact fun h => False.elim ((mem_filter.mp (good k).1).2 h)
      · exact fun h => congrArg Fin.succ (ind k l h)

end PEqualNP.Outside.L_meta_8869.Matching

namespace PEqualNP.Outside.L_meta_8869.Matching
open Finset
variable {α β : Type} [DecidableEq α] [DecidableEq β]

theorem peel (R : α → β → Prop) [DecidableRel R] (lin : Linear R) (k : Nat)
    (E : Finset (α × β)) (P : Finset α) (L : Finset β) (sub : E ⊆ P ×ˢ L) (inc : ∀ e∈E,R e.1 e.2)
    (no : ¬Induced R E (k+1)) : E.card ≤ k*(P.card+L.card-1) := by
  classical
  have aux (t : Nat) : ∀ (P : Finset α) (L : Finset β) (E : Finset (α × β)),
      P.card+L.card=t → E ⊆ P ×ˢ L → (∀ e∈E,R e.1 e.2) →
      ¬Induced R E (k+1) → E.card ≤ k*(P.card+L.card-1) := by
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro P L E total sub inc no
      by_cases nz : E.Nonempty
      swap
      · simp [Finset.not_nonempty_iff_eq_empty.mp nz]
      obtain ⟨e,he⟩ := nz
      obtain ⟨ep,el⟩ := mem_product.mp (sub he)
      have pp := card_pos.mpr (show P.Nonempty from ⟨e.1,ep⟩)
      have lp := card_pos.mpr (show L.Nonempty from ⟨e.2,el⟩)
      by_cases rows : ∀ p∈P,k+1≤(L.filter (fun b => (p,b)∈E)).card
      · by_cases cols : ∀ b∈L,k+1≤(P.filter (fun p => (p,b)∈E)).card
        · obtain ⟨a,b,good,unique⟩ := induced_min R E lin inc (k+1) P L (fun _ => ⟨e.1,ep⟩) rows cols
          exact False.elim (no ⟨a,b,fun i => (good i).2.2,unique⟩)
        · push_neg at cols
          obtain ⟨v,hv,small⟩ := cols
          let F := E.filter (fun z => z.2≠v)
          let D := E.filter (fun z => z.2=v)
          have save : D.card≤(P.filter (fun b => (b,v)∈E)).card := by
            apply card_le_card_of_injOn Prod.fst
            · rintro ⟨p,l⟩ hit
              obtain ⟨ee,eq⟩ := mem_filter.mp hit
              change l=v at eq
              subst v
              exact mem_filter.mpr ⟨(mem_product.mp (sub ee)).1,ee⟩
            · rintro ⟨p,l⟩ hit ⟨p',l'⟩ hit' h
              have eq := (mem_filter.mp hit).2
              have eq' := (mem_filter.mp hit').2
              exact Prod.ext h (eq.trans eq'.symm)
          have parts : D.card+F.card=E.card := card_filter_add_card_filter_not (s:=E) (fun z => z.2=v)
          have fsub : F⊆P ×ˢ (L.erase v) := by
            intro f hf
            obtain ⟨old,diff⟩ := mem_filter.mp hf
            obtain ⟨p,l⟩ := mem_product.mp (sub old)
            exact mem_product.mpr ⟨p,mem_erase.mpr ⟨diff,l⟩⟩
          have er := card_erase_add_one hv
          have lt : P.card+(L.erase v).card<t := by omega
          have bd := ih _ lt P (L.erase v) F rfl fsub (fun f hf => inc f (mem_filter.mp hf).1) (by
            rintro ⟨a,b,ok,mat⟩
            exact no ⟨a,b,fun i => (mem_filter.mp (ok i)).1,mat⟩)
          have diff : P.card+L.card-1=(P.card+(L.erase v).card-1)+1 := by omega
          rw [diff,Nat.mul_add,Nat.mul_one]
          omega
      · push_neg at rows
        obtain ⟨u,hu,small⟩ := rows
        let F := E.filter (fun z => z.1≠u)
        let D := E.filter (fun z => z.1=u)
        have save : D.card≤(L.filter (fun b => (u,b)∈E)).card := by
          apply card_le_card_of_injOn Prod.snd
          · rintro ⟨p,l⟩ hit
            obtain ⟨ee,eq⟩ := mem_filter.mp hit
            change p=u at eq
            subst u
            exact mem_filter.mpr ⟨(mem_product.mp (sub ee)).2,ee⟩
          · rintro ⟨p,l⟩ hit ⟨p',l'⟩ hit' h
            have eq := (mem_filter.mp hit).2
            have eq' := (mem_filter.mp hit').2
            exact Prod.ext (eq.trans eq'.symm) h
        have parts : D.card+F.card=E.card := card_filter_add_card_filter_not (s:=E) (fun z => z.1=u)
        have fsub : F⊆(P.erase u) ×ˢ L := by
          intro f hf
          obtain ⟨old,diff⟩ := mem_filter.mp hf
          obtain ⟨p,l⟩ := mem_product.mp (sub old)
          exact mem_product.mpr ⟨mem_erase.mpr ⟨diff,p⟩,l⟩
        have er := card_erase_add_one hu
        have lt : (P.erase u).card+L.card<t := by omega
        have bd := ih _ lt (P.erase u) L F rfl fsub (fun f hf => inc f (mem_filter.mp hf).1) (by
          rintro ⟨a,b,ok,mat⟩
          exact no ⟨a,b,fun i => (mem_filter.mp (ok i)).1,mat⟩)
        have diff : P.card+L.card-1=((P.erase u).card+L.card-1)+1 := by omega
        rw [diff,Nat.mul_add,Nat.mul_one]
        omega
  exact aux _ P L E rfl sub inc no
end PEqualNP.Outside.L_meta_8869.Matching


namespace PEqualNP.Outside.L_meta_8869.Certificate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

section Circ2

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩


end Circ2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def input {N : ℕ} (P L : Finset (Fin N)) : Fin (N+N) → Bool :=
  Fin.addCases (fun p => decide (p∈P)) (fun l => decide (l∈L))

def Hit {N : ℕ} (I : Fin N → Fin N → Prop) (P L : Finset (Fin N)) : Prop :=
  ∃ p ∈ P, ∃ l ∈ L, I p l

theorem input_l {N} (P L : Finset (Fin N)) (p : Fin N) :
    input P L (Fin.castAdd N p) = decide (p∈P) := Fin.addCases_left ..
theorem input_r {N} (P L : Finset (Fin N)) (l : Fin N) :
    input P L (Fin.natAdd N l) = decide (l∈L) := Fin.addCases_right ..

theorem wire_mono {N} {C : Circuit} (hm : Monotone2 C) {P P' L L' : Finset (Fin N)}
    (hp : P ⊆ P') (hl : L ⊆ L') (w : ℕ) :
    val C (input P L) w = true → val C (input P' L') w = true := by
  apply acts_mono hm
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp only [input_l,decide_eq_true_eq]
    exact fun h => hp h
  · intro l
    simp only [input_r,decide_eq_true_eq]
    exact fun h => hl h

def andOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

def ands (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter fun j => andOp C.gates[j.val].op = true

def choices {n : ℕ} (C : Circuit) (x : Fin n → Bool) : Finset (Fin C.gates.length) :=
  (ands C).filter fun j => val C x (C.gates[j.val].inputs.getD 0 0) = true

theorem union_false {n} (C : Circuit) (hm : Monotone2 C)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g → ∃ a b : ℕ, g.inputs=[a,b] ∧ a<n+j ∧ b<n+j)
    (x y z : Fin n → Bool) (hz : ∀ i, z i = (x i || y i))
    (same : choices C x = choices C y) :
    ∀ i, val C x i=false → val C y i=false → val C z i=false := by
  classical
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hx hy
    by_cases raw : i<n
    · let j : Fin n := ⟨i,raw⟩
      change val C z j.val = false
      rw [val_input, hz, ←val_input C x, ←val_input C y]
      simp [j,hx,hy]
    by_cases gone : n + C.gates.length ≤ i
    · exact val_beyond _ _ gone
    let k := i-n
    have hk : k<C.gates.length := by dsimp [k]; omega
    let j : Fin C.gates.length := ⟨k,hk⟩
    let g : Gate := C.gates[j.val]
    have hg : C.gates[k]?=some g := List.getElem?_eq_some_iff.mpr ⟨hk,rfl⟩
    obtain ⟨a,b,ins,ab,bk⟩ := hs k g hg
    have node : n+k=i := by dsimp [k]; omega
    have ai : a < i := by omega
    have bi : b < i := by omega
    have ev (t : Fin n → Bool) : val C t i=g.op.eval [val C t a,val C t b] := by
      have h := val_gate C t hg
      rw [node,ins] at h
      simpa [operand,ai,bi] using h
    rw [ev] at hx hy ⊢
    have hop := (hm g (List.mem_of_getElem? hg)).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    rcases hop with hand | hor
    · have eq : val C x a = val C y a := by
        have h : j ∈ choices C x ↔ j ∈ choices C y := by rw [same]
        have h' : val C x a=true ↔ val C y a=true := by
          have active : j∈ands C := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,show andOp g.op=true by rw [hand]; rfl⟩
          simp only [choices,Finset.mem_filter,active,true_and] at h
          rw [show C.gates[j.val].inputs=[a,b] from ins] at h
          exact h
        cases ax : val C x a <;> cases ay : val C y a <;> simp_all
      rw [hand] at hx hy ⊢
      simp only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true] at hx hy ⊢
      cases ax : val C x a with
      | false =>
        have ay : val C y a=false := eq.symm.trans ax
        simp [ih a ai ax ay]
      | true =>
        have ay : val C y a=true := eq.symm.trans ax
        have bx : val C x b=false := by simpa [ax] using hx
        have by' : val C y b=false := by simpa [ay] using hy
        simp [ih b bi bx by']
    · rw [hor] at hx hy ⊢
      simp only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_false_iff] at hx hy ⊢
      exact ⟨ih a ai hx.1 hy.1,ih b bi hx.2 hy.2⟩

theorem input_union {N} (P Q L M : Finset (Fin N)) (i : Fin (N+N)) :
    input (P∪Q) (L∪M) i = (input P L i || input Q M i) := by
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp [input_l,Finset.mem_union]
  · intro l
    rw [input_r,input_r,input_r]; simp [Finset.mem_union]

open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover Finset
theorem induced_cost {N q d : Nat} (I : Fin N → Fin N → Prop) (C : Circuit) (ao : IsAO2 (N+N) C)
    (a b : Fin d → Fin N) (lim : d≤q) (ind : ∀ i j,I (a i) (b j) → i=j)
    (on : ∀ i,wireVal (N+N) C C.output (fun r => decide (r=Fin.castAdd N (a i) ∨ r=Fin.natAdd N (b i)))=true)
    (off : ∀ x : Fin (N+N) → Bool,Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q →
      (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → wireVal (N+N) C C.output x=false) :
    d ≤ (ands C).card := by
  classical
  have mon : Monotone2 C := fun g hg => ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,
    (ao.2.2 g hg).le⟩
  have shape (j : Nat) (g : Gate) (hg : C.gates[j]?=some g) :
      ∃ r s : Nat, g.inputs=[r,s] ∧ r<N+N+j ∧ s<N+N+j := by
    obtain ⟨hj,eq⟩ := List.getElem?_eq_some_iff.mp hg
    have gg : gateAt C j=g := by simp [gateAt,List.getD,hg]
    obtain ⟨r,s,ab⟩ := List.length_eq_two.mp (ao.2.2 g (List.mem_of_getElem? hg))
    have pre := ao.2.1 j hj
    rw [gg,ab] at pre
    exact ⟨r,s,ab,pre r (by simp),pre s (by simp)⟩
  let P (t : Finset (Fin d)) := t.image a
  let L (t : Finset (Fin d)) := (univ\t).image b
  let row (t : Finset (Fin d)) := input (P t) (L t)
  have neg (t : Finset (Fin d)) : val C (row t) C.output=false := by
    apply off
    · have sz : (L t).card≤d := card_image_le.trans ((card_le_card (subset_univ _)).trans_eq (by simp))
      have cardeq : (univ.filter (fun l : Fin N => row t (Fin.natAdd N l)=true)).card=(L t).card := by
        congr 1
        ext l
        simp only [mem_filter,mem_univ,true_and,row,input_r,decide_eq_true_eq]
      rw [Fintype.card_subtype,cardeq]
      exact sz.trans lim
    · rintro ⟨p,l,hit,px,lx⟩
      rw [show row t (Fin.castAdd N p)=_ from input_l (P t) (L t) p] at px
      rw [show row t (Fin.natAdd N l)=_ from input_r (P t) (L t) l] at lx
      obtain ⟨i,it,rfl⟩ := mem_image.mp (of_decide_eq_true px)
      obtain ⟨j,jt,rfl⟩ := mem_image.mp (of_decide_eq_true lx)
      exact (mem_sdiff.mp jt).2 ((ind i j hit) ▸ it)
  let tag (t : Finset (Fin d)) : Finset (Fin C.gates.length) := choices C (row t)
  have encode : (univ : Finset (Fin d)).powerset.card≤(ands C).powerset.card := by
    apply card_le_card_of_injOn tag
    · intro t _
      exact mem_powerset.mpr (filter_subset _ _)
    · intro s _ t _ same
      have zero := union_false C mon shape (row s) (row t) (input (P s ∪ P t) (L s ∪ L t))
        (fun i => input_union _ _ _ _ i) same C.output (neg s) (neg t)
      have impossible (i : Fin d) (inP : i∈s ∨ i∈t) (inL : i∉s ∨ i∉t) : False := by
        have pin : a i ∈ P s ∪ P t := mem_union.mpr (inP.imp (mem_image_of_mem _) (mem_image_of_mem _))
        have ln {k : Finset (Fin d)} (no : i∉k) : b i∈L k := mem_image_of_mem _ (mem_sdiff.mpr ⟨mem_univ _,no⟩)
        have lin : b i∈L s ∪ L t := mem_union.mpr (inL.imp ln ln)
        have yes : val C (input (P s ∪ P t) (L s ∪ L t)) C.output=true := by
          apply acts_mono mon _ _ (on i)
          intro z h
          rcases of_decide_eq_true h with rfl|rfl
          · exact (input_l ..).trans (decide_eq_true pin)
          · exact (input_r ..).trans (decide_eq_true lin)
        rw [zero] at yes
        cases yes
      ext i
      constructor
      · intro is
        by_contra no
        exact impossible i (.inl is) (.inr no)
      · intro it
        by_contra no
        exact impossible i (.inr it) (.inl no)
  simp only [card_powerset,card_univ,Fintype.card_fin] at encode
  by_contra! bad
  have strict := Nat.pow_lt_pow_right (by decide : 1<2) bad
  omega
end PEqualNP.Outside.L_meta_8869.Certificate

namespace PEqualNP.Outside.L_meta_8869
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge Finset

abbrev pair {n : Nat} (e : Fin n × Fin n) (r : Fin (n+n)) := decide (r=Fin.castAdd n e.1 ∨ r=Fin.natAdd n e.2)
abbrev quiet {n : Nat} (q : Nat) (R : Fin n → Fin n → Prop) (C : Circuit) := ∀ x : Fin (n+n) → Bool,
  Fintype.card {l : Fin n // x (Fin.natAdd n l)=true} ≤ q →
    (¬∃ p l,R p l ∧ x (Fin.castAdd n p)=true ∧ x (Fin.natAdd n l)=true) → wireVal (n+n) C C.output x=false

theorem single_off {n q : Nat} {R : Fin n → Fin n → Prop} {C : Circuit} (hq : 1≤q) (sound : quiet q R C)
    (v : Fin (n+n)) : wireVal (n+n) C C.output (fun r => decide (r=v))=false := by
  apply sound
  · apply le_trans _ hq
    apply Fintype.card_le_one_iff_subsingleton.mpr
    constructor
    intro a b
    apply Subtype.ext
    exact Fin.natAdd_injective _ _ ((of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm)
  · rintro ⟨p,l,_,hv,hw⟩
    have eq := (of_decide_eq_true hv).trans (of_decide_eq_true hw).symm
    have h : p.val=n+l.val := congrArg Fin.val eq
    have := p.isLt
    omega


open PEqualNP.MetaComplexity
private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private def run (gs : List Gate) (xs : List Bool) : List Bool :=
  evalFrom false GateOp.eval gs xs

private lemma run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++ [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
  simp [run, evalFrom, List.foldl_append]

private lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length :=
  evalFrom_length false GateOp.eval gs xs

private lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (run gs x).length = j := by simp [run_length, hx, j]
    have ey : (run gs y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem essential_bits {n : Nat} (C : Circuit) (ao : IsAO2 n C) (I : Finset (Fin n))
    (sens : ∀ i∈I,∃ x y : Fin n → Bool,(∀ j,j≠i → x j=y j) ∧ wireVal n C C.output x≠wireVal n C C.output y) :
    I.card≤C.size+1 := by
  obtain ⟨S,hS,hs⟩ := supports n C.gates (fun g hg => (ao.2.2 g hg).le) {C.output}
  have sub : I.image Fin.val ⊆ S := by
    rintro _ hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    by_contra miss
    obtain ⟨x,y,agree,ne⟩ := sens i hi
    apply ne
    apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
    intro j hj
    by_cases bound : j<n
    · rw [List.getD_eq_getElem _ _ (by simpa using bound),List.getD_eq_getElem _ _ (by simpa using bound)]
      simp only [List.getElem_ofFn]
      apply agree
      intro eq
      have e : j=i.val := congrArg Fin.val eq
      exact miss (e ▸ hj)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt bound),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt bound)]
  have card := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at card
  simpa only [Finset.card_singleton, Nat.add_comm 1,Circuit.size] using card.trans hS

theorem shores {n q : Nat} (R : Fin n → Fin n → Prop) (C : Circuit) (E : Finset (Fin n × Fin n))
    (hq : 1≤q) (ao : IsAO2 (n+n) C) (sound : quiet q R C)
    (on : ∀ e∈E,wireVal (n+n) C C.output (pair e)=true) :
    (E.image Prod.fst).card + (E.image Prod.snd).card ≤ C.size+1 := by
  classical
  let P := (E.image Prod.fst).image (Fin.castAdd n)
  let L := (E.image Prod.snd).image (Fin.natAdd n)
  have dis : Disjoint P L := by
    rw [Finset.disjoint_left]
    intro u hp hl
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨l,_,bad⟩ := Finset.mem_image.mp hl
    have eq := congrArg Fin.val bad
    change n+l.val=p.val at eq
    omega
  have all := essential_bits C ao (P ∪ L) (by
    intro i hi
    rcases Finset.mem_union.mp hi with pin|lin
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp pin
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
      refine ⟨pair e,fun r => decide (r=Fin.natAdd n e.2),?_,?_⟩
      · intro j ne
        simp only [pair,ne,false_or,or_false]
      · rw [on e he,single_off hq sound]
        decide
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp lin
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
      refine ⟨pair e,fun r => decide (r=Fin.castAdd n e.1),?_,?_⟩
      · intro j ne
        simp only [pair,ne,false_or,or_false]
      · rw [on e he,single_off hq sound]
        decide)
  rw [Finset.card_union_of_disjoint dis] at all
  have pc : P.card=(E.image Prod.fst).card := card_image_of_injective _ (Fin.castAdd_injective n n)
  have lc : L.card=(E.image Prod.snd).card := card_image_of_injective _ (Fin.natAdd_injective n n)
  simpa only [pc,lc] using all

end PEqualNP.Outside.L_meta_8869
namespace PEqualNP.Outside.L_meta_8869
open Finset PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge

theorem and_price {n q k : Nat} (R : Fin n → Fin n → Prop) [DecidableRel R] (C : Circuit)
    (E : Finset (Fin n × Fin n)) (lim : k+1≤q)
    (linear : ∀ p t,p≠t → ∃! l,R p l ∧ R t l) (ao : IsAO2 (n+n) C) (sound : quiet q R C)
    (on : ∀ e∈E,R e.1 e.2 ∧ wireVal (n+n) C C.output (pair e)=true)
    (few : (Certificate.ands C).card≤k) : E.card≤k*C.size := by
  classical
  have four : Matching.Linear R := by
    intro a a' b b' ne hab hab' h'ab h'ab'
    obtain ⟨_,_,only⟩ := linear a a' ne
    exact (only b ⟨hab,h'ab⟩).trans (only b' ⟨hab',h'ab'⟩).symm
  have no : ¬Matching.Induced R E (k+1) := by
    rintro ⟨a,b,yes,mat⟩
    have bound := Certificate.induced_cost R C ao a b lim mat (fun i => (on _ (yes i)).2) sound
    omega
  let P := E.image Prod.fst
  let L := E.image Prod.snd
  have upper := Matching.peel R four k E P L (fun e he => mem_product.mpr
    ⟨mem_image_of_mem _ he,mem_image_of_mem _ he⟩) (fun e he => (on _ he).1) no
  have count := shores R C E (by omega : 1≤q) ao sound (fun e he => (on _ he).2)
  change P.card+L.card≤C.size+1 at count
  exact upper.trans (Nat.mul_le_mul_left k (by omega))

theorem eight_ands {n q : Nat} (R : Fin n → Fin n → Prop) [DecidableRel R] (C : Circuit)
    (E : Finset (Fin n × Fin n)) (large : 9≤q)
    (linear : ∀ p t,p≠t → ∃! l,R p l ∧ R t l) (ao : IsAO2 (n+n) C) (sound : quiet q R C)
    (on : ∀ e∈E,R e.1 e.2 ∧ wireVal (n+n) C C.output (pair e)=true)
    (few : (Certificate.ands C).card≤8) : E.card≤8*C.size :=
  and_price R C E large linear ao sound on few
end PEqualNP.Outside.L_meta_8869
