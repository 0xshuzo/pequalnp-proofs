import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7263.Research

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Vertex := Fin 10
abbrev Assignment := Vertex → Bool

def pet (x : Assignment) : Bool :=
  (List.finRange 5).any fun i =>
    x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) ||
    x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
    x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))

def edge (i j : Vertex) : Bool :=
  (([50,69,138,276,521,385,770,548,104,208] : List Nat).getD i.val 0).testBit j.val

def one (i : Vertex) : Assignment := fun j => decide (j=i)
def two (i j : Vertex) : Assignment := fun k => decide (k=i ∨ k=j)

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem graph_geometry :
    (∀ i j, pet (two i j) = edge i j) ∧
    (∀ i, pet (one i) = false) ∧
    (∀ i j, (List.ofFn (two i j)).count true ≤ 2) ∧
    (∀ i j, edge i j = false → ∃ t, edge i t = true ∧ edge j t = true) ∧
    (∀ a b c d : Vertex, a ≠ b → c ≠ d → edge a c = true → edge a d = true →
      edge b c = true → edge b d = true → False) := by decide +kernel

lemma both_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

def promise (P : Assignment → Bool) : Prop :=
  ∀ x, pet x = false ∨ (List.ofFn x).count true ≤ 2 → P x = pet x

/-- Positive sensitivity from the singleton at a neighbor to the corresponding
    edge. Both rows are fixed by the promise. -/
def senses (A : Assignment → Bool) (i : Vertex) : Prop :=
  ∃ t : Vertex, edge i t = true ∧ A (one t) = false ∧ A (two i t) = true

lemma exceptions (R : Vertex → Prop) :
    (∃ i : Vertex, ∀ j, j ≠ i → R j) ∨
    ∃ i j : Vertex, i ≠ j ∧ ¬R i ∧ ¬R j := by
  classical
  by_cases all : ∀ i, R i
  · exact Or.inl ⟨0,fun j _ => all j⟩
  push_neg at all
  obtain ⟨i, hi⟩ := all
  by_cases rest : ∀ j, j ≠ i → R j
  · exact Or.inl ⟨i,rest⟩
  push_neg at rest
  obtain ⟨j,hj,missing⟩ := rest
  exact Or.inr ⟨i,j,Ne.symm hj,hi,missing⟩

/-- The exceptional vertex sets for the two factors span a complete
    bipartite subgraph of Petersen. Consequently one factor is positively
    sensitive on at least nine of the ten variables. -/
theorem factor_sensitivity (A B : Assignment → Bool) (agree : promise (fun x => A x && B x)) :
    (∀ i j, ¬senses A i → ¬senses B j → edge i j = true) ∧
    ((∃ i : Vertex, ∀ j, j ≠ i → senses A j) ∨ (∃ i : Vertex, ∀ j, j ≠ i → senses B j)) := by
  obtain ⟨pairVal, singleVal, pairSize, common, noSquare⟩ := graph_geometry
  have pairOn (i t : Vertex) (it : edge i t = true) :
      A (two i t) = true ∧ B (two i t) = true := by
    apply both_true
    exact (agree _ (Or.inr (pairSize i t))).trans ((pairVal i t).trans it)
  have cross (i j : Vertex) (hi : ¬senses A i) (hj : ¬senses B j) : edge i j = true := by
    cases h : edge i j with
    | true => rfl
    | false =>
      obtain ⟨t,it,jt⟩ := common i j h
      have atOne : A (one t) = true := by
        cases z : A (one t) with
        | true => rfl
        | false => exact (hi ⟨t,it,z,(pairOn i t it).1⟩).elim
      have btOne : B (one t) = true := by
        cases z : B (one t) with
        | true => rfl
        | false => exact (hj ⟨t,jt,z,(pairOn j t jt).2⟩).elim
      have impossible := (agree (one t) (Or.inl (singleVal t))).trans (singleVal t)
      change (A (one t) && B (one t)) = false at impossible
      simp [atOne,btOne] at impossible
  refine ⟨cross,?_⟩
  rcases exceptions (senses A) with hit | ⟨a,b,ab,ha,hb⟩
  · exact Or.inl hit
  rcases exceptions (senses B) with hit | ⟨c,d,cd,hc,hd⟩
  · exact Or.inr hit
  exact (noSquare a b c d ab cd (cross a c ha hc) (cross a d ha hd)
    (cross b c hb hc) (cross b d hb hd)).elim

def move (i j v : Vertex) : Vertex :=
  let code := ([0x0,0x0,0x8253761049,0x3528740169,0x0,0x0,0x5180672349,0x5308472169,0x2031475869,0x251743869,0x0,0x0,0x0,0x2537810496,0x5287301694,0x2517038694,0x0,0x5207183496,0x3024185796,0x354812796,0x2873516940,0x0,0x0,0x0,0x5378204961,0x3548027961,0x5170286943,0x0,0x8065134972,0x845316972,0x3782549610,0x8735269401,0x0,0x0,0x0,0x8453069721,0x5480379612,0x5608179432,0x0,0x651849723,0x0,0x7825396104,0x7352894016,0x0,0x0,0x6518097234,0x4530897216,0x4203197586,0x7025194386,0x0,0x0,0x8765932104,0x3742985016,0x2473910586,0x5678901234,0x0,0x5470983216,0x0,0x0,0x745912386,0x6789512340,0x0,0x7659821043,0x6489310572,0x4739205861,0x7459023861,0x0,0x4609138572,0x0,0x0,0x7392458610,0x7895623401,0x0,0x6598710432,0x4893605721,0x0,0x4590738612,0x0,0x6091485723,0x0,0x8936457210,0x3984627501,0x8956734012,0x0,0x5987604321,0x0,0x0,0x5907486123,0x0,0x954716832,0x9876543210,0x9374268501,0x9846375012,0x9567840123,0x0,0x9547068321,0x0,0x0,0x9064175832,0x0] : List Nat).getD (10*i.val+j.val) 0
  Fin.ofNat 10 ((code >>> (4*v.val)) % 16)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem moving_data : ∀ i j : Vertex, i ≠ j → edge i j = false →
    Function.Injective (move i j) ∧ move i j i = 9 ∧ move i j j = 0 ∧
    ∀ a b, edge (move i j a) (move i j b) = edge a b := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem sample_data :
    (∀ x : Assignment, pet x = true ↔ ∃ a b, edge a b = true ∧ x a = true ∧ x b = true) ∧
    (∀ i j : Vertex, i ≠ j → ∀ r s : Bool, (r && s) = false ∨ edge i j = true →
      ∃ a b, edge a b = true ∧ two a b i = r ∧ two a b j = s) := by decide +kernel

def nonedgeCofactor : Circuit :=
  ⟨[⟨.or,[1,3]⟩, ⟨.and,[2,9]⟩, ⟨.or,[3,5]⟩, ⟨.and,[8,11]⟩,
    ⟨.or,[10,12]⟩, ⟨.or,[13,4]⟩, ⟨.or,[14,6]⟩, ⟨.or,[15,7]⟩,
    ⟨.not,[0]⟩, ⟨.and,[16,17]⟩],18⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem cofactor_data : FanInTwo nonedgeCofactor ∧ nonedgeCofactor.size = 10 ∧
    ∀ y : Fin 9 → Bool, nonedgeCofactor.eval (List.ofFn y) =
      (pet (Fin.lastCases true y) && !y 0) := by
  refine ⟨?_,rfl,?_⟩
  · intro g hg
    simp [nonedgeCofactor] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · decide +kernel

def desired (P : Assignment → Bool) : Prop :=
  ∃ (σ : Equiv.Perm Vertex) (t : Bool) (D : Circuit),
    (∀ x, pet (x ∘ σ) = pet x) ∧ FanInTwo D ∧ D.size ≤ (if t then 10 else 15) ∧
    ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = P ((Fin.lastCases t y : Assignment) ∘ σ)

theorem move_correct (σ : Equiv.Perm Vertex)
    (hσ : ∀ a b, edge (σ a) (σ b) = edge a b) : ∀ x, pet (x ∘ σ) = pet x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [sample_data.1, sample_data.1]
  constructor
  · rintro ⟨a,b,ab,xa,xb⟩
    exact ⟨σ a,σ b,(hσ a b).trans ab,xa,xb⟩
  · rintro ⟨a,b,ab,xa,xb⟩
    obtain ⟨a',rfl⟩ := σ.surjective a
    obtain ⟨b',rfl⟩ := σ.surjective b
    exact ⟨a',b',(hσ a' b').symm.trans ab,xa,xb⟩

theorem guarded_nonedge_minor (P : Assignment → Bool) (u v : Vertex) (uv : u ≠ v)
    (nonedge : edge u v = false) (shape : ∀ x, P x = (pet x && !(x u && x v))) : desired P := by
  obtain ⟨inj,hu,hv,adj⟩ := moving_data u v uv nonedge
  let σ : Equiv.Perm Vertex := Equiv.ofBijective (move u v) ((Finite.injective_iff_bijective).mp inj)
  have aut : ∀ x, pet (x ∘ σ) = pet x := move_correct σ adj
  obtain ⟨fan,sz,ev⟩ := cofactor_data
  refine ⟨σ,true,nonedgeCofactor,aut,fan,by simpa [sz],?_⟩
  intro y
  rw [shape, aut, ev]
  change _ = (_ && !(Fin.lastCases true y (move u v u) && Fin.lastCases true y (move u v v)))
  rw [hu,hv] <;> rfl

/-- A factor supported on two variables is their NAND on the only
    nonconstant feasible case. If the other factor is monotone on the
    edge-positive rows, the posted small cofactor follows. -/
theorem two_variable_factor (A B : Assignment → Bool) (agree : promise (fun x => A x && B x))
    (off : ∃ x, A x = false) (dominates : ∀ x, pet x = true → B x = true)
    (u v : Vertex) (uv : u ≠ v) (f : Bool → Bool → Bool)
    (support : ∀ x, A x = f (x u) (x v)) : desired (fun x => A x && B x) := by
  have phi : ∀ r s : Bool, (r && s) = false ∨ edge u v = true → f r s = true := by
    intro r s hrs
    obtain ⟨a,b,ab,ar,bs⟩ := sample_data.2 u v uv r s hrs
    have z := (agree (two a b) (Or.inr (graph_geometry.2.2.1 a b))).trans
      ((graph_geometry.1 a b).trans ab)
    have onA := (both_true z).1
    rwa [support,ar,bs] at onA
  obtain ⟨w,hw⟩ := off
  rw [support] at hw
  have nonedge : edge u v = false := by
    cases e : edge u v with
    | false => rfl
    | true =>
      have clash := phi (w u) (w v) (Or.inr e)
      rw [hw] at clash
      cases clash
  have f11 : f true true = false := by
    cases wu : w u <;> cases wv : w v <;> rw [wu,wv] at hw
    · rw [phi false false (Or.inl rfl)] at hw; cases hw
    · rw [phi false true (Or.inl rfl)] at hw; cases hw
    · rw [phi true false (Or.inl rfl)] at hw; cases hw
    · exact hw
  have form (x : Assignment) : A x = !(x u && x v) := by
    rw [support]
    cases x u <;> cases x v
    · exact phi false false (Or.inl rfl)
    · exact phi false true (Or.inl rfl)
    · exact phi true false (Or.inl rfl)
    · exact f11
  apply guarded_nonedge_minor _ u v uv nonedge
  intro x
  cases e : pet x with
  | false => simpa [e] using agree x (Or.inl e)
  | true => simp [dominates x e,form]

/-- Every monotone opposite factor satisfies the required domination. -/
theorem dominates_of_mono (A B : Assignment → Bool) (agree : promise (fun x => A x && B x))
    (mono : ∀ y x : Assignment, (∀ v, y v = true → x v = true) → B y = true → B x = true) :
    ∀ x, pet x = true → B x = true := by
  intro x pos
  obtain ⟨a,b,ab,xa,xb⟩ := (sample_data.1 x).mp pos
  have hit := (agree (two a b) (Or.inr (graph_geometry.2.2.1 a b))).trans
    ((graph_geometry.1 a b).trans ab)
  apply mono (two a b) x _ (both_true hit).2
  intro q hq
  simp only [two,decide_eq_true_eq] at hq
  rcases hq with rfl | rfl <;> assumption

end PEqualNP.Outside.L_meta_7263.Research

namespace PetersenRestriction
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

abbrev Stat := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def inserted (p : Equiv.Perm (Fin 10)) (v : Bool) (y : Fin 9 → Bool) : Fin 10 → Bool :=
  (Fin.lastCases v y : Fin 10 → Bool) ∘ p

def restrictedWire (D : Circuit) (p : Equiv.Perm (Fin 10)) (v : Bool) (i : ℕ) (y : Fin 9 → Bool) :=
  (D.wires (List.ofFn (inserted p v y))).getD i false

def prefixW (D : Circuit) (p : Equiv.Perm (Fin 10)) (v : Bool) (j : ℕ) (y : Fin 9 → Bool) :=
  wiresFrom (D.gates.take j) (List.ofFn (inserted p v y))

lemma prefix_len {D : Circuit} {p v j y} (hj : j ≤ D.size) :
    (prefixW D p v j y).length = 10+j := by
  simp [prefixW,length_wiresFrom,Nat.min_eq_left (show j ≤ D.gates.length from hj)]

lemma prefix_old {D : Circuit} {p v j y i} (hj : j ≤ D.size) (hi : i < 10+j) :
    (prefixW D p v j y).getD i false = restrictedWire D p v i y := by
  change _ = (wiresFrom D.gates (List.ofFn (inserted p v y))).getD i false
  rw [←List.take_append_drop j D.gates,wiresFrom_append]
  symm
  apply getD_wiresFrom
  change i < (prefixW D p v j y).length
  rwa [prefix_len hj]

lemma inv_record {y w acc} {s : Stat} {t : Bool} (h : Inv 9 y w acc)
    (hv : s.Valid (9+acc.2.length)) (he : s.val (wiresFrom acc.2 y) = t) :
    Inv 9 y (w++[t]) (acc.1++[s],acc.2) := by
  refine ⟨by simp [h.1],?_⟩
  intro i
  by_cases hi : i=w.length
  · subst i
    rw [getD_snoc_len _ _ _ _ h.1,getD_snoc_eq]
    exact ⟨hv,he⟩
  · rw [getD_snoc_ne _ _ _ _ (by rw [h.1]; exact hi),getD_snoc_ne _ _ _ _ hi]
    exact h.2 i

def initialStatus (p : Equiv.Perm (Fin 10)) (v : Bool) (i : Fin 10) : Stat :=
  if (p i).val < 9 then Sum.inr (p i).val else Sum.inl v

lemma initialStatus_sound (p : Equiv.Perm (Fin 10)) (v : Bool) (y : Fin 9 → Bool) :
    Inv 9 (List.ofFn y) (List.ofFn (inserted p v y)) (List.ofFn (initialStatus p v),[]) := by
  refine ⟨by simp,?_⟩
  intro j
  by_cases hj : j < 10
  · let i : Fin 10 := ⟨j,hj⟩
    have hs : (List.ofFn (initialStatus p v)).getD j (Sum.inl false) = initialStatus p v i := by
      rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
    have hx : (List.ofFn (inserted p v y)).getD j false = inserted p v y i := by
      rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
    rw [hs,hx]
    change (if (p i).val < 9 then Sum.inr (p i).val else Sum.inl v : Stat).Valid 9 ∧
      Stat.val (List.ofFn y) (if (p i).val < 9 then Sum.inr (p i).val else Sum.inl v) =
        Fin.lastCases v y (p i)
    generalize p i = t
    refine Fin.lastCases ?_ (fun t => ?_) t
    · rw [Fin.lastCases_last]
      exact ⟨trivial,rfl⟩
    · rw [Fin.lastCases_castSucc]
      simp only [Fin.val_castSucc, if_pos t.isLt]
      refine ⟨t.isLt,?_⟩
      change (List.ofFn y).getD t.val false = y t
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using t.isLt),List.getElem_ofFn]
  · have hs : (List.ofFn (initialStatus p v)).getD j (Sum.inl false) = Sum.inl false :=
      List.getD_eq_default _ _ (by simp; omega)
    have hx : (List.ofFn (inserted p v y)).getD j false = false :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [hs,hx]
    exact ⟨trivial,rfl⟩

lemma compress_columns (D : Circuit) (p : Equiv.Perm (Fin 10)) (v : Bool) (K : Finset ℕ)
    (fan : FanInTwo D)
    (rep : ∀ j < D.size, j ∉ K →
      (∃ t : Bool, restrictedWire D p v (10+j) = fun _ => t) ∨
      ∃ i < 10+j, restrictedWire D p v (10+j) = restrictedWire D p v i) :
    HasCircuitSize 9 (fun y => D.eval (List.ofFn (inserted p v y))) (max K.card 1) := by
  classical
  have build (j : ℕ) (hj : j ≤ D.size) : ∃ acc : List Stat × List Gate,
      (∀ g ∈ acc.2, Ok g) ∧ acc.2.length ≤ ((Finset.range j) ∩ K).card ∧
      ∀ y, Inv 9 (List.ofFn y) (prefixW D p v j y) acc := by
    induction j with
    | zero =>
      exact ⟨(List.ofFn (initialStatus p v),[]),by simp,by simp,initialStatus_sound p v⟩
    | succ j ih =>
      have hlt : j < D.gates.length := hj
      let g := D.gates[j]
      have gok : Ok g := fan g (List.getElem_mem _)
      obtain ⟨acc,leg,len,inv⟩ := ih (by omega)
      let next (y : Fin 9 → Bool) := g.op.eval (g.inputs.map (fun i => (prefixW D p v j y).getD i false))
      have step (y : Fin 9 → Bool) : prefixW D p v (j+1) y = prefixW D p v j y ++ [next y] := by
        unfold prefixW
        rw [List.take_succ_eq_append_getElem hlt,wiresFrom_append] <;> rfl
      by_cases mem : j ∈ K
      · let B := elim 9 [g] acc
        refine ⟨B,elim_ok 9 [g] _ leg,?_,?_⟩
        · have hl := elim_len 9 [g] acc
          have hc : ((Finset.range (j+1)) ∩ K).card = ((Finset.range j) ∩ K).card+1 := by
            have eq : Finset.range (j+1) ∩ K = insert j (Finset.range j ∩ K) := by
              ext k
              simp only [Finset.mem_inter,Finset.mem_range,Finset.mem_insert]
              constructor
              · rintro ⟨lt,inside⟩
                by_cases h : k = j
                · exact Or.inl h
                · exact Or.inr ⟨by omega, inside⟩
              · rintro (rfl | ⟨lt, inside⟩)
                · exact ⟨by omega, mem⟩
                · exact ⟨by omega, inside⟩
            rw [eq,Finset.card_insert_of_notMem (by simp)]
          change (elim 9 [g] acc).2.length ≤ _
          simp only [List.length_singleton] at hl
          omega
        · intro y
          rw [step]
          exact inv_elim 9 _ (by simp) [g] _ _ (by simpa using gok) (inv y)
      · have hc : ((Finset.range (j+1)) ∩ K) = ((Finset.range j) ∩ K) := by
          ext k
          simp only [Finset.mem_inter,Finset.mem_range]
          constructor <;> rintro ⟨a,b⟩
          · have ne : k ≠ j := fun eq => mem (eq ▸ b)
            exact ⟨by omega,b⟩
          · exact ⟨by omega,b⟩
        have col (y : Fin 9 → Bool) : next y = restrictedWire D p v (10+j) y := by
          rw [←prefix_old hj (by omega),step,getD_snoc_len _ _ _ _ (prefix_len (by omega))]
        obtain ⟨t,ct⟩ | ⟨i,hi,eq⟩ := rep j hlt mem
        · refine ⟨(acc.1++[Sum.inl t],acc.2),leg,hc.symm ▸ len,?_⟩
          intro y
          rw [step]
          apply inv_record (s := Sum.inl t) (inv y) trivial
          exact ((col y).trans (congrFun ct y)).symm
        · let s := acc.1.getD i (Sum.inl false)
          refine ⟨(acc.1++[s],acc.2),leg,hc.symm ▸ len,?_⟩
          intro y
          rw [step]
          have hs := (inv y).2 i
          apply inv_record (inv y) hs.1
          exact hs.2.trans ((prefix_old (by omega) hi).trans ((congrFun eq y).symm.trans (col y).symm))
  obtain ⟨acc,leg,len,inv⟩ := build D.size (by omega)
  have hvalue (y : Fin 9 → Bool) :
      (acc.1.getD D.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        D.eval (List.ofFn (inserted p v y)) := by
    have hw := ((inv y).2 D.output).2
    simpa [prefixW,Circuit.size,Circuit.eval,Circuit.wires,wiresFrom] using hw
  have count : acc.2.length ≤ K.card := le_trans len (Finset.card_le_card Finset.inter_subset_right)
  cases hx : acc.1.getD D.output (Sum.inl false) with
  | inr wire =>
    refine ⟨⟨acc.2,wire⟩,leg,le_trans count (le_max_left _ _),?_⟩
    intro y
    have hv := hvalue y
    rw [hx] at hv
    exact hv
  | inl t =>
    let gate : Gate := ⟨if t then .and else .or,[]⟩
    refine ⟨⟨[gate],9⟩,?_,le_max_right _ _,?_⟩
    · intro g hg
      obtain rfl := List.mem_singleton.mp hg
      cases t <;> simp [gate]
    · intro y
      change _ = D.eval (List.ofFn (inserted p v y))
      rw [←hvalue y, hx]
      change (List.ofFn y ++ [gate.op.eval []]).getD 9 false = t
      rw [getD_snoc_len _ _ _ _ List.length_ofFn]
      cases t <;> rfl


end PetersenRestriction

namespace PEqualNP.Outside.L_meta_7263.Research

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PetersenRestriction

abbrev Nine := Fin 9 → Bool

def wire (C : Circuit) (i : Nat) (x : Assignment) : Bool :=
  (C.wires (List.ofFn x)).getD i false

/-- A gate can be omitted when its entire restricted column is constant or
agrees with an earlier wire on all 512 rows. -/
def removable (C : Circuit) (p : Equiv.Perm Vertex) (j : Nat) : Prop :=
  (∃ t : Bool, restrictedWire C p false (10+j) = fun _ => t) ∨
  ∃ i < 10+j, restrictedWire C p false (10+j) = restrictedWire C p false i

def before (C : Circuit) (p : Equiv.Perm Vertex) (j i : Nat) (y : Nine) : Bool :=
  (prefixW C p false j y).getD i false

theorem at_gate (C : Circuit) (p : Equiv.Perm Vertex) (j : Nat) (hj : j < C.gates.length)
    (y : Nine) : restrictedWire C p false (10+j) y =
      C.gates[j].op.eval (C.gates[j].inputs.map (fun i => before C p j i y)) := by
  rw [←prefix_old (j := j+1) (by change j+1 ≤ C.gates.length; omega) (by omega)]
  have step : prefixW C p false (j+1) y = prefixW C p false j y ++
      [C.gates[j].op.eval (C.gates[j].inputs.map (fun i => before C p j i y))] := by
    unfold prefixW
    rw [List.take_succ_eq_append_getElem hj,wiresFrom_append] <;> rfl
  rw [step,getD_snoc_len _ _ _ _ (prefix_len (Nat.le_of_lt hj))]

theorem before_raw (C : Circuit) (p : Equiv.Perm Vertex) (j : Nat) (u : Vertex) (y : Nine) :
    before C p j u.val y = inserted p false y u := by
  unfold before prefixW
  rw [getD_wiresFrom _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using u.isLt),List.getElem_ofFn]

/-- The auxiliary alternative permits the other input of a binary gate
to be out of range. In that case the original model reads false. -/
theorem removable_before (C : Circuit) (p : Equiv.Perm Vertex) (j i : Nat)
    (hj : j < C.size) (h : ∀ y, restrictedWire C p false (10+j) y = before C p j i y) :
    removable C p j := by
  by_cases hi : i < 10+j
  · exact Or.inr ⟨i,hi,funext fun y => (h y).trans (prefix_old (Nat.le_of_lt hj) hi)⟩
  · refine Or.inl ⟨false,funext fun y => (h y).trans ?_⟩
    apply List.getD_eq_default
    rw [prefix_len (Nat.le_of_lt hj)]
    omega

noncomputable def eff (g : Gate) : List Nat := by
  classical
  exact if g.op = .not then g.inputs.take 1 else g.inputs

theorem reader_removable (C : Circuit) (p : Equiv.Perm Vertex) (j : Nat)
    (hj : j < C.gates.length) (fan : FanInTwo C) (i : Nat) (c : Bool)
    (read : i ∈ eff C.gates[j]) (frozen : ∀ y, before C p j i y = c) :
    removable C p j := by
  let g := C.gates[j]
  have eval := at_gate C p j hj
  change ∀ y, restrictedWire C p false (10+j) y =
    g.op.eval (g.inputs.map (fun i => before C p j i y)) at eval
  change i ∈ eff g at read
  have ok : Ok g := fan _ (List.getElem_mem _)
  obtain ⟨op,ins⟩ := g
  rcases ok with ⟨hop, len⟩
  change ins.length ≤ 2 at len
  change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hop
  rcases hop with rfl | rfl | rfl
  · simp [eff] at read
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d,s⟩⟩⟩
    · simp at read
    · simp at read
      subst i
      exact Or.inl ⟨c,funext fun y => by simpa [GateOp.eval,frozen] using eval y⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at read
      rcases read with rfl | rfl <;> cases c
      · exact Or.inl ⟨false,funext fun y => by simpa [GateOp.eval,frozen] using eval y⟩
      · exact removable_before C p j b hj (fun y => by simpa [GateOp.eval,frozen] using eval y)
      · exact Or.inl ⟨false,funext fun y => by simpa [GateOp.eval,frozen] using eval y⟩
      · exact removable_before C p j a hj (fun y => by simpa [GateOp.eval,frozen] using eval y)
    · simp at len
  · simp [eff] at read
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d,s⟩⟩⟩
    · simp at read
    · simp at read
      subst i
      exact Or.inl ⟨c,funext fun y => by simpa [GateOp.eval,frozen] using eval y⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at read
      rcases read with rfl | rfl <;> cases c
      · exact removable_before C p j b hj (fun y => by simpa [GateOp.eval,frozen] using eval y)
      · exact Or.inl ⟨true,funext fun y => by simpa [GateOp.eval,frozen] using eval y⟩
      · exact removable_before C p j a hj (fun y => by simpa [GateOp.eval,frozen] using eval y)
      · exact Or.inl ⟨true,funext fun y => by simpa [GateOp.eval,frozen] using eval y⟩
    · simp at len
  · rcases ins with _ | ⟨a,s⟩
    · simp [eff] at read
    · simp [eff] at read
      subst i
      exact Or.inl ⟨!c,funext fun y => by simpa [GateOp.eval,frozen] using eval y⟩

theorem true_factor_three (C : Circuit) (a b : Nat) (fan : FanInTwo C) (size : C.size ≤ 18)
    (p : Equiv.Perm Vertex) (aut : ∀ x, pet (x ∘ p) = pet x)
    (unit : ∀ y, restrictedWire C p false a y = true)
    (J : Finset Nat) (hs : J ⊆ Finset.range C.size) (card : 3 ≤ J.card)
    (hj : ∀ j ∈ J, removable C p j) :
    desired (fun x => wire C a x && wire C b x) := by
  let D : Circuit := ⟨C.gates,b⟩
  let K := Finset.range C.size \ J
  have sz : K.card + J.card = C.size := by
    rw [Finset.card_sdiff_of_subset hs]
    have cap := Finset.card_le_card hs
    simp only [Finset.card_range] at cap ⊢
    omega
  have comp := compress_columns D p false K (show FanInTwo D from fan) (by
    intro j lt h
    have hjJ : j ∈ J := by
      by_contra no
      exact h (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr lt,no⟩)
    exact hj j hjJ)
  obtain ⟨E,legal,count,eval⟩ := comp
  refine ⟨p,false,E,aut,legal,?_,?_⟩
  · change E.size ≤ 15
    omega
  · intro y
    rw [eval]
    change _ = (restrictedWire C p false a y && restrictedWire C p false b y)
    rw [unit] <;> rfl

theorem two_readers_nand_minor (C : Circuit) (ga b j k : Nat) (fan : FanInTwo C)
    (size : C.size ≤ 18) (ag : ga < C.size) (jg : j < C.gates.length) (kg : k < C.gates.length)
    (gaj : ga ≠ j) (gak : ga ≠ k) (jk : j ≠ k)
    (u v : Vertex) (uv : u ≠ v) (nonedge : edge u v = false)
    (ra : u.val ∈ eff C.gates[j]) (rb : u.val ∈ eff C.gates[k])
    (nand : ∀ x, wire C (10+ga) x = !(x u && x v)) :
    desired (fun x => wire C (10+ga) x && wire C b x) := by
  obtain ⟨inj,hu,_,adj⟩ := moving_data u v uv nonedge
  let p : Equiv.Perm Vertex := Equiv.ofBijective (move u v) ((Finite.injective_iff_bijective).mp inj)
  have fixed (y : Nine) : inserted p false y u = false := by
    change Fin.lastCases false y (move u v u) = false
    rw [hu] <;> rfl
  have unit (y : Nine) : restrictedWire C p false (10+ga) y = true := by
    change wire C (10+ga) (inserted p false y) = true
    rw [nand,fixed] <;> rfl
  have discard (m : Nat) (hm : m < C.gates.length) (hr : u.val ∈ eff C.gates[m]) :
      removable C p m :=
    reader_removable C p m hm fan u.val false hr (fun y => (before_raw C p m u y).trans (fixed y))
  apply true_factor_three C (10+ga) b fan size p (move_correct p adj) unit {ga,j,k}
  · intro t ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
  · simp [gaj,gak,jk]
  · intro t ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl ⟨true,funext unit⟩
    · exact discard _ jg ra
    · exact discard _ kg rb

end PEqualNP.Outside.L_meta_7263.Research
namespace PEqualNP.Outside.L_meta_7263.Research

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PetersenRestriction

def pre (C : Circuit) (j : Nat) (x : Assignment) :=
  wiresFrom (C.gates.take j) (List.ofFn x)

theorem pre_len (C : Circuit) (j : Nat) (hj : j ≤ C.size) (x : Assignment) :
    (pre C j x).length = 10+j := by
  simp [pre,length_wiresFrom,Nat.min_eq_left (show j ≤ C.gates.length from hj)]

theorem pre_old (C : Circuit) (j : Nat) (hj : j ≤ C.size) (x : Assignment)
    (k : Nat) (hk : k < 10+j) : (pre C j x).getD k false = wire C k x := by
  change _ = (wiresFrom C.gates (List.ofFn x)).getD k false
  rw [←List.take_append_drop j C.gates,wiresFrom_append]
  symm
  apply getD_wiresFrom
  change k < (pre C j x).length
  rwa [pre_len C j hj]

theorem gate_wire (C : Circuit) (j : Nat) (hj : j < C.gates.length) (x : Assignment) :
    wire C (10+j) x = C.gates[j].op.eval (C.gates[j].inputs.map
      (fun i => (pre C j x).getD i false)) := by
  rw [←pre_old C (j+1) (by change j+1 ≤ C.gates.length; omega) x (10+j) (by omega)]
  have step : pre C (j+1) x = pre C j x ++
      [C.gates[j].op.eval (C.gates[j].inputs.map (fun i => (pre C j x).getD i false))] := by
    unfold pre
    rw [List.take_succ_eq_append_getElem hj,wiresFrom_append] <;> rfl
  rw [step,getD_snoc_len _ _ _ _ (pre_len C j (Nat.le_of_lt hj) x)]

theorem wire_raw (C : Circuit) (x : Assignment) (u : Vertex) :
    wire C u.val x = x u := by
  change (wiresFrom C.gates (List.ofFn x)).getD u.val false = x u
  rw [getD_wiresFrom _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using u.isLt),List.getElem_ofFn]

theorem eff_congr (g : Gate) (f h : Nat → Bool) (agree : ∀ i ∈ eff g, f i = h i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map h) := by
  obtain ⟨op,ins⟩ := g
  by_cases hn : op = GateOp.not
  · subst op
    cases ins with
    | nil => rfl
    | cons a s =>
      have ha := agree a (by simp [eff])
      simp [GateOp.eval,ha]
  · have heq : ins.map f = ins.map h := by
      apply List.map_congr_left
      intro i hi
      exact agree i (by simpa [eff,hn] using hi)
    rw [heq]

/-- If two rows differing at a single raw input are distinguished by a
different output, some gate directly reads the changed raw input and its
own output differs on those rows. -/
theorem differing_reader (C : Circuit) (u : Vertex) (x y : Assignment)
    (same : ∀ v, v ≠ u → x v = y v) (b : Nat) (bu : b ≠ u.val)
    (changeB : wire C b x ≠ wire C b y) :
    ∃ j : Nat, ∃ hj : j < C.gates.length, u.val ∈ eff C.gates[j] ∧
      wire C (10+j) x ≠ wire C (10+j) y := by
  by_contra! none
  have eq (j : Nat) (hj : j ≤ C.size) :
      ∀ i < 10+j, i ≠ u.val → wire C i x = wire C i y := by
    induction j with
    | zero =>
      intro i hi ne
      let v : Vertex := ⟨i,by omega⟩
      exact (wire_raw C x v).trans ((same v (fun e => ne (congrArg Fin.val e))).trans
        (wire_raw C y v).symm)
    | succ j ih =>
      have hlt : j < C.gates.length := hj
      have hle : j ≤ C.size := Nat.le_of_lt hlt
      intro i hi ne
      by_cases prev : i < 10+j
      · exact ih hle _ prev ne
      have e : i = 10+j := by omega
      subst i
      by_cases reads : u.val ∈ eff C.gates[j]
      · exact none j hlt reads
      rw [gate_wire C j hlt x,gate_wire C j hlt y]
      apply eff_congr
      intro k hk
      by_cases hprior : k < 10+j
      · rw [pre_old C j hle x k hprior,pre_old C j hle y k hprior]
        exact ih hle _ hprior (by rintro rfl; exact reads hk)
      · rw [List.getD_eq_default _ _ (by rw [pre_len C j hle x]; omega),
            List.getD_eq_default _ _ (by rw [pre_len C j hle y]; omega)]
  apply changeB
  by_cases inBounds : b < 10+C.size
  · exact eq C.size (by rfl) b inBounds bu
  · change (wiresFrom C.gates (List.ofFn x)).getD b false =
      (wiresFrom C.gates (List.ofFn y)).getD b false
    have hxb : (wiresFrom C.gates (List.ofFn x)).length ≤ b := by
      simpa [length_wiresFrom,Circuit.size] using Nat.le_of_not_gt inBounds
    have hyb : (wiresFrom C.gates (List.ofFn y)).length ≤ b := by
      simpa [length_wiresFrom,Circuit.size] using Nat.le_of_not_gt inBounds
    rw [List.getD_eq_default _ _ hxb,List.getD_eq_default _ _ hyb]

set_option maxRecDepth 10000 in
theorem nand_witnesses :
    (∀ u v : Vertex, u ≠ v → edge u v = false →
      ∃ t : Vertex, t ≠ u ∧ t ≠ v ∧ edge u t = true) ∧
    (∀ u : Vertex, ∃ a b : Vertex, edge a b = true ∧ two a b u = false) := by decide +kernel

/-- A shared NAND and positive product give a small cofactor even when the
companion output is signed and unrestricted. -/
theorem shared_product_minor (C : Circuit) (ga gp b : Nat) (fan : FanInTwo C)
    (size : C.size ≤ 18) (ag : ga < C.size) (pg : gp < C.size)
    (u v : Vertex) (uv : u ≠ v) (nonedge : edge u v = false)
    (nand : ∀ x, wire C (10+ga) x = !(x u && x v))
    (prod : ∀ x, wire C (10+gp) x = (x u && x v))
    (agree : promise (fun x => wire C (10+ga) x && wire C b x)) :
    desired (fun x => wire C (10+ga) x && wire C b x) := by
  have pairOn (s t : Vertex) (st : edge s t = true) : wire C b (two s t) = true :=
    (both_true ((agree _ (Or.inr (graph_geometry.2.2.1 s t))).trans
      ((graph_geometry.1 s t).trans st))).2
  have bu : b ≠ u.val := by
    obtain ⟨s,t,st,off⟩ := nand_witnesses.2 u
    rintro rfl
    have impossible := pairOn s t st
    rw [wire_raw,off] at impossible
    cases impossible
  obtain ⟨t,tu,tv,ut⟩ := nand_witnesses.1 u v uv nonedge
  have off1 : one t v = false := by simp [one,Ne.symm tv]
  have off2 : two u t v = false := by simp [two,Ne.symm uv,Ne.symm tv]
  have a1 : wire C (10+ga) (one t) = true := by simp [nand,off1]
  have a2 : wire C (10+ga) (two u t) = true := by simp [nand,off2]
  have p1 : wire C (10+gp) (one t) = false := by simp [prod,off1]
  have p2 : wire C (10+gp) (two u t) = false := by simp [prod,off2]
  have b1 : wire C b (one t) = false := by
    have h := (agree (one t) (Or.inl (graph_geometry.2.1 t))).trans (graph_geometry.2.1 t)
    change (wire C (10+ga) (one t) && wire C b (one t)) = false at h
    simpa [a1] using h
  obtain ⟨j,jg,read,changed⟩ := differing_reader C u (one t) (two u t)
    (fun w hw => by simp [one,two,hw]) b bu (by rw [b1,pairOn _ _ ut]; decide)
  have ja : j ≠ ga := by rintro rfl; exact changed (a1.trans a2.symm)
  have jp : j ≠ gp := by rintro rfl; exact changed (p1.trans p2.symm)
  have ap : ga ≠ gp := by rintro rfl; rw [a1] at p1; cases p1
  obtain ⟨inj,hu,_,adj⟩ := moving_data u v uv nonedge
  let p : Equiv.Perm Vertex := Equiv.ofBijective (move u v) ((Finite.injective_iff_bijective).mp inj)
  have fixed (y : Nine) : inserted p false y u = false := by
    change Fin.lastCases false y (move u v u) = false
    rw [hu] <;> rfl
  have unit (y : Nine) : restrictedWire C p false (10+ga) y = true := by
    change wire C (10+ga) (inserted p false y) = true
    rw [nand,fixed] <;> rfl
  have zero (y : Nine) : restrictedWire C p false (10+gp) y = false := by
    change wire C (10+gp) (inserted p false y) = false
    rw [prod,fixed] <;> rfl
  apply true_factor_three C (10+ga) b fan size p (move_correct p adj) unit {j,ga,gp}
  · intro m hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
  · simp [ja,jp,ap]
  · intro m hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact reader_removable C p _ jg fan u.val false read (fun y => (before_raw C p _ u y).trans (fixed y))
    · exact Or.inl ⟨true,funext unit⟩
    · exact Or.inl ⟨false,funext zero⟩

end PEqualNP.Outside.L_meta_7263.Research
namespace PEqualNP.Outside.L_meta_7263.Research

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PetersenRestriction

/-- If the only initial disagreements belong to S, an observed disagreement
outside S must pass through a changing gate outside S reading S. -/
theorem trace_outside (C : Circuit) (x y : Assignment) (S : Nat → Prop)
    (initial : ∀ i : Vertex, ¬S i.val → x i = y i) (b : Nat) (outside : ¬ S b)
    (different : wire C b x ≠ wire C b y) :
    ∃ j : Nat, ∃ hj : j < C.gates.length, ¬ S (10+j) ∧
      (∃ k ∈ eff C.gates[j], S k) ∧ wire C (10+j) x ≠ wire C (10+j) y := by
  classical
  by_contra none
  have agreement (j : Nat) (hj : j ≤ C.size) :
      ∀ i < 10+j, ¬ S i → wire C i x = wire C i y := by
    induction j with
    | zero =>
      intro i hi hS
      let v : Vertex := ⟨i,by omega⟩
      exact (wire_raw C x v).trans ((initial v hS).trans (wire_raw C y v).symm)
    | succ j ih =>
      have hlt : j < C.gates.length := hj
      have hle : j ≤ C.size := Nat.le_of_lt hlt
      intro i hi hS
      by_cases prev : i < 10+j
      · exact ih hle _ prev hS
      have e : i = 10+j := by omega
      subst i
      by_cases reads : ∃ k ∈ eff C.gates[j], S k
      · by_contra ch
        exact none ⟨j,hlt,hS,reads,ch⟩
      rw [gate_wire C j hlt x,gate_wire C j hlt y]
      apply eff_congr
      intro k hk
      by_cases hprior : k < 10+j
      · rw [pre_old C j hle x k hprior,pre_old C j hle y k hprior]
        exact ih hle _ hprior (fun sk => reads ⟨k,hk,sk⟩)
      · rw [List.getD_eq_default _ _ (by rw [pre_len C j hle x]; omega),
            List.getD_eq_default _ _ (by rw [pre_len C j hle y]; omega)]
  apply different
  by_cases hb : b < 10+C.size
  · exact agreement C.size (le_rfl) b hb outside
  · change (wiresFrom C.gates (List.ofFn x)).getD b false =
      (wiresFrom C.gates (List.ofFn y)).getD b false
    have hxb : (wiresFrom C.gates (List.ofFn x)).length ≤ b := by
      simpa [length_wiresFrom,Circuit.size] using Nat.le_of_not_gt hb
    have hyb : (wiresFrom C.gates (List.ofFn y)).length ≤ b := by
      simpa [length_wiresFrom,Circuit.size] using Nat.le_of_not_gt hb
    rw [List.getD_eq_default _ _ hxb,List.getD_eq_default _ _ hyb]

set_option maxRecDepth 10000 in
theorem anchor_data : ∀ u : Vertex, (∃ t : Vertex, t ≠ u ∧ edge u t = true) ∧
    ∃ v : Vertex, u ≠ v ∧ edge u v = false := by decide +kernel

/-- A factor identically true on a deleted vertex and any second constant
gate suffice. The vertex must still propagate a separate changing signal
to the companion output. -/
theorem frozen_factor_minor (C : Circuit) (a r b : Nat) (fan : FanInTwo C)
    (size : C.size ≤ 18) (ha : a < C.size) (hr : r < C.size) (ar : a ≠ r)
    (u : Vertex) (c : Bool) (unit : ∀ x, x u = false → wire C (10+a) x = true)
    (frozen : ∀ x, x u = false → wire C (10+r) x = c)
    (agree : promise (fun x => wire C (10+a) x && wire C b x)) :
    desired (fun x => wire C (10+a) x && wire C b x) := by
  obtain ⟨⟨t,tu,ut⟩,v,uv,nonedge⟩ := anchor_data u
  have pairOn (k l : Vertex) (kl : edge k l = true) :
      wire C (10+a) (two k l) = true ∧ wire C b (two k l) = true :=
    both_true ((agree _ (Or.inr (graph_geometry.2.2.1 k l))).trans
      ((graph_geometry.1 k l).trans kl))
  have off1 : one t u = false := by simp [one,Ne.symm tu]
  have a1 := unit (one t) off1
  have b1 : wire C b (one t) = false := by
    have h := (agree (one t) (Or.inl (graph_geometry.2.1 t))).trans (graph_geometry.2.1 t)
    change (wire C (10+a) (one t) && wire C b (one t)) = false at h
    simpa [a1] using h
  obtain ⟨k,l,kl,off⟩ := nand_witnesses.2 u
  have bu : b ≠ u.val := by
    intro e
    have z := (pairOn k l kl).2
    rw [e,wire_raw,off] at z
    cases z
  have br : b ≠ 10+r := by
    intro e
    have z := (pairOn k l kl).2
    rw [e, frozen _ off] at z
    have h := b1
    rw [e, frozen _ off1,z] at h
    cases h
  obtain ⟨j,hj,jout,⟨q,read,qsrc⟩,diff⟩ := trace_outside C (one t) (two u t)
    (fun i => i = u.val ∨ i = 10+r)
    (fun w hw => by
      have ne : w ≠ u := fun e => hw (Or.inl (congrArg Fin.val e))
      simp [one,two,ne]) b (fun h => h.elim bu br) (by rw [b1,(pairOn _ _ ut).2]; decide)
  have ja : j ≠ a := by rintro rfl; exact diff (a1.trans (pairOn _ _ ut).1.symm)
  have jr : j ≠ r := by rintro rfl; exact jout (Or.inr rfl)
  obtain ⟨inj,hu,_,adj⟩ := moving_data u v uv nonedge
  let p : Equiv.Perm Vertex := Equiv.ofBijective (move u v) ((Finite.injective_iff_bijective).mp inj)
  have fixed (y : Nine) : inserted p false y u = false := by
    change Fin.lastCases false y (move u v u) = false
    rw [hu] <;> rfl
  have unit' (y : Nine) : restrictedWire C p false (10+a) y = true := unit _ (fixed y)
  have frozen' (y : Nine) : restrictedWire C p false (10+r) y = c := frozen _ (fixed y)
  have remove_j : removable C p j := by
    rcases qsrc with e | e
    · subst q
      exact reader_removable C p _ hj fan u.val false read (fun y => (before_raw C p _ u y).trans (fixed y))
    · subst q
      by_cases earlier : 10+r < 10+j
      · apply reader_removable C p j hj fan (10+r) c read
        intro y
        exact (prefix_old (Nat.le_of_lt hj) earlier).trans (frozen' y)
      · apply reader_removable C p j hj fan (10+r) false read
        intro y
        apply List.getD_eq_default
        rw [prefix_len (Nat.le_of_lt hj)]
        omega
  apply true_factor_three C (10+a) b fan size p (move_correct p adj) unit' {j,a,r}
  · intro m hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
  · simp [ja,jr,ar]
  · intro m hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact remove_j
    · exact Or.inl ⟨true,funext unit'⟩
    · exact Or.inl ⟨c,funext frozen'⟩

end PEqualNP.Outside.L_meta_7263.Research
namespace PEqualNP.Outside.L_meta_7263.Research

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PetersenRestriction

theorem pre_raw (C : Circuit) (j : Nat) (x : Assignment) (u : Vertex) :
    (pre C j x).getD u.val false = x u := by
  unfold pre
  rw [getD_wiresFrom _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using u.isLt),List.getElem_ofFn]

/-- The three physical operations have their usual forcing values when
an effective input is raw. -/
theorem raw_forcing (C : Circuit) (j : Nat) (hj : j < C.gates.length)
    (u : Vertex) (read : u.val ∈ eff C.gates[j]) :
    (C.gates[j].op = .and → ∀ x : Assignment, x u = false → wire C (10+j) x = false) ∧
    (C.gates[j].op = .or → ∀ x : Assignment, x u = true → wire C (10+j) x = true) ∧
    (C.gates[j].op = .not → ∀ x : Assignment, wire C (10+j) x = !(x u)) := by
  constructor
  · intro hand x hx
    rw [gate_wire C j hj x,hand]
    have mem : u.val ∈ C.gates[j].inputs := by simpa [eff,hand] using read
    cases h : GateOp.and.eval (C.gates[j].inputs.map (fun i => (pre C j x).getD i false)) with
    | false => rfl
    | true =>
      change List.all _ id = true at h
      have impos := List.all_eq_true.mp h _ (List.mem_map.mpr ⟨u.val,mem,rfl⟩)
      change (pre C j x).getD u.val false = true at impos
      rw [pre_raw,hx] at impos
      cases impos
  constructor
  · intro hor x hx
    rw [gate_wire C j hj x,hor]
    have mem : u.val ∈ C.gates[j].inputs := by simpa [eff,hor] using read
    apply List.any_eq_true.mpr
    exact ⟨_,List.mem_map.mpr ⟨u.val,mem,rfl⟩,(pre_raw C j x u).trans hx⟩
  · intro hnot x
    rw [gate_wire C j hj x,hnot]
    have mem : u.val ∈ C.gates[j].inputs.take 1 := by simpa [eff,hnot] using read
    cases eq : C.gates[j].inputs with
    | nil => simp [eq] at mem
    | cons a s =>
      have equal : u.val = a := by simpa [eq] using mem
      subst a
      simp only [eq,GateOp.eval,List.map_cons,List.head?_cons,Option.getD_some]
      rw [pre_raw]
      rfl

theorem nand_not_reader (C : Circuit) (ga : Nat) (hg : ga < C.gates.length) (fan : FanInTwo C)
    (u v : Vertex) (uv : u ≠ v) (nand : ∀ x, wire C (10+ga) x = !(x u && x v)) :
    u.val ∉ eff C.gates[ga] := by
  intro read
  obtain ⟨hand,hor,hnot⟩ := raw_forcing C ga hg u read
  have ok := (fan C.gates[ga] (List.getElem_mem _)).1
  change C.gates[ga].op = .and ∨ C.gates[ga].op = .or ∨ C.gates[ga].op = .not at ok
  rcases ok with h | h | h
  · have bad := hand h (fun _ => false) rfl
    rw [nand] at bad
    cases bad
  · have bad := hor h (fun _ => true) rfl
    rw [nand] at bad
    cases bad
  · have bad := hnot h (one u)
    rw [nand] at bad
    simp [one,Ne.symm uv] at bad

theorem pre_unread (C : Circuit) (j : Nat) (hj : j ≤ C.size) (v : Vertex)
    (none : ∀ m (hm : m < C.gates.length), m < j → v.val ∉ eff C.gates[m])
    (x y : Assignment) (same : ∀ z, z ≠ v → x z = y z) (k : Nat) (kv : k ≠ v.val) :
    (pre C j x).getD k false = (pre C j y).getD k false := by
  let D : Circuit := ⟨C.gates.take j,k⟩
  change wire D k x = wire D k y
  by_contra diff
  obtain ⟨m,hm,read,_⟩ := differing_reader D v x y same k kv diff
  change m < (C.gates.take j).length at hm
  have bounds : m < C.gates.length ∧ m < j := by
    simp only [List.length_take] at hm
    omega
  apply none m bounds.1 bounds.2
  simpa [D,List.getElem_take] using read

/-- If a NAND endpoint has only one reader and its other endpoint has
no earlier reader, that sole reader is constant upon deletion. The OR
case uses the factor's dependence when the other endpoint is one. -/
theorem earliest_frozen (C : Circuit) (ga r : Nat) (ha : ga < C.size) (hr : r < C.gates.length)
    (fan : FanInTwo C) (u v : Vertex) (uv : u ≠ v)
    (nand : ∀ x, wire C (10+ga) x = !(x u && x v))
    (read : u.val ∈ eff C.gates[r])
    (sole : ∀ m (hm : m < C.gates.length), u.val ∈ eff C.gates[m] → m = r)
    (early : ∀ m (hm : m < C.gates.length), m < r → v.val ∉ eff C.gates[m]) :
    ∃ c : Bool, ∀ x : Assignment, x u = false → wire C (10+r) x = c := by
  obtain ⟨hand,hor,hnot⟩ := raw_forcing C r hr u read
  have ok := (fan C.gates[r] (List.getElem_mem _)).1
  change C.gates[r].op = .and ∨ C.gates[r].op = .or ∨ C.gates[r].op = .not at ok
  rcases ok with op | op | op
  · exact ⟨false,hand op⟩
  · refine ⟨false,?_⟩
    intro x xu
    let y := Function.update x v true
    let z := Function.update y u true
    have yu : y u = false := by simp [y,uv,xu]
    have yv : y v = true := by simp [y]
    have zu : z u = true := by simp [z]
    have zv : z v = true := by simp [z,Ne.symm uv,yv]
    have ng : 10+ga ≠ u.val := by have := u.isLt; omega
    have fa : wire C (10+ga) y ≠ wire C (10+ga) z := by simp [nand,yu,yv,zu,zv]
    obtain ⟨m,hm,mread,mchange⟩ := differing_reader C u y z
      (fun q hq => by simp [z,hq]) _ ng fa
    have mr := sole m hm mread
    subst m
    have ry : wire C (10+r) y = false := by
      cases h : wire C (10+r) y with
      | true => exact (mchange (h.trans (hor op z zu).symm)).elim
      | false => rfl
    cases rx : wire C (10+r) x with
    | false => rfl
    | true =>
      rw [gate_wire C r hr x,op] at rx
      change List.any _ id = true at rx
      obtain ⟨bit,hbit,val⟩ := List.any_eq_true.mp rx
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hbit
      have ky : (pre C r y).getD k false = true := by
        by_cases kv : k = v.val
        · subst k
          exact (pre_raw C r y v).trans yv
        · exact (pre_unread C r (Nat.le_of_lt hr) v early x y
             (fun q hq => by simp [y,hq]) k kv).symm.trans val
      have hit : wire C (10+r) y = true := by
        rw [gate_wire C r hr y,op]
        exact List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨k,hk,rfl⟩,ky⟩
      rw [ry] at hit
      cases hit
  · exact ⟨true,fun x hx => by rw [hnot op,hx] <;> rfl⟩

/-- Covers an arbitrary signed prefix with a NAND factor on any nonedge,
with no condition on the other factor's behavior on unspecified rows. -/
theorem nand_factor_minor (C : Circuit) (ga b : Nat) (fan : FanInTwo C) (size : C.size ≤ 18)
    (ha : ga < C.size) (u v : Vertex) (uv : u ≠ v) (nonedge : edge u v = false)
    (nand : ∀ x, wire C (10+ga) x = !(x u && x v))
    (agree : promise (fun x => wire C (10+ga) x && wire C b x)) :
    desired (fun x => wire C (10+ga) x && wire C b x) := by
  classical
  have finish (s t : Vertex) (st : s ≠ t) (ne : edge s t = false)
      (shape : ∀ x, wire C (10+ga) x = !(x s && x t))
      (r : Nat) (hr : r < C.gates.length) (read : s.val ∈ eff C.gates[r])
      (early : ∀ m (hm : m < C.gates.length), m < r → t.val ∉ eff C.gates[m]) :
      desired (fun x => wire C (10+ga) x && wire C b x) := by
    have distinct (m : Nat) (hm : m < C.gates.length) (hread : s.val ∈ eff C.gates[m]) : ga ≠ m := by
      rintro rfl
      exact nand_not_reader C _ hm fan s t st shape hread
    by_cases sole : ∀ m (hm : m < C.gates.length), s.val ∈ eff C.gates[m] → m = r
    · obtain ⟨c,frozen⟩ := earliest_frozen C ga r ha hr fan s t st shape read sole early
      apply frozen_factor_minor C ga r b fan size ha hr (distinct _ hr read) s c _ frozen agree
      intro x hx
      simp [shape,hx]
    · push_neg at sole
      obtain ⟨m,hm,hread,mr⟩ := sole
      exact two_readers_nand_minor C ga b r m fan size ha hr hm (distinct _ hr read)
        (distinct _ hm hread) mr.symm s t st ne read hread shape
  let R (m : Nat) := ∃ hm : m < C.gates.length, u.val ∈ eff C.gates[m] ∨ v.val ∈ eff C.gates[m]
  have existsR : ∃ m, R m := by
    let x := one v
    let y := two u v
    have same (w : Vertex) (hw : w ≠ u) : x w = y w := by simp [x,y,one,two,hw]
    have diff : wire C (10+ga) x ≠ wire C (10+ga) y := by simp [nand,x,y,one,two,uv]
    obtain ⟨m,hm,read,_⟩ := differing_reader C u x y same _ (by have := u.isLt; omega) diff
    exact ⟨m,hm,Or.inl read⟩
  let r := Nat.find existsR
  obtain ⟨hr,read⟩ := Nat.find_spec existsR
  change u.val ∈ eff C.gates[r] ∨ v.val ∈ eff C.gates[r] at read
  have early (m : Nat) (hm : m < C.gates.length) (lt : m < r) :
      u.val ∉ eff C.gates[m] ∧ v.val ∉ eff C.gates[m] :=
    ⟨fun h => Nat.find_min existsR lt ⟨hm,Or.inl h⟩, fun h => Nat.find_min existsR lt ⟨hm,Or.inr h⟩⟩
  rcases read with read | read
  · exact finish u v uv nonedge nand r hr read (fun m hm lt => (early m hm lt).2)
  · have sym : ∀ s t : Vertex, edge s t = edge t s := by decide +kernel
    exact finish v u uv.symm ((sym v u).trans nonedge)
      (fun x => (nand x).trans (by rw [Bool.and_comm])) r hr read (fun m hm lt => (early m hm lt).1)

end PEqualNP.Outside.L_meta_7263.Research

namespace PEqualNP.Outside.L_meta_7263.Research

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PetersenRestriction

theorem two_support_shape (A B : Assignment → Bool) (agree : promise (fun x => A x && B x))
    (off : ∃ x, A x = false) (u v : Vertex) (uv : u ≠ v) (f : Bool → Bool → Bool)
    (support : ∀ x, A x = f (x u) (x v)) :
    edge u v = false ∧ ∀ x, A x = !(x u && x v) := by
  have phi : ∀ r s : Bool, (r && s) = false ∨ edge u v = true → f r s = true := by
    intro r s hrs
    obtain ⟨a,b,ab,ar,bs⟩ := sample_data.2 u v uv r s hrs
    have z := (agree (two a b) (Or.inr (graph_geometry.2.2.1 a b))).trans
      ((graph_geometry.1 a b).trans ab)
    have onA := (both_true z).1
    rwa [support,ar,bs] at onA
  obtain ⟨w,hw⟩ := off
  rw [support] at hw
  have nonedge : edge u v = false := by
    cases e : edge u v with
    | false => rfl
    | true =>
      have clash := phi (w u) (w v) (Or.inr e)
      rw [hw] at clash
      cases clash
  have f11 : f true true = false := by
    cases wu : w u <;> cases wv : w v <;> rw [wu,wv] at hw
    · rw [phi false false (Or.inl rfl)] at hw; cases hw
    · rw [phi false true (Or.inl rfl)] at hw; cases hw
    · rw [phi true false (Or.inl rfl)] at hw; cases hw
    · exact hw
  have form (x : Assignment) : A x = !(x u && x v) := by
    rw [support]
    cases x u <;> cases x v
    · exact phi false false (Or.inl rfl)
    · exact phi false true (Or.inl rfl)
    · exact phi true false (Or.inl rfl)
    · exact f11
  exact ⟨nonedge,form⟩

/-- Any two-variable factor in the posted incomparable pair gives the
required cofactor, without assuming positivity or sparsity of its companion. -/
theorem signed_two_support (C : Circuit) (a b : Nat) (fan : FanInTwo C) (size : C.size ≤ 18)
    (agree : promise (fun x => wire C a x && wire C b x)) (off : ∃ x, wire C a x = false)
    (u v : Vertex) (uv : u ≠ v) (f : Bool → Bool → Bool)
    (support : ∀ x, wire C a x = f (x u) (x v)) :
    desired (fun x => wire C a x && wire C b x) := by
  obtain ⟨nonedge,shape⟩ := two_support_shape _ _ agree off u v uv f support
  have ba : 10 ≤ a := by
    by_contra! lt
    let z : Vertex := ⟨a,lt⟩
    have on := shape (fun _ => false)
    have raw := wire_raw C (fun _ => false) z
    change wire C a (fun _ => false) = false at raw
    rw [raw] at on
    cases on
  have bound : a < 10+C.size := by
    by_contra! ge
    have on := shape (fun _ => false)
    have zero : wire C a (fun _ => false) = false := by
      change (wiresFrom C.gates (List.ofFn (fun _ : Vertex => false))).getD a false = false
      apply List.getD_eq_default
      simpa [length_wiresFrom,Circuit.size] using ge
    rw [zero] at on
    cases on
  let ga := a-10
  have idx : 10+ga = a := by dsimp [ga]; omega
  have ag : ga < C.size := by omega
  rw [←idx] at shape agree ⊢
  exact nand_factor_minor C ga b fan size ag u v uv nonedge shape agree

end PEqualNP.Outside.L_meta_7263.Research
namespace PEqualNP.Outside.L_meta_7263.Research

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PetersenRestriction

/-- Prior intermediate wires cannot distinguish modifications of a set of
raw variables until a gate has read one of them. -/
theorem pre_unread_many (C : Circuit) (j : Nat) (hj : j ≤ C.size) (S : Nat → Prop)
    (none : ∀ m (hm : m < C.gates.length), m < j → ∀ q ∈ eff C.gates[m], ¬ S q)
    (x y : Assignment) (same : ∀ z : Vertex, ¬ S z.val → x z = y z)
    (k : Nat) (kv : ¬ S k) :
    (pre C j x).getD k false = (pre C j y).getD k false := by
  let D : Circuit := ⟨C.gates.take j,k⟩
  change wire D k x = wire D k y
  by_contra diff
  obtain ⟨m,hm,_,⟨q,qin,hq⟩,_⟩ := trace_outside D x y S same k kv diff
  change m < (C.gates.take j).length at hm
  have bounds : m < C.gates.length ∧ m < j := by simp only [List.length_take] at hm; omega
  apply none m bounds.1 bounds.2 q _ hq
  simpa [D,List.getElem_take] using qin

/-- Any factor which rejects precisely the assignments containing a
fixed set of at least two vertices gives the required false cofactor. -/
theorem negated_monomial_minor (C : Circuit) (ga b : Nat) (fan : FanInTwo C) (size : C.size ≤ 18)
    (ha : ga < C.size) (S : Finset Vertex) (pair : ∃ u ∈ S, ∃ v ∈ S, u ≠ v)
    (shape : ∀ x, wire C (10+ga) x = decide (∃ v ∈ S, x v = false))
    (agree : promise (fun x => wire C (10+ga) x && wire C b x)) :
    desired (fun x => wire C (10+ga) x && wire C b x) := by
  classical
  obtain ⟨s,hs,t,ht,hst⟩ := pair
  let T (q : Nat) := ∃ v ∈ S, q = v.val
  let R (m : Nat) := ∃ hm : m < C.gates.length, ∃ q ∈ eff C.gates[m], T q
  have high : wire C (10+ga) (fun _ => true) = false := by simp [shape]
  have unit (v : Vertex) (hv : v ∈ S) (x : Assignment) (xv : x v = false) :
      wire C (10+ga) x = true := by
    rw [shape,decide_eq_true_eq]
    exact ⟨v,hv,xv⟩
  have existsR : ∃ m, R m := by
    let y : Assignment := fun i => decide (i ≠ s)
    have diff : wire C (10+ga) y ≠ wire C (10+ga) (fun _ => true) := by
      rw [unit s hs y (by simp [y]),high]; decide
    obtain ⟨m,hm,read,_⟩ := differing_reader C s y (fun _ => true)
      (fun i hi => by simp [y,hi]) _ (by have := s.isLt; omega) diff
    exact ⟨m,hm,s.val,read,s,hs,rfl⟩
  let r := Nat.find existsR
  obtain ⟨hr,q,read,u,hu,rfl⟩ := Nat.find_spec existsR
  change u.val ∈ eff C.gates[r] at read
  have early (m : Nat) (hm : m < C.gates.length) (lt : m < r) (q : Nat)
      (hq : q ∈ eff C.gates[m]) : ¬ T q :=
    fun h => Nat.find_min existsR lt ⟨hm,q,hq,h⟩
  have forbid : u.val ∉ eff C.gates[ga] := by
    intro rr
    obtain ⟨ha',ho',hn'⟩ := raw_forcing C ga ha u rr
    have gok := (fan C.gates[ga] (List.getElem_mem _)).1
    change C.gates[ga].op = .and ∨ C.gates[ga].op = .or ∨ C.gates[ga].op = .not at gok
    rcases gok with h | h | h
    · have z := ha' h (fun _ => false) rfl
      rw [unit u hu _ rfl] at z
      cases z
    · have z := ho' h (fun _ => true) rfl
      rw [high] at z
      cases z
    · have z := hn' h (one u)
      obtain ⟨w,hw,wu⟩ : ∃ w ∈ S, w ≠ u := by
        by_cases su : s = u
        · exact ⟨t,ht,by simpa [←su] using hst.symm⟩
        · exact ⟨s,hs,su⟩
      rw [unit w hw _ (by simp [one,wu])] at z
      simp [one] at z
  have distinct (m : Nat) (hm : m < C.gates.length) (hread : u.val ∈ eff C.gates[m]) : ga ≠ m := by
    rintro rfl
    exact forbid hread
  let p0 := (anchor_data u).2
  obtain ⟨v,uv,nonedge⟩ := p0
  obtain ⟨inj,hu9,_,adj⟩ := moving_data u v uv nonedge
  let p : Equiv.Perm Vertex := Equiv.ofBijective (move u v) ((Finite.injective_iff_bijective).mp inj)
  have fixed (y : Nine) : inserted p false y u = false := by
    change Fin.lastCases false y (move u v u) = false
    rw [hu9] <;> rfl
  have unit' (y : Nine) : restrictedWire C p false (10+ga) y = true := unit u hu _ (fixed y)
  by_cases sole : ∀ m (hm : m < C.gates.length), u.val ∈ eff C.gates[m] → m = r
  · suffices frozen : ∃ c : Bool, ∀ x : Assignment, x u = false → wire C (10+r) x = c by
      obtain ⟨c,fc⟩ := frozen
      exact frozen_factor_minor C ga r b fan size ha hr (distinct _ hr read) u c (unit u hu) fc agree
    obtain ⟨forceAnd,forceOr,forceNot⟩ := raw_forcing C r hr u read
    have ok := (fan C.gates[r] (List.getElem_mem _)).1
    change C.gates[r].op = .and ∨ C.gates[r].op = .or ∨ C.gates[r].op = .not at ok
    rcases ok with op | op | op
    · exact ⟨false,forceAnd op⟩
    · refine ⟨false,?_⟩
      intro x xu
      let y : Assignment := fun k => if k ∈ S then decide (k ≠ u) else x k
      let z := Function.update y u true
      have yu : y u = false := by simp [y,hu]
      have zu : z u = true := by simp [z]
      have zall (k : Vertex) (hk : k ∈ S) : z k = true := by
        by_cases e : k = u
        · simpa [e] using zu
        · simp [z,e,y,hk]
      have uz : wire C (10+ga) z = false := by
        rw [shape]
        simp only [decide_eq_false_iff_not]
        rintro ⟨k,hk,off⟩
        rw [zall k hk] at off
        cases off
      have fa : wire C (10+ga) y ≠ wire C (10+ga) z := by rw [unit u hu _ yu,uz]; decide
      obtain ⟨m,hm,mread,chg⟩ := differing_reader C u y z
        (fun k hk => by simp [z,hk]) _ (by have := u.isLt; omega) fa
      have mr := sole m hm mread
      subst m
      have ry : wire C (10+r) y = false := by
        cases e : wire C (10+r) y with
        | false => rfl
        | true => exact (chg (e.trans (forceOr op z zu).symm)).elim
      cases rx : wire C (10+r) x with
      | false => rfl
      | true =>
        rw [gate_wire C r hr x,op] at rx
        change List.any _ id = true at rx
        obtain ⟨bit,hbit,val⟩ := List.any_eq_true.mp rx
        obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hbit
        have ky : (pre C r y).getD k false = true := by
          by_cases kt : T k
          · obtain ⟨w,hw,rfl⟩ := kt
            have eq := (pre_raw C r x w).symm.trans val
            have wu : w ≠ u := by rintro rfl; rw [xu] at eq; cases eq
            rw [pre_raw]
            simp [y,hw,wu]
          · apply (pre_unread_many C r (Nat.le_of_lt hr) T early x y _ k kt).symm.trans val
            intro w nw
            have out : w ∉ S := fun h => nw ⟨w,h,rfl⟩
            simp [y,out]
        have hit : wire C (10+r) y = true := by
          rw [gate_wire C r hr y,op]
          exact List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨k,hk,rfl⟩,ky⟩
        rw [ry] at hit
        cases hit
    · exact ⟨true,fun x hx => by rw [forceNot op,hx] <;> rfl⟩
  · push_neg at sole
    obtain ⟨m,hm,hread,mr⟩ := sole
    have discard (k : Nat) (hk : k < C.gates.length) (hread : u.val ∈ eff C.gates[k]) :
        removable C p k :=
      reader_removable C p k hk fan u.val false hread (fun y => (before_raw C p k u y).trans (fixed y))
    have ar := distinct _ hr read
    have am := distinct _ hm hread
    apply true_factor_three C (10+ga) b fan size p (move_correct p adj) unit' {m,ga,r}
    · intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
    · have ar' : ga ≠ r := ar
      simp [am.symm,mr,ar']
    · intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · exact discard _ hm hread
      · exact Or.inl ⟨true,funext unit'⟩
      · exact discard _ hr read

end PEqualNP.Outside.L_meta_7263.Research
namespace PEqualNP.Outside.L_meta_7263.Research

def three (i a b : Vertex) : Assignment := fun k => decide (k = i ∨ k = a ∨ k = b)

/- At an independent set of size at most two, adding either of any
prescribed pair of vertices can create an edge. Repeated vertices are
permitted in both parameters and witnesses. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem triple_witnesses : ∀ i j : Vertex, ∃ a b : Vertex,
    pet (two a b) = false ∧ pet (three i a b) = true ∧ pet (three j a b) = true := by
  decide +kernel

def independent_of (A : Assignment → Bool) (v : Vertex) : Prop :=
  ∀ x y : Assignment, (∀ w, w ≠ v → x w = y w) → A x = A y

/-- A failure of both factors to depend on all ten variables witnesses a
specific omitted positive row of weight at most three. -/
theorem missing_triple (A B : Assignment → Bool) (agree : promise (fun x => A x && B x))
    (i j : Vertex) (ai : independent_of A i) (bj : independent_of B j) :
    ∃ a b, pet (two a b) = false ∧ pet (three i a b) = true ∧
      pet (three j a b) = true ∧ (A (three i a b) = false ∨ B (three j a b) = false) := by
  obtain ⟨a,b,zero,posI,posJ⟩ := triple_witnesses i j
  refine ⟨a,b,zero,posI,posJ,?_⟩
  have ea := ai (three i a b) (two a b) (fun w hw => by simp [three,two,hw])
  have eb := bj (three j a b) (two a b) (fun w hw => by simp [three,two,hw])
  rw [ea,eb]
  have off := (agree (two a b) (Or.inl zero)).trans zero
  change (A (two a b) && B (two a b)) = false at off
  cases aa : A (two a b) with
  | false => exact Or.inl rfl
  | true => exact Or.inr (by simpa [aa] using off)

theorem full_factor_of_triples (A B : Assignment → Bool) (agree : promise (fun x => A x && B x))
    (trip : ∀ i a b, pet (three i a b) = true → A (three i a b) = true ∧ B (three i a b) = true) :
    (∀ i, ¬ independent_of A i) ∨ ∀ j, ¬ independent_of B j := by
  classical
  by_cases all : ∀ i, ¬ independent_of A i
  · exact Or.inl all
  · push_neg at all
    obtain ⟨i,hi⟩ := all
    refine Or.inr (fun j hj => ?_)
    obtain ⟨a,b,_,posI,posJ,left|right⟩ := missing_triple A B agree i j hi hj
    · rw [(trip i a b posI).1] at left
      cases left
    · rw [(trip j a b posJ).2] at right
      cases right

end PEqualNP.Outside.L_meta_7263.Research

namespace PEqualNP.Outside.L_meta_7263.Research

def inside (s : Fin 1024) (v : Vertex) : Bool := s.val.testBit v.val

def label (a : Fin 11) : Assignment := fun v=>decide (v.val=a.val)

def rows (s : Fin 1024) : Finset (Fin 11) := Finset.univ.filter (fun a=>
  ∀v : Vertex,label a v = true → inside s v=true)

def profile (s : Fin 1024) (a : Fin 11) : Assignment := fun v=>
  if inside s v then false else pet (fun i=>label a i || one v i)

def distinctProfiles (s : Fin 1024) := ((rows s).image (profile s)).card

def keep (s : Fin 1024) (x : Assignment) : Assignment :=
  fun i=>if inside s i then x i else false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem probe_small : ∀a : Fin 11,∀v : Vertex,(List.ofFn (fun i=>label a i || one v i)).count true≤2 := by
  decide +kernel

theorem communication {m : Nat} (s : Fin 1024) (P : Assignment→Bool) (ag : promise P)
    (msg : Assignment→Fin m) (localOnly : ∀x,msg x=msg (keep s x))
    (separates : ∀x y,(∀i,inside s i=false → x i=y i) → msg x=msg y → P x=P y) :
    distinctProfiles s ≤ m := by
  classical
  have hold {a : Fin 11} (ha : a∈rows s) (v : Vertex) (hv : inside s v=false) :
      keep s (fun i=>label a i || one v i)=label a := by
    funext i
    have mem := (Finset.mem_filter.mp ha).2
    by_cases hi : inside s i=true
    · have neq : i≠v := fun eq=>by rw [eq,hv] at hi;cases hi
      simp [keep,hi,one,neq]
    · have off : label a i=false := by
        cases flag : label a i with
        | false => rfl
        | true => exact (hi (mem i flag)).elim
      simp [keep,hi,off]
  have sep {a b : Fin 11} (ha : a∈rows s) (hb : b∈rows s)
      (same : msg (label a)=msg (label b)) : profile s a=profile s b := by
    funext v
    by_cases hv : inside s v=true
    · simp [profile,hv]
    · have out : inside s v=false := Bool.eq_false_iff.mpr hv
      let x : Assignment := fun i=>label a i || one v i
      let y : Assignment := fun i=>label b i || one v i
      have equal : msg x=msg y := (localOnly x).trans ((congrArg msg (hold ha v out)).trans
        (same.trans ((congrArg msg (hold hb v out)).symm.trans (localOnly y).symm)))
      have outside (i : Vertex) (hi : inside s i=false) : x i=y i := by
        have off (z : Fin 11) (hz : z∈rows s) : label z i=false := by
          cases h : label z i with
          | false => rfl
          | true => exact (Bool.noConfusion (hi.symm.trans ((Finset.mem_filter.mp hz).2 i h)))
        simp [x,y,off a ha,off b hb]
      have eq := separates x y outside equal
      rw [ag x (Or.inr (probe_small a v)),ag y (Or.inr (probe_small b v))] at eq
      simpa [profile,out,x,y] using eq
  let R := (rows s).image (profile s)
  have witness (z : R) : ∃a∈rows s,profile s a=z.val := Finset.mem_image.mp z.property
  choose a ha ident using witness
  let key (z : R) := msg (label (a z))
  have inj : Function.Injective key := by
    intro i j same
    exact Subtype.ext ((ident i).symm.trans ((sep (ha i) (ha j) same).trans (ident j)))
  change R.card≤m
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective key inj

end PEqualNP.Outside.L_meta_7263.Research

namespace PEqualNP.Outside.L_meta_7263.Research

def maskSize (s : Fin 1024) := (Finset.univ.filter fun v : Vertex=>inside s v=true).card

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem five_profiles : ∀s : Fin 1024,maskSize s=5 → 5≤distinctProfiles s := by
  decide +kernel

theorem no_two_bit_cut (s : Fin 1024) (hs : maskSize s=5) (P : Assignment→Bool) (ag : promise P)
    (msg : Assignment→Fin 4) (localOnly : ∀x,msg x=msg (keep s x))
    (separates : ∀x y,(∀i,inside s i=false → x i=y i) → msg x=msg y → P x=P y) : False := by
  have lower := five_profiles s hs
  have upper := communication s P ag msg localOnly separates
  omega

end PEqualNP.Outside.L_meta_7263.Research

namespace Promise7263
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_7263.Research
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Finset Sig) : Nat → Finset Sig → Prop
  | 0,S => S=target ∧ ∀t∈target,proper t
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Finset Sig} (hp : ∀t∈target,proper t) : Live u target 0 target := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Finset Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Finset Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : ∀t∈target,proper t), motive 0 target (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : ∀t∈target,proper t) (hout : ∀t∈target,t∈(execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,target,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]


abbrev Row := Fin 128
def masks : List Nat := [0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,42,48,50,52,64,65,66,68,69,72,73,80,84,96,100,104,112,116,128,129,130,132,136,137,138,144,146,160,192,193,200,201,208,256,257,258,260,261,264,272,274,276,288,320,384,385,386,400,402,512,513,514,516,517,520,521,522,528,544,546,548,552,554,576,640,768,769,770,772,773]
def assignment (r : Row) : Assignment := fun i=>(masks.getD r.val 0).testBit i.val
def table (f : Row→Bool) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem bit_table (f : Row→Bool) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]; simp [r.isLt]
def inputs := List.ofFn (fun i : Vertex=>table (fun r=>assignment r i))
def goal := table (fun r=>pet (assignment r))
def bank (C : Circuit) := execute C.gates inputs
def factor (C : Circuit) (a : Nat) := (bank C).getD a zero
noncomputable def ends (C : Circuit) (a b : Nat) : Finset Sig := by
  classical
  exact ({nrm true (factor C a),nrm true (factor C b)} : Finset Sig).filter proper

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rows_valid : ∀r : Row,pet (assignment r)=false ∨ (List.ofFn (assignment r)).count true≤2 := by
  decide +kernel

theorem input_rows (r : Row) : inputs.map (bit r)=List.ofFn (assignment r) := by
  simp [inputs,List.map_ofFn,Function.comp_def,bit_table]

theorem factor_bit (C : Circuit) (fan : FanInTwo C) (a : Nat) (r : Row) :
    bit r (factor C a)=wire C a (assignment r) := by
  unfold factor bank
  rw [←b_read,execute_bits _ _ _ (fun g hg=>(fan g hg).1),input_rows]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem all_plain : inputs.map (nrm true)=inputs := by decide +kernel

theorem realize_pair (C : Circuit) (fan : FanInTwo C) (a b : Nat)
    (ag : promise (fun x=>wire C a x && wire C b x)) :
    factor C a &&& factor C b=goal ∧ ∃k S,k≤C.gates.countP (fun g=>!isNot g) ∧
      Live true (ends C a b) k S ∧ ∀z∈S,z∈inputs := by
  classical
  constructor
  · apply bit_ext
    intro r
    change bit r (bin 0 (factor C a) (factor C b))=bit r (table _)
    rw [bit_bin,bit_table]
    simpa [factor_bit C fan] using ag (assignment r) (rows_valid r)
  · have good (z) (hz : z∈ends C a b) : proper z := (Finset.mem_filter.mp hz).2
    have mem (z) (hz : z∈ends C a b) : z∈(execute C.gates inputs).map (nrm true) := by
      have on (i : Nat) (p : proper (nrm true (factor C i))) :
          nrm true (factor C i)∈(execute C.gates inputs).map (nrm true) :=
        (get_rep (u:=true) (bank C) i).resolve_right (fun n=>n p)
      have h := (Finset.mem_filter.mp hz).1
      simp only [Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with rfl|rfl <;> apply on <;> exact good _ hz
    obtain ⟨k,S,bound,run,raw⟩ := extract C.gates inputs fan (u:=true) (by simp) good mem
    exact ⟨k,S,bound,run,by simpa only [all_plain] using raw⟩

end Promise7263
