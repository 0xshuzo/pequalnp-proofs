import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1972
section Geometry
open SimpleGraph
variable {n : ℕ} {G : SimpleGraph (Fin n)}
def girthFive (G : SimpleGraph (Fin n)) := ∀ u (p : G.Walk u u), p.IsCycle → 5 ≤ p.length

lemma triangle (h : girthFive G) {u v w : Fin n} (uv : G.Adj u v) (vw : G.Adj v w)
    (wu : G.Adj w u) : False := by
  let p := Walk.cons uv (Walk.cons vw (Walk.cons wu Walk.nil))
  have hp : p.IsCycle := by
    unfold p
    rw [Walk.cons_isCycle_iff]
    have a := uv.ne
    have b := vw.ne
    have c := wu.ne
    constructor <;> simp [Walk.cons_isPath_iff,Sym2.eq_iff,a,b,c,Ne.symm a,Ne.symm b,Ne.symm c]
  have bound := h u p hp
  simp [p] at bound

lemma square (h : girthFive G) {u a w b : Fin n} (ua : G.Adj u a) (aw : G.Adj a w)
    (wb : G.Adj w b) (bu : G.Adj b u) (uw : u ≠ w) (ab : a ≠ b) : False := by
  let p := Walk.cons ua (Walk.cons aw (Walk.cons wb (Walk.cons bu Walk.nil)))
  have hp : p.IsCycle := by
    unfold p
    rw [Walk.cons_isCycle_iff]
    have h1 := ua.ne
    have h2 := aw.ne
    have h3 := wb.ne
    have h4 := bu.ne
    constructor <;> simp [Walk.cons_isPath_iff,Sym2.eq_iff,h1,h2,h3,h4,uw,ab,
      Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm uw,Ne.symm ab]
  have bound := h u p hp
  simp [p] at bound

end Geometry
open SimpleGraph
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

def excluded (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v p : Fin n) : Finset (Fin n) :=
  (G.neighborFinset v).filter fun z => z=p ∨ G.Adj p z

theorem excluded_card {v p : Fin n} (wide : girthFive G) (vp : v≠p) :
    (excluded G v p).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s hs t ht
  obtain ⟨vs,bs⟩ := Finset.mem_filter.mp hs
  obtain ⟨vt,bt⟩ := Finset.mem_filter.mp ht
  have vs := (G.mem_neighborFinset v s).mp vs
  have vt := (G.mem_neighborFinset v t).mp vt
  by_contra ne
  rcases bs with rfl|ps <;> rcases bt with rfl|pt
  · exact ne rfl
  · exact triangle wide vs pt vt.symm
  · exact triangle wide vt ps vs.symm
  · exact square wide vs ps.symm pt vt.symm vp ne

theorem third_private {v p q : Fin n} (wide : girthFive G) (degree : (G.neighborSet v).ncard=3)
    (vp : v≠p) (vq : v≠q) :
    ∃ t, G.Adj v t ∧ t≠p ∧ ¬G.Adj p t ∧ t≠q ∧ ¬G.Adj q t := by
  classical
  have size : (G.neighborFinset v).card=3 := by
    change G.degree v=3
    rw [←G.ncard_neighborSet]
    exact degree
  have a := excluded_card wide vp
  have b := excluded_card wide vq
  have union := Finset.card_union_le (excluded G v p) (excluded G v q)
  have bad : ¬G.neighborFinset v ⊆ excluded G v p ∪ excluded G v q := by
    intro h
    have le := Finset.card_le_card h
    omega
  obtain ⟨t,ht,nt⟩ := Finset.not_subset.mp bad
  have pfree : t≠p ∧ ¬G.Adj p t := by
    by_contra! h
    exact nt (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht,by tauto⟩))
  have qfree : t≠q ∧ ¬G.Adj q t := by
    by_contra! h
    exact nt (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht,by tauto⟩))
  exact ⟨t,(G.mem_neighborFinset v t).mp ht,pfree.1,pfree.2,qfree.1,qfree.2⟩

open PEqualNP.MetaComplexity.NestedCover

theorem sensitivePattern (A : Finset (Fin n)) {v p q : Fin n} (wide : girthFive G)
    (degree : (G.neighborSet v).ncard=3) (iso : ∀ i j, G.Adj i j → i∉A)
    (po : p∉A) (qo : q∉A) (vp : v≠p) (vq : v≠q) (pq : p≠q) (a b : Bool)
    (legal : a=true → b=true → ¬G.Adj p q) :
    ∃ x : Fin n → Bool, x p=a ∧ x q=b ∧ x v=false ∧ graphFun G A x=false ∧
      graphFun G A (Function.update x v true)=true := by
  classical
  obtain ⟨t,vt,tp,pt,tq,qt⟩ := third_private wide degree vp vq
  let x : Fin n → Bool := fun i => decide (i=t ∨ (i=p ∧ a=true) ∨ (i=q ∧ b=true))
  have xp : x p=a := by cases a <;> simp [x,tp.symm,pq]
  have xq : x q=b := by cases b <;> simp [x,tq.symm,pq.symm]
  have xv : x v=false := by simp [x,vt.ne,vp,vq]
  have xon (i : Fin n) : x i=true ↔ i=t ∨ (i=p ∧ a=true) ∨ (i=q ∧ b=true) := by simp [x]
  have off : graphFun G A x=false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    have lifted : (∃ a∈A, x a=true) ∨ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true := by
      simpa only [graphFun,Bool.or_eq_true,decide_eq_true_eq] using (show graphFun G A x=true from yes)
    rcases lifted with ⟨i,hi,xi⟩|⟨i,j,ij,xi,xj⟩
    · rcases (xon i).mp xi with rfl|⟨rfl,_⟩|⟨rfl,_⟩
      · exact iso _ _ vt.symm hi
      · exact po hi
      · exact qo hi
    · rcases (xon i).mp xi with rfl|⟨rfl,ap⟩|⟨rfl,bq⟩ <;>
        rcases (xon j).mp xj with rfl|⟨rfl,ap'⟩|⟨rfl,bq'⟩
      · exact ij.ne rfl
      · exact pt ij.symm
      · exact qt ij.symm
      · exact pt ij
      · exact ij.ne rfl
      · exact legal ap bq' ij
      · exact qt ij
      · exact legal ap' bq ij.symm
      · exact ij.ne rfl
  refine ⟨x,xp,xq,xv,off,?_⟩
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inr ⟨v,t,vt,by simp,by simpa [Function.update_of_ne vt.ne.symm] using (xon t).mpr (Or.inl rfl)⟩

theorem binaryShield (A : Finset (Fin n)) {v p q : Fin n} (wide : girthFive G)
    (degree : (G.neighborSet v).ncard=3) (iso : ∀ i j, G.Adj i j → i∉A)
    (po : p∉A) (qo : q∉A) (vp : v≠p) (vq : v≠q) (pq : p≠q)
    (W : Bool → Bool → Bool) (required : Bool)
    (shield : ∀ x, x v=false → graphFun G A x=false → graphFun G A (Function.update x v true)=true →
      W (x p) (x q) = required) :
    (∀ a b, W a b ≠ required → a=true ∧ b=true ∧ G.Adj p q) := by
  intro a b mismatch
  by_contra! h
  have legal : a=true → b=true → ¬G.Adj p q := by tauto
  obtain ⟨x,xp,xq,xv,off,on⟩ := sensitivePattern A wide degree iso po qo vp vq pq a b legal
  exact mismatch (by simpa [xp,xq] using shield x xv off on)

open PEqualNP.MetaComplexity.NestedCover
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

def independent (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ p∈S, ∀ q∈S, ¬G.Adj p q

theorem project_sensitive (A : Finset (Fin n)) (v : Fin n) (S Z : Finset (Fin n))
    (vo : v∉A) (vS : v∉S) (away : Disjoint A S) (sz : Disjoint S Z)
    (iso : ∀ i j, G.Adj i j → i∉A) :
    (∃ x : Fin n → Bool, (∀ p∈S, x p=true) ∧ (∀ q∈Z, x q=false) ∧ x v=false ∧
      graphFun G A x=false ∧ graphFun G A (Function.update x v true)=true) ↔
    independent G S ∧ ∃ t, G.Adj v t ∧ t∉Z ∧ ∀ p∈S, ¬G.Adj p t := by
  classical
  constructor
  · rintro ⟨x,pos,neg,xv,off,on⟩
    have forbid : ¬ ((∃ a∈A, x a=true) ∨ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true) := by
      intro bad
      have yes : graphFun G A x=true := by simpa only [graphFun,Bool.or_eq_true,decide_eq_true_eq] using bad
      rw [off] at yes
      contradiction
    have indep : independent G S := fun a ha b hb e => forbid (Or.inr ⟨a,b,e,pos a ha,pos b hb⟩)
    have claim (t : Fin n) (vt : G.Adj v t) (xt : x t=true) :
        G.Adj v t ∧ t∉Z ∧ ∀ p∈S, ¬G.Adj p t :=
      ⟨vt,fun h => Bool.noConfusion ((neg t h).symm.trans xt),
        fun p hp e => forbid (Or.inr ⟨p,t,e,pos p hp,xt⟩)⟩
    refine ⟨indep,?_⟩
    simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq] at on
    rcases on with ⟨a,am,va⟩ | ⟨a,b,ab,xa,xb⟩
    · have av : a≠v := fun eq => vo (eq ▸ am)
      exact False.elim (forbid (Or.inl ⟨a,am,by simpa only [Function.update_of_ne av] using va⟩))
    · by_cases av : a=v
      · subst a
        exact ⟨b,claim _ ab (by simpa only [Function.update_of_ne ab.ne.symm] using xb)⟩
      by_cases bv : b=v
      · subst b
        exact ⟨a,claim _ ab.symm (by simpa only [Function.update_of_ne ab.ne] using xa)⟩
      exact False.elim (forbid (Or.inr ⟨a,b,ab,by simpa [Function.update_of_ne av] using xa,
        by simpa [Function.update_of_ne bv] using xb⟩))
  · rintro ⟨indep,t,vt,tz,pt⟩
    let x : Fin n → Bool := fun i => decide (i=t ∨ i∈S)
    have xt : x t=true := by simp [x]
    have xon (i : Fin n) : x i=true ↔ i=t ∨ i∈S := by simp [x]
    refine ⟨x,fun p hp => (xon p).mpr (Or.inr hp),?_,by simp [x,vt.ne,vS],?_,?_⟩
    · intro q hq
      have qt : q≠t := fun h => tz (h ▸ hq)
      have qs : q∉S := fun h => Finset.disjoint_left.mp sz h hq
      simp [x,qt,qs]
    · apply Bool.eq_false_iff.mpr
      intro yes
      have lifted : (∃ a∈A, x a=true) ∨ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true := by
        simpa only [graphFun,Bool.or_eq_true,decide_eq_true_eq] using (show graphFun G A x=true from yes)
      rcases lifted with ⟨p,ap,xp⟩|⟨p,q,pq,xp,xq⟩
      · rcases (xon p).mp xp with rfl|hp
        · exact iso _ _ vt.symm ap
        · exact Finset.disjoint_left.mp away ap hp
      · rcases (xon p).mp xp with rfl|sp <;> rcases (xon q).mp xq with rfl|sq
        · exact pq.ne rfl
        · exact pt _ sq pq.symm
        · exact pt _ sp pq
        · exact indep _ sp _ sq pq
    · simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
      exact Or.inr ⟨v,t,vt,by simp,by simpa only [Function.update_of_ne vt.ne.symm] using xt⟩

theorem missing_branch (A B : Finset (Fin n)) {v t : Fin n} (vt : G.Adj v t)
    (vo : v∉A) (vB : v∉B) (iso : ∀ i j, G.Adj i j → i∉A)
    (fresh : t∉B) (openT : ∀ p∈B, ¬G.Adj p t)
    (F : (Fin n → Bool) → Bool) (localF : ∀ x y, (∀ p∈B, x p=y p) → F x=F y)
    (required : Bool)
    (onChange : ∀ x, x v=false → graphFun G A x=false → graphFun G A (Function.update x v true)=true →
      F x=required) :
    ∀ x, graphFun G A x=false → F x=required := by
  classical
  intro x off
  let P := B.filter fun p => x p=true
  let Z := B.filter fun p => x p=false
  have forbid : ¬ ((∃ a∈A, x a=true) ∨ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true) := by
    intro bad
    have yes : graphFun G A x=true := by simpa only [graphFun,Bool.or_eq_true,decide_eq_true_eq] using bad
    rw [off] at yes
    contradiction
  have pinfo (p) (h : p∈P) : p∈B ∧ x p=true := Finset.mem_filter.mp h
  have zinfo (p) (h : p∈Z) : p∈B ∧ x p=false := Finset.mem_filter.mp h
  have dp : Disjoint A P := by
    apply Finset.disjoint_left.mpr
    intro p hp h
    exact forbid (Or.inl ⟨p,hp,(pinfo p h).2⟩)
  have dz : Disjoint P Z := by
    apply Finset.disjoint_left.mpr
    intro p hp hz
    exact Bool.noConfusion ((zinfo p hz).2.symm.trans (pinfo p hp).2)
  have ip : independent G P := fun a ha b hb e =>
    forbid (Or.inr ⟨a,b,e,(pinfo _ ha).2,(pinfo _ hb).2⟩)
  obtain ⟨y,yP,yZ,yv,yo,yi⟩ := (project_sensitive A v P Z vo
    (fun h => vB (pinfo _ h).1) dp dz iso).mpr ⟨ip,t,vt,fun h => fresh (zinfo _ h).1,
      fun p hp => openT p (pinfo _ hp).1⟩
  rw [localF x y]
  · exact onChange y yv yo yi
  · intro p hp
    cases h : x p
    · exact (yZ p (Finset.mem_filter.mpr ⟨hp,h⟩)).symm
    · exact (yP p (Finset.mem_filter.mpr ⟨hp,h⟩)).symm

theorem outside_or (F W : (Fin n → Bool) → Bool)
    (H : (Fin n → Bool) → Bool → Bool) (v : Fin n)
    (orig : ∀ x, F x=H x (x v || W x)) (absorbed : ∀ x, F x=false → W x=false) :
    ∀ x, F x=(H x (x v) || W x) := by
  intro x
  cases w : W x with
  | false => simpa only [w,Bool.or_false] using orig x
  | true =>
    rw [Bool.or_true]
    cases f : F x with
    | true => rfl
    | false => exact False.elim (Bool.noConfusion (w.symm.trans (absorbed x f)))

end PEqualNP.Outside.L_meta_1972

namespace PEqualNP.Outside.L_meta_1972.Pin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat : Type := Bool ⊕ ℕ

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

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
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

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
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

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
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

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
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

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

def reads (pin : ℕ) (g : Gate) : Bool := (normGate g).inputs.contains pin

def restrict (bank : List (Option (Fin m))) (x : Fin m → Bool) : List Bool :=
  bank.map fun p => p.elim false x

def layout (bank : List (Option (Fin m))) : List Stat :=
  bank.map (fun p => p.elim (.inl false) (fun k => .inr k.val))

theorem eliminate_pin (bank : List (Option (Fin m))) (pin : ℕ) (C : Circuit)
    (fan : FanInTwo C) (absent : bank[pin]? = some none)
    (hasFalse : ∃ x : Fin m → Bool, C.eval (restrict bank x) = false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP (reads pin) ≤ C.size ∧
      ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (restrict bank x) := by
  let initial := layout bank
  let gs := C.gates.map normGate
  let acc := elim m gs (initial, [])
  let S := Finset.univ.filter (fun i : Fin C.gates.length => reads pin (C.gates.get i))
  have cardS : C.gates.countP (reads pin) = S.card := by
    simpa [S] using List.countP_ofFn (fun i : Fin C.gates.length => C.gates.get i) (reads pin)
  have normOk : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok _ (fan _ hg0)
  have hp : pin < bank.length := (List.getElem?_eq_some_iff.mp absent).1
  have constant : initial.getD pin (.inl false) = .inl false := by
    simp [initial, layout, List.getD_eq_getElem?_getD, absent]
  have penalty := elim_count m (initial, []) gs normOk (S.image Fin.val) (by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hr := (Finset.mem_filter.mp hi).2
    have member : pin ∈ (normGate (C.gates.get i)).inputs := by simpa [reads] using hr
    refine ⟨normGate (C.gates.get i), ?_, pin, member, ?_, false, ?_⟩
    · simp [gs, i.isLt]
    · have len : initial.length = bank.length := by simp [initial,layout]
      change pin < initial.length + i.val
      omega
    · rw [elim_getD m pin _ gs _ (by simp [initial,layout,hp])]
      exact constant)
  have count : acc.2.length + C.gates.countP (reads pin) ≤ C.size := by
    rw [cardS]
    simpa [acc, gs, Circuit.size, Finset.card_image_of_injective S Fin.val_injective] using penalty
  have inv (x : Fin m → Bool) :
      Inv m (List.ofFn x) (wiresFrom gs (restrict bank x)) acc := by
    apply inv_elim _ _ (by simp) _ _ _ (fun g hg => (normOk g hg).1)
    refine ⟨by simp [initial,layout,restrict], ?_⟩
    intro k
    by_cases h : k < bank.length
    · have index := List.getElem?_eq_getElem h
      cases val : bank[k] with
      | none =>
        have eq : bank[k]? = some none := index.trans (congrArg some val)
        simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,wiresFrom]
      | some i =>
        have eq : bank[k]? = some (some i) := index.trans (congrArg some val)
        simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,
          wiresFrom,i.isLt]
    · have eq : bank[k]? = none := List.getElem?_eq_none (by omega)
      simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,wiresFrom]
  have eval (x : Fin m → Bool) :
      (acc.1.getD C.output (.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = C.eval (restrict bank x) := by
    rw [((inv x).2 C.output).2, show gs = C.gates.map normGate from rfl, wiresFrom_norm]
    rfl
  cases hout : acc.1.getD C.output (.inl false) with
  | inr k =>
    refine ⟨⟨acc.2, k⟩, elim_ok m gs _ (by simp), count, fun x => ?_⟩
    change (wiresFrom acc.2 (List.ofFn x)).getD k false = _
    simpa only [hout,Stat.val] using eval x
  | inl b =>
    have fixed (x : Fin m → Bool) : b = C.eval (restrict bank x) := by
      simpa only [hout,Stat.val] using eval x
    obtain ⟨x, hx⟩ := hasFalse
    have hb := (fixed x).trans hx
    subst b
    refine ⟨⟨[], m⟩, by simp [FanInTwo], by change 0 + _ ≤ _; omega, fun x => ?_⟩
    change (List.ofFn x).getD m false = _
    simpa using fixed x

end PEqualNP.Outside.L_meta_1972.Pin

namespace PEqualNP.Outside.L_meta_1972.Ports
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
theorem m1892_eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl step x).getD C.output false := rfl

theorem m1892_getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

def shift (cut replacement i : Nat) : Nat :=
  if i < cut then i else if i=cut then replacement else i-1

def change (cut replacement : Nat) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (shift cut replacement)⟩

def bypass (n : Nat) (pre post : List Gate) (o replacement : Nat) : Circuit :=
  ⟨pre ++ post.map (change (n+pre.length) replacement),shift (n+pre.length) replacement o⟩

def value (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem foldLength (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,step] <;> omega

theorem extendRead (old fresh : List Bool) (cut replacement : Nat)
    (size : old.length = fresh.length+1) (room : cut ≤ fresh.length)
    (valid : replacement < cut ∨ fresh.length < replacement)
    (agree : ∀ i, old.getD i false = fresh.getD (shift cut replacement i) false)
    (v : Bool) (i : Nat) :
    (old++[v]).getD i false = (fresh++[v]).getD (shift cut replacement i) false := by
  rw [m1892_getD_snoc,m1892_getD_snoc,agree]
  by_cases ie : i=old.length
  · have se : shift cut replacement i = fresh.length := by
      have gt : cut < i := by omega
      simp [shift,show ¬i < cut by omega,show i≠cut by omega] <;> omega
    rw [if_pos ie,if_pos se]
  · have se : shift cut replacement i ≠ fresh.length := by
      simp only [shift]
      split_ifs <;> omega
    rw [if_neg ie,if_neg se]

theorem foldAgree (cut replacement : Nat) (post : List Gate) (old fresh : List Bool)
    (size : old.length=fresh.length+1) (room : cut ≤ fresh.length)
    (valid : replacement < cut ∨ fresh.length+post.length ≤ replacement)
    (agree : ∀ i, old.getD i false = fresh.getD (shift cut replacement i) false) :
    ∀ i, (post.foldl step old).getD i false =
      ((post.map (change cut replacement)).foldl step fresh).getD (shift cut replacement i) false := by
  induction post generalizing old fresh with
  | nil => exact agree
  | cons g post ih =>
    have v : value old g = value fresh (change cut replacement g) := by
      unfold value change
      simp only [List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => agree i)
    simp only [List.map_cons,List.foldl_cons]
    apply ih
    · simp [step,size]
    · simp [step] <;> omega
    · simp [step,List.length_cons] at * <;> omega
    · intro i
      change (old ++ [value old g]).getD i false =
        (fresh ++ [value fresh (change cut replacement g)]).getD _ false
      rw [←v]
      apply extendRead old fresh cut replacement size room _ agree
      simp only [List.length_cons] at valid
      omega

theorem evalBypass (n : Nat) (pre post : List Gate) (o replacement : Nat)
    (valid : replacement < n+pre.length ∨ n+pre.length+post.length ≤ replacement)
    (x : Fin n → Bool) :
    (bypass n pre post o replacement).eval (List.ofFn x) =
      (let w := pre.foldl step (List.ofFn x);
       post.foldl step (w ++ [w.getD replacement false])).getD o false := by
  let w := pre.foldl step (List.ofFn x)
  have len : w.length = n+pre.length := by simp [w,foldLength]
  rw [m1892_eval_eq]
  change ((pre ++ post.map (change (n+pre.length) replacement)).foldl step _).getD _ false = _
  rw [List.foldl_append]
  change ((post.map (change (n+pre.length) replacement)).foldl step w).getD _ false = _
  symm
  apply foldAgree (n+pre.length) replacement post (w++[w.getD replacement false]) w
  · simp
  · omega
  · omega
  · intro i
    rw [m1892_getD_snoc]
    by_cases lt : i < w.length
    · simp [shift,←len,lt,show i≠w.length by omega]
    by_cases eq : i=w.length
    · simp [shift,←len,lt,eq]
    · have h1 : w.length ≤ i := by omega
      have h2 : w.length ≤ i-1 := by omega
      simp [shift,←len,lt,eq,List.getD_eq_getElem?_getD,List.getElem?_eq_none h1,
        List.getElem?_eq_none h2]

theorem short (n : Nat) (pre post : List Gate) (o r : Nat) (g : Gate) :
    (bypass n pre post o r).size+1=(Circuit.mk (pre++g::post) o).size := by
  simp [bypass,Circuit.size] <;> omega


def source (pre post : List Gate) (a b o : Nat) : Circuit :=
  ⟨pre ++ ⟨.or,[a,b]⟩ :: post,o⟩

def tailOr (n : Nat) (C : Circuit) (w : Nat) : Circuit :=
  ⟨C.gates++[⟨.or,[C.output,w]⟩],n+C.size⟩

theorem prefix_read (gs : List Gate) (w : List Bool) (j : Nat) (room : j<w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ room

theorem tail_eval (n : Nat) (C : Circuit) (w : Nat) (x : Fin n → Bool) :
    (tailOr n C w).eval (List.ofFn x) =
      (C.eval (List.ofFn x) || (C.gates.foldl step (List.ofFn x)).getD w false) := by
  let W := C.gates.foldl step (List.ofFn x)
  have len : W.length = n+C.size := by simp [W,foldLength,Circuit.size]
  change ((C.gates++[Gate.mk .or [C.output,w]]).foldl step (List.ofFn x)).getD (n+C.size) false = _
  rw [List.foldl_append]
  change (W++[_]).getD (n+C.size) false = (W.getD C.output false || W.getD w false)
  rw [m1892_getD_snoc,if_pos len.symm]
  simp [GateOp.eval,W]

theorem source_eval (n : Nat) (pre post : List Gate) (a b o : Nat) (x : Fin n → Bool) :
    (source pre post a b o).eval (List.ofFn x) =
      (let w := pre.foldl step (List.ofFn x);
        (post.foldl step (w++[w.getD a false || w.getD b false])).getD o false) := by
  rw [m1892_eval_eq]
  simp [source,List.foldl_append,step,GateOp.eval]

theorem move_or (n : Nat) (pre post : List Gate) (a b o : Nat) (ab : a<n+pre.length)
    (bb : b<n+pre.length) (fan : FanInTwo (source pre post a b o))
    (absorb : ∀ x : Fin n → Bool, (source pre post a b o).eval (List.ofFn x)=false →
      (pre.foldl step (List.ofFn x)).getD b false=false) :
    let D := tailOr n (bypass n pre post o a) b
    FanInTwo D ∧ D.size = (source pre post a b o).size ∧
      D.gates.getLast? = some ⟨.or,[(bypass n pre post o a).output,b]⟩ ∧
      circuitFun n D = circuitFun n (source pre post a b o) := by
  let B := bypass n pre post o a
  let D := tailOr n B b
  refine ⟨?_,?_,?_,?_⟩
  · intro h hh
    change h ∈ (pre++post.map (change (n+pre.length) a))++[⟨.or,[B.output,b]⟩] at hh
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hh
    rcases hh with (hp|⟨g,hg,rfl⟩)|rfl
    · exact fan h (List.mem_append_left _ hp)
    · obtain ⟨op,ar⟩ := fan g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))
      exact ⟨op,by simpa [change] using ar⟩
    · simp
  · simp [D,B,tailOr,source,bypass,Circuit.size]
  · simp [D,tailOr,B]
  · funext x
    change (tailOr n B b).eval (List.ofFn x) = (source pre post a b o).eval (List.ofFn x)
    rw [tail_eval]
    let w := pre.foldl step (List.ofFn x)
    have bw : b < w.length := by simpa [w,foldLength] using bb
    have back : (B.gates.foldl step (List.ofFn x)).getD b false = w.getD b false := by
      change ((pre++_).foldl step (List.ofFn x)).getD b false = _
      rw [List.foldl_append]
      exact prefix_read _ _ _ bw
    rw [back]
    cases hb : w.getD b false with
    | false =>
      rw [Bool.or_false,source_eval,evalBypass n pre post o a (Or.inl ab)]
      change (post.foldl step (w++[w.getD a false])).getD o false =
        (post.foldl step (w++[w.getD a false || w.getD b false])).getD o false
      rw [hb,Bool.or_false]
    | true =>
      rw [Bool.or_true]
      cases eq : (source pre post a b o).eval (List.ofFn x) with
      | true => rfl
      | false => exact False.elim (Bool.noConfusion (hb.symm.trans (absorb x eq)))

def pins (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
def reads (v : Nat) (g : Gate) := (pins g).contains v
def mark {n : Nat} (S : Finset (Fin n)) (v : Fin n) := decide (v ∈ S)
def atBank (g : Gate) (z : List Bool) := g.op.eval (g.inputs.map fun k => z.getD k false)

lemma eval_from_pins (g : Gate) (z w : List Bool)
    (fan : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (agree : ∀ i ∈ pins g, z.getD i false = w.getD i false) : atBank g z = atBank g w := by
  obtain ⟨op,ins⟩ := g
  rcases fan with ⟨opok,arity⟩
  change op = .and ∨ op = .or ∨ op = .not at opok
  change ins.length ≤ 2 at arity
  rcases opok with rfl|rfl|rfl <;> cases ins with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | nil =>
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢ <;> simp [ha]
    | cons b t =>
      have empty : t=[] := by simpa using arity
      subst t
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢
      rw [ha]
      all_goals
        have hb := agree b (by simp [pins,GateOp.eval])
        simp only [List.getD_eq_getElem?_getD] at hb
        rw [hb]

theorem kept_eq (j : Fin n) (x : Fin n → Bool) (gs : List Gate) :
    (gs.foldl step (List.ofFn x)).getD j.val false=x j := by
  rw [prefix_read _ _ _ (by simp)]
  simp

def quiet (v : Fin n) (gs : List Gate) : Prop := ∀ g∈gs, v.val∉pins g
def near (v : Nat) (a b : List Bool) : Prop :=
  a.length=b.length ∧ ∀ j, j ≠ v → a.getD j false = b.getD j false

theorem snocNear {v : Nat} {a b : List Bool} (ab : near v a b) (val : Bool) :
    near v (a++[val]) (b++[val]) := by
  refine ⟨by simp [ab.1],?_⟩
  intro i ne
  rw [m1892_getD_snoc,m1892_getD_snoc,ab.1,ab.2 i ne]

theorem foldQuiet {v : Fin n} {gs : List Gate} (q : quiet v gs)
    (fan : ∀ g∈gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    {w z : List Bool} (e : near v.val w z) : near v.val (gs.foldl step w) (gs.foldl step z) := by
  induction gs generalizing w z with
  | nil => exact e
  | cons g gs ih =>
    have val := eval_from_pins g w z (fan g (by simp)) (fun i hi =>
      e.2 i (fun eq => q g (by simp) (eq ▸ hi)))
    simp only [List.foldl_cons]
    apply ih (fun i hi => q i (List.mem_cons_of_mem _ hi)) (fun i hi => fan i (List.mem_cons_of_mem _ hi))
    change near v.val (w++[atBank g w]) (z++[atBank g z])
    rw [val]
    exact snocNear e _

theorem rawNear (v : Fin n) (x : Fin n → Bool) : near v.val (List.ofFn x) (List.ofFn (Function.update x v true)) := by
  refine ⟨by simp,?_⟩
  intro i ne
  by_cases hi : i<n
  · let j : Fin n := ⟨i,hi⟩
    have different : j≠v := fun e => ne (congrArg Fin.val e)
    change (List.ofFn x).getD j.val false = (List.ofFn (Function.update x v true)).getD j.val false
    simp [Function.update_of_ne different]
  · simp [List.getD_eq_getElem?_getD,hi]

theorem quiet_of_sole {v : Fin n} {pre post : List Gate} (w : Nat)
    (one : ((pre ++ Gate.mk .or [v.val,w] :: post).filter (fun g => (pins g).contains v.val)).length ≤ 1) :
    quiet v pre ∧ quiet v post := by
  have a : (((pre.filter fun g => (pins g).contains v.val).length) +
      ((post.filter fun g => (pins g).contains v.val).length)+1 ≤ 1) := by
    simpa [List.filter_append,List.filter_cons,pins,GateOp.eval,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using one
  have q (gs : List Gate) (zero : (gs.filter fun g => (pins g).contains v.val).length=0) : quiet v gs := by
    intro g hg hv
    have m : g∈gs.filter fun g => (pins g).contains v.val :=
      List.mem_filter.mpr ⟨hg,List.contains_iff_mem.mpr hv⟩
    have nil := List.length_eq_zero_iff.mp zero
    simp [nil] at m
  exact ⟨q pre (by omega),q post (by omega)⟩

theorem changeNeedsLow (v : Fin n) (pre post : List Gate) (j o : Nat) (jo : j≠v.val) (oo : o≠v.val)
    (fan : FanInTwo (source pre post v.val j o)) (qp : quiet v pre) (qs : quiet v post)
    (x : Fin n → Bool)
    (flips : (source pre post v.val j o).eval (List.ofFn x) ≠
      (source pre post v.val j o).eval (List.ofFn (Function.update x v true))) :
    (pre.foldl step (List.ofFn x)).getD j false=false := by
  let y := Function.update x v true
  let a := pre.foldl step (List.ofFn x)
  let b := pre.foldl step (List.ofFn y)
  have relation : near v.val a b := foldQuiet qp (fun g hg => fan g (List.mem_append_left _ hg)) (rawNear v x)
  cases hj : a.getD j false with
  | false => rfl
  | true =>
    have bj : b.getD j false=true := (relation.2 j jo).symm.trans hj
    have tail := foldQuiet qs (fun g hg => fan g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))) (snocNear relation true)
    apply False.elim
    apply flips
    rw [source_eval,source_eval]
    change (post.foldl step (a++[a.getD v.val false || a.getD j false])).getD o false =
      (post.foldl step (b++[b.getD v.val false || b.getD j false])).getD o false
    simp only [hj,bj,Bool.or_true]
    exact tail.2 o oo



theorem renamed_read (k a : Nat) (g : Gate)
    (h : Pin.reads k g=true) : Pin.reads a (change k a g)=true := by
  have inputs : (Pin.normGate (change k a g)).inputs =
      (Pin.normGate g).inputs.map (shift k a) := by
    rcases g with ⟨op,ins⟩
    cases op <;> simp [Pin.normGate,change,List.map_take]
  apply List.contains_iff_mem.mpr
  rw [inputs]
  exact List.mem_map.mpr ⟨k,List.contains_iff_mem.mp h,by simp [shift]⟩

theorem exposed_count (post : List Gate) (k a : Nat) :
    post.countP (Pin.reads k) ≤ (post.map (change k a)).countP (Pin.reads a) := by
  induction post with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons,List.countP_cons]
    cases h : Pin.reads k g with
    | false => simp only [Bool.false_eq_true,if_false]; split <;> omega
    | true =>
      simp only [renamed_read k a g h,if_true]
      omega

theorem pay_by_consumers (v : Fin n) (pre post : List Gate) (b o : Nat)
    (bb : b<n+pre.length) (fan : FanInTwo (source pre post v.val b o))
    (null : (source pre post v.val b o).eval (List.ofFn (fun _ : Fin n => false))=false)
    (absorb : ∀ x : Fin n → Bool, (source pre post v.val b o).eval (List.ofFn x)=false →
      (pre.foldl step (List.ofFn x)).getD b false=false) :
    ∃ Q : Circuit, FanInTwo Q ∧ Q.size+post.countP (Pin.reads (n+pre.length)) ≤
      (source pre post v.val b o).size ∧ ∀ x : Fin n → Bool, Q.eval (List.ofFn x) =
        (source pre post v.val b o).eval (List.ofFn (Function.update x v false)) := by
  classical
  let D := tailOr n (bypass n pre post o v.val) b
  obtain ⟨dfan,dsize,_,deq⟩ := move_or n pre post v.val b o (by have := v.isLt; omega) bb fan absorb
  change FanInTwo D at dfan
  have evalD (x : Fin n → Bool) : D.eval (List.ofFn x) = (source pre post v.val b o).eval (List.ofFn x) :=
    congrFun deq x
  have expose : post.countP (Pin.reads (n+pre.length)) ≤ D.gates.countP (Pin.reads v.val) := by
    have h := exposed_count post (n+pre.length) v.val
    change _ ≤ ((pre++post.map (change (n+pre.length) v.val))++_).countP (Pin.reads v.val)
    simp only [List.countP_append]
    omega
  let f (i : Fin n) : Option (Fin n) := if i=v then none else some i
  let bank := List.ofFn f
  have absent : bank[v.val]? = some none := by simp [bank,f]
  have pull (x : Fin n → Bool) : Pin.restrict bank x = List.ofFn (Function.update x v false) := by
    simp only [Pin.restrict,bank,List.map_ofFn]
    congr 1
    funext i
    by_cases eq : i=v
    · subst i; simp [Function.comp_def,f]
    · simp [Function.comp_def,f,eq,Function.update_of_ne eq]
  have hn : ∃ x : Fin n → Bool, D.eval (Pin.restrict bank x)=false := by
    refine ⟨fun _ => false,?_⟩
    rw [pull,evalD]
    have eu : Function.update (fun _ : Fin n => false) v false = (fun _ => false) := by
      funext i
      by_cases hi : i=v <;> simp [hi,Function.update_of_ne]
    rw [eu,null]
  obtain ⟨Q,hQ,sz,Qeq⟩ := Pin.eliminate_pin bank v.val D dfan absent hn
  change D.size=(source pre post v.val b o).size at dsize
  exact ⟨Q,hQ,by omega,fun x => (Qeq x).trans ((congrArg D.eval (pull x)).trans (evalD _))⟩

open PEqualNP.MetaComplexity.NestedCover

theorem branch_consumers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (v t : Fin n) (vt : G.Adj v t)
    (vo : v∉A) (vB : v∉B) (iso : ∀ i j, G.Adj i j → i∉A)
    (fresh : t∉B) (outside : ∀ p∈B, ¬G.Adj p t)
    (pre post : List Gate) (b o : Nat) (bb : b<n+pre.length) (bv : b ≠ v.val)
    (fan : FanInTwo (source pre post v.val b o))
    (rep : ∀ x, (source pre post v.val b o).eval (List.ofFn x)=graphFun G A x)
    (sole : (((source pre post v.val b o).gates.filter (fun g => (pins g).contains v.val)).length ≤ 1))
    (depends : ∀ x y : Fin n → Bool, (∀ p∈B, x p=y p) →
      (pre.foldl step (List.ofFn x)).getD b false = (pre.foldl step (List.ofFn y)).getD b false)
    (four : 4 ≤ post.countP (Pin.reads (n+pre.length))) :
    ∃ Q : Circuit, FanInTwo Q ∧ Q.size+4 ≤ (source pre post v.val b o).size ∧
      ∀ x, Q.eval (List.ofFn x)=graphFun G A (Function.update x v false) := by
  classical
  let C := source pre post v.val b o
  have oo : o ≠ v.val := by
    intro ho
    let one : Fin n → Bool := fun i => decide (i=v)
    have actual : C.eval (List.ofFn one)=true := by
      change (C.gates.foldl step (List.ofFn one)).getD o false=true
      rw [ho,kept_eq]
      simp [one]
    have off : graphFun G A one=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have yes : (∃ a∈A, one a=true) ∨ ∃ a b, G.Adj a b ∧ one a=true ∧ one b=true := by
        simpa only [graphFun,Bool.or_eq_true,decide_eq_true_eq] using (show graphFun G A one=true from h)
      rcases yes with ⟨a,ha,va⟩|⟨a,b',ab,va,vb⟩
      · have av : a=v := by simpa [one] using va
        exact vo (av ▸ ha)
      · have av : a=v := by simpa [one] using va
        have bv' : b'=v := by simpa [one] using vb
        exact ab.ne (av.trans bv'.symm)
    exact Bool.noConfusion (actual.symm.trans ((rep one).trans off))
  obtain ⟨quietPre,quietPost⟩ := quiet_of_sole b sole
  let H (x : Fin n → Bool) := (pre.foldl step (List.ofFn x)).getD b false
  have absorb : ∀ x, graphFun G A x=false → H x=false := by
    apply missing_branch A B vt vo vB iso fresh outside H depends false
    intro x _ off on
    apply changeNeedsLow v pre post b o bv oo fan quietPre quietPost x
    rw [rep,rep,off,on]
    decide
  have z : C.eval (List.ofFn (fun _ : Fin n => false))=false := by
    rw [show C=source pre post v.val b o from rfl,rep]
    simp [graphFun]
  obtain ⟨Q,qfan,cost,qeq⟩ := pay_by_consumers v pre post b o bb fan z (fun x h =>
    absorb x ((rep x).symm.trans h))
  exact ⟨Q,qfan,by omega,fun x => (qeq x).trans (rep _)⟩

end PEqualNP.Outside.L_meta_1972.Ports
