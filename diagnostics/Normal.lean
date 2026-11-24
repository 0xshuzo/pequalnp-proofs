import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
namespace Repair5284
def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]

theorem keepW (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (W gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g t ih =>
    change (W t (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := {C with gates := C.gates.set j g}
def off : Gate := ⟨.or,[]⟩
def literal {n : ℕ} (p r : Fin n) : Gate := ⟨.and,[p.val,r.val]⟩

theorem take_set' {α : Type} (L : List α) (k : ℕ) (h : k<L.length) (g : α) :
    L.set k g = L.take k ++ g :: L.drop (k+1) := by
  induction L generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change a :: t.set k g = a :: (t.take k ++ g :: t.drop (k+1))
      exact congrArg (List.cons a) (ih k (by simpa using h))

theorem psize (C : Circuit) (j : ℕ) (g : Gate) : (patch C j g).size = C.size := by
  change (C.gates.set j g).length = C.gates.length
  simp

theorem pop (C : Circuit) (j i : ℕ) (g : Gate) (hj : j<C.size) :
    gateAt (patch C j g) i = if i=j then g else gateAt C i := by
  change (C.gates.set j g).getD i _ = _
  rw [List.getD_eq_getElem?_getD]
  by_cases eq : i=j
  · subst i
    simp [List.getElem?_set,hj]
  · rw [if_neg eq,List.getElem?_set_ne (Ne.symm eq)]
    exact (List.getD_eq_getElem?_getD ..).symm

theorem pmono {C : Circuit} (m : Monotone2 C) {j : ℕ} (hj : j<C.size) {g : Gate}
    (good : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    Monotone2 (patch C j g) := by
  intro x hx
  change x∈C.gates.set j g at hx
  rw [take_set' C.gates j hj] at hx
  rcases List.mem_append.mp hx with hp | ht
  · exact m _ (List.mem_of_mem_take hp)
  · rcases List.mem_cons.mp ht with rfl | h
    · exact good
    · exact m _ (List.mem_of_mem_drop h)

def value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem pairValue {n : ℕ} (pre : List Gate) (x : Fin n → Bool) (u v : Fin n) :
    value (literal u v) (W pre (List.ofFn x)) = (x u && x v) := by
  have atRaw (w : Fin n) : (W pre (List.ofFn x)).getD w.val false = x w := by
    rw [keepW _ _ _ (by simp)]
    simp [ofFn_getD]
  simp [literal,value,GateOp.eval,atRaw]

theorem offValue (w : List Bool) : value off w=false := rfl

theorem ppLe {n : ℕ} (C : Circuit) (m : Monotone2 C) {j : ℕ} (hj : j<C.size)
    (g f : Gate) (x : Fin n → Bool)
    (rise : value g (W (C.gates.take j) (List.ofFn x)) = true →
      value f (W (C.gates.take j) (List.ofFn x)) = true) :
    Le ((patch C j g).wires (List.ofFn x)) ((patch C j f).wires (List.ofFn x)) := by
  let w := W (C.gates.take j) (List.ofFn x)
  have op (a : Gate) (ha : a ∈ C.gates.drop (j+1)) : a.op=.and ∨ a.op=.or := by
    simpa using (m _ (List.mem_of_mem_drop ha)).1
  have step (h : Gate) : (patch C j h).wires (List.ofFn x) =
      W (C.gates.drop (j+1)) (w++[value h w]) := by
    change W (C.gates.set j h) _ = _
    rw [take_set' _ _ hj]
    simp [W,w,value,List.foldl_append]
  rw [step,step]
  apply W_mono _ op _ _ (by simp)
  intro i h
  rw [getD_snoc] at h ⊢
  by_cases lt : i<w.length
  · simpa [lt] using h
  by_cases eq : i=w.length
  · simpa [lt,eq] using rise (by simpa [lt,eq] using h)
  · simpa [lt,eq] using h

theorem orig (C : Circuit) {j : ℕ} (hj : j<C.size) : patch C j (gateAt C j) = C := by
  have eq : gateAt C j = C.gates[j] := by
    change C.gates.getD j _ = _
    exact List.getD_eq_getElem _ _ hj
  cases C with
  | mk gs out =>
    change (⟨gs.set j (gateAt ⟨gs,out⟩ j),out⟩ : Circuit) = _
    rw [eq]
    simp

theorem selfWire {n : ℕ} (C : Circuit) {j : ℕ} (hj : j<C.size)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = value g (W (C.gates.take j) (List.ofFn x)) := by
  let w := W (C.gates.take j) (List.ofFn x)
  have len : w.length=n+j := by simp [w,W_length,List.length_take,Nat.min_eq_left hj.le]
  change (W (C.gates.set j g) (List.ofFn x)).getD (n+j) false = _
  rw [take_set' _ _ hj]
  have rs : W (C.gates.take j ++ g :: C.gates.drop (j+1)) (List.ofFn x) =
      W (C.gates.drop (j+1)) (w++[value g w]) := by simp [W,w,value,List.foldl_append]
  rw [rs,keepW _ _ _ (by simp [len]),←len]
  simp [w]

def word {n : ℕ} (e : Sym2 (Fin n)) (v : Fin n) := decide (v∈e)
def lost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :=
  G.edgeFinset.filter fun e => (patch C j off).eval (List.ofFn (word e))=false

def One (n : ℕ) (B : Circuit) : Prop := ∀ j < B.size, (gateAt B j).op=.and →
  ∀ v : Fin n, gateVal n B j (pairInput v v)=false

noncomputable def bad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun j => (gateAt C j).op=.and ∧
    ∃ x, gateVal n C j x=true ∧ graphFun G ∅ x=false

theorem bad_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
    j ∈ bad G C ↔ j<C.size ∧ (gateAt C j).op=.and ∧
    ∃ x, gateVal n C j x=true ∧ graphFun G ∅ x=false := by classical simp [bad]

theorem hit_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x=true ↔ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true := by simp [graphFun]

theorem selfOff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    graphFun G ∅ (pairInput u u) = false := by simp [graphFun,pairInput]

theorem pairOn {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {u v : Fin n} (adj : G.Adj u v) :
    graphFun G ∅ (word s(u,v))=true :=
  (hit_iff _ _).2 ⟨u,v,adj,by simp [word],by simp [word]⟩

theorem evalMono {n : ℕ} (B : Circuit) (m : Monotone2 B) {x y : Fin n → Bool}
    (le : ∀ i, x i=true → y i=true) : B.eval (List.ofFn x)=true → B.eval (List.ofFn y)=true := by
  refine W_mono B.gates (fun g hg => by simpa using (m g hg).1) (List.ofFn x) (List.ofFn y) (by simp) ?_ B.output
  intro i
  rw [ofFn_getD,ofFn_getD]
  by_cases hi : i<n
  · simpa [hi] using le ⟨i,hi⟩
  · simp [hi]

theorem improve {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (mono : Monotone2 C) (exactC : circuitFun n C=graphFun G ∅)
    (one : One n C) (j : ℕ) (dirty : j ∈ bad G C) (few : (lost G C j).card ≤ 1) :
    ∃ B : Circuit, Monotone2 B ∧ B.size=C.size ∧ circuitFun n B=graphFun G ∅ ∧ One n B ∧
      (bad G B).card < (bad G C).card := by
  classical
  obtain ⟨hj,agr,witness⟩ := bad_iff.mp dirty
  let pre := C.gates.take j
  have chooseGate : ∃ f : Gate,
      (f.op∈({GateOp.and,GateOp.or} : Set GateOp) ∧ f.inputs.length ≤ 2) ∧
      (∀ x, graphFun G ∅ x=false → value f (W pre (List.ofFn x))=false) ∧
      (∀ e ∈ lost G C j, value f (W pre (List.ofFn (word e)))=true) := by
    by_cases live : (lost G C j).Nonempty
    · obtain ⟨e,he⟩ := live
      induction e using Sym2.inductionOn with
      | _ u v =>
        have heG := (Finset.mem_filter.mp he).1
        have adj : G.Adj u v := by simpa using heG
        refine ⟨literal u v,by simp [literal],?_,?_⟩
        · intro x hf
          rw [pairValue]
          cases a : x u <;> cases b : x v <;> simp
          have ht := (hit_iff G x).2 ⟨u,v,adj,a,b⟩
          rw [hf] at ht
          contradiction
        · intro e' he'
          have eq := (Finset.card_le_one.mp few) e' he' s(u,v) he
          rw [eq,pairValue]
          simp [word]
    · refine ⟨off,by simp [off],fun _ _ => rfl,?_⟩
      exact fun e he => (live ⟨e,he⟩).elim
  obtain ⟨f,good,safe,saves⟩ := chooseGate
  let B := patch C j f
  have bm : Monotone2 B := pmono mono hj good
  have bs : B.size=C.size := psize ..
  have down (x : Fin n → Bool) (hf : graphFun G ∅ x = false) :
      Le (B.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    have h := ppLe C mono hj f (gateAt C j) x (by
      rw [safe x hf]
      intro z; contradiction)
    rwa [orig C hj] at h
  have ed (u v : Fin n) (adj : G.Adj u v) : B.eval (List.ofFn (word s(u,v)))=true := by
    let x := word s(u,v)
    have goodC : C.eval (List.ofFn x)=true := (congrFun exactC x).trans (pairOn G adj)
    by_cases lostEdge : s(u,v) ∈ lost G C j
    · have high := saves _ lostEdge
      have h := ppLe C mono hj (gateAt C j) f x (fun _ => high)
      rw [orig C hj] at h
      exact h C.output goodC
    · have eG : s(u,v) ∈ G.edgeFinset := by simpa using adj
      have yes : (patch C j off).eval (List.ofFn x)=true := by
        cases test : (patch C j off).eval (List.ofFn x) with
        | false => exact (lostEdge (Finset.mem_filter.mpr ⟨eG,test⟩)).elim
        | true => rfl
      have h := ppLe C mono hj off f x (by intro z; contradiction)
      exact h C.output yes
  have exactB : circuitFun n B=graphFun G ∅ := by
    funext x
    cases out : graphFun G ∅ x with
    | false =>
      cases ev : B.eval (List.ofFn x) with
      | false => exact ev
      | true =>
        have ht := down x out C.output ev
        have hf := (congrFun exactC x).trans out
        exact (Bool.noConfusion (ht.symm.trans hf)).elim
    | true =>
      obtain ⟨u,v,adj,hu,hv⟩ := (hit_iff G x).1 out
      apply evalMono B bm _ (ed u v adj)
      intro w hw
      have hvw : w=u ∨ w=v := by simpa [word] using hw
      rcases hvw with rfl | rfl <;> assumption
  have singles : One n B := by
    intro k hkb and v
    by_cases eq : k=j
    · subst k
      rw [selfWire C hj f]
      exact safe _ (selfOff G v)
    · have same := pop C j k f hj
      rw [if_neg eq] at same
      have hfalse := one k (bs ▸ hkb) (same ▸ and) v
      cases e : gateVal n B k (pairInput v v) with
      | false => rfl
      | true =>
        have hit := down _ (selfOff G v) (n+k) e
        exact (Bool.noConfusion (hit.symm.trans hfalse)).elim
  have subset : bad G B ⊆ (bad G C).erase j := by
    intro k hk
    obtain ⟨hb,ag,x,hx,hf⟩ := bad_iff.mp hk
    by_cases eq : k=j
    · subst k
      have hx' : gateVal n (patch C j f) j x=true := hx
      rw [selfWire C hj f, safe x hf] at hx'
      contradiction
    · refine Finset.mem_erase.mpr ⟨eq, bad_iff.mpr ⟨bs ▸ hb,?_,x,down x hf (n+k) hx,hf⟩⟩
      have h := pop C j k f hj
      rw [if_neg eq] at h
      exact h ▸ ag
  have bnd := Finset.card_le_card subset
  have erase := Finset.card_erase_add_one dirty
  exact ⟨B,bm,bs,exactB,singles,by omega⟩


theorem normal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let F := graphFun G ∅
      let one (B : Circuit) := ∀ j < B.size, (gateAt B j).op=.and →
        ∀ v : Fin n, gateVal n B j (pairInput v v)=false
      let loss (B : Circuit) (j : ℕ) := G.edgeFinset.filter fun e =>
        ({B with gates := B.gates.set j ⟨.or,[]⟩} : Circuit).eval (List.ofFn fun v : Fin n => decide (v∈e)) = false
      let fixed (B : Circuit) := ∀ j < B.size, (gateAt B j).op=.and →
        (∃ x, gateVal n B j x=true ∧ F x=false) → 2 ≤ (loss B j).card
      ∀ C : Circuit, Monotone2 C → circuitFun n C=F → one C →
      ∃ D : Circuit, Monotone2 D ∧ D.size≤C.size ∧ circuitFun n D=F ∧ one D ∧ fixed D := by
  intro n G inst F one loss fixed C mono exactC single
  classical
  let fits (w : ℕ) := ∃ D : Circuit, Monotone2 D ∧ D.size≤C.size ∧ circuitFun n D=F ∧
    One n D ∧ (bad G D).card=w
  have existsW : ∃ w, fits w := ⟨_,C,mono,le_rfl,exactC,single,rfl⟩
  obtain ⟨B,bm,bs,be,bo,cost⟩ := Nat.find_spec existsW
  refine ⟨B,bm,bs,be,bo,?_⟩
  intro j hin and w
  have bj : j∈bad G B := bad_iff.mpr ⟨hin,and,w⟩
  by_contra! low
  have few : (lost G B j).card≤1 := by change (lost G B j).card<2 at low; omega
  obtain ⟨K,km,ks,ke,ko,strict⟩ := improve G B bm be bo j bj few
  have ok : fits (bad G K).card := ⟨K,km,ks.le.trans bs,ke,ko,rfl⟩
  have lb := Nat.find_min' existsW ok
  omega

end Repair5284
