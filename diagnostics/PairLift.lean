import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8323

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pgRel (u v : Fin 42) : Bool :=
  decide (u.val < 21 ∧ 21 ≤ v.val ∧
    (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))

def adj (u v : Fin 42) : Bool :=
  pgRel u v || pgRel v u

def computes (C : Circuit) : Prop :=
  ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 42, pgRel u v = true ∧ x u = true ∧ x v = true

def clean (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
    ∀ x : Fin 42 → Bool, (C.wires (List.ofFn x)).getD (42 + j) false = true →
      C.eval (List.ofFn x) = true

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

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_append_eq]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def wval (C : Circuit) (x : Fin 42 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wval_input (C : Circuit) (x : Fin 42 → Bool) (i : Fin 42) :
    wval C x i.val = x i := by
  unfold wval
  rw [wires_eq_run, run_input _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

lemma wval_gate (C : Circuit) (x : Fin 42 → Bool) (j : ℕ) (hj : j < C.gates.length) :
    wval C x (42 + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < 42 + j then wval C x i else false) := by
  unfold wval
  have := run_gate C.gates (List.ofFn x) j hj
  simpa [wires_eq_run] using this

lemma wval_oob (C : Circuit) (x : Fin 42 → Bool) (w : ℕ) (hw : 42 + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [wires_eq_run, List.getD_eq_default]
  rw [run_length]; simp; omega

lemma eval_eq_wval (C : Circuit) (x : Fin 42 → Bool) :
    C.eval (List.ofFn x) = wval C x C.output := rfl

lemma mono_wval (C : Circuit) (hM : Monotone2 C) {x y : Fin 42 → Bool}
    (hxy : ∀ i : Fin 42, x i = true → y i = true) :
    ∀ w : ℕ, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < 42
    · have hw' : wval C x (⟨w, h1⟩ : Fin 42).val = true := hw
      rw [wval_input] at hw'
      change wval C y (⟨w, h1⟩ : Fin 42).val = true
      rw [wval_input]
      exact hxy ⟨w, h1⟩ hw'
    · by_cases h2 : w < 42 + C.gates.length
      · set j := w - 42
        have hwj : w = 42 + j := by omega
        have hj : j < C.gates.length := by omega
        rw [hwj] at hw ⊢
        rw [wval_gate C x j hj] at hw
        rw [wval_gate C y j hj]
        have hop := (hM C.gates[j] (List.getElem_mem hj)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hw ⊢
          intro i hi
          have hwi := hw i hi
          split_ifs at hwi ⊢ with hilt
          · exact ih i (by omega) hwi
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hw ⊢
          rcases hw with ⟨i, hi, hwi⟩
          refine ⟨i, hi, ?_⟩
          split_ifs at hwi ⊢ with hilt
          · exact ih i (by omega) hwi
      · rw [wval_oob C x w (by omega)] at hw
        cases hw

def singleIn (v : Fin 42) : Fin 42 → Bool :=
  fun i => decide (i = v)


def probes : List Nat := [4398044413952,2097151,2656437797206,87047805064,3852596283296,275666561028,1308358877393,332056297514,1125340188163,2817909740080,151536812297,562375589952,39504716800,792471801925,4146828739200,2358493053988,43042999554,1847175676952,72277692418,147270975497,2226544969728]
def probe (m : Nat) (v : Fin 42) := m.testBit v.val

private theorem zeroProbe : ∃m∈probes,True := by decide +kernel
private theorem negativeProbes : ∀m∈probes,∀p q,pgRel p q=true → probe m p=true → probe m q=false := by decide +kernel
private theorem coverPair : ∀p q,adj p q=false → ∃m∈probes,probe m p=true ∧ probe m q=true := by decide +kernel

def probeClean (C : Circuit) := ∀j (hj : j<C.gates.length), C.gates[j].op=.and →
  ∀m∈probes,wval C (probe m) (42+j)=false

private def hitOne (C : Circuit) (x : Fin 42 → Bool) (w : Nat) :=
  ∃p,x p=true ∧ wval C (singleIn p) w=true

private theorem impossibleAnd (C : Circuit) (mc : Monotone2 C) (rightC : computes C)
    (silent : probeClean C) (x : Fin 42 → Bool) (negative : C.eval (List.ofFn x)=false)
    (j : Nat) (hj : j<C.gates.length) (op : C.gates[j].op=.and)
    (ind : ∀i<42+j,wval C x i=true → hitOne C x i)
    (fire : wval C x (42+j)=true) : False := by
  have width := (mc _ (List.getElem_mem hj)).2
  rw [wval_gate C x j hj,op] at fire
  simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at fire
  have sources (i : Nat) (hi : i∈C.gates[j].inputs) : i<42+j ∧ hitOne C x i := by
    have on := fire i hi
    split_ifs at on with before
    · exact ⟨before,ind i before on⟩
    · contradiction
  have incFree (p q : Fin 42) (hp : x p=true) (hq : x q=true) :
      ∃m∈probes,probe m p=true ∧ probe m q=true := by
    apply coverPair
    apply Bool.eq_false_iff.mpr
    intro h
    have y : C.eval (List.ofFn x)=true := by
      apply (rightC _).2
      rcases Bool.or_eq_true.mp h with e|e
      · exact ⟨p,q,e,hp,hq⟩
      · exact ⟨q,p,e,hq,hp⟩
    rw [negative] at y
    contradiction
  have liftOne (i m : Nat) (p : Fin 42) (hp : probe m p=true) (hi : wval C (singleIn p) i=true) :
      wval C (probe m) i=true := by
    apply mono_wval C mc _ i hi
    intro k hk
    have e : k=p := of_decide_eq_true hk
    exact e ▸ hp
  have finish (m : Nat) (hm : m∈probes)
      (on : ∀i∈C.gates[j].inputs,i<42+j ∧ wval C (probe m) i=true) : False := by
    have zero := silent j hj op m hm
    rw [wval_gate C (probe m) j hj,op] at zero
    have high : GateOp.and.eval (C.gates[j].inputs.map fun i=>
        if i<42+j then wval C (probe m) i else false)=true := by
      simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
      intro i hi
      rw [if_pos (on i hi).1]
      exact (on i hi).2
    rw [zero] at high
    contradiction
  cases ports : C.gates[j].inputs with
  | nil =>
    obtain ⟨m,hm,_⟩ := zeroProbe
    exact finish m hm (by simp [ports])
  | cons a rest =>
    obtain ⟨la,p,xp,ap⟩ := sources a (by simp [ports])
    cases rest with
    | nil =>
      obtain ⟨m,hm,pm,_⟩ := incFree p p xp xp
      apply finish m hm
      simpa [ports] using And.intro la (liftOne a m p pm ap)
    | cons b tail =>
      have empty : tail=[] := by
        simp only [ports,List.length_cons] at width
        exact List.length_eq_zero_iff.mp (by omega)
      subst tail
      obtain ⟨lb,q,xq,bq⟩ := sources b (by simp [ports])
      obtain ⟨m,hm,pm,qm⟩ := incFree p q xp xq
      apply finish m hm
      intro i hi
      simp only [ports,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl
      · exact ⟨la,liftOne _ _ _ pm ap⟩
      · exact ⟨lb,liftOne _ _ _ qm bq⟩

theorem clean_iff_probes (C : Circuit) (mc : Monotone2 C) (rightC : computes C) :
    clean C ↔ probeClean C := by
  constructor
  · intro hc j hj op m hm
    apply Bool.eq_false_iff.mpr
    intro on
    have yes := hc j C.gates[j] (List.getElem?_eq_getElem hj) op (probe m) on
    obtain ⟨p,q,e,hp,hq⟩ := (rightC _).1 yes
    rw [negativeProbes m hm p q e hp] at hq
    contradiction
  · intro silent j g hg ha x on
    by_contra failure
    have negative : C.eval (List.ofFn x)=false := Bool.eq_false_iff.mpr failure
    have sources : ∀ w,wval C x w=true → hitOne C x w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro fire
        by_cases raw : w<42
        · let v : Fin 42 := ⟨w,raw⟩
          refine ⟨v,(wval_input C x v).symm.trans fire,?_⟩
          change wval C (singleIn v) v.val=true
          rw [wval_input]
          simp [singleIn]
        by_cases available : w<42+C.gates.length
        · obtain ⟨k,rfl⟩ : ∃k,w=42+k := ⟨w-42,by omega⟩
          have hk : k<C.gates.length := by omega
          have ops := (mc _ (List.getElem_mem hk)).1
          simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
          rcases ops with han|hor
          · exact (impossibleAnd C mc rightC silent x negative k hk han ih fire).elim
          · rw [wval_gate C x k hk,hor] at fire
            simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at fire
            obtain ⟨i,hi,lit⟩ := fire
            split_ifs at lit with before
            · obtain ⟨p,xp,ip⟩ := ih i before lit
              refine ⟨p,xp,?_⟩
              rw [wval_gate C (singleIn p) k hk,hor]
              simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
              exact ⟨i,hi,by rw [if_pos before];exact ip⟩
            · contradiction
        · rw [wval_oob C x w (by omega)] at fire
          contradiction
    have hj : j<C.gates.length := by
      by_contra! far
      rw [List.getElem?_eq_none far] at hg
      contradiction
    have ge : C.gates[j]=g := by simpa [List.getElem?_eq_getElem hj] using hg
    exact impossibleAnd C mc rightC silent x negative j hj (ge ▸ ha) (fun i _ => sources i) on

end PEqualNP.Outside.L_meta_8323
