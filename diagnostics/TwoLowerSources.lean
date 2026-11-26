import PEqualNP.Outside.L_meta_2069
import PEqualNP.Outside.L_meta_2067
namespace Rail5206
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2069
lemma everyDark {m : Nat} (a b : Fin m → Nat) (S : Nat → Sup) (o : Nat)
    (step : ∀ j, S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j))
    (tight : 2*(roots a b S o).card + (merges a b S).card = m+1) :
    ∀ j : Fin m, S (W j)=∅ → Needed a b o (W j) := by
  classical
  let U := roots a b S o
  let M := merges a b S
  let D := darks a b S o
  let P := usedPins a b S o
  change 2*U.card + M.card = m+1 at tight
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun j _ => pc a b S o j (step j))
  change (∑ j, ((P j).card + 2 * (if j ∈ U then 1 else 0) + (if j ∈ M then 1 else 0))) ≤
    ∑ j, (1 + (if j ∈ D then 1 else 0)) at bound
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at bound
  simp at bound
  have sub : D.image W ⊆ insert o (Finset.univ.biUnion P) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨_,nu,h0⟩ := Finset.mem_filter.mp hj
    rcases parent nu with eq | ⟨k,nk,pk⟩
    · exact eq ▸ Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨k,Finset.mem_univ _,?_⟩
      change W j ∈ usedPins a b S o k
      simp only [usedPins,ite_eq_left nk,pins,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
      exact ⟨pk.imp Eq.symm Eq.symm,h0⟩
  have dsub := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ W_inj] at dsub
  have ins := Finset.card_insert_le o (Finset.univ.biUnion P)
  have uni := Finset.card_biUnion_le (s := Finset.univ) (t := P)
  have allEq : ∀ k : Fin m,
      (P k).card + 2*(if k ∈ U then 1 else 0) + (if k ∈ M then 1 else 0) =
        1 + (if k ∈ D then 1 else 0) := by
    intro k
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun k _ => pc a b S o k (step k))).mp ?_ _ (Finset.mem_univ _)
    change (∑ k, ((P k).card + 2 * (if k ∈ U then 1 else 0) + (if k ∈ M then 1 else 0))) =
      ∑ k, (1 + (if k ∈ D then 1 else 0))
    simp only [Finset.sum_add_distrib,← Finset.mul_sum]
    simp
    omega
  intro j zero
  by_contra no
  have notU : j ∉ U := fun h => no (Finset.mem_filter.mp h).2.1
  have notD : j ∉ D := fun h => no (Finset.mem_filter.mp h).2.1
  have notM : j ∉ M := fun h => (Finset.mem_filter.mp h).2.1 zero
  have em : P j=∅ := if_neg no
  have eq := allEq j
  simp [em,notU,notD,notM] at eq
set_option maxHeartbeats 2000000 in
lemma allNeeded {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (A : Fin m → Prop) (o : ℕ)
    (ha : ∀ j, a j < W j) (hb : ∀ j, b j < W j) (neab : ∀ j, a j ≠ b j)
    (hsz : m ≤ 64) (hout : o < 26+m)
    (inp : ∀ t : Vtx, S t.val = {t}) (out0 : S o = ∅)
    (ops : ∀ j, (A j → S (W j) = ∅) ∧ (¬ A j → S (W j) = S (a j) ∪ S (b j)))
    (Q : Vtx → Vtx → ℕ → Prop)
    (qIn : ∀ x y t : Vtx, Q x y t.val → t = x ∨ t = y)
    (qOut : ∀ x y, adjb x y = true → Q x y o)
    (qStep : ∀ x y j, Q x y (W j) →
      (A j → Q x y (a j) ∧ Q x y (b j)) ∧ (¬ A j → Q x y (a j) ∨ Q x y (b j)))
    (sound : ∀ j, Needed a b o (W j) → A j → ∀ x ∈ S (a j), ∀ y ∈ S (b j), adjb x y = true)
    : ∀ j, A j → Needed a b o (W j) := by
  classical
  let U := roots a b S o
  have rootAnd (j : Fin m) (hj : j ∈ U) : A j := by
    by_contra no
    obtain ⟨_,h0,f⟩ := (Finset.mem_filter.mp hj).2
    rw [(ops j).2 no,Finset.union_eq_empty] at h0
    exact f.1.ne_empty h0.1
  have sov (j : Fin m) (hj : j ∈ U) := sound j (Finset.mem_filter.mp hj).2.1 (rootAnd j hj)
  obtain ⟨z,leaf,hside,hstar⟩ := starChoice a b S o sov
  have wlt (j : Fin m) : W j < 26+m := Nat.add_lt_add_left j.isLt _
  have seek (s t : Vtx) (h : adjb s t = true) : ∃ j ∈ U, Cross a b S j s t := by
    suffices run : ∀ w < 26+m, Needed a b o w → Q s t w →
        (s ∈ S w ∨ t ∈ S w) ∨ ∃ j ∈ U, Cross a b S j s t by
      simpa [out0] using run o hout (fun _ ho _ => ho) (qOut s t h)
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw nw qw
      rcases decomp hw with lo | ⟨j,rfl⟩
      · let v : Vtx := ⟨w,lo⟩
        have eq : S w = {v} := inp v
        rcases qIn s t v qw with e | e
        · exact .inl (.inl (by rw [eq,Finset.mem_singleton]; exact e.symm))
        · exact .inl (.inr (by rw [eq,Finset.mem_singleton]; exact e.symm))
      obtain ⟨na,nb⟩ := children nw
      by_cases aj : A j
      · obtain ⟨qa,qb⟩ := (qStep s t j qw).1 aj
        rcases ih _ (ha j) ((ha j).trans hw) na qa with hitsA | got
        · rcases ih _ (hb j) ((hb j).trans hw) nb qb with hitsB | got
          · right
            have single (v) (h1 : v ∈ S (a j)) (h2 : v ∈ S (b j)) : False := by
              have e := sound j nw aj v h1 v h2
              rw [adj_irr] at e
              contradiction
            rcases hitsA with aa | aa <;> rcases hitsB with bb | bb
            · exact (single s aa bb).elim
            · exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,nw,(ops j).1 aj,⟨s,aa⟩,⟨t,bb⟩⟩,.inl ⟨aa,bb⟩⟩
            · exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,nw,(ops j).1 aj,⟨t,aa⟩,⟨s,bb⟩⟩,.inr ⟨aa,bb⟩⟩
            · exact (single t aa bb).elim
          · exact .inr got
        · exact .inr got
      · rcases (qStep s t j qw).2 aj with qa | qb
        · have hh := ih _ (ha j) ((ha j).trans hw) na qa
          rw [(ops j).2 aj]
          simp only [Finset.mem_union]
          tauto
        · have hh := ih _ (hb j) ((hb j).trans hw) nb qb
          rw [(ops j).2 aj]
          simp only [Finset.mem_union]
          tauto
  have st (j) : S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j) := by
    by_cases aj : A j
    · exact .inl ((ops j).1 aj)
    · exact .inr ((ops j).2 aj)
  have low (w : ℕ) (hw : w < 26) : (S w).card ≤ 1 := by
    rw [inp (⟨w,hw⟩ : Vtx)]
    simp
  have bound (j) : leaf j < 26+m := (hside j).elim (fun e => e.symm ▸ (ha j).trans (wlt j))
    (fun e => e.symm ▸ (hb j).trans (wlt j))
  obtain ⟨tight,full,apart⟩ := tallyRoots a b S o z leaf low ha hb st bound hsz
    (fun j hj => (hstar j hj).1) (by
      rintro ⟨s,t⟩ he
      obtain ⟨_,hst,adj⟩ := Finset.mem_filter.mp he
      obtain ⟨j,hj,hcr⟩ := seek s t adj
      obtain ⟨u,hu,eq⟩ := (hstar j hj).2 s t hcr
      exact ⟨j,hj,u,hu,by simpa [tag,min_eq_left hst.le,max_eq_right hst.le] using eq⟩)
  intro j aj
  exact everyDark a b S o st tight j ((ops j).1 aj)

inductive Rail (C : Circuit) (v : Vtx) : ℕ → Prop
  | input : Rail C v v.val
  | next (j : Fin C.gates.length) {w : ℕ} (hop : C.gates[j.val].op=.or)
      (hw : w ∈ C.gates[j.val].inputs) (h : Rail C v w) : Rail C v (26+j.val)

lemma rail_raw (C : Circuit) (v t : Vtx) : Rail C v t.val ↔ t=v := by
  constructor
  · intro h
    generalize eq : t.val=z at h
    cases h with
    | input => exact Fin.ext eq
    | next j op hw hr => have := t.isLt; omega
  · rintro rfl
    exact .input

lemma rail_gate (C : Circuit) (v : Vtx) (j : Fin C.gates.length) :
    Rail C v (26+j.val) ↔ C.gates[j.val].op=.or ∧
      ∃ w∈C.gates[j.val].inputs, Rail C v w := by
  constructor
  · intro h
    generalize eq : 26+j.val=z at h
    cases h with
    | input => have := v.isLt; omega
    | next k op hw hr =>
      have e : j=k := Fin.ext (by omega)
      subst k
      exact ⟨op,_,hw,hr⟩
  · rintro ⟨op,w,hw,hr⟩
    exact .next j op hw hr

def Live (C : Circuit) (w : ℕ) : Prop :=
  ∀ H : ℕ → Prop, H C.output →
    (∀ j : Fin C.gates.length, H (26+j.val) → ∀ i∈C.gates[j.val].inputs, H i) → H w

def SoundCross (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length, Live C (26+j.val) → C.gates[j.val].op=.and →
    ∀ a b : ℕ, C.gates[j.val].inputs=[a,b] → ∀ u v : Vtx,
      Rail C u a → Rail C v b → adjb u v=true


theorem all_and_live (C : Circuit) (size : C.size≤64) (gates : (∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat,
    g.inputs = [a,b] ∧ a≠b ∧ a<26+j ∧ b<26+j)) (correct : (∀ x : Fin 26 → Bool, C.eval (List.ofFn x)=true ↔ ∃ p l : Fin 13,
    p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true))
  (sound : SoundCross C) : ∀ d : Fin C.gates.length, C.gates[d.val].op=.and → Live C (26+d.val) := by
  classical
  let m := C.gates.length
  let g (j : Fin m) := C.gates[j.val]
  have hg (j : Fin m) : C.gates[j.val]? = some (g j) := List.getElem?_eq_getElem j.isLt
  have raw (j : Fin m) := (gates j (g j) (hg j)).2
  choose a b pins ne ha hb using raw
  let A (j : Fin m) := (g j).op = GateOp.and
  have orOp (j : Fin m) (no : ¬ A j) : (g j).op = GateOp.or :=
    ((gates j (g j) (hg j)).1).resolve_left no
  let V (f : Vtx → Bool) w := val C.gates w f = true
  let one (v : Vtx) (u : Vtx) := decide (u=v)
  let S (w : ℕ) : Sup := Finset.univ.filter fun v => Rail C v w
  have mem (w : ℕ) (u : Vtx) : u ∈ S w ↔ Rail C u w := by simp [S]
  have andEv (f : Vtx → Bool) (j : Fin m) (op : A j) :
      V f (W j) ↔ V f (a j) ∧ V f (b j) := by
    have h := val_and C.gates f j.val j.isLt op
    change _ ↔ ∀ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  have orEv (f : Vtx → Bool) (j : Fin m) (op : ¬A j) :
      V f (W j) ↔ V f (a j) ∨ V f (b j) := by
    have h := val_or C.gates f j.val j.isLt (orOp j op)
    change _ ↔ ∃ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  have same (s t : Vtx) : V (pr s t) C.output ↔ adjb s t = true :=
    (correct (pr s t)).trans (pairSpec s t).symm
  have off (s : Vtx) : ¬V (one s) C.output := by
    intro h
    have eq : one s = pr s s := by funext v; simp [one,pr]
    rw [eq] at h
    have h1 := (same s s).1 h
    simp [adj_irr] at h1
  have railOne (v : Vtx) (w : ℕ) (h : Rail C v w) : V (one v) w := by
    induction h with
    | input =>
      change val C.gates v.val (one v) =true
      rw [val_input _ _ _ v.isLt]
      simp [one]
    | @next j i ho hi hr ih =>
      have no : ¬ A j := by change (g j).op ≠ .and; rw [show (g j).op=.or from ho]; intro eq; cases eq
      apply (orEv _ j no).mpr
      change i∈(g j).inputs at hi
      rw [pins j] at hi
      rcases List.mem_cons.mp hi with ha | hb
      · exact Or.inl (ha ▸ ih)
      · obtain e : i=b j := List.mem_singleton.mp hb
        exact Or.inr (e ▸ ih)
  let X : Vtx := 0
  let Y : Vtx := 13
  have edge : adjb X Y=true := by decide
  have hout : C.output < 26+m := by
    by_contra! h
    have yes := (same X Y).2 edge
    change val C.gates C.output (pr X Y) = true at yes
    rw [val_big _ _ _ h] at yes
    contradiction
  have all := allNeeded a b S A C.output ha hb ne size hout ?_ ?_ ?_
    (fun s t w => V (pr s t) w) ?_ (fun s t => (same s t).2) ?_ ?_
  · intro d hd H ho down
    apply all d hd H ho
    intro j hj
    have z := down j hj
    change ∀ i∈(g j).inputs, H i at z
    rw [pins j] at z
    exact ⟨z _ (by simp),z _ (by simp)⟩
  · intro t
    ext s
    rw [mem,rail_raw,Finset.mem_singleton]
    exact eq_comm
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    exact fun v hv => off v (railOne v _ ((mem _ _).mp hv))
  · intro j
    constructor
    · intro aj
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have ho := ((rail_gate C v j).mp ((mem _ _).mp hv)).1
      change (g j).op=.or at ho
      rw [show (g j).op=.and from aj] at ho
      contradiction
    · intro no
      ext v
      simp only [Finset.mem_union,mem]
      change Rail C v (26+j.val) ↔ _
      rw [rail_gate]
      change (g j).op=.or ∧ (∃ i∈(g j).inputs, Rail C v i) ↔ _
      simp [orOp j no,pins j]
  · intro s t v h
    change val C.gates v.val (pr s t) = true at h
    rw [val_input _ _ _ v.isLt] at h
    exact of_decide_eq_true h
  · intro s t j h
    exact ⟨fun op => (andEv _ j op).1 h,fun op => (orEv _ j op).1 h⟩
  · intro j needed op s hs t ht
    apply sound j _ op _ _ (pins j) s t ((mem _ _).mp hs) ((mem _ _).mp ht)
    intro H hOut hstep
    apply needed H hOut
    intro k hk
    have both := hstep k hk
    change ∀ i∈(g k).inputs, H i at both
    rw [pins k] at both
    exact ⟨both _ (by simp),both _ (by simp)⟩

theorem rail_pair {C : Circuit} (gates : (∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat,
    g.inputs = [a,b] ∧ a≠b ∧ a<26+j ∧ b<26+j)) (u v : Vtx) {w : Nat} (hr : Rail C u w) :
    val C.gates w (pr u v) = true := by
  induction hr with
  | input => rw [val_input _ _ _ u.isLt]; simp [pr]
  | @next j z op inz _ ih =>
    have h := (val_or C.gates (pr u v) j.val j.isLt op).2
    apply h
    exact ⟨z,inz,by
      have shape := (gates j.val _ (List.getElem?_eq_getElem j.isLt)).2
      obtain ⟨a,b,eq,_,ha,hb⟩ := shape
      rw [eq] at inz
      rcases (show z=a ∨ z=b by simpa using inz) with rfl|rfl
      · simpa [ha] using ih
      · simpa [hb] using ih⟩

theorem dirty_in_output_cone (C : Circuit) (size : C.size≤64) (gates : (∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat,
    g.inputs = [a,b] ∧ a≠b ∧ a<26+j ∧ b<26+j)) (correct : (∀ x : Fin 26 → Bool, C.eval (List.ofFn x)=true ↔ ∃ p l : Fin 13,
    p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true))
  (dirty : ∃ k : Fin C.gates.length, C.gates[k.val].op=.and ∧ ∃ x : Fin 26 → Bool,
    val C.gates (26+k.val) x=true ∧ C.eval (List.ofFn x)=false) :
    ∃ k : Fin C.gates.length, Live C (26+k.val) ∧ C.gates[k.val].op=.and ∧ ∃ x : Fin 26 → Bool,
      val C.gates (26+k.val) x=true ∧ C.eval (List.ofFn x)=false := by
  classical
  by_cases sound : SoundCross C
  · obtain ⟨k,op,non⟩ := dirty
    exact ⟨k,all_and_live C size gates correct sound k op,op,non⟩
  · simp only [SoundCross, not_forall, not_imp] at sound
    obtain ⟨k,live,op,a,b,ins,u,v,ru,rv,bad⟩ := sound
    have hit := (gates k.val _ (List.getElem?_eq_getElem k.isLt)).2
    obtain ⟨a',b',e,ne,ha,hb⟩ := hit
    have eq : a'=a ∧ b'=b := by simpa only [List.cons.injEq,and_true] using e.symm.trans ins
    subst a'; subst b'
    have eu := rail_pair gates u v ru
    have ev := rail_pair gates v u rv
    have comm : pr v u=pr u v := by funext t; simp [pr,or_comm]
    rw [comm] at ev
    refine ⟨k,live,op,pr u v,?_,?_⟩
    · have h := val_and C.gates (pr u v) k.val k.isLt op
      apply h.mpr
      rw [ins]; simp [ha,hb,eu,ev]
    · exact Bool.eq_false_iff.mpr (fun on => bad ((pairSpec u v).mpr ((correct _).mp on)))
end Rail5206
namespace Source2071

abbrev Gate (m : ℕ) := Fin m
def w {m : ℕ} (j : Gate m) := 26+j.val

inductive Feed {m : ℕ} (a b : Gate m → ℕ) (k : Gate m) : ℕ → Prop
  | here : Feed a b k (w k)
  | left (j : Gate m) (h : Feed a b k (a j)) : Feed a b k (w j)
  | right (j : Gate m) (h : Feed a b k (b j)) : Feed a b k (w j)

def SourceOnly {m : ℕ} (a b : Gate m → ℕ) (A : Gate m → Prop) (d : Gate m) :=
  ∀ k j, A k → A j → (Feed a b k (a j) ∨ Feed a b k (b j)) → k=d

def Live {m : ℕ} (a b : Gate m → ℕ) (o i : ℕ) :=
  ∀ H : ℕ → Prop, H o → (∀ j, H (w j) → H (a j) ∧ H (b j)) → H i

lemma reaches {m} {a b : Gate m → ℕ} {k : Gate m} {o : ℕ} (h : Live a b o (w k)) :
    Feed a b k o := by
  by_contra absent
  have h' := h (fun i => ¬Feed a b k i) absent (fun j hj =>
    ⟨fun ha => hj (.left j ha),fun hb => hj (.right j hb)⟩)
  exact h' .here

def Values {m} (a b : Gate m → ℕ) (A : Gate m → Prop) (D : ℕ → Bool) :=
  ∀ j, (A j → D (w j) = (D (a j) && D (b j))) ∧
    (¬A j → D (w j) = (D (a j) || D (b j)))

lemma source_dirty {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {d k : Gate m} {o}
    (one : SourceOnly a b A d) (ak : A k) (hk : Live a b o (w k)) (Y : ℕ → Bool)
    (value : Values a b A Y) (yk : Y (w k)=true) (yo : Y o=false) : Y (w d)=true := by
  by_cases same : k=d
  · rwa [←same]
  have forward (i : ℕ) (h : Feed a b k i) : Y i=true := by
    induction h with
    | here => exact yk
    | left j hj ih =>
      have nj : ¬A j := fun aj => same (one k j ak aj (.inl hj))
      simp [(value j).2 nj,ih]
    | right j hj ih =>
      have nj : ¬A j := fun aj => same (one k j ak aj (.inr hj))
      simp [(value j).2 nj,ih]
  exact Bool.noConfusion ((forward o (reaches hk)).symm.trans yo)

inductive Parse {m} (a b : Gate m → ℕ) (A : Gate m → Prop) (x y : ℕ) :
    ℕ → ℕ → ℕ → Prop
  | xleaf : Parse a b A x y x 1 0
  | yleaf : Parse a b A x y y 0 1
  | join (j : Gate m) (op : A j) {u v s t : ℕ}
      (ha : Parse a b A x y (a j) u v) (hb : Parse a b A x y (b j) s t) :
      Parse a b A x y (w j) (u+s) (v+t)
  | left (j : Gate m) (op : ¬A j) {u v : ℕ} (ha : Parse a b A x y (a j) u v) :
      Parse a b A x y (w j) u v
  | right (j : Gate m) (op : ¬A j) {u v : ℕ} (hb : Parse a b A x y (b j) u v) :
      Parse a b A x y (w j) u v

lemma feed_le {m} {a b : Gate m → ℕ} (ha : ∀ j,a j < w j) (hb : ∀ j,b j < w j)
    {k : Gate m} {i : ℕ} (f : Feed a b k i) : w k ≤ i := by
  induction f with
  | here => exact le_rfl
  | left j _ h => exact h.trans (ha j).le
  | right j _ h => exact h.trans (hb j).le

def Above {m} (a b : Gate m → ℕ) (A : Gate m → Prop) (w0 : ℕ) (S : Gate m → Prop) :=
  ∀ k, A k → Feed a b k w0 → S k

-- For any chosen proof, a wire with no AND ancestors contributes one leaf.
-- If its only possible AND ancestor is d, it contributes at most two;
-- if d is true on Y and the wire is false, it contributes just one.
lemma bound {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {d : Gate m} {x y i u v}
    (ha : ∀ j,a j<w j) (hb : ∀ j,b j<w j) (one : SourceOnly a b A d)
    {Y : ℕ → Bool} (yd : Y (w d)=true) (val : Values a b A Y)
    (proof : Parse a b A x y i u v) :
    (Above a b A i (fun _ => False) → u+v=1) ∧
    (Above a b A i (fun k => k=d) → u+v ≤ 2 ∧ (Y i=false → u+v=1)) ∧
    (Y i=false → u+v ≤ 3) := by
  induction proof with
  | xleaf => simp
  | yleaf => simp
  | @join j op u v s t pr1 pr2 ih1 ih2 =>
    have oa : Above a b A (a j) (fun k => k=d) := fun k ak f => one k j ak op (.inl f)
    have ob : Above a b A (b j) (fun k => k=d) := fun k ak f => one k j ak op (.inr f)
    obtain ⟨small1,short1⟩ := ih1.2.1 oa
    obtain ⟨small2,short2⟩ := ih2.2.1 ob
    refine ⟨fun empty => (empty j op .here).elim,?_,?_⟩
    · intro only
      have eq : j=d := only j op .here
      have e1 : u+v=1 := ih1.1 (fun k ak f => by
        have same := (oa k ak f).trans eq.symm
        have le := feed_le ha hb f
        rw [same] at le
        exact (Nat.not_le_of_lt (ha j)) le)
      have e2 : s+t=1 := ih2.1 (fun k ak f => by
        have same := (ob k ak f).trans eq.symm
        have le := feed_le ha hb f
        rw [same] at le
        exact (Nat.not_le_of_lt (hb j)) le)
      refine ⟨by omega,?_⟩
      intro h
      rw [eq,yd] at h
      contradiction
    · intro no
      rw [(val j).1 op,Bool.and_eq_false_iff] at no
      rcases no with h | h
      · have := short1 h; omega
      · have := short2 h; omega
  | left j op pr ih =>
    have pull (S : Gate m → Prop) (all : Above a b A (w j) S) : Above a b A (a j) S :=
      fun k ak f => all k ak (.left j f)
    have back (no : Y (w j)=false) := (Bool.or_eq_false_iff.mp (((val j).2 op).symm.trans no)).1
    exact ⟨fun e => ih.1 (pull _ e), fun e => ⟨(ih.2.1 (pull _ e)).1,
      fun n => (ih.2.1 (pull _ e)).2 (back n)⟩,fun n => ih.2.2 (back n)⟩
  | right j op pr ih =>
    have pull (S : Gate m → Prop) (all : Above a b A (w j) S) : Above a b A (b j) S :=
      fun k ak f => all k ak (.right j f)
    have back (no : Y (w j)=false) := (Bool.or_eq_false_iff.mp (((val j).2 op).symm.trans no)).2
    exact ⟨fun e => ih.1 (pull _ e), fun e => ⟨(ih.2.1 (pull _ e)).1,
      fun n => (ih.2.1 (pull _ e)).2 (back n)⟩,fun n => ih.2.2 (back n)⟩

lemma parse_of_value {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {x y}
    (ha : ∀ j,a j<w j) (hb : ∀ j,b j<w j)
    (D : ℕ → Bool) (ops : Values a b A D)
    (raw : ∀ i<26,D i=true → i=x ∨ i=y) :
    ∀ i, i<26+m → D i=true → ∃ u v, Parse a b A x y i u v := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi on
    by_cases small : i<26
    · rcases raw i small on with rfl | rfl
      · exact ⟨1,0,.xleaf⟩
      · exact ⟨0,1,.yleaf⟩
    let j : Gate m := ⟨i-26,by omega⟩
    have eq : i=w j := by dsimp [w,j]; omega
    have pa := ih (a j) ((ha j).trans_le eq.symm.le) (by have := ha j; omega)
    have pb := ih (b j) ((hb j).trans_le eq.symm.le) (by have := hb j; omega)
    rw [eq] at on ⊢
    by_cases op : A j
    · obtain ⟨va,vb⟩ := Bool.and_eq_true_iff.mp (((ops j).1 op).symm.trans on)
      obtain ⟨u,v,pu⟩ := pa va
      obtain ⟨s,t,pv⟩ := pb vb
      exact ⟨_,_,.join j op pu pv⟩
    · rcases Bool.or_eq_true_iff.mp (((ops j).2 op).symm.trans on) with va | vb
      · obtain ⟨u,v,pu⟩ := pa va
        exact ⟨_,_,.left j op pu⟩
      · obtain ⟨s,t,pv⟩ := pb vb
        exact ⟨_,_,.right j op pv⟩


lemma parse_support {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {x y i u v : Nat}
    {X Y : ℕ → Bool} (vx : Values a b A X) (vy : Values a b A Y) (xx : X x=true) (yy : Y y=true)
    (proof : Parse a b A x y i u v) : (u=0 → Y i=true) ∧ (v=0 → X i=true) := by
  induction proof with
  | xleaf => simp [xx]
  | yleaf => simp [yy]
  | @join j op u v s t _ _ ia ib =>
    exact ⟨fun e => by simp [(vy j).1 op,ia.1 (by omega),ib.1 (by omega)],
      fun e => by simp [(vx j).1 op,ia.2 (by omega),ib.2 (by omega)]⟩
  | left j op _ ih => exact ⟨fun e => by simp [(vy j).2 op,ih.1 e],fun e => by simp [(vx j).2 op,ih.2 e]⟩
  | right j op _ ih => exact ⟨fun e => by simp [(vy j).2 op,ih.1 e],fun e => by simp [(vx j).2 op,ih.2 e]⟩

lemma feed_live {m} {a b : Gate m → ℕ} {j : Gate m} {v o : ℕ} (p : Feed a b j v)
    (live : Live a b o v) : Live a b o (w j) := by
  induction p with
  | here => exact live
  | left k f ih => exact ih (fun H ho step => (step k (live H ho step)).1)
  | right k f ih => exact ih (fun H ho step => (step k (live H ho step)).2)

lemma dirty_eq {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {d k : Gate m} {o}
    (one : SourceOnly a b A d) (ak : A k) (hk : Live a b o (w k)) (Y : ℕ → Bool)
    (value : Values a b A Y) (yk : Y (w k)=true) (yo : Y o=false) : k=d := by
  by_contra same
  have forward (i : ℕ) (h : Feed a b k i) : Y i=true := by
    induction h with
    | here => exact yk
    | left j hf ih =>
      have nj : ¬A j := fun aj => same (one k j ak aj (.inl hf))
      simp [(value j).2 nj,ih]
    | right j hf ih =>
      have nj : ¬A j := fun aj => same (one k j ak aj (.inr hf))
      simp [(value j).2 nj,ih]
  exact Bool.noConfusion ((forward o (reaches hk)).symm.trans yo)

lemma local_mark_impossible {m} {a b : Gate m → Nat} {A : Gate m → Prop} {d k : Gate m}
    {o x y : Nat} (ha : ∀ j,a j<w j) (hb : ∀ j,b j<w j) (one : SourceOnly a b A d)
    (ak : A k) (live : Live a b o (w k)) {B X Y Z : Nat → Bool}
    (vb : Values a b A B) (vx : Values a b A X) (vy : Values a b A Y) (vz : Values a b A Z)
    (raw : ∀ i<26,B i=true → i=x ∨ i=y) (xx : X x=true) (yy : Y y=true)
    (on : B (w k)=true) (qx : X (a k)=false ∧ X (b k)=false)
    (qy : Y (a k)=false ∧ Y (b k)=false) (dz : Z (w d)=true) (zo : Z o=false) : False := by
  obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp (((vb k).1 ak).symm.trans on)
  have wk : w k<26+m := Nat.add_lt_add_left k.isLt _
  obtain ⟨u,v,L⟩ := parse_of_value ha hb B vb raw _ ((ha k).trans wk) hl
  obtain ⟨s,t,R⟩ := parse_of_value ha hb B vb raw _ ((hb k).trans wk) hr
  have ps := parse_support vx vy xx yy L
  have qs := parse_support vx vy xx yy R
  rw [qx.1,qy.1] at ps
  rw [qx.2,qy.2] at qs
  have pos : 0<u ∧ 0<v ∧ 0<s ∧ 0<t := by simp_all
  by_cases kz : Z (w k)=true
  · have e := dirty_eq one ak live Z vz kz zo
    have all : Above a b A (a k) (fun _ => False) := by
      intro h ah fh
      have same := one h k ah ak (.inl fh)
      have le := feed_le ha hb fh
      rw [same,←e] at le
      exact (Nat.not_le_of_gt (ha k)) le
    have n := (bound ha hb one dz vz L).1 all
    omega
  · have n := (bound ha hb one dz vz (Parse.join k ak L R)).2.2 (Bool.eq_false_iff.mpr kz)
    omega
end Source2071

namespace Local5206
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2069
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
def UniqueLower (C : Circuit) :=
  ∃ d : Fin C.gates.length, ∀ k j : Fin C.gates.length,
    C.gates[k.val].op = .and → C.gates[j.val].op = .and →
    InCone 26 C k.val j.val → k=d


theorem unique_impossible : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = x3;     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     UniqueLower x1 ∧ x1.size ≤ (64 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, x6 x10 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x4 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ), x6 x10 ∧ ((26 : ℕ) + x10 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 x10 (x1.output - (26 : ℕ))) ∧ x4 x10 x9 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), x5 (PEqualNP.TopForm.opnd x1 x10 x11) x7 = Bool.false ∧ x5 (PEqualNP.TopForm.opnd x1 x10 x11) x8 = Bool.false := by
  rintro ⟨C,h⟩
  dsimp only at h
  obtain ⟨⟨d,hd⟩,size,gates,correct,⟨j,hj,ja,xx,jy,jo⟩,k,ka,live,bon,quiet⟩ := h
  classical
  let root : Fin C.gates.length := ⟨j,hj⟩
  have jop : C.gates[root.val].op=.and := by
    have eq := PEqualNP.Outside.L_meta_2067.gateAt_some (C:=C) (List.getElem?_eq_getElem hj)
    rw [eq] at ja
    exact ja
  obtain ⟨bad,liveBad,badOp,z,dirtyOn,dirtyOut⟩ := Rail5206.dirty_in_output_cone C size gates correct
    ⟨root,jop,xx,jy,jo⟩
  let m := C.gates.length
  let g (j : Fin m) := C.gates[j.val]
  have hg (j : Fin m) : C.gates[j.val]? = some (g j) := List.getElem?_eq_getElem j.isLt
  have raw (j : Fin m) := (gates j (g j) (hg j)).2
  choose a b pins ne ha hb using raw
  let A (j : Fin m) := (g j).op = GateOp.and
  have orOp (j : Fin m) (no : ¬ A j) : (g j).op = GateOp.or :=
    ((gates j (g j) (hg j)).1).resolve_left no
  let V (f : Vtx → Bool) w := val C.gates w f = true
  let one (v : Vtx) (u : Vtx) := decide (u=v)
  have andEv (f : Vtx → Bool) (j : Fin m) (op : A j) :
      V f (W j) ↔ V f (a j) ∧ V f (b j) := by
    have h := val_and C.gates f j.val j.isLt op
    change _ ↔ ∀ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  have orEv (f : Vtx → Bool) (j : Fin m) (op : ¬A j) :
      V f (W j) ↔ V f (a j) ∨ V f (b j) := by
    have h := val_or C.gates f j.val j.isLt (orOp j op)
    change _ ↔ ∃ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  let E (x : Vtx → Bool) (i : ℕ) := val C.gates i x
  have vals (x : Vtx → Bool) : Source2071.Values a b A (E x) := by
    intro j
    constructor
    · intro op
      apply Bool.eq_iff_iff.mpr
      simpa only [V,E,W,Source2071.w,Bool.and_eq_true] using andEv x j op
    · intro no
      apply Bool.eq_iff_iff.mpr
      simpa only [V,E,W,Source2071.w,Bool.or_eq_true] using orEv x j no
  have gj (j : Fin m) : gateAt C j.val=g j := PEqualNP.Outside.L_meta_2067.gateAt_some (hg j)
  have liftStep {z i j : Fin m} (hi : W i = a j ∨ W i = b j)
      (reach : z=i ∨ InCone 26 C z.val i.val) : InCone 26 C z.val j.val := by
    have mem : W i ∈ (gateAt C j.val).inputs := by
      rw [gj,pins j]
      rcases hi with h|h <;> simp [h]
    have lt : i.val<j.val := by
      have ai := ha j
      have bi := hb j
      simp only [W] at hi
      rcases hi with h|h <;> omega
    exact (PEqualNP.Outside.L_meta_2067.inCone_iff 26 C z.val j.val).2
      ⟨j.isLt,i.val,lt,mem,reach.imp (congrArg Fin.val) id⟩
  have origin (z : Fin m) (i : ℕ) (f : Source2071.Feed a b z i) :
      ∃ j : Fin m, W j=i ∧ (z=j ∨ InCone 26 C z.val j.val) := by
    induction f with
    | here => exact ⟨z,rfl,Or.inl rfl⟩
    | left j _ ih =>
      obtain ⟨k,hk,root⟩ := ih
      exact ⟨j,rfl,.inr (liftStep (.inl hk) root)⟩
    | right j _ ih =>
      obtain ⟨k,hk,root⟩ := ih
      exact ⟨j,rfl,.inr (liftStep (.inr hk) root)⟩
  have unique : Source2071.SourceOnly a b A d := by
    intro z j az aj f
    apply hd z j az aj
    rcases f with f | f
    · obtain ⟨k,hk,root⟩ := origin z _ f
      exact liftStep (.inl hk) root
    · obtain ⟨k,hk,root⟩ := origin z _ f
      exact liftStep (.inr hk) root
  have kh : k < C.gates.length := by
    by_contra hh
    change (C.gates.getD k ⟨.or,[]⟩).op=.and at ka
    rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hh)] at ka
    cases ka
  let r : Fin m := ⟨k,kh⟩
  have kr : A r := by change (g r).op=.and; rwa [←gj r]
  have liveB : Source2071.Live a b C.output (W bad) := by
    intro H ho step
    apply liveBad H ho
    intro j hj i hin
    change i∈(g j).inputs at hin
    rw [pins j] at hin
    rcases List.mem_cons.mp hin with e|rest
    · exact e ▸ (step j hj).1
    · exact (List.mem_singleton.mp rest) ▸ (step j hj).2
  have sourceOn := Source2071.source_dirty unique badOp liveB (E z) (vals z) dirtyOn dirtyOut
  have chain (i j : Fin m) (h : InCone 26 C i.val j.val) : Source2071.Feed a b i (W j) := by
    induction jj : j.val using Nat.strong_induction_on generalizing j with
    | ind n ih =>
      obtain ⟨_,v,lt,mem,e|co⟩ := (PEqualNP.Outside.L_meta_2067.inCone_iff 26 C i.val j.val).1 h
      all_goals
        let u : Fin m := ⟨v,lt.trans j.isLt⟩
        rw [gj j,pins j] at mem
        have cond : W u=a j ∨ W u=b j := by simpa [W,u] using mem
      · have eq : u=i := Fin.ext e.symm
        have f : Source2071.Feed a b i (W u) := eq ▸ Source2071.Feed.here
        rcases cond with h|h
        · exact .left j (h ▸ f)
        · exact .right j (h ▸ f)
      · have f := ih v (by omega) u co rfl
        rcases cond with h|h
        · exact .left j (h ▸ f)
        · exact .right j (h ▸ f)
  have need : Source2071.Live a b C.output (W r) := by
    rcases live with e|co
    · exact fun H ho _ => e ▸ ho
    · obtain ⟨idx,prev,lt,_,_⟩ := (PEqualNP.Outside.L_meta_2067.inCone_iff 26 C k (C.output-26)).1 co
      let out : Fin m := ⟨C.output-26,idx⟩
      have eq : W out=C.output := by change 26+(C.output-26)=C.output; omega
      have f := chain r out co
      apply Source2071.feed_live f
      exact fun H ho _ => eq ▸ ho
  let X : Vtx := 0
  let Y : Vtx := 13
  have qa : PEqualNP.TopForm.opnd C k 0=a r := by simp [PEqualNP.TopForm.opnd,show gateAt C k=g r from gj r,pins]
  have qb : PEqualNP.TopForm.opnd C k 1=b r := by simp [PEqualNP.TopForm.opnd,show gateAt C k=g r from gj r,pins,List.getD_eq_getElem?_getD]
  apply Source2071.local_mark_impossible (x:=X.val) (y:=Y.val) ha hb unique kr need
    (vals (pr X Y)) (vals (pairInput X X)) (vals (pairInput Y Y)) (vals z) ?_ ?_ ?_ bon ?_ ?_ sourceOn dirtyOut
  · intro i hi hi'
    change val C.gates i (pr X Y)=true at hi'
    rw [val_input _ _ _ hi] at hi'
    exact (of_decide_eq_true hi').imp (congrArg Fin.val) (congrArg Fin.val)
  · change val C.gates X.val (pairInput X X)=true
    rw [val_input _ _ _ X.isLt]; simp [pairInput]
  · change val C.gates Y.val (pairInput Y Y)=true
    rw [val_input _ _ _ Y.isLt]; simp [pairInput]
  · exact ⟨qa ▸ (quiet 0).1,qb ▸ (quiet 1).1⟩
  · exact ⟨qa ▸ (quiet 0).2,qb ▸ (quiet 1).2⟩
end Local5206
