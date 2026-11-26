import PEqualNP.Outside.L_meta_2069
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
