import Mathlib
import PEqualNP.Outside.L_meta_3483

namespace Components4970

variable {α : Type} [DecidableEq α]

def Uniform (c : α → α) (s : Finset α) := ∀ x ∈ s, ∀ y ∈ s, c x = c y

def merge (a b x : α) : α := if x = a then b else x

theorem merge_cost (U : Finset α) (c : α → α) (a b : α) :
    (U.image c).card ≤ (U.image (fun x => merge a b (c x))).card + 1 := by
  have sub : U.image c ⊆ insert a (U.image (fun x => merge a b (c x))) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    by_cases h : c x = a
    · simp [h]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨x, hx, by simp [merge,h]⟩
  exact (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)

theorem merge_union {c : α → α} {A B : Finset α} (ha : Uniform c A) (hb : Uniform c B)
    (U : Finset α) : ∃ d : α → α, (U.image c).card ≤ (U.image (d ∘ c)).card + 1 ∧
      Uniform (d ∘ c) (A ∪ B) := by
  rcases A.eq_empty_or_nonempty with rfl|⟨a,aa⟩
  · refine ⟨id,by simp,?_⟩; simpa [Uniform] using hb
  rcases B.eq_empty_or_nonempty with rfl|⟨b,bb⟩
  · refine ⟨id,by simp,?_⟩; simpa [Uniform] using ha
  let d := merge (c b) (c a)
  refine ⟨d,merge_cost U c (c b) (c a),?_⟩
  have same (z) (hz : z ∈ A ∪ B) : d (c z) = c a := by
    rcases Finset.mem_union.mp hz with h|h
    · rw [ha z h a aa]; simp [d,merge]
    · rw [hb z h b bb]; simp [d,merge]
  exact fun x hx y hy => (same x hx).trans (same y hy).symm

/-- Eligible means that the wire is false on the fixed negative test.
    At an AND choose a false child; at an OR both children are false. -/
def Rules (S : ℕ → Finset α) (good paid : ℕ → Prop) (m : ℕ) :=
  ∀ i < m, good i →
    (S i).card ≤ 1 ∨
    (∃ a < i, good a ∧ S i ⊆ S a) ∨
    (paid i ∧ ∃ a < i, ∃ b < i, good a ∧ good b ∧ S i ⊆ S a ∪ S b)

theorem labels (U : Finset α) (S : ℕ → Finset α) (good paid : ℕ → Prop)
    [DecidablePred paid] (m : ℕ) (rules : Rules S good paid m) :
    ∃ c : α → α, U.card ≤ (U.image c).card + ((Finset.range m).filter paid).card ∧
      ∀ w < m, good w → Uniform c (S w) := by
  induction m with
  | zero => exact ⟨id,by simp,by simp⟩
  | succ m ih =>
    obtain ⟨c,rank,inv⟩ := ih (fun i hi => rules i (by omega))
    have cost : ((Finset.range m).filter paid).card ≤ ((Finset.range (m+1)).filter paid).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
    have keep (atM : good m → Uniform c (S m)) : ∀ w < m+1, good w → Uniform c (S w) := by
      intro w hw hg
      rcases Nat.lt_or_ge w m with h|h
      · exact inv w h hg
      · obtain rfl : w=m := by omega
        exact atM hg
    by_cases yes : good m
    · rcases rules m (by omega) yes with tiny|⟨a,lt,ga,sub⟩|⟨pm,a,la,b,lb,ga,gb,sub⟩
      · apply Exists.intro c; refine ⟨by omega,keep (fun _ x hx y hy => ?_)⟩
        exact congrArg c ((Finset.card_le_one.mp tiny) x hx y hy)
      · exact ⟨c,by omega,keep (fun _ x hx y hy => inv a lt ga x (sub hx) y (sub hy))⟩
      · obtain ⟨d,loss,uniform⟩ := merge_union (inv a la ga) (inv b lb gb) U
        have add : ((Finset.range (m+1)).filter paid).card = ((Finset.range m).filter paid).card+1 := by
          rw [Finset.range_add_one, Finset.filter_insert, if_pos pm, Finset.card_insert_of_notMem]
          simp
        refine ⟨d ∘ c,by omega,?_⟩
        intro w hw hg
        rcases Nat.lt_or_ge w m with h|h
        · exact fun x hx y hy => congrArg d (inv w h hg x hx y hy)
        · obtain rfl : w=m := by omega
          exact fun x hx y hy => uniform x (sub hx) y (sub hy)
    · exact ⟨c,by omega,keep (fun h => (yes h).elim)⟩

/-- A family of witnessed stars can overlap. Take one vertex in R per
    connected component of the hypergraph of witnessed leaf sets. -/
theorem components (U R : Finset α) (S : ℕ → Finset α) (good paid : ℕ → Prop)
    [DecidablePred paid] (m : ℕ) (rules : Rules S good paid m)
    (paths : ∀ x ∈ U, ∃ y ∈ R, Relation.ReflTransGen
      (fun u v => ∃ w < m, good w ∧ u ∈ S w ∧ v ∈ S w) x y) :
    U.card ≤ R.card + ((Finset.range m).filter paid).card := by
  obtain ⟨c,cost,flat⟩ := labels U S good paid m rules
  have sub : U.image c ⊆ R.image c := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y,hy,path⟩ := paths x hx
    have eq : c x = c y := by
      clear hy
      induction path with
      | refl => rfl
      | tail _ h ih =>
        obtain ⟨w,hw,hg,ha,hb⟩ := h
        exact ih.trans (flat w hw hg _ ha _ hb)
    exact Finset.mem_image.mpr ⟨y,hy,eq.symm⟩
  have bound := (Finset.card_le_card sub).trans Finset.card_image_le
  omega

end Components4970
namespace Components4970
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3483_aux
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

variable {α : Type} [DecidableEq α] {n : Nat} (C : Circuit)

def probeSet (U : Finset α) (probes : α → Fin n → Bool) (w : Nat) :=
  U.filter (fun x => val C (probes x) w = true)

def offAt (base : Fin n → Bool) (w : Nat) : Prop := val C base w = false

def isMerge (U : Finset α) (probes : α → Fin n → Bool) (base : Fin n → Bool) (w : Nat) : Prop :=
  n ≤ w ∧ (gateAt C (w-n)).op = GateOp.or ∧ offAt C base w ∧ 2 ≤ (probeSet C U probes w).card

theorem physicalRules (ao : IsAO2 n C) (U : Finset α) (probes : α → Fin n → Bool)
    (base : Fin n → Bool)
    (raw : ∀i : Fin n, base i=false → (U.filter (fun x=>probes x i=true)).card ≤ 1) :
    Rules (probeSet C U probes) (offAt C base) (isMerge C U probes base) (n+C.gates.length) := by
  classical
  intro w hw bad
  by_cases small : w<n
  · left
    let i : Fin n := ⟨w,small⟩
    have r (z : Fin n→Bool) : val C z w=z i := val_input C z i
    change val C base w=false at bad
    rw [r base] at bad
    simpa only [probeSet,r] using raw i bad
  let j := w-n
  have eqw : n+j=w := by dsimp [j]; omega
  have hj : j<C.gates.length := by omega
  let g := gateAt C j
  have ge : g=C.gates[j] := List.getD_eq_getElem _ _ hj
  have get : C.gates[j]?=some g := by simp [ge,hj]
  have gm : g∈C.gates := by rw [ge]; exact List.getElem_mem ..
  obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g gm)
  have la : a<w := by rw [←eqw]; exact ao.2.1 j hj a (by change a∈g.inputs; rw [ins]; simp)
  have lb : b<w := by rw [←eqw]; exact ao.2.1 j hj b (by change b∈g.inputs; rw [ins]; simp)
  have ev (x : Fin n → Bool) : val C x w = g.op.eval [val C x a,val C x b] := by
    rw [←eqw,val_gate C x get,ins]
    simp [operand,eqw,la,lb]
  change val C base w=false at bad
  rcases ao.1 g gm with op|op
  · right; left
    have off : val C base a=false ∨ val C base b=false := by
      rw [ev,op] at bad
      cases h : val C base a
      · exact Or.inl rfl
      · exact Or.inr (by simpa [GateOp.eval,h] using bad)
    have sb : probeSet C U probes w ⊆ probeSet C U probes a ∩ probeSet C U probes b := by
      intro i hi
      obtain ⟨mem,hit⟩ := Finset.mem_filter.mp hi
      rw [ev,op] at hit
      have hits : val C (probes i) a=true ∧ val C (probes i) b=true := by simpa [GateOp.eval] using hit
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨mem,hits.1⟩,Finset.mem_filter.mpr ⟨mem,hits.2⟩⟩
    rcases off with h|h
    · exact ⟨a,la,h,fun i hi => (Finset.mem_inter.mp (sb hi)).1⟩
    · exact ⟨b,lb,h,fun i hi => (Finset.mem_inter.mp (sb hi)).2⟩
  · by_cases few : (probeSet C U probes w).card ≤ 1
    · exact Or.inl few
    right; right
    have off : val C base a=false ∧ val C base b=false := by simpa [ev base,op,GateOp.eval] using bad
    refine ⟨⟨by omega,op,bad,by omega⟩,a,la,b,lb,off.1,off.2,?_⟩
    intro i hi
    obtain ⟨mem,hit⟩ := Finset.mem_filter.mp hi
    have hits : val C (probes i) a=true ∨ val C (probes i) b=true := by simpa [ev (probes i),op,GateOp.eval] using hit
    rcases hits with h|h
    · exact Finset.mem_union.mpr (Or.inl (show i ∈ probeSet C U probes a from Finset.mem_filter.mpr ⟨mem,h⟩))
    · exact Finset.mem_union.mpr (Or.inr (show i ∈ probeSet C U probes b from Finset.mem_filter.mpr ⟨mem,h⟩))

end Components4970
namespace Components4970
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3483_aux
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

variable {n : Nat} {A B : Type} [DecidableEq A] [DecidableEq B]

/-- U are the active points; N a are their line neighbourhoods. Each full
    neighbourhood is witnessed as a line star (or has at most one member).
    The second family of tests fixes all lines true and toggles one point. -/
theorem totalOR (C : Circuit) (ao : IsAO2 n C) (U : Finset A) (N : A → Finset B)
    (line : B → Fin n → Bool) (outside : A → Fin n → Bool)
    (anc : Fin n → Bool) (pos : A → Fin n → Bool)
    (leftRaw : ∀a∈U, ∀i : Fin n, outside a i=false → ((N a).filter (fun b=>line b i=true)).card ≤ 1)
    (rootRaw : ∀i : Fin n, anc i=false → (U.filter (fun a=>pos a i=true)).card ≤ 1)
    (monoLeft : ∀a b, b∉N a → ∀i, line b i=true → outside a i=true)
    (monoRoot : ∀b i, line b i=true → anc i=true)
    (c4 : ∀ a∈U, ∀ d∈U, a≠d → (N a ∩ N d).card ≤ 1)
    (star : ∀a∈U, (N a).card ≤ 1 ∨ ∃w < n+C.gates.length, val C (outside a) w=false ∧
        ∀b∈N a, val C (line b) w=true)
    (goal : C.output < n+C.gates.length ∧ val C anc C.output=false ∧
         ∀a∈U, val C (pos a) C.output=true) :
    ∑a∈U, (N a).card ≤ 1 + ((Finset.range (n+C.gates.length)).filter
         (fun w=>n≤w ∧ (gateAt C (w-n)).op=GateOp.or)).card := by
  classical
  let m := n+C.gates.length
  let R := Finset.range m
  let paid := fun a => R.filter (isMerge C (N a) line (outside a))
  let downstream := R.filter (isMerge C U pos anc)
  let ORs := R.filter (fun w => n≤w ∧ (gateAt C (w-n)).op=GateOp.or)
  have mono : Monotone2 C := fun g hg => ⟨ao.1 g hg,(ao.2.2 g hg).le⟩
  have single {D : Type} [DecidableEq D] (W : Finset D) (ts : D→Fin n→Bool)
      (neg : Fin n→Bool) (raw : ∀i : Fin n, neg i=false → (W.filter (fun v=>ts v i=true)).card ≤ 1)
      (w : Nat) (hw : w < m) (f : val C neg w=false) (t : ∀v∈W,val C (ts v) w=true) :
      W.card ≤ 1 + (R.filter (isMerge C W ts neg)).card := by
    obtain ⟨c, rank, consistent⟩ := labels W (probeSet C W ts) (offAt C neg) (isMerge C W ts neg) m
      (physicalRules C ao W ts neg raw)
    have eq : probeSet C W ts w = W := by
      ext v; simp only [probeSet,Finset.mem_filter]; exact ⟨And.left,fun h=>⟨h,t v h⟩⟩
    have hr := consistent w hw f
    rw [eq] at hr
    have hi : (W.image c).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
      exact hr u hu v hv
    change W.card ≤ 1 + ((Finset.range m).filter _).card
    omega
  have row (a : A) (ha : a∈U) : (N a).card≤1+(paid a).card := by
    rcases star a ha with small|⟨w,hw,neg,val⟩
    · omega
    · exact single _ _ _ (leftRaw a ha) w hw neg val
  have pr (a : A) {w : Nat} (h : w∈paid a) : isMerge C (N a) line (outside a) w := (Finset.mem_filter.mp h).2
  have dis : (U : Set A).PairwiseDisjoint paid := by
    intro a ha d hd ad
    apply Finset.disjoint_left.mpr
    intro w wa wd
    have aa := pr a wa
    have dd := pr d wd
    have s : probeSet C (N a) line w ⊆ N a ∩ N d := by
      intro b hb
      obtain ⟨mba,truth⟩ := Finset.mem_filter.mp hb
      apply Finset.mem_inter.mpr; refine ⟨mba,?_⟩
      by_contra no
      have h := acts_mono mono (monoLeft d b no) w truth
      exact Bool.false_ne_true (dd.2.2.1 ▸ h)
    have size := (Finset.card_le_card s).trans (c4 a ha d hd ad)
    have big := aa.2.2.2
    omega
  have across : Disjoint (U.biUnion paid) downstream := by
    apply Finset.disjoint_left.mpr
    intro w wp wd
    obtain ⟨a,_,wa⟩ := Finset.mem_biUnion.mp wp
    have aa := pr a wa
    obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < (probeSet C (N a) line w).card by have h := aa.2.2.2; omega)
    have h := acts_mono mono (monoRoot b) w (Finset.mem_filter.mp hb).2
    have down : isMerge C U pos anc w := (Finset.mem_filter.mp wd).2
    exact Bool.false_ne_true (down.2.2.1 ▸ h)
  have all_in : (U.biUnion paid) ∪ downstream ⊆ ORs := by
    intro w hw
    rcases Finset.mem_union.mp hw with h|h
    · obtain ⟨a,_,wa⟩ := Finset.mem_biUnion.mp h
      have aa := pr a wa
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp wa).1,aa.1,aa.2.1⟩
    · have dd : isMerge C U pos anc w := (Finset.mem_filter.mp h).2
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1,dd.1,dd.2.1⟩
  have pay := Finset.card_le_card all_in
  rw [Finset.card_union_of_disjoint across,Finset.card_biUnion dis] at pay
  have e := Finset.sum_le_sum row
  rw [Finset.sum_add_distrib] at e
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one] at e
  have g : U.card≤1+downstream.card := single _ _ _ rootRaw C.output goal.1 goal.2.1 goal.2.2
  change _ ≤ 1 + ORs.card
  omega
end Components4970
