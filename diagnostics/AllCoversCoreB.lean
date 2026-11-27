import PEqualNP.Defs
namespace Covers18597

open PEqualNP.AndCount

abbrev V := Fin 42

abbrev rel (a b : V) : Prop :=
  a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)

abbrev adj (a b : V) : Prop := rel a b ∨ rel b a

def graph : SimpleGraph V := SimpleGraph.fromRel rel

def color (v : V) : Bool := decide (v.val < 21)

lemma edge_iff (a b : V) : graph.Adj a b ↔ adj a b := by
  rw [graph, SimpleGraph.fromRel_adj]
  refine and_iff_right_of_imp ?_
  rintro (h | h) rfl <;> omega

lemma adj_symm {a b : V} : adj a b → adj b a := Or.symm

lemma adj_color {a b : V} (h : adj a b) : color a ≠ color b := by
  rcases h with h | h
  · simp [color, h.1, not_lt_of_ge h.2.1]
  · simp [color, h.1, not_lt_of_ge h.2.1]

def raw (C : AndCountCircuit 42) (i : Fin C.size) (s : Bool) : Finset V :=
  if s then C.leftVars i else C.rightVars i

def part (C : AndCountCircuit 42) (i : Fin C.size) (s t : Bool) : Finset V :=
  (raw C i s).filter fun v => color v = t

lemma hit_transfer (C : AndCountCircuit 42) (U W : Finset V)
    (h : ∀ i s v, v ∈ raw C i s → v ∈ U → ∃ w ∈ raw C i s, w ∈ W) :
    ∀ d i, C.gateValFuel U d i = true → C.gateValFuel W d i = true := by
  intro d
  induction d with
  | zero => simp [AndCountCircuit.gateValFuel]
  | succ d ih =>
    intro i hi
    have transfer (s : Bool) (F : Finset (Fin C.size))
        (hs : AndCountCircuit.sideTrue U (raw C i s) F i (C.gateValFuel U d) = true) :
        AndCountCircuit.sideTrue W (raw C i s) F i (C.gateValFuel W d) = true := by
      unfold AndCountCircuit.sideTrue at hs ⊢
      rw [decide_eq_true_eq] at hs ⊢
      rcases hs with ⟨v, hv, hvU⟩ | ⟨j, hj, hji, hjU⟩
      · exact Or.inl (h i s v hv hvU)
      · exact Or.inr ⟨j, hj, hji, ih j hjU⟩
    simp only [AndCountCircuit.gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨transfer true _ hi.1, transfer false _ hi.2⟩


instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def hood (v : V) : Finset V := Finset.univ.filter (fun b => graph.Adj v b)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem deg : ∀ v:V, (hood v).card = 5 := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma commonBound : ∀v w:V, v≠w → (hood v ∩ hood w).card ≤ 1 := by decide +kernel
lemma neighbor (v : V) (W : Finset V) (away : v∉W) (few : W.card≤4) :
    ∃b, graph.Adj v b ∧ ∀w∈W, ¬graph.Adj w b := by
  classical
  by_contra! all
  let U := W.biUnion fun w => hood v ∩ hood w
  have cap : U.card≤W.card*1 := by
    apply Finset.card_biUnion_le_card_mul
    intro w hw
    apply commonBound
    rintro rfl
    exact away hw
  have subset : hood v ⊆ U := by
    intro b hb
    obtain ⟨w,hw,edge⟩ := all b (Finset.mem_filter.mp hb).2
    exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_inter.mpr ⟨hb,Finset.mem_filter.mpr ⟨Finset.mem_univ _,edge⟩⟩⟩
  have h := Finset.card_le_card subset
  rw [deg] at h
  omega
def readers (C:AndCountCircuit 42) (v:V) : Finset (Fin C.size) :=
  Finset.univ.filter fun i => v∈C.leftVars i ∨ v∈C.rightVars i
def independent (I:Finset V) := ∀a∈I,∀b∈I,¬graph.Adj a b

theorem separates_all (C : AndCountCircuit 42) (correct : C.Computes graph)
    (dis : ∀i,Disjoint (C.leftVars i) (C.rightVars i))
    (v:V) (few : (readers C v).card ≤ 4) (I:Finset V) (indep: independent I) (hv:v∉I) :
    ∃i s, v∈raw C i s ∧ Disjoint (raw C i s) I := by
  classical
  by_contra! fail
  have alt (i:Fin C.size) (s:Bool) (a:v∈raw C i s) : ∃w∈I,w∈raw C i s := by
    by_contra! empty
    apply fail i s a
    exact Finset.disjoint_left.mpr (fun w hw hi => empty w hi hw)
  let R := readers C v
  have chooseOne (j:R) : ∃w∈I,∀s,v∈raw C j.val s → w∈raw C j.val s := by
    obtain hl|hr := (Finset.mem_filter.mp j.property).2
    · obtain ⟨w,wi,wl⟩ := alt j.val true hl
      refine ⟨w,wi,?_⟩
      intro s hs
      cases s
      · exact False.elim (Finset.disjoint_left.mp (dis j.val) hl hs)
      · exact wl
    · obtain ⟨w,wi,wr⟩ := alt j.val false hr
      refine ⟨w,wi,?_⟩
      intro s hs
      cases s
      · exact wr
      · exact False.elim (Finset.disjoint_left.mp (dis j.val) hs hr)
  choose f hi same using chooseOne
  let W := Finset.univ.image f
  have sub : W ⊆ I := by
    intro w hw
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
    exact hi j
  have bound : W.card ≤ 4 := by
    calc
      W.card ≤ (Finset.univ : Finset R).card := Finset.card_image_le
      _ = R.card := by simp
      _ ≤ 4 := few
  obtain ⟨b,vb,none⟩ := neighbor v W (fun h => hv (sub h)) bound
  let J := insert b W
  have neg : independent J := by
    intro x hx y hy e
    rcases Finset.mem_insert.mp hx with rfl|xw <;> rcases Finset.mem_insert.mp hy with rfl|yw
    · exact graph.loopless.irrefl _ e
    · exact none _ yw e.symm
    · exact none _ xw e
    · exact indep _ (sub xw) _ (sub yw) e
  have pos := (correct {v,b}).mpr ⟨v,by simp,b,by simp,vb⟩
  have push (i:Fin C.size) (s:Bool) (u:V) (hr:u∈raw C i s) (hu:u∈({v,b}:Finset V)) :
      ∃w∈raw C i s,w∈J := by
    rcases Finset.mem_insert.mp hu with rfl|single
    · have mem : i∈R := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        cases s
        · exact Or.inr hr
        · exact Or.inl hr
      let j : R := ⟨i,mem⟩
      exact ⟨f j,same j s hr,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)⟩
    · have ub := Finset.mem_singleton.mp single
      exact ⟨u,hr,Finset.mem_insert.mpr (Or.inl ub)⟩
  have outEmpty : C.outVars = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have ev : C.eval {a} = true := by
      rw [AndCountCircuit.eval,decide_eq_true_eq]
      exact Or.inl ⟨a,ha,by simp⟩
    obtain ⟨x,hx,y,hy,e⟩ := (correct _).mp ev
    simp only [Finset.mem_singleton] at hx hy
    rw [hx,hy] at e
    exact graph.loopless.irrefl a e
  have ev : C.eval J = true := by
    simp only [AndCountCircuit.eval,decide_eq_true_eq,outEmpty,Finset.notMem_empty,false_and,
      exists_false,false_or] at pos ⊢
    obtain ⟨i,hi0,vpos⟩ := pos
    exact ⟨i,hi0,hit_transfer C {v,b} J push C.size i vpos⟩
  obtain ⟨x,hx,y,hy,e⟩ := (correct _).mp ev
  exact neg _ hx _ hy e
end Covers18597
