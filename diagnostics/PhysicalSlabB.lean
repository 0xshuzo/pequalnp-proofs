import PEqualNP.Defs
open Finset
namespace Plane9341Slab
abbrev V := Fin 21
abbrev Box := Finset V × Finset V
def board (r c : V) := (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List Nat).getD r.val 0).testBit c.val
def holds (b : Box) (r c : V) : Prop := r∈b.1 ∧ c∈b.2
instance (b : Box) (r c : V) : Decidable (holds b r c) := inferInstanceAs (Decidable (_ ∧ _))
def law (b : Box) : Prop := ∀r∈b.1,∀c∈b.2,board r c=false
def slab (p q r c : V) : Bool := !board r c && (board r q || board p c)
def fringe (L : List Box) (p q : V) := L.filter fun b => !(decide (holds b p q))
def shared (L : List Box) (p q : V) := L.filter fun b => decide (holds b p q)

theorem separates (p q r c : V) (b : Box) (ok : law b)
    (h : slab p q r c = true) (rc : holds b r c) : ¬holds b p q := by
  intro pq
  have hq := ok _ rc.1 _ pq.2
  have hp := ok _ pq.1 _ rc.2
  simp [slab,hq,hp] at h

theorem physicalSlab (p q : V) (L : List Box) (ok : ∀b∈L,law b)
    (covers : ∀r c, board r c=false → ∃b∈L,holds b r c) :
    (∀b∈fringe L p q,law b) ∧
    (∀r c, slab p q r c=true → ∃b∈fringe L p q,holds b r c) ∧
    (fringe L p q).length+(shared L p q).length=L.length := by
  refine ⟨fun b hb => ok b (List.mem_filter.mp hb).1,?_,?_⟩
  · intro r c hs
    have legal : board r c=false := by
      cases he : board r c <;> simp_all [slab]
    obtain ⟨b,hb,rc⟩ := covers r c legal
    have ne := separates p q r c b (ok b hb) hs rc
    exact ⟨b,List.mem_filter.mpr ⟨hb,by simp [ne]⟩,rc⟩
  · clear ok covers
    induction L with
    | nil => rfl
    | cons a L ih =>
      by_cases ha : holds a p q <;> simp [fringe,shared,ha,List.filter_cons] at ih ⊢ <;> omega

def mask (n : Nat) := Finset.univ.filter (fun i : V => n.testBit i.val)
def data : List (Nat×Nat) := [(131074, 581300), (606834, 1179776), (794564, 1048577), (32774, 209944), (1059212, 131105), (131108, 1362241), (32800, 992077), (1438744, 160)]
def boxes : List Box := data.map fun b => (mask b.1,mask b.2)
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
def cleanMask (b : Nat × Nat) : Bool := decide (∀ r c : V,
    b.1.testBit r.val = true → b.2.testBit c.val = true → board r c=false)
theorem cleanData : data.all cleanMask = true := by decide +kernel
theorem coversData : ∀ r c : V, slab 0 1 r c = true →
    data.any (fun b => b.1.testBit r.val && b.2.testBit c.val) = true := by decide +kernel
theorem witness : boxes.length=8 ∧
    (∀b∈boxes, ∀r∈b.1,∀c∈b.2,board r c=false) ∧
    (∀ r c : V, slab 0 1 r c=true → ∃b∈boxes, r∈b.1 ∧ c∈b.2) := by
  refine ⟨by decide,?_,?_⟩
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    have clean := List.all_eq_true.mp cleanData a ha
    have h : ∀ r c : V, a.1.testBit r.val = true → a.2.testBit c.val = true → board r c=false :=
      of_decide_eq_true clean
    intro r hr c hc
    exact h r c (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hc).2
  · intro r c hc
    obtain ⟨a,ha,hit⟩ := List.any_eq_true.mp (coversData r c hc)
    have hp : a.1.testBit r.val = true ∧ a.2.testBit c.val = true := by simpa using hit
    exact ⟨(mask a.1,mask a.2),List.mem_map.mpr ⟨a,ha,rfl⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp.1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp.2⟩⟩

end Plane9341Slab
