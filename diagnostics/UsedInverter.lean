import PEqualNP.Defs
namespace SignedWindow9762
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 10000
abbrev K := Fin 10
abbrev Slot := Fin 83
abbrev W := Nat → Bool
def positives : Array Nat := #[0x800800,0x2004d8,0x200020,0x800f7d,0x200250,0x40004,0x200876,0x2002,0x20002,0x100010]
def negatives : Array Nat := #[0x800,0x2000d8,0x20,0x80077d,0x200050,0x4,0x200856,0x2,0x2,0x10]
def tags : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x6,0x0,0x0,0x0,0x4,0x1,0x3,0x0,0x7,0x0,0x0,0x0,0x8,0x5,0x0,0x9,0x2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8,0x0,0x0,0x0,0x7,0x0,0x0,0x0,0x0,0x0,0x0,0x9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x6,0x4,0x1,0x1,0x0,0x8,0x9,0x1,0x1,0x1,0x0,0x1,0x0,0x1,0x1]
def hi (i : K) := (positives[i.val]?).getD 0
def lo (i : K) := (negatives[i.val]?).getD 0
def edges : List (Nat × Nat) := [(0, 16), (0, 22), (0, 24), (1, 13), (1, 17), (1, 23), (2, 13), (2, 14), (2, 18), (2, 24), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 17), (8, 19), (8, 20), (8, 24), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23), (12, 15), (12, 21), (12, 23), (12, 24)]
def gates : List (Nat × Bool × Nat × Nat) := [(25,true,3,4),(26,true,6,25),(27,true,12,26),(28,false,15,27),(29,true,6,9),(30,true,7,29),(31,true,2,30),(32,false,18,31),(33,true,5,11),(34,true,3,33),(35,true,2,34),(36,false,14,35),(37,true,6,11),(38,true,10,37),(39,true,0,38),(40,false,22,39),(41,true,1,8),(42,true,5,41),(43,true,6,42),(44,false,17,43),(45,true,4,10),(46,true,1,45),(47,true,2,46),(48,false,13,47),(49,true,1,12),(50,true,7,49),(51,false,23,50),(52,true,8,11),(53,true,4,52),(54,true,9,53),(55,false,20,54),(56,true,7,8),(57,true,10,56),(58,true,3,57),(59,false,19,58),(60,true,0,12),(61,true,2,8),(62,true,60,61),(63,false,24,62),(64,true,4,5),(65,true,0,64),(66,true,7,65),(67,false,16,66),(68,true,5,12),(69,true,9,68),(70,true,10,69),(71,false,21,70),(72,true,59,63),(73,true,28,44),(74,true,51,55),(75,true,71,73),(76,true,48,75),(77,true,74,76),(78,true,40,67),(79,true,32,77),(80,true,36,72),(81,true,78,79),(82,true,80,81)]
def allowed (i : Slot) := (0x1471fffffffffffffffff : Nat).testBit i.val
def target (x : Nat) := edges.any fun e => x.testBit e.1 && x.testBit e.2
def step (x : Nat) (g : Nat × Bool × Nat × Nat) : Nat :=
  let a := x.testBit g.2.2.1
  let b := x.testBit g.2.2.2
  if (if g.2.1 then a || b else a && b) then x ||| (1 <<< g.1) else x
def source (i : Slot) (x : Nat) := (gates.foldl step x).testBit i.val
def free : List W := ((List.finRange 83).filter allowed).map source
def observes (w : W) (i : K) := w (hi i) ≠ w (lo i)
def agrees (c : K → K) (w : W) := ∀ i j, observes w i → observes w j → c i=c j
def tag (i : Slot) : K := Fin.ofNat 10 ((tags[i.val]?).getD 0)
theorem truth : ∀ i : K, target (hi i)=true ∧ target (lo i)=false := by decide +kernel
theorem stored : ∀ i : Slot,allowed i=true → ∀ j : K,
    source i (hi j) ≠ source i (lo j) → j=tag i := by decide +kernel


def binary (op : Bool → Bool → Bool) (u v : W) : W := fun x=>op (u x) (v x)
def unary (op : Bool → Bool) (u : W) : W := fun x=>op (u x)
inductive Built : List W → Nat → Nat → Prop
  | start : Built free 0 0
  | addBinary {bank b t u v} (old : Built bank b t) (hu : u∈bank) (hv : v∈bank)
      (op : Bool→Bool→Bool) : Built (binary op u v :: bank) (b+1) t
  | addUnary {bank b t u} (old : Built bank b t) (hu : u∈bank) (op : Bool→Bool) :
      Built (unary op u :: bank) b (t+1)
theorem reaches (op : Bool→Bool→Bool) (u v : W) (i : K) :
    observes (binary op u v) i → observes u i ∨ observes v i := by
  classical
  intro h
  by_cases a : observes u i
  · exact Or.inl a
  · right
    intro b
    apply h
    have eq : u (hi i)=u (lo i) := Classical.not_not.mp a
    simp [binary,eq,b]
theorem unaryReaches (op : Bool→Bool) (u : W) (i : K) : observes (unary op u) i → observes u i := by
  intro h e
  apply h
  simp [unary,e]
def palette (c : K → K) : Finset K := univ.image c
theorem recolorCost (c : K → K) (a b : K) :
    (palette c).card ≤ (palette (fun i => if c i=b then a else c i)).card+1 := by
  classical
  let newColor := fun i => if c i=b then a else c i
  have sub : (palette c).erase b ⊆ palette newColor := by
    intro w hw
    obtain ⟨ne,wp⟩ := mem_erase.mp hw
    obtain ⟨i,_,rfl⟩ := mem_image.mp wp
    exact mem_image.mpr ⟨i,mem_univ i,by simp [newColor,ne]⟩
  have le := card_le_card sub
  by_cases h : b∈palette c
  · have er := card_erase_add_one h
    change (palette c).card ≤ (palette newColor).card+1
    omega
  · rw [erase_eq_of_notMem h] at le
    exact Nat.le.step le


theorem merge (c : K→K) {u v : W} (a : agrees c u) (b : agrees c v)
    (op : Bool→Bool→Bool) : ∃ e : K→K, agrees e (binary op u v) ∧
    (∀ i j,c i=c j → e i=e j) ∧ (palette c).card ≤ (palette e).card+1 := by
  classical
  let pick (w : W) : K := if z : ∃ i, observes w i then z.choose else 0
  have one {w : W} (h : agrees c w) {i} (z : observes w i) : c i=c (pick w) := by
    have ex : ∃ j, observes w j := ⟨i,z⟩
    simpa only [pick,dif_pos ex] using h i ex.choose z ex.choose_spec
  let e (i : K) := if c i=c (pick v) then c (pick u) else c i
  have both (i : K) (z : observes (binary op u v) i) : e i=c (pick u) := by
    rcases reaches op u v i z with yes | other
    · simp [e,one a yes]
    · simp [e,one b other]
  exact ⟨e,fun i j ai aj=>(both i ai).trans (both j aj).symm,
    fun i j eq=>by simp only [e,eq],recolorCost c _ _⟩



theorem budget {bank b t} (s : Built bank b t) :
    ∃ c : K→K, (∀ w∈bank,agrees c w) ∧ 10≤(palette c).card+b := by
  induction s with
  | start =>
    refine ⟨id,?_,?_⟩
    · intro w hw
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
      have av := (List.mem_filter.mp hj).2
      intro u v a b
      exact (stored j av u a).trans (stored j av v b).symm
    · simp [palette,K]
  | addBinary old hu hv op ih =>
    obtain ⟨c,valid,h⟩ := ih
    obtain ⟨e,gate,coarse,cost⟩ := merge c (valid _ hu) (valid _ hv) op
    refine ⟨e,?_,by omega⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact gate
    · exact fun i j ai aj=>coarse _ _ (valid w hw i j ai aj)
  | addUnary old hu op ih =>
    obtain ⟨c,valid,h⟩ := ih
    refine ⟨c,?_,h⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact fun i j a b=>valid _ hu i j (unaryReaches _ _ _ a) (unaryReaches _ _ _ b)
    · exact valid _ hw

theorem signedPrice {bank : List W} {b t : Nat} (built : Built bank b t)
    {w : W} (mem : w∈bank) (correct : ∀ x,x<2^25 → w x=target x) :
    9≤b ∧ (1≤t → 10≤b+t) := by
  classical
  obtain ⟨c,valid,lim⟩ := budget built
  have rangeH : ∀ i : K,hi i<2^25 ∧ lo i<2^25 := by decide +kernel
  have seen (i : K) : observes w i := by
    unfold observes
    rw [correct _ (rangeH i).1,correct _ (rangeH i).2,(truth i).1,(truth i).2]
    decide
  have sub : palette c ⊆ {c 0} := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    simpa only [mem_singleton] using valid w mem i 0 (seen i) (seen 0)
  have price := card_le_card sub
  simp only [card_singleton] at price
  omega

namespace Directed
def rises (w : W) (i : K) := w (hi i)=true ∧ w (lo i)=false
def upward (w : W) := ∀ i : K,w (lo i)=true → w (hi i)=true
def coherent (c : K→K) (w : W) := ∀ i j,rises w i → rises w j → c i=c j
def gate (d : Bool) (u v : W) := fun x=> if d then u x || v x else u x && v x
def neg (u : W) : W := fun x => !(u x)
theorem sourcesUp : ∀ (j : Slot),allowed j=true → ∀ i : K,source j (lo i)=true → source j (hi i)=true := by decide +kernel

theorem gateRise (d : Bool) (u v : W) (i : K) : rises (gate d u v) i → rises u i ∨ rises v i := by
  cases d <;> cases a : u (hi i) <;> cases b : u (lo i) <;>
    cases c : v (hi i) <;> cases e : v (lo i) <;> simp [rises,gate,a,b,c,e]
theorem gateUp (d : Bool) {u v : W} (hu : upward u) (hv : upward v) : upward (gate d u v) := by
  intro i
  cases d <;> cases a : u (hi i) <;> cases b : u (lo i) <;>
    cases c : v (hi i) <;> cases e : v (lo i) <;> simp_all [gate,upward]
theorem negCannotRise {u : W} (h : upward u) (i : K) : ¬rises (neg u) i := by
  intro z
  obtain ⟨a,b⟩ := z
  have low : u (lo i)=true := by simpa [neg] using b
  have high := h i low
  simp [neg,high] at a
theorem posMerge (c : K→K) {u v : W} (a : coherent c u) (b : coherent c v)
    (op : Bool) : ∃ e : K→K, coherent e (gate op u v) ∧
    (∀ i j,c i=c j → e i=e j) ∧ (palette c).card ≤ (palette e).card+1 := by
  classical
  let pick (w : W) : K := if z : ∃ i, rises w i then z.choose else 0
  have one {w : W} (h : coherent c w) {i} (z : rises w i) : c i=c (pick w) := by
    have ex : ∃ j, rises w j := ⟨i,z⟩
    simpa only [pick,dif_pos ex] using h i ex.choose z ex.choose_spec
  let e (i : K) := if c i=c (pick v) then c (pick u) else c i
  have both (i : K) (z : rises (gate op u v) i) : e i=c (pick u) := by
    rcases gateRise op u v i z with yes | other
    · simp [e,one a yes]
    · simp [e,one b other]
  exact ⟨e,fun i j ai aj=>(both i ai).trans (both j aj).symm,
    fun i j eq=>by simp only [e,eq],recolorCost c _ _⟩




inductive Trail (start : List W) : List W → Nat → Prop
  | init : Trail start start 0
  | add {bank n u v} (old : Trail start bank n) (a : u∈bank) (b : v∈bank) (d : Bool) :
      Trail start (gate d u v :: bank) (n+1)
def Account (bank : List W) (b : Nat) :=
  ∃ c : K→K,(∀ w∈bank,coherent c w) ∧ 10≤(palette c).card+b

theorem initial : Account free 0 := by
  refine ⟨id,?_,?_⟩
  · intro w h
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp h
    have av := (List.mem_filter.mp hs).2
    intro i j a b
    have diff {t : K} (x : rises (source s) t) : observes (source s) t := by
      unfold observes
      rw [x.1,x.2]
      decide
    exact (stored s av i (diff a)).trans (stored s av j (diff b)).symm
  · simp [palette,K]

theorem travel {start bank p q} (s : Trail start bank q) (ini : Account start p) : Account bank (p+q) := by
  induction s with
  | init => simpa using ini
  | add prev ha hb d ih =>
    obtain ⟨c,valid,h⟩ := ih
    obtain ⟨e,good,coarse,cost⟩ := posMerge c (valid _ ha) (valid _ hb) d
    refine ⟨e,?_,by omega⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact good
    · exact fun i j a b=>coarse _ _ (valid w hw i j a b)

theorem prefixUp {bank p} (s : Trail free bank p) : ∀v∈bank,upward v := by
  induction s with
  | init =>
    intro v h
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    exact sourcesUp j (List.mem_filter.mp hj).2
  | add prev ha hb d ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact gateUp d (ih _ ha) (ih _ hb)
    · exact ih _ hw

theorem noCharge {bank b w} (acc : Account bank b) (dead : ∀i,¬rises w i) :
    Account (w::bank) b := by
  obtain ⟨c,v,h⟩ := acc
  refine ⟨c,?_,h⟩
  intro u hu
  rcases List.mem_cons.mp hu with rfl|hu
  · exact fun i _ rise _=>False.elim (dead i rise)
  · exact v _ hu

theorem discounted {bank b w v} (acc : Account bank b) (dead : ∀i,¬rises w i) (hv : v∈bank) (d : Bool) :
    Account (gate d w v :: bank) b := by
  obtain ⟨c,valid,h⟩ := acc
  refine ⟨c,?_,h⟩
  intro u hu
  rcases List.mem_cons.mp hu with rfl|hu
  · intro i j a b
    exact valid _ hv i j ((gateRise _ _ _ _ a).resolve_left (dead i))
      ((gateRise _ _ _ _ b).resolve_left (dead j))
  · exact valid _ hu

theorem usedInverter {B D E : List W} {u v w : W} {p q r : Nat}
    (pre : Trail free B p) (hu : u∈B) (mid : Trail (neg u::B) D q) (hv : v∈D) (d : Bool)
    (post : Trail (gate d (neg u) v :: D) E r) (out : w∈E)
    (ok : ∀ x,x<2^25 → w x=target x) : 11 ≤ p+1+q+1+r := by
  classical
  have a := travel pre initial
  have dead := negCannotRise (prefixUp pre u hu)
  have b := travel mid (noCharge a dead)
  have e := travel post (discounted b dead hv d)
  obtain ⟨c,valid,lim⟩ := e
  have bounded : ∀ i : K, hi i<2^25 ∧ lo i<2^25 := by decide +kernel
  have seen (i : K) : rises w i := by
    unfold rises
    rw [ok _ (bounded i).1,ok _ (bounded i).2]
    exact truth i
  have sub : palette c ⊆ {c 0} := by
    intro j hj
    obtain ⟨i,_,rfl⟩ := mem_image.mp hj
    simpa only [mem_singleton] using valid w out i 0 (seen i) (seen 0)
  have price := card_le_card sub
  simp only [card_singleton] at price
  omega
end Directed
end SignedWindow9762
