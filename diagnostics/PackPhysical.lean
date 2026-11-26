import PEqualNP.Defs

namespace Window9744
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 10000
abbrev K := Fin 13
abbrev Slot := Fin 165
abbrev W := Nat → Bool
def positives : Array Nat := #[0x800008,0x800008,0x1000008,0x20000008,0x80000008,0x20000000008,0x400004,0x400020,0x40002000,0x1000080,0x408000,0x210000,0x2100000]
def negatives : Array Nat := #[0x9affb3,0x1ff5e600008,0x1ff5e600008,0x1ff5e600008,0x1ff5e600008,0x1ff5e600008,0x5d7fd9,0x5d7fd9,0x401fd9eb,0x115ff67,0x5d7fd9,0x3ebfed,0x20bfecf]
def tags : Array Nat := #[0x0,0x0,0x6,0x0,0x0,0x7,0x0,0x9,0x0,0x0,0x0,0x0,0x0,0x8,0x0,0xa,0xb,0x0,0x0,0x0,0xc,0x0,0x0,0x1,0x2,0x0,0x0,0x0,0x0,0x3,0x0,0x4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7,0x0,0x0,0x0,0x0,0x6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2,0x4,0x2,0x2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8,0x0,0x2,0x0,0x0,0x0,0x0,0x2,0xb,0xb,0x0,0x0,0x0,0xa,0x2,0xc,0x2,0x2,0xc,0x2,0x2]
def hi (i : K) := (positives[i.val]?).getD 0
def lo (i : K) := (negatives[i.val]?).getD 0
def edges : List (Nat × Nat) := [(0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]
def gates : List (Nat × Bool × Nat × Nat) := [(42,true,24,22),(43,true,38,42),(44,true,37,43),(45,true,44,34),(46,false,17,45),(47,true,35,24),(48,true,27,47),(49,true,48,28),(50,true,49,33),(51,false,7,50),(52,true,31,35),(53,true,21,34),(54,true,53,40),(55,true,54,52),(56,false,14,55),(57,true,36,37),(58,true,57,21),(59,true,58,33),(60,true,23,59),(61,false,16,60),(62,true,39,29),(63,true,62,22),(64,true,27,63),(65,true,64,21),(66,false,1,65),(67,true,41,27),(68,true,25,67),(69,true,68,37),(70,true,40,69),(71,false,20,70),(72,true,32,33),(73,true,38,29),(74,true,72,73),(75,true,74,40),(76,false,12,75),(77,true,25,39),(78,true,77,23),(79,true,38,78),(80,true,79,35),(81,false,18,80),(82,true,38,31),(83,true,82,30),(84,true,27,83),(85,true,84,36),(86,false,10,85),(87,true,29,35),(88,true,26,87),(89,true,30,88),(90,true,89,37),(91,false,9,90),(92,true,37,31),(93,true,28,39),(94,true,32,93),(95,true,94,92),(96,false,11,95),(97,true,41,22),(98,true,97,32),(99,true,35,36),(100,true,98,99),(101,false,15,100),(102,true,38,41),(103,true,28,26),(104,true,102,103),(105,false,0,104),(106,true,31,25),(107,true,33,106),(108,true,107,22),(109,true,26,108),(110,false,5,109),(111,true,30,28),(112,true,22,40),(113,true,23,111),(114,true,112,113),(115,false,2,114),(116,true,32,21),(117,true,25,116),(118,true,30,117),(119,true,24,118),(120,false,4,119),(121,true,36,40),(122,true,24,121),(123,true,26,39),(124,true,123,122),(125,false,19,124),(126,true,34,26),(127,true,126,32),(128,true,23,127),(129,true,27,128),(130,false,6,129),(131,true,24,29),(132,true,41,31),(133,true,132,131),(134,false,3,133),(135,true,25,29),(136,true,135,36),(137,true,28,136),(138,true,34,137),(139,false,8,138),(140,true,33,34),(141,true,30,39),(142,true,41,140),(143,true,142,141),(144,false,13,143),(145,true,130,96),(146,true,144,134),(147,true,125,81),(148,true,66,46),(149,true,120,145),(150,true,147,105),(151,true,146,115),(152,true,61,76),(153,true,152,150),(154,true,91,149),(155,true,56,154),(156,true,86,139),(157,true,148,101),(158,true,110,151),(159,true,71,156),(160,true,51,158),(161,true,157,160),(162,true,155,159),(163,true,161,153),(164,true,163,162)]
def allowed (i : Slot) := (0x4bf7bff87ffffffffffffffffffffffffffffffff : Nat).testBit i.val

def target (x : Nat) := edges.any fun e => x.testBit e.1 && x.testBit e.2
def step (x : Nat) (g : Nat × Bool × Nat × Nat) : Nat :=
  let a := x.testBit g.2.2.1
  let b := x.testBit g.2.2.2
  if (if g.2.1 then a || b else a && b) then x ||| (1 <<< g.1) else x
def source (i : Slot) (x : Nat) := (gates.foldl step x).testBit i.val
def free : List W := ((List.finRange 165).filter allowed).map source
def observes (w : W) (i : K) := w (hi i)=true ∧ w (lo i)=false
def agrees (c : K → K) (w : W) := ∀ i j, observes w i → observes w j → c i=c j
def tag (i : Slot) : K := Fin.ofNat 13 ((tags[i.val]?).getD 0)
theorem truth : ∀ i : K, target (hi i)=true ∧ target (lo i)=false := by decide +kernel
theorem stored : ∀ i : Slot,allowed i=true → ∀ j : K,
    source i (hi j)=true → source i (lo j)=false → j=tag i := by decide +kernel

def binary (op : Bool) (a b : W) : W := fun x=> if op then a x || b x else a x && b x
inductive Built : List W → Nat → Prop
  | start : Built free 0
  | add {bank n u v} (old : Built bank n) (a : u ∈ bank) (b : v ∈ bank) (op : Bool) :
      Built (binary op u v :: bank) (n+1)

theorem reaches (op : Bool) (u v : W) (i : K) :
    observes (binary op u v) i → observes u i ∨ observes v i := by
  cases op <;> cases a : u (hi i) <;> cases b : u (lo i) <;>
    cases c : v (hi i) <;> cases d : v (lo i) <;> simp [observes,binary,a,b,c,d]

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
    (op : Bool) : ∃ e : K→K, agrees e (binary op u v) ∧
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


theorem budget {bank n} (s : Built bank n) :
    ∃ c : K→K, (∀ w∈bank,agrees c w) ∧ 13≤(palette c).card+n := by
  induction s with
  | start =>
    refine ⟨id,?_,?_⟩
    · intro w hw
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
      have av := (List.mem_filter.mp hj).2
      intro u v a b
      exact (stored j av u a.1 a.2).trans (stored j av v b.1 b.2).symm
    · simp [palette,K]
  | add old hu hv op ih =>
    obtain ⟨c,valid,h⟩ := ih
    obtain ⟨e,gate,coarse,cost⟩ := merge c (valid _ hu) (valid _ hv) op
    refine ⟨e,?_,by omega⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact gate
    · exact fun i j ai aj=>coarse _ _ (valid w hw i j ai aj)

theorem atLeastTwelve {bank : List W} {n : Nat} (built : Built bank n)
    {w : W} (mem : w∈bank) (correct : ∀ x,w x=target x) : 12≤n := by
  classical
  obtain ⟨c,valid,lim⟩ := budget built
  have seen (i : K) : observes w i := by simpa [observes,correct] using truth i
  have sub : palette c ⊆ {c 0} := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    simpa only [mem_singleton] using valid w mem i 0 (seen i) (seen 0)
  have price := card_le_card sub
  simp only [card_singleton] at price
  omega
theorem boundedInputs {bank : List W} {n : Nat} (built : Built bank n)
    {w : W} (mem : w∈bank) (correct : ∀ x,x<2^42 → w x=target x) : 12≤n := by
  classical
  obtain ⟨c,valid,lim⟩ := budget built
  have rangeH : ∀ i : K, hi i < 2^42 ∧ lo i < 2^42 := by decide +kernel
  have seen (i : K) : observes w i := by
    unfold observes
    rw [correct _ (rangeH i).1,correct _ (rangeH i).2]
    exact truth i
  have sub : palette c ⊆ {c 0} := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    simpa only [mem_singleton] using valid w mem i 0 (seen i) (seen 0)
  have price := card_le_card sub
  simp only [card_singleton] at price
  omega
end Window9744
