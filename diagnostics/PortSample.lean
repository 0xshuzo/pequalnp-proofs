import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9763.Port
abbrev Port := Fin 83
abbrev Bank := Port → Bool
abbrev Op := Port → Bool → Bool → Bool
abbrev Node := Port × Port × Port

def paint (w : Bank) (port : Port) (b : Bool) : Bank :=
  fun i => if i=port then b else w i
def step (op : Op) (g : Node) (w : Bank) : Bank :=
  paint w g.1 (op g.1 (w g.2.1) (w g.2.2))
def run (op : Op) : List Node → Bank → Bank
  | [], w => w
  | g :: gs, w => run op gs (step op g w)
def both : Op := fun _ a b => a && b
def Fit (q x y : Bank) := ∀ v, q v = true → x v = y v

theorem step_fit {q x y : Bank} (h : Fit q x y) (op : Op) (g : Node) :
    Fit (step both g q) (step op g x) (step op g y) := by
  intro v hv
  by_cases eq : v=g.1
  · subst v
    have hh : q g.2.1=true ∧ q g.2.2=true := by simpa [step,paint,both] using hv
    simp [step,paint,h _ hh.1,h _ hh.2]
  · have hv' : q v=true := by simpa [step,paint,eq] using hv
    simpa [step,paint,eq] using h v hv'

theorem run_fit (gs : List Node) (op : Op) : ∀ {q x y : Bank}, Fit q x y →
    Fit (run both gs q) (run op gs x) (run op gs y) := by
  induction gs with
  | nil => exact fun h => h
  | cons g gs ih => exact fun h => ih (step_fit h op g)

structure Chart where
  pre : List Node
  post : List Node
  tap : Port
  words : List Nat

def raw (c : Chart) (i : Fin 3) (j : Fin 4) (v : Port) := (c.words.getD (4*i.val+j.val) 0).testBit v.val
def left (c : Chart) (v : Port) : Bool := decide (∀ (i : Fin 3) (j : Fin 4), raw c i j v = raw c i 0 v)
def right (c : Chart) (v : Port) : Bool := decide (∀ (i : Fin 3) (j : Fin 4), raw c i j v = raw c 0 j v)
def output (c : Chart) (op : Op) (i : Fin 3) (j : Fin 4) :=
  run op c.post (run op c.pre (raw c i j)) 82

def target (r : Bank) : Bool := (r 0 && r 16) || (r 0 && r 22) || (r 0 && r 24) || (r 1 && r 13) || (r 1 && r 17) || (r 1 && r 23) || (r 2 && r 13) || (r 2 && r 14) || (r 2 && r 18) || (r 2 && r 24) || (r 3 && r 14) || (r 3 && r 15) || (r 3 && r 19) || (r 4 && r 13) || (r 4 && r 15) || (r 4 && r 16) || (r 4 && r 20) || (r 5 && r 14) || (r 5 && r 16) || (r 5 && r 17) || (r 5 && r 21) || (r 6 && r 15) || (r 6 && r 17) || (r 6 && r 18) || (r 6 && r 22) || (r 7 && r 16) || (r 7 && r 18) || (r 7 && r 19) || (r 7 && r 23) || (r 8 && r 17) || (r 8 && r 19) || (r 8 && r 20) || (r 8 && r 24) || (r 9 && r 18) || (r 9 && r 20) || (r 9 && r 21) || (r 10 && r 13) || (r 10 && r 19) || (r 10 && r 21) || (r 10 && r 22) || (r 11 && r 14) || (r 11 && r 20) || (r 11 && r 22) || (r 11 && r 23) || (r 12 && r 15) || (r 12 && r 21) || (r 12 && r 23) || (r 12 && r 24)
def Test (c : Chart) : Prop :=
  run both c.pre (left c) c.tap=true ∧
  run both c.post (paint (run both c.pre (right c)) c.tap true) 82=true ∧
  ∀ i k : Fin 3, i≠k → ∃ j : Fin 4, target (raw c i j) ≠ target (raw c k j)
instance (c : Chart) : Decidable (Test c) := by unfold Test; infer_instance

theorem collide : ∀ f : Fin 3 → Bool, ∃ i k : Fin 3, i≠k ∧ f i=f k := by decide +kernel

theorem obstruction {c : Chart} (hc : Test c) (op : Op) :
    ¬ ∀ (i : Fin 3) (j : Fin 4), output c op i j = target (raw c i j) := by
  intro exactOn
  obtain ⟨hl,hr,separate⟩ := hc
  let w (i : Fin 3) (j : Fin 4) : Bank := run op c.pre (raw c i j)
  have leftPort (i : Fin 3) (j : Fin 4) : w i j c.tap = w i 0 c.tap := by
    apply run_fit c.pre op (q:=left c) _ c.tap hl
    intro v hv
    exact (of_decide_eq_true hv : ∀ (a : Fin 3) (b : Fin 4), raw c a b v=raw c a 0 v) i j
  obtain ⟨i,k,ne,he⟩ := collide (fun u => w u 0 c.tap)
  obtain ⟨j,hj⟩ := separate i k ne
  have hfit : Fit (run both c.pre (right c)) (w i j) (w k j) := by
    apply run_fit c.pre op
    intro v hv
    have zz := (of_decide_eq_true hv : ∀ (a : Fin 3) (b : Fin 4), raw c a b v=raw c 0 b v)
    exact (zz i j).trans (zz k j).symm
  have hpaint : Fit (paint (run both c.pre (right c)) c.tap true) (w i j) (w k j) := by
    intro v hv
    by_cases eq : v=c.tap
    · subst v; exact (leftPort i j).trans (he.trans (leftPort k j).symm)
    · exact hfit v (by simpa [paint,eq] using hv)
  apply hj
  rw [←exactOn i j,←exactOn k j]
  exact run_fit c.post op hpaint 82 hr

def c166 : Chart := ⟨[(25,10,12),(26,5,25),(27,21,26),(28,10,11),(29,0,28),(30,6,29),(31,22,30),(32,27,31)],[(33,11,12),(34,1,33),(35,7,34),(36,23,35),(37,32,36),(38,0,8),(39,12,38),(40,2,39),(41,24,40),(42,37,41),(43,1,10),(44,2,43),(45,4,44),(46,13,45),(47,42,46),(48,2,11),(49,3,48),(50,5,49),(51,14,50),(52,47,51),(53,3,12),(54,4,53),(55,6,54),(56,15,55),(57,52,56),(58,0,4),(59,5,58),(60,7,59),(61,16,60),(62,57,61),(63,1,5),(64,6,63),(65,8,64),(66,17,65),(67,62,66),(68,2,9),(69,6,68),(70,7,69),(71,18,70),(72,67,71),(73,3,10),(74,7,73),(75,8,74),(76,19,75),(77,72,76),(78,4,9),(79,11,78),(80,8,79),(81,20,80),(82,77,81)],32,[1, 513, 1, 1, 2097153, 2097665, 2097153, 2097153, 4194305, 4194817, 4194305, 4194305]⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem c166_valid : Test c166 := by decide +kernel

end PEqualNP.Outside.L_meta_9763.Port
