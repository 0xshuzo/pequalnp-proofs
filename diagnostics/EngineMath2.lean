import PEqualNP.Defs
-- General packed decision procedure from L_meta_8405 on project main, itself derived
-- from the L_meta_1673 search engine. The input, sample layout and certificates here are new.

-- The search engine is adapted from PEqualNP.Outside.L_meta_1673 by Trey Kind (pull request 6929, Apache License 2.0).
-- This file declares its own data types (records for the search state and inductive predicates).

namespace PEqualNP.Outside.L_meta_8399
-- Computational declarations are placed first using the organization of public L_meta_8401.
section hz1
variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
def Z0 : ℕ → ℕ := fun _ => 0
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (R : ℕ → ℕ) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
def Min (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live R m T k t S ∧ ∀ q < k, ¬ Sol Z0 m T q (C m S)
def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
end hz1
section hz2
variable {R : ℕ → ℕ}
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
end hz2
section hz3
variable {R : ℕ → ℕ}
open Finset in
def Acc (n T k b : ℕ) (D : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∀ U ⊆ S, ∀ q, q + b < k + ∑ w ∈ S \ U, D w → ¬ Sol Z0 n (T &&& n) q (C n (Im n U))
inductive Kd
  | N | K0 | KA | KC
def Kd.ok (n : ℕ) (d : Bool) (a c : ℕ) : Kd → Prop
  | .N => True
  | .K0 => Cst n (op d a c)
  | .KA => op d a c &&& n = a &&& n
  | .KC => op d a c &&& n = c &&& n
def Kd.del (la lc : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => 1 + la + lc
  | .KA => 1 + lc
  | .KC => 1 + la
def Kd.out (la lc : ℕ) : Kd → ℕ
  | .N => 1 + la + lc
  | .K0 => 0
  | .KA => la
  | .KC => lc
def Kd.kpa (x : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => x
  | .KA => 0
  | .KC => x
def Kd.kpc (x : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => x
  | .KA => x
  | .KC => 0
structure DStep (κ : Kd) (D D' : ℕ → ℕ) (g a c : ℕ) (S' : Finset ℕ) : Prop where
  hg : D' g ≤ κ.out (if a ∈ S' then 0 else D a) (if c ∈ S' then 0 else D c)
  ha : a ∈ S' → D' a ≤ κ.kpa (D a)
  hc : c ∈ S' → D' c ≤ κ.kpc (D c)
  ho : ∀ w ∈ S', w ≠ g → w ≠ a → w ≠ c → D' w ≤ D w
structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat
  d : Nat
structure Cm where
  a : List Nat
  b : List Nat
def NN : Nat := 714
def AA : Nat := 0x1fffeffff7befbfffeeffff7fffbfffddfffef7fffbdefb7fffbdfffef7bedef6fbeeeef7ff555b55b7ffdad5adfff55ab6d7ffdb6db6db5adb5ad6b57ffdb6adab6b5fff6dfff6afffb57ffdfff7ffdfff0000000000000000
def HX : Nat := 0xaaa4aa4800252a52000aa549280024924924a524a5294a800249525494a00092000950004a800200080020000000000000000000
def HY : Nat := 0x20001000084104000110000800040002200010800042104800042000108412109041111080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
end hz3
noncomputable section hz4
variable {R : ℕ → ℕ}
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def join (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hits f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hits f c.b)) (hits f c.a)) cs
def bip (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => join ih f cs [f] [] []) (flag false l o w)) v
def anyE (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hits f t)) m
def rmF (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hit f e)) m
def star (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF f t))) false (hits f (rmF f t))) (anyE t)) (hits f t)) m
def flk (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flag false l o w)) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f : Nat → List W → Bool) (g : Nat) (kb : Bool) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) (st z (fun z => mk (f z))) false kb) (Nat.beq (Nat.land z g) g)
def laneL (w : Nat) (L : List Nat) : Nat := List.rec (motive := fun _ => Nat) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih w) d) L
def WL (N : Nat) : Nat := Nat.succ (Nat.mul 2 N)
def FM2 (N : Nat) : Nat := Nat.sub (Nat.pow 2 (Nat.mul 2 N)) 1
def R16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 1)
def MM16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 (FM2 N))
def GG16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 (Nat.pow 2 (Nat.mul 2 N)))
def MD16 (N : Nat) : Nat := Nat.sub (Nat.pow 2 (WL N)) 32
def U16 : Nat := laneL 5 (List.replicate 16 1)
def natHold (x : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (f 0) (fun n _ => f n) (Nat.succ x)
def smearStep (s x : Nat) := natHold x fun a => Nat.lor a (Nat.shiftRight a s)
def gatherSixteen (s x : Nat) := smearStep (8*s) (smearStep (4*s) (smearStep (2*s) (smearStep s x)))
def broadcastAdd (s x : Nat) := natHold x fun a => Nat.add a (Nat.shiftLeft a s)
def broadcastSixteen (w x : Nat) := broadcastAdd (w*8) (broadcastAdd (w*4) (broadcastAdd (w*2) (broadcastAdd w x)))
def zflG (N np q nc : Nat) : Nat := Nat.land (Nat.xor U16 (Nat.land (gatherSixteen (Nat.sub (WL N) 5) (Nat.shiftRight (Nat.land (Nat.add (Nat.land (broadcastSixteen (WL N) (Nat.land q (FM2 N))) np) (MM16 N)) (GG16 N)) (Nat.mul 2 N))) U16)) nc
def zfl (np q nc : Nat) : Nat := zflG NN np q nc
def MU (f : Nat) : Nat := Nat.mul 31 f
def rmk (sa : Nat) (ka : Bool) (da : Nat) (sc : Nat) (kc : Bool) (dc : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (ih h) (st dc fun d => W.rec (motive := fun _ => Bool) (fun s a b c r0 _ => ih (fun r => h (⟨s, a, b, c, r0, d⟩ :: r))) w) kc) (Nat.beq w.s sc))
    (Bool.rec (motive := fun _ => Bool) (ih h) (st da fun d => W.rec (motive := fun _ => Bool) (fun s a b c r0 _ => ih (fun r => h (⟨s, a, b, c, r0, d⟩ :: r))) w) ka) (Nat.beq w.s sa)) v
def rmkB (sa da sc dc d0 : Nat) (v : List W) (h : List W → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (rmk sa true da sc true dc v h) (h v) (Nat.beq d0 0)
def put (m s x y : Nat) (v : List W) (d : Nat) (h : List W → Bool) : Bool :=
  st s fun s => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (st x fun x1 => st y fun y1 => st (Nat.lor x y) fun w => st d fun d => ins ⟨s, x1, y1, w, 0, d⟩ v h) false (Nat.beq s m)) false (Nat.beq s 0)
def kids (c : Bool → ((List W → Bool) → Bool) → Nat → Bool) (e n z u w fA fC : Nat) (a c' : W) (oa oc ka kc kb : Bool) (mk : Nat → (List W → Bool) → Bool) : Bool :=
  (fun fN sA sC =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
        (c kb (fun h => mk fN (fun r => rmkB a.s (Nat.land sC a.d) c'.s (Nat.land sA c'.d) (Nat.add a.d c'.d) r h)) (Nat.sub (Nat.sub z a.c) c'.c))
        (Nat.ble (Nat.succ (Nat.succ n)) e)) true
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (c kc (fun h => mk (Nat.add fN (Nat.land (MU (Nat.add fN fA)) a.d)) (fun r => rmk a.s false 0 c'.s true (Nat.land sA c'.d) r h)) (Nat.sub (Nat.sub z (Nat.land sC a.d)) c'.c)) oa) true
        (Bool.rec (motive := fun _ => Bool) false
          (c ka (fun h => mk (Nat.add fN (Nat.land (MU (Nat.add fN fC)) c'.d)) (fun r => rmk a.s true (Nat.land sC a.d) c'.s false 0 r h)) (Nat.sub (Nat.sub z a.c) (Nat.land sA c'.d))) oc)) (Nat.ble (Nat.succ n) e))) true
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (c false (fun h => mk (Nat.add (Nat.add fN (Nat.land (MU (Nat.add fN fA)) a.d)) (Nat.land (MU (Nat.add fN fC)) c'.d)) (fun r => rmk a.s false 0 c'.s false 0 r h)) (Nat.sub (Nat.sub z (Nat.land sC a.d)) (Nat.land sA c'.d))) oc) oa))
  (Nat.sub (Nat.sub (Nat.sub u w) fA) fC) (MU (Nat.add w fA)) (MU (Nat.add w fC))
def mid (f : Nat → List W → Bool) (m g np e n z : Nat) (v : List W) (a c : W) (oa oc ka kc kb : Bool) (s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    ((fun u w => (fun nc => st (zfl np (Nat.xor a.s s) nc) fun eA => st (zfl np (Nat.xor c.s s) (Nat.sub nc eA)) fun eC =>
      Bool.rec (motive := fun _ => Bool) false
        (st (Nat.sub (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) (Nat.add eA eC)) fun z =>
          kids (child f g) e n z u w (Nat.add eA (Nat.sub c.c (Nat.land c.c w))) (Nat.add eC (Nat.sub a.c (Nat.land a.c w))) a c oa oc ka kc kb (put m s x y v))
        (Nat.beq (Nat.land (Nat.sub (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) (Nat.add eA eC)) g) g))
      (Nat.sub u (Nat.lor (Nat.lor a.c c.c) w))) (Nat.shiftRight g 4) (Nat.lor x y))
    (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (Bool.rec (motive := fun _ => Bool)
    (st (Nat.xor a.s m) fun s => st (Nat.sub z a.c) fun z => (fun u =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (st u fun d1 => ins ⟨s, a.b, a.a, a.c, 0, d1⟩ v (fun v => child (f s) g false (rmk a.s true 0 a.s true 0 v) (Nat.sub z a.c))) (Nat.ble (Nat.succ n) e)) true
        (Bool.rec (motive := fun _ => Bool) false (st (Nat.add u a.d) fun d1 => ins ⟨s, a.b, a.a, a.c, 0, d1⟩ v (fun v => child (f s) g false (rmk a.s false 0 a.s false 0 v) z)) (Nat.ble n e)))
      (Nat.sub (Nat.shiftRight g 4) a.c)) false (Nat.beq (Nat.succ a.s) q))) r
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d
end hz4
section hz5
variable {R : ℕ → ℕ}
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
def segsX : List (ℕ × ℕ) := [(63, 77), (77, 91), (91, 105), (105, 119), (119, 121), (121, 123), (123, 126), (126, 140), (140, 142), (142, 144), (144, 147), (147, 161), (161, 164), (164, 167), (167, 181), (181, 183), (183, 186), (186, 188), (188, 191), (191, 194), (194, 196), (196, 198), (198, 201), (201, 204), (204, 206), (206, 208), (208, 211), (211, 214), (214, 217), (217, 231), (231, 233), (233, 235), (235, 238), (238, 240), (240, 243), (243, 245), (245, 248), (248, 250), (250, 253), (253, 255), (255, 258), (258, 261), (261, 264), (264, 266), (266, 269), (269, 271), (271, 274), (274, 277), (277, 280), (280, 283), (283, 286), (286, 289), (289, 292), (292, 295), (295, 298), (298, 301), (301, 315), (315, 317), (317, 320), (320, 323), (323, 326), (326, 328), (328, 330), (330, 333), (333, 335), (335, 337), (337, 339), (339, 353), (353, 356), (356, 358), (358, 361), (361, 363), (363, 365), (365, 368), (368, 370), (370, 373), (373, 387), (387, 390), (390, 393), (393, 395), (395, 397), (397, 399), (399, 402), (402, 405), (405, 407), (407, 409), (409, 411), (411, 413), (413, 415)]
def segsY : List (ℕ × ℕ) := [(415, 427), (427, 432), (432, 436), (436, 440), (440, 444), (444, 450), (450, 456), (456, 459), (459, 464), (464, 469), (469, 472), (472, 478), (478, 483), (483, 488), (488, 505), (505, 510), (510, 527), (527, 530), (530, 536), (536, 541), (541, 546), (546, 563), (563, 568), (568, 585), (585, 589), (589, 606), (606, 623), (623, 640), (640, 644), (644, 662), (662, 668), (668, 674), (674, 679), (679, 696), (696, 713)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
def lane (w n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (w * j)
def fb (x j : ℕ) : ℕ := (x.testBit (5 * j)).toNat
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ (b : ℕ → ℕ) (D : ℕ → ℕ → ℕ), (∀ j < P.length, b j ≤ 15) ∧ (∀ j < P.length, Acc (P.getD j 0) T k (b j) (D j) S) ∧
    (∀ w ∈ v, w.d = pk P.length (fun j => D j w.s)) ∧ (∀ j < P.length, k + ∑ s ∈ S, D j s ≤ 15) ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g np T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
  hnp : ∃ f : ℕ → ℕ, (∀ j < 16, f j < 2 ^ (2 * NN)) ∧ np = lane (WL NN) 16 f ∧ ∀ j < P.length, j < 16 → P.getD j 0 &&& f j = P.getD j 0
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0, 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0, 0⟩
def wd (w : W) (d : ℕ) : W := ⟨w.s, w.a, w.b, w.c, w.r, d⟩
def upd (sa da sc dc : ℕ) (w : W) : W := bif Nat.beq w.s sa then wd w da else bif Nat.beq w.s sc then wd w dc else w
def kp (sa : ℕ) (ka : Bool) (sc : ℕ) (kc : Bool) (w : W) : Bool := bif Nat.beq w.s sa then ka else bif Nat.beq w.s sc then kc else true
def kdOf (fo FA FC : ℕ) : Kd := if fo = 1 then .K0 else if FA = 1 then .KA else if FC = 1 then .KC else .N
def fAo (e o c : ℕ) : ℕ := Nat.add e (Nat.sub c (Nat.land c o))
def fNo (u w fA fC : ℕ) : ℕ := Nat.sub (Nat.sub (Nat.sub u w) fA) fC
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0, 0⟩
end hz5
noncomputable section hz6
variable {R : ℕ → ℕ}
def len (v : List W) : Nat := List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) v
def geo (w n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.add (Nat.shiftLeft ih w) 1) n
def LNN : Nat := Nat.mul 12 NN
def LN2 : Nat := Nat.mul 24 NN
def LN4 : Nat := Nat.mul 48 NN
def LM1 : Nat := Nat.mul 13 NN
def LM2 : Nat := Nat.mul 26 NN
def LM4 : Nat := Nat.mul 52 NN
def RL : Nat := geo NN 12
def PLN : Nat := Nat.pow 2 LNN
def AAR : Nat := Nat.mul AA RL
def HXR : Nat := Nat.mul HX (geo NN 84)
def HYR : Nat := Nat.mul HY (geo NN 84)
def MRR : Nat := Nat.mul (Nat.sub (Nat.pow 2 NN) (Nat.pow 2 64)) (geo NN 84)
def TOPR : Nat := Nat.shiftLeft (geo NN 72) LM1
def GMD : Nat := Nat.sub (Nat.pow 2 (Nat.sub NN 1)) 1
def pkd (d : Bool) (l : Nat) (v : List W) : Nat := List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.shiftLeft (sp d l w.s) (Nat.mul NN (len t))) ih) v
def dbl (m x : Nat) : Nat := Nat.lor x (Nat.shiftLeft x m)
def eg2 (G : Nat) : Nat := Nat.shiftRight (Nat.mod (Nat.land (Nat.land (Nat.add (Nat.land G HXR) MRR) (Nat.add (Nat.land G HYR) MRR)) TOPR) GMD) 1
def eg1 (F : Nat) : Nat := eg2 (Nat.land (dbl LN4 (dbl LN2 (dbl LNN F))) (dbl LM4 (dbl LM2 (dbl LM1 F))))
def edg (d : Bool) (l o : Nat) (v : List W) : Nat := eg1 (Nat.mod (Nat.add (Nat.land (pkd d l v) (Nat.mul o RL)) AAR) PLN)
def f12c (b : Nat) : Nat := Nat.land (Nat.lor b (Nat.shiftRight b 12)) 4095
def f12b (a : Nat) : Nat := f12c (Nat.lor a (Nat.shiftRight a 24))
def f12 (w : Nat) : Nat := f12b (Nat.lor w (Nat.shiftRight w 48))
def f13c (b : Nat) : Nat := Nat.land (Nat.lor b (Nat.shiftRight b 13)) 4095
def f13b (a : Nat) : Nat := f13c (Nat.lor a (Nat.shiftRight a 26))
def f13 (w : Nat) : Nat := f13b (Nat.lor w (Nat.shiftRight w 52))
def nbr (e S : Nat) : Nat := Nat.lor (f12 (Nat.land e (Nat.mul S 302268352895954163081217))) (f13 (Nat.land e (Nat.mul S 4723519685917965029377)))
def bfs (e : Nat) (fuel : Nat) : Nat → Nat → (Nat → Bool) → Bool := Nat.rec (motive := fun _ => Nat → Nat → (Nat → Bool) → Bool) (fun _ _ _ => false)
  (fun _ ih A B k => st (Nat.lor A (nbr e B)) (fun a => st (Nat.lor B (nbr e a)) (fun b => Bool.rec (motive := fun _ => Bool) true
    (Bool.rec (motive := fun _ => Bool) (ih a b k) (k (Nat.lor a b)) (Nat.beq (Nat.lor A B) (Nat.lor a b))) (Nat.beq (Nat.land a b) 0)))) fuel
def nonb (e : Nat) (fuel : Nat) : Nat → Bool := Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
  (fun _ ih r => Bool.rec (motive := fun _ => Bool) (bfs e 12 (Nat.gcd r 2048) 0 (fun c => ih (Nat.sub r (Nat.land r c)))) false (Nat.beq r 0)) fuel
def nonbip (e : Nat) : Bool := nonb e 12 (Nat.lor (f12 e) (f13 e))
def tch (i : Nat) : Nat := Nat.lor (Nat.mul i 302268352895954163081217) (Nat.mul i 4723519685917965029377)
def del (e i : Nat) : Nat := Nat.xor (Nat.lor e (tch i)) (tch i)
def ne0 (e : Nat) : Bool := Bool.rec (motive := fun _ => Bool) true false (Nat.beq e 0)
def kF (_ : Nat) : Bool := false
def kF2 (_ _ : Nat) : Bool := false
def kT2 (_ _ : Nat) : Bool := true
def tst1 (h : Nat) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (F (fun i => ne0 (del h i)) kT2) false (nonbip h)
def tri5 (a L r : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (Nat.lor a (Nat.gcd L 4096)) r (Nat.beq L 0)
def tri4 (h i N k r : Nat) : Nat := tri5 (Nat.lor i k) (Nat.land (nbr h k) N) r
def tri3 (h i N M r : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (tri4 h i N (Nat.gcd M 4096) r) r (Nat.beq M 0)
def tri2 (h i N r : Nat) : Nat := tri3 h i N (Nat.land (nbr h N) N) r
def tri1 (h i r : Nat) : Nat := tri2 h i (nbr h i) r
def tri (h : Nat) (fuel : Nat) : Nat → Nat := Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
  (fun _ ih r => Bool.rec (motive := fun _ => Nat) (tri1 h (Nat.gcd r 2048) (ih (Nat.sub r (Nat.gcd r 2048)))) 0 (Nat.beq r 0)) fuel
def k1 (h i : Nat) : Bool := nonbip (del h i)
def k2 (h i j : Nat) : Bool := ne0 (del (del h i) j)
def k3 (h T i : Nat) : Bool := Bool.rec (motive := fun _ => Bool) (nonbip (del h i)) true (Nat.beq (Nat.land i T) 0)
def k4 (h T i j : Nat) : Bool := Bool.rec (motive := fun _ => Bool) true (ne0 (del (del h i) j)) (Nat.beq (Nat.land (Nat.lor i j) T) (Nat.lor i j))
def tst2 (h : Nat) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool := st (tri h 12 (f12 h)) (fun T => Bool.rec (motive := fun _ => Bool) (F (k3 h T) (k4 h T)) (F (k1 h) (k2 h)) (Nat.beq T 0))
def tsn (d : Bool) (l e : Nat) (v : List W) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool :=
  (fun n => (fun o => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F kF kF2) (st (edg false l o v) (fun h => tst2 h F)) (Nat.beq (Nat.succ (Nat.succ n)) e))
      (st (edg false l o v) (fun h => tst1 h F)) (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) false (F kF kF2) (!(rect d l o v []))) (Nat.beq n e)) (wst d l v)) (len v)
end hz6
section hz7
variable {R : ℕ → ℕ}
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
  i : Nat
end hz7
noncomputable section hz8
variable {R : ℕ → ℕ}
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w t ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o, Nat.shiftLeft 1 (len t)⟩ :: ih) v
def f0 (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (ia ic da dc s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (h a c true true true true true s x y) (Nat.beq (Nat.lor da dc) 0)
def f1 (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (ia ic da dc s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (h a c false false true true false s x y) false (κ2 ia ic))
      (Bool.rec (motive := fun _ => Bool) (h a c false true false true (κ2 ia ic) s x y) (Bool.rec (motive := fun _ => Bool) (h a c false false true true false s x y) false (κ2 ia ic)) (κ ia)) (Nat.beq dc 0))
    (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (h a c true false true false (κ2 ia ic) s x y) (Bool.rec (motive := fun _ => Bool) (h a c false false true true false s x y) false (κ2 ia ic)) (κ ic))
      (h a c true true (κ ia) (κ ic) (κ2 ia ic) s x y) (Nat.beq dc 0))
    (Nat.beq da 0)
def f2 (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (ia ic da dc s x y : Nat) : Bool :=
  h a c (Nat.beq da 0) (Nat.beq dc 0) false false false s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u i => X.rec (motive := fun _ => Bool) (fun c s' q' u' j => Bool.rec (motive := fun _ => Bool)
    (h a c i j (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) true
    (h a c i j (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : X → X → Bool) (xs : List X) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : X → X → Bool) (xs : List X) : Bool := pairs h (fs xs)
def nodeH (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (d : Bool) (l e n : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 κ κ2 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ (Nat.succ n)) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g np e n z : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (go : (X → X → Bool) → List X → Bool) : Bool :=
  nodeH (mid f m g np e (Nat.pred n) z v) d l e n v κ κ2 go
def forb (fm fh s : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight fh (Nat.mod s fm)) 1) 1
def mid1 (fm fh : Nat) (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (oa oc ka kc kb : Bool) (s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (h a c oa oc ka kc kb s x y) false (forb fm fh s)
def node1 (f : Nat → List W → Bool) (d : Bool) (l m g np fm fh e n z : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (go : (X → X → Bool) → List X → Bool) : Bool :=
  nodeH (mid1 fm fh (mid f m g np e (Nat.pred n) z v)) d l e n v κ κ2 go
def mv (F : Nat → Nat → Nat → List W → Bool) (l m g np k t z : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tsn (pos s) l (Nat.sub k s) v (fun κ κ2 =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tsn (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun κ κ2 =>
          st (Nat.sub k 3) fun k3 => node (F k3 s) (pos s) l m g np (Nat.sub (Nat.sub k 2) s) (len v) z v κ κ2 (pairsQ q q'))))
          m g (Nat.sub (Nat.sub k 1) s) (len v) z (Nat.succ q) v v)) true
        (st (Nat.sub k 2) fun k2 => node (F k2 s) (pos s) l m g np (Nat.sub (Nat.sub k 1) s) (len v) z v κ κ2 (pairsP q)))))
      m g (Nat.sub k s) n z 0 v v)) true
    (st (Nat.sub k 1) fun k1 => node (F k1 t) (pos t) l m g np (Nat.sub k t) n z v κ κ2 pairsN)) (len v)
def look (l m g np : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (Nat.sub (Nat.succ k) t) v (fun κ κ2 => mv ih l m g np k t z v κ κ2)) true (Nat.ble (len v) 1)) fuel
def look1 (l m g np fm fh K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (Nat.sub (Nat.succ k) t) v (fun κ κ2 =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g np k) l m g np k t z v κ κ2) true
        (st (Nat.sub k 1) fun k1 => node1 (ih k1 t) (pos t) l m g np fm fh (Nat.sub k t) (len v) z v κ κ2 pairsS))) true (Nat.ble (len v) 1)) fuel
end hz8
section hz9
variable {R : ℕ → ℕ}
def Pos (v : List W) (w : W) (i : ℕ) : Prop := ∃ pre t, v = pre ++ w :: t ∧ t.length = i
structure KP (R : ℕ → ℕ) (m T k' t : ℕ) (S : Finset ℕ) (v : List W) (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool) : Prop where
  g1 : ∀ {d : Bool} {a b : ℕ} {S1 : Finset ℕ} {k0 : ℕ}, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → a ∈ S1 → b ∉ S1 →
    ∀ w i, Pos v w i → w.s = a → κ (2 ^ i) = false
  g2 : ∀ {d : Bool} {a b : ℕ} {S1 : Finset ℕ} {k0 : ℕ}, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → a ∈ S1 → b ∈ S1 →
    ∀ wa i wb j, Pos v wa i → wa.s = a → Pos v wb j → wb.s = b → κ2 (2 ^ i) (2 ^ j) = false
def segOkR (s : ℕ × ℕ) : Bool := decide (s.2 < NN) && (List.range 12).all (fun i =>
  decide (AAR % 2 ^ (NN * i + s.2) + 2 ^ (NN * i + s.1 + 1) = 2 ^ (NN * i + s.2) + AAR % 2 ^ (NN * i + s.1)) && !AAR.testBit (NN * i + s.2))
def laneOk (p : ℕ) : Bool := decide (MRR % 2 ^ (NN * p + NN) + 2 ^ (NN * p + 63 + 1) = 2 ^ (NN * p + NN) + MRR % 2 ^ (NN * p + 63)) &&
  !MRR.testBit (NN * p + NN) && !HXR.testBit (NN * p + NN) && !HXR.testBit (NN * p + 63) && !HYR.testBit (NN * p + NN) && !HYR.testBit (NN * p + 63)
def Hq (d : Bool) (l o a b : ℕ) : Prop :=
  (∃ s ∈ segsX, ∃ i1 i2, s.1 < i1 ∧ i1 < s.2 ∧ s.1 < i2 ∧ i2 < s.2 ∧ (Nat.land (sp d l a) o).testBit i1 = true ∧ (Nat.land (sp d l b) o).testBit i2 = true) ∧
  (∃ s ∈ segsY, ∃ i1 i2, s.1 < i1 ∧ i1 < s.2 ∧ s.1 < i2 ∧ i2 < s.2 ∧ (Nat.land (sp d l a) o).testBit i1 = true ∧ (Nat.land (sp d l b) o).testBit i2 = true)
def Adj (e x y : ℕ) : Prop := ∃ p, e.testBit p = true ∧ ((p % 13 = x ∧ p % 12 = y) ∨ (p % 13 = y ∧ p % 12 = x))
def Eb (e : ℕ) : Prop := ∀ p, e.testBit p = true → 12 ≤ p ∧ p < 84
def Pc (e : ℕ) (c : ℕ → Bool) : Prop := ∀ x y, Adj e x y → c x ≠ c y
def Cod (R : ℕ → ℕ) (v : List W) : Prop := ∀ w ∈ v, w.r = 0 ∨ w.r = R w.s
def RR (R : ℕ → ℕ) : Prop := ∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b
def xof (d : Bool) (l o : ℕ) (w : W) (i : ℕ) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o, 2 ^ i⟩
def modeH (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (n e : ℕ) (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool) : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ (Nat.succ n)) e then f2 h else f1 κ κ2 h) else f0 h
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
def rawP : List ℕ := [0xffff8000000000ffff00000000000003e0000000000000f80000000003c000100000c44000003110000040444004800805080001004448020002008512000120000904004821200482120bf9cfce33ffe61fe00436021b0820ab6360011b008da3c6c002361008d842f8004d84013610be0212082222f01b040000300000000c000002b0100003600603420002c0b10001802188634000000000afff857ffc0007ffdffffe73f38cfff987f8,0x3fffc003e00000000000000000007fff81fffe078000000000000000003c00f8038000000610608300800820c0422030830210040200161084210860400100400218832180890c04486021888602191cfd752dfff3ad2b4088aae45004f8028a0024501228051451e8a047a281e0800a288028a210244f013e04e1045001841800002002000011880c0001860301802d84210840001808c23085fff0c00062000310001fff0001fff73f5d4b7ffceb4ad,0x7fff800000f800000000000000000000000000000000001fffe07fff81e007803e003800000010010100660460403104818100c48020100200020080100e0c280a0284061840612203091018407101c4062cfeba56fff3d2d595d0c048603e10050c00486024300a188050c201430841127c3009f0c07841e20f840e42086004004000018118000041a0600001b0180c058005816057ffc30a0280b00006000068000340001fff7ffc000b3fae95bffcf4b56,0x1fffe00000000001fffef0000000007fffbc0000003efb80000004001400092005000250000090096001003680024005a8012404800ad0004a0904a800250d412c04a012804a37fbf39b0343e7f9c12500928108201850218284f94050a00285044f943c020091410b750f0080844fbee004128100050000000140000054006d7ffc00c00db001b0016b0000036002b6000006dfff00000357ffc0000000000dfefce6c0d0f9fe7,0x7fffbfffde000000003fffc0000000007fffbc000000001fffef0000000007bd80000000001016c0019246b00064a156a8019280026d00000496a0001a48092b40000694126951ab4a801a506941a506940fe3c3fb338e7e1815c60ae3078000206008f300418020c011e60f02181004025d83c046040101ef62084008030405b0000001ac00000055ab00000000db600001b5ac000000036ad800000006dfff6afff80000000000000003f8f0fecce39f860,0x3fffdfffeffff7000000000000001fffef7fffbdefb0000000000000154000001c62152107380000001cc00369b4d6a0000000038c0daa6a9ad0e7000e6000730003980e603980e609ab1ded5514faabc6080304021040c0804af4057a02bd01c5080014200080035e03cd780f7bec080010008024055000000001ad5adfff000000000000db6db5ac0000000000036adab6b5fff0000000000000000000000000026ac77b55453eaaf,0x3fffdfffeffff77fffbdfffef7bec000000000000000000000000000154254241f80000007c00000001f00034da6d4b6d4b52d43f06000000000f8000f80007c0003e00f803e00f80ad32ef6aa197d55d8100c0804208301008cf8067c033e01d9f00f67c03defb4600011800020010004000800480555b55b7ffc00000000000000000000db6db5adb5ad6b57ffd800000000000000000000000000000000000002b4cbbdaa865f557,0x7fffbfffdefbeffffb8000000000000000000000000000000000000000000000000000000000148149e004a04a780156ad25e006d8000000000000001c000000000007000070000380001c007001c007003f63ff03cf2d9f86dfe00ff007befbfe00ef00078003c0011e0008780021082780021e000842080008208000700555b55b7ffdad5adfff55ab6d7ffdb6000000000000000000000000000000000000000000000000000000000fd8ffc0f3cb67e1b]
def TG : ℕ := 0x1fffeffff7befbfffeeffff7fffbfffddfffef7fffbdefb7fffbdfffef7bedef6fbeeeef7ff555b55b7ffdad5adfff55ab6d7ffdb6db6db5adb5ad6b57ffdb6adab6b5fff6dfff6afffb57ffdfff7ffdfffffffffffffffffff
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def pinMask (Z : ℕ) : ℕ := (List.range 8).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else
  (bif Nat.testBit Z (i + 8) then Nat.lor x (Nat.xor FULL (Nat.land (rawP.getD i 0) (Nat.lor (Nat.shiftRight (rawP.getD i 0) NN) FPM))) else x)) 0
def relationCuts : List ℕ := [0x0,0x202010000802020000100008040400202000808020800008000020002001000200210010000000000000000000000800000006000000200020080000180000000400000000020000100000000001fff7271d084ffc884a8,0x40400020020004040000200010080800004000010001000410001040084020008002020020000000000000000000002000000030000004000000001000000200803000000000080000400000007ffc000b272e108ffc90350,0x10000800000101000008008401020000100008404020000400011010080000082200400800000000000000000000000010000000000300000000b000000000086000000000000000057ffc0000000000de63c20c0d0987e0,0x42002100800020200011000080204000220100080004000480400200010021200000080100000000000000000000002b0000000000600000002c0000000002180000000000000afff80000000000000003e03038cce398060,0x80000010000803fffc000000000000000004004010010be00000000000000040000001000000c04000000001000000603420000000002000021886340800008000040000200080020008026207384545182a8,0x200000010000803fffc0020010080042f80000000000000000000000000000040000301000000004000000001000000603420002c0b10201800000000080000800004000020008002000802a40b388a8618550,0x40002000820bfffe000000000200000000000000000800000000000002000000000000000040000310000000c400002b01100036000000000000000100000000000040000400002000010004001000400fc03f00c3cb00618,0x8080404004100008000040002000100040800102004000082000208010004201040440004000000000000000000001800000018000000000040100400000080200800000000060000300001fff000000033f0c013ffce0004,0x800000200000000000100000000080007fff8000000000002002000004013e0000000000040000400000001010000c00400000018001800108000800000230000200c02000010310080020008002053e5c4240d0e94a5,0x800ffff000000000002000000000001fffe00200000000080080000000004f0008000000000180002080200008201188002080000300000184200002100008c000008400c840624200021008402100840338504a4ce08b020,0x8020400004000800024001200050041080004200080000a008028021024080010008004000000000000200200000000000000000301802c00000000000008c23085fff0000000000000000000000000022a454b55442a0ad,0x8000000800000002000100004005fffe07fff81e080000000000000000000000000000001841800c00000003000000000c0000301802d842108401818000000000600006000030000180060018006023449092a844b405,0x800ffff004f80200000000000000001000004000010000000000000000000000200000000001841820002002080011880c2001860000000000000002000000000000800008000040000200080020008007185d4073c863409,0x1000000000800000000000020000000000000010008000010001fffe00000800f8400000000000000000801000004400060001000000c0000000160000103000280000086000800004340020008002000893eac8480d0f0b46,0x1fffe0400000000000004000000000000040020000000007fff80040000001e202000000000004000040118000100841a000402000180000000580000402030a00000101061010688080040410104041010338a0948ce094840,0x40000000010000000004000200008008000000000000007fff81fffe078400000000000000000000000198118000c000000003000180c05800000000003030a0280b0018000180000c000060018006001822a8611154434a06,0x10100008002000010000480024000a0080500201400841106000018000200100040008000800040040000000000000000000000000180c058005816057ffc000000000000000000000000000000000000002348a95aa8454156,0x1fffe040003e100400000000000000000000000000000002000008000040000008000000000004004040018118100041a0604001b0000000000000000400000000000100001000008000040010004001000b18ae80b3c864a12,0x104008201000000400082004100008000840402101000001101004404000084420840000200000000000000000000540000000000c0000001b00000000003600000000006dfff0000000000000000000001f8f0e6c0c099860,0x8007fff81000000000040000000010011fffef008000001000000001000000020801400084000000021000c00db0000000000041036002b6001080010800084000420108042010806ac462404038aa7,0x8007fff810000080047fffbc02000000010000000000040000000001000500024000000090000000024000c00db001b0016b00480000000000120001200009000048012004801200b4c8a4808059547,0x1200090010820180021000480004000020000480020000080000a000800000008208000100100050000000140000054006d7ffc00000000000000000000000000000000000000000000000000000000000dd8fcc0c0c061e03,0x400020002000000000ffff0400020000100000000000007fffbc040040100080000000000040000000411ac000108000000042000db6000000000000082036ad8000021000210001080008402100840210268c07a44411e820,0x1000080004000000000ffff0400020001fffef0200100400400000000000010000000000000405b000048000000120000000048000db600001b5ac0000900000000000240002400012000090024009002402b0c0bc88821f040,0x1fffeffff780002000080000000000001000080000000002000200000000000000000000000405b0006001ac00180055ab0060000000000000000000060000000000018000180000c0000600180060018003d8f0c0c0c307800,0xffff7fffbfffdc10000040000800040000100002000000000000000055000000700000001c0000000070000db6db5ac00000000e0000000000038000380001c0000e003800e00380220c33900041e007,0x6000300021040c0004a000500028001040000100000000300020c00084208000000000020055000000001ad5adfff000000000000000000000000000000000000000000000000000000000000000000000248c740514126a0b,0x18000c0004208300008c0006000300011800086000210824000010000000000000000000400555b55b7ffc00000000000000000000000000000000000000000000000000000000000000000000000000000290cb80a28247413]
def kz (Z : ℕ) : ℕ := pinMask Z ||| relationCuts.getD (Z >>> 16) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
def tw (e : Bool × ℕ × ℕ) : ℕ := op e.1 (rawP.getD e.2.1 0) (rawP.getD e.2.2 0)
def rawL (E : List (Bool × ℕ × ℕ)) : List ℕ := rawP ++ E.map tw
def WZ (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}
def Imp (E : List (Bool × ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
def trivE (e : Bool × ℕ × ℕ) (Z : ℕ) : Bool :=
  (fun m => (fun s => Nat.beq s 0 || Nat.beq s m || rawP.any (fun w => Nat.beq (Nat.land w m) s)) (Nat.land (tw e) m)) (mz Z)
def tabV (e : Bool × ℕ × ℕ) (own : List ℕ) (x : ℕ × ℕ) : ℕ := bif own.any (fun c => Nat.beq c x.1) || trivE e x.1 then x.2 else Nat.sub x.2 1
def tabE (e : Bool × ℕ × ℕ) (own : List ℕ) (raw : List (ℕ × ℕ)) : List (ℕ × ℕ) := raw.map (fun x => (x.1, tabV e own x))
def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)
def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
def npOf (P : List ℕ) : ℕ := laneL (WL NN) ((List.range 16).map (fun j => P.getD j 0))
end hz9
noncomputable section hz10
variable {R : ℕ → ℕ}
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end hz10
section hz11
variable {R : ℕ → ℕ}
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
end hz11
noncomputable section hz12
variable {R : ℕ → ℕ}
def fl0 (s : ℕ) (P : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun n _ ih => Nat.add (Nat.shiftLeft ih 5) (bit01 (Nat.beq (Nat.land s n) 0))) P
def fl1 (s : ℕ) (P : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun n _ ih => Nat.add (Nat.shiftLeft ih 5) (bit01 (Nat.beq (Nat.land s n) n))) P
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, fl0 s P, fl1 s P, Nat.lor (fl0 s P) (fl1 s P), 3, 0⟩
def addN (o : ℕ) (v : List ℕ) : List ℕ := List.rec (motive := fun _ => List ℕ) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List ℕ) (w :: ih) (Bool.rec (motive := fun _ => List ℕ) (o :: w :: t) (w :: t) (Nat.beq o w)) (Nat.ble w o)) v
def avl (m : ℕ) (L : List ℕ) : List ℕ := List.rec (motive := fun _ => List ℕ) []
  (fun w _ ih => Bool.rec (motive := fun _ => List ℕ) (Bool.rec (motive := fun _ => List ℕ) (addN (Nat.land w m) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def mkA (P : List ℕ) (L : List ℕ) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun s _ ih h => st s fun s => st (fl0 s P) fun a => st (fl1 s P) fun b => st (Nat.lor a b) fun c => ih fun r => h (⟨s, a, b, c, 3, 0⟩ :: r)) L
def frcP (L : List ℕ) : (List ℕ → Bool) → Bool := List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun h => h [])
  (fun s _ ih h => st s fun s => ih fun r => h (s :: r)) L
def anySub (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (cov d l t)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def fbit (fm fh s : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight fh (Nat.mod s fm)) 1) 1
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
end hz12
section hz13
variable {R : ℕ → ℕ}
def Srt (v : List ℕ) : Prop := v.Pairwise (fun a b => b < a)
def mFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)
def FF : ℕ := 2 ^ MM - 1
def fbOk (E F : List (Bool × ℕ × ℕ)) (fb : ℕ × ℕ) : Bool :=
  (fun m => (fun W => (fun G => W.all (fun x => W.all (fun y => Nat.beq x y ||
      ((!fbit fb.1 fb.2 (Nat.land x y) || G.any (Nat.beq (Nat.land x y))) && (!fbit fb.1 fb.2 (Nat.lor x y) || G.any (Nat.beq (Nat.lor x y)))))))
    (F.map (fun e => Nat.land (tw e) m))) ((rawL E).map (fun w => Nat.land w m))) (mz 0)
def pwr (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : ℕ := (E.map fun e => Nat.land (tw e) (mz Z)).headD 0
open Classical in
noncomputable def RZ (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : ℕ → ℕ := fun s => if s ∈ WZ E Z then 3 else 0
end hz13
noncomputable section hz14
variable {R : ℕ → ℕ}
def frcQ (Q : List (ℕ × ℕ)) : (List (ℕ × ℕ) → Bool) → Bool := List.rec (motive := fun _ => (List (ℕ × ℕ) → Bool) → Bool) (fun h => h [])
  (fun x _ ih h => st x.1 fun c => st x.2 fun L => ih fun r => h ((c, L) :: r)) Q
def lnW (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) v
def anyN (h : ℕ → Bool) (L : List ℕ) : Bool := List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (h a)) L
def pre (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (Z K : ℕ) (h : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) : Bool :=
  frcQ Q fun Q => frcP (PZ Q) fun P => st (lz Z) fun l => st (mz Z) fun m => st (npOf P) fun np => st (pL (Q.map fun _ => 16)) fun g => st (pL (Q.map fun e => 16 + (K - e.2))) fun B =>
    st (pwr E Z) fun p => frcP (avl m (rawL E)) fun sg => mkA P sg fun v => h l m np g B p v
def startG (f : ℕ → List W → Bool) (g B K t p : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child f g false (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble (lnW v) (Nat.sub (Nat.succ K) t))) (hasP p v)
def chkG (top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (fb : ℕ × ℕ) (Z K t H ph : ℕ) : Bool :=
  st fb.1 fun fm => st fb.2 fun fh => pre E Q Z K fun l m np g B p v => anySub (pos t) l v 0 fun r => startG (fun z r => top l m g np fm fh K H ph K t z r) g B K t p r
def chkT (top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (fb : ℕ × ℕ) (Z K : ℕ) (ts : List ℕ) (H ph : ℕ) : Bool :=
  st fb.1 fun fm => st fb.2 fun fh => pre E Q Z K fun l m np g B p v => anyN (fun t => anySub (pos t) l v 0 fun r => startG (fun z r => top l m g np fm fh K H ph K t z r) g B K t p r) ts
end hz14
section hz15
variable {R : ℕ → ℕ}
def TopOk (top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) : Prop :=
  ∀ {P : List ℕ} {l m g np T : ℕ}, Ctx P l m g np T → ∀ {R : ℕ → ℕ}, (∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b) → (∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) →
    ∀ {fm fh K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)} {Fs : Set ℕ}, mFull M = true → (∀ p ∈ M, top l m g np fm fh K p.1 p.2 k t z v = false) →
      StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) → ∀ {k' : ℕ}, k' ≤ k → Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) →
      (∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs) →
      (∀ s ∈ Fs, ∀ q < k', ¬ Sol Z0 m T q (C m (insert s ({x | R x ≠ 0} ∪ (S : Set ℕ))))) → False
def MW (R : ℕ → ℕ) (m T k : ℕ) (S : Finset ℕ) : Prop := ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))
def MF (R : ℕ → ℕ) (m T k : ℕ) (Fs : Set ℕ) (S : Finset ℕ) : Prop := ∀ s ∈ Fs, ∀ q < k, ¬ Sol Z0 m T q (C m (insert s ({x | R x ≠ 0} ∪ (S : Set ℕ))))
end hz15
noncomputable section hz16
variable {R : ℕ → ℕ}
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g np fm fh K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (Nat.sub (Nat.succ k) t) v (fun κ κ2 =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g np k) l m g np k t z v κ κ2) (Nat.beq ph 1)) true
      (st (Nat.sub k 1) fun k1 => node1 (look1 l m g np fm fh K K k1 t) (pos t) l m g np fm fh (Nat.sub k t) (len v) z v κ κ2 (fun h xs => pairsC H h (fs xs))))) true (Nat.ble (len v) 1)
end hz16
section hz17
variable {R : ℕ → ℕ}
def P1 (R : ℕ → ℕ) (P : List ℕ) (l m T : ℕ) (Fs : Set ℕ) (f : ℕ → ℕ → ℕ → List W → Bool) : Prop :=
  ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
    ∀ k' ≤ k, Live Z0 m T k' t S → MW R m T k' S → MF R m T k' Fs S → False
abbrev TopT := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool
noncomputable def okR (top : TopT) (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (x : ℕ × ℕ) : Bool :=
  pOk x.1 Q && Nat.ble x.2 15 && (Q.any (fun y => Nat.ble x.2 y.2) || !chkT top E Q (1, 0) x.1 (x.2 - 1) (List.range x.2) FF 1)
def pr (T : List (ℕ × ℕ)) (c : ℕ) : List (ℕ × ℕ) := T.filter (fun y => Nat.beq (Nat.land c y.1) c && !Nat.beq c y.1)
def pick (T : List (ℕ × ℕ)) (cs : List ℕ) : List (ℕ × ℕ) := cs.filterMap (fun c => T.find? (fun x => Nat.beq x.1 c))
noncomputable def okU (top : TopT) (T : List (ℕ × ℕ)) (r : (ℕ × ℕ) × List ℕ) : Bool := okR top [] (pick T r.2) r.1
noncomputable def okO (top : TopT) (e : Bool × ℕ × ℕ) (own : List ℕ) (raw : List (ℕ × ℕ)) (r : (ℕ × ℕ) × List ℕ) : Bool :=
  raw.all (fun x => !Nat.beq x.1 r.1.1 || Nat.beq x.2 r.1.2) && okR top [e] (tabE e own (pick raw r.2)) r.1
def inC (cs : List ℕ) (x : ℕ × ℕ) : Bool := cs.any (fun c => Nat.beq c x.1)
def rho (p : List ℕ) (w : ℕ) : ℕ := p.foldr (fun i x => 2 * x + (w.testBit i).toNat) 0
end hz17

variable {R : ℕ → ℕ}
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
lemma Al.symm {d : Bool} {a b : ℕ} (h : Al R d a b) : Al R d b a := by unfold Al at *; rwa [Nat.and_comm]
lemma al0 (d : Bool) (a b : ℕ) : Al Z0 d a b := by simp [Al, Z0]
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol R m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R' : ℕ → ℕ} {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Sol R' m T q S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) : Sol Z0 m T q S := h.rel fun d a b _ => al0 d a b
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : Sol Z0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb hal _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl, hal⟩ := h; exact .bi hab hal hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') : Bi R d b a S S' := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm], hal.symm⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (al0 _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min R m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi R d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_, hal⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min R m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi R d a b S S1 ∧ Live R m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi R d (a ^^^ m) c S1 S2 ∧ Live R m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi R d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live R m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hal hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl, hal⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live R m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (al0 _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) : Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min R m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hal : Al R d a b) (hl : Live R m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min R m T k t (insert (op d a b) U) := by
  have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live R m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min R m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live R m T k 0 S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hal hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hal hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hal hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect
section chrom
variable {N m T : ℕ}
lemma Ht.symm {e : Bool} {S : Finset ℕ} {a b : ℕ} (h : Ht N m T e S a b) : Ht N m T e S b a := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  exact ⟨i2, i1, j2, j1, l2, l1, l4, l3, fun w hw => (r1 w hw).symm, fun w hw => (r2 w hw).symm, u2, u1, u4, u3, p2, p1⟩
lemma bi_uq2 {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hi : Lg N m T i) (hc : c ∈ insert a (insert b U)) (h1 : c = a → a ∉ U) (h2 : c = b → b ∉ U)
    (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hcU : c ∉ U := by
      rcases hcc with rfl | rfl; exacts [h1 rfl, h2 rfl]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl; exact hcU hx
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma pol_op {a b i : ℕ} {d e : Bool} (ha : sepb N e a i = true) (hb : sepb N e b i = false) (ho : sepb N e (op d a b) i = true) :
    (op d a b).testBit i = a.testBit i := by
  revert ha hb ho; unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
    cases b.testBit (N + i) <;> simp
lemma pol_phi {a b c i : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (h : Uq N e (insert a (insert b U)) c i)
    (hu : Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i) :
    (if c = a ∨ c = b then op d a b else c).testBit i = c.testBit i := by
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc] at hu ⊢
    rcases hcc with rfl | rfl
    · exact pol_op h.1 (h.2 b (by simp) (Ne.symm hab)) hu.1
    · rw [op_comm] at hu ⊢
      exact pol_op h.1 (h.2 a (by simp) hab) hu.1
  · rw [ite_eq_right hcc]
lemma ht_bi {a b k t c1 c2 : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hc1 : c1 ∈ insert a (insert b U)) (hc2 : c2 ∈ insert a (insert b U))
    (h1 : c1 = a → a ∉ U) (h1' : c1 = b → b ∉ U) (h2 : c2 = a → a ∉ U) (h2' : c2 = b → b ∉ U)
    (h : Ht N m T e (insert a (insert b U)) c1 c2) :
    Ht N m T e (insert (op d a b) U) (if c1 = a ∨ c1 = b then op d a b else c1) (if c2 = a ∨ c2 = b then op d a b else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := bi_uq2 he hl l1 hc1 h1 h1' u1
  have v2 := bi_uq2 he hl l2 hc2 h2 h2' u2
  have v3 := bi_uq2 he hl l3 hc1 h1 h1' u3
  have v4 := bi_uq2 he hl l4 hc2 h2 h2' u4
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, v1, v2, v3, v4, ?_, ?_⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r1 a (by simp), r1 b (by simp)]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r2 a (by simp), r2 b (by simp)]
    · exact r2 w (by simp [hw])
  · rw [pol_phi hab u1 v1, pol_phi hab u3 v3, p1]
  · rw [pol_phi hab u2 v2, pol_phi hab u4 v4, p2]
lemma ht_merge {a b k t : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (h : Ht N m T e (insert a (insert b U)) a b) : False := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := (bi_uq2 he hl l1 (by simp) (fun _ => ha) (fun _ => hb) u1).1
  have v2 := (bi_uq2 he hl l2 (by simp) (fun _ => ha) (fun _ => hb) u2).1
  have v3 := (bi_uq2 he hl l3 (by simp) (fun _ => ha) (fun _ => hb) u3).1
  have v4 := (bi_uq2 he hl l4 (by simp) (fun _ => ha) (fun _ => hb) u4).1
  simp only [true_or, or_true, if_true] at v1 v2 v3 v4
  have e1 := r1 a (by simp); have e2 := r2 a (by simp); have e1b := r1 b (by simp); have e2b := r2 b (by simp)
  have n1 := u1.2 b (by simp) (Ne.symm hab); have n3 := u3.2 b (by simp) (Ne.symm hab)
  have n2 := u2.2 a (by simp) hab; have n4 := u4.2 a (by simp) hab
  have s1 := u1.1; have s2 := u2.1; have s3 := u3.1; have s4 := u4.1
  revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 v1 v2 v3 v4 p1 p2
  unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> simp <;> grind
lemma un_uq2 {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (h1 : c = a → a ∉ U) (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  by_cases hca : c = a
  · exact un_uq hi (h1 hca) hc h
  · rw [ite_eq_right hca]
    have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
    · exact h.2 x (by simp [hx]) hne
lemma ht_un {a c1 c2 : ℕ} {U : Finset ℕ} (hc1 : c1 ∈ insert a U) (hc2 : c2 ∈ insert a U) (h1 : c1 = a → a ∉ U) (h2 : c2 = a → a ∉ U)
    (h : Ht N m T true (insert a U) c1 c2) :
    Ht N m T true (insert (a ^^^ m) U) (if c1 = a then a ^^^ m else c1) (if c2 = a then a ^^^ m else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
      (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
    intro c i j m1 m2 p
    split_ifs with h
    · subst h; simp [m1, m2, p]
    · exact p
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, un_uq2 l1 h1 hc1 u1, un_uq2 l2 h2 hc2 u2, un_uq2 l3 h1 hc1 u3, un_uq2 l4 h2 hc2 u4,
    pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r1 a (by simp), l1.1, l2.1]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r2 a (by simp), l3.2.1, l4.2.1]
    · exact r2 w (by simp [hw])
lemma chrom {e : Bool} {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (he : e = true ∨ t = 0) :
    ∃ (x : ℕ) (f : ℕ → ℕ), S.card + t + x = k + 1 ∧ (∀ a ∈ S, f a ≤ x) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Ht N m T e S a b → f a ≠ f b := by
  induction hl with
  | stop =>
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t a U hl ih =>
    have he1 : e = true := he.resolve_right (by omega)
    subst he1
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have hmin := hu.min hl hm
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at hx
    have sm : ∀ {i1 i2 : ℕ}, m.testBit i1 = true → m.testBit i2 = true → (∀ w ∈ insert a U, w.testBit i1 = w.testBit i2) →
        ∀ w ∈ insert (a ^^^ m) U, w.testBit i1 = w.testBit i2 := by
      intro i1 i2 m1 m2 r w hw
      simp at hw
      rcases hw with rfl | hw
      · simp [r a (by simp), m1, m2]
      · exact r w (by simp [hw])
    by_cases ha : a ∈ U
    · have eS : insert a U = U := Finset.insert_eq_of_mem ha
      refine ⟨x + 1, fun c => if c = a then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
      · intro c hcS
        rw [eS] at hcS
        by_cases hca : c = a
        · simp [hca]
        · simp only [hca, if_false]
          have := hfx c (by simp [hcS]); omega
      · intro c1 h1 c2 h2 h12 hh
        rw [eS] at h1 h2
        by_cases q1 : c1 = a
        · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
          have := hfx c2 (by simp [h2])
          simp only [q1, q2, if_true, if_false]; omega
        · by_cases q2 : c2 = a
          · have := hfx c1 (by simp [h1])
            simp only [q1, q2, if_true, if_false]; omega
          · simp only [q1, q2, if_false]
            refine hc c1 (by simp [h1]) c2 (by simp [h2]) h12 ?_
            obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
            have tr : ∀ {c i : ℕ}, c ≠ a → Lg N m T i → Uq N true (insert a U) c i → Uq N true (insert (a ^^^ m) U) c i := by
              intro c i hca hi h
              refine ⟨h.1, fun y hy hne => ?_⟩
              simp at hy
              rcases hy with rfl | hy
              · have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
                rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
              · exact h.2 y (by simp [hy]) hne
            exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, tr q1 l1 u1, tr q2 l2 u2, tr q1 l3 u3, tr q2 l4 u4, p1, p2⟩
    · rw [Finset.card_insert_of_notMem ha]
      have mem : ∀ {c : ℕ}, c ∈ insert a U → (if c = a then a ^^^ m else c) ∈ insert (a ^^^ m) U := by
        intro c hcS; split_ifs with h <;> simp at hcS ⊢; tauto
      refine ⟨x, fun c => f (if c = a then a ^^^ m else c), by omega, fun c hcS => hfx _ (mem hcS), ?_⟩
      intro c1 h1 c2 h2 h12 hh
      refine hc _ (mem h1) _ (mem h2) ?_ ?_
      · split_ifs with p q q
        · exact absurd (p.trans q.symm) h12
        · intro e; simp at h2; rw [← e] at h2; rcases h2 with h | h
          · exact q (by rw [← e, h])
          · exact hf h
        · intro e; simp at h1; rw [e] at h1; rcases h1 with h | h
          · exact p (by rw [e, h])
          · exact hf h
        · exact h12
      · obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
        have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
            (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
          intro c i j m1 m2 p
          split_ifs with h
          · subst h; simp [m1, m2, p]
          · exact p
        exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, un_uq l1 ha h1 u1, un_uq l2 ha h2 u2, un_uq l3 ha h1 u3, un_uq l4 ha h2 u4,
          pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hu.fresh hl hm (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have hmin := hu.min hl hm
    have he2 : e = true ∨ e = pos' t := by
      rcases he with h | h
      · exact Or.inl h
      · subst h; cases e <;> simp [pos']
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 he
    rw [Finset.card_insert_of_notMem hf] at hx
    have mem : ∀ {c : ℕ}, c ∈ insert a (insert b U) → (if c = a ∨ c = b then op d a b else c) ∈ insert (op d a b) U := fun h => phi_mem h
    by_cases ha : a ∈ U
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = U := by rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
        refine ⟨x + 2, fun c => if c = a then x + 2 else if c = b then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
        · intro c hcS
          rw [eS] at hcS
          have := hfx c (by simp [hcS])
          dsimp only; split_ifs <;> omega
        · intro c1 h1 c2 h2 h12 hh
          have k1 := h1; have k2 := h2
          rw [eS] at h1 h2
          have f1 := hfx c1 (by simp [h1]); have f2 := hfx c2 (by simp [h2])
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
            · by_cases q3 : c1 = b
              · have q4 : c2 ≠ b := fun e => h12 (q3.trans e.symm)
                simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
              · by_cases q4 : c2 = b
                · simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
                · simp only [q1, q2, q3, q4, if_false]
                  have := ht_bi hab he2 hl k1 k2 (fun e => absurd e q1) (fun e => absurd e q3) (fun e => absurd e q2) (fun e => absurd e q4) hh
                  simp only [q1, q2, q3, q4, or_self, if_false] at this
                  exact hc c1 (by simp [h1]) c2 (by simp [h2]) h12 this
      · have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
        refine ⟨x + 1, fun c => if c = a then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem hb]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = a
          · simp [hca]
          · simp only [hca, if_false, false_or] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, false_or] at f2 ⊢; omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false, false_or] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun e => absurd e q1) (fun _ => hb) (fun e => absurd e q2) (fun _ => hb) hh
              simp only [q1, q2, if_false, false_or] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = b ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = b ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = insert a U := by rw [Finset.insert_eq_of_mem hb]
        refine ⟨x + 1, fun c => if c = b then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem ha]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = b
          · simp [hca]
          · simp only [hca, if_false, or_false] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = b
          · have q2 : c2 ≠ b := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, or_false] at f2 ⊢; omega
          · by_cases q2 : c2 = b
            · simp only [q1, q2, if_true, if_false, or_false] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun e => absurd e q1) (fun _ => ha) (fun e => absurd e q2) hh
              simp only [q1, q2, if_false, or_false] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = a ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = a ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
      · refine ⟨x, fun c => f (if c = a ∨ c = b then op d a b else c), ?_, fun c hcS => hfx _ (mem hcS), ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]; omega
        · intro c1 h1 c2 h2 h12 hh
          by_cases hab' : (c1 = a ∨ c1 = b) ∧ (c2 = a ∨ c2 = b)
          · exfalso
            have : Ht N m T e (insert a (insert b U)) a b := by
              rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
              · exact absurd rfl h12
              · exact hh
              · exact hh.symm
              · exact absurd rfl h12
            exact ht_merge hab he2 hl ha hb this
          · exact hc _ (mem h1) _ (mem h2) (phi_ne hf h1 h2 h12 hab')
              (ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun _ => hb) (fun _ => ha) (fun _ => hb) hh)
end chrom
lemma Acc.start {n T K b L : ℕ} {W : Set ℕ} {S : Finset ℕ} (h : ∀ q < L, ¬ Sol Z0 n (T &&& n) q (C n W)) (hS : Im n S ⊆ W)
    (hb : K ≤ b + L) : Acc n T K b (fun _ => 0) S := by
  intro U hU q hq hs
  simp only [Finset.sum_const_zero] at hq
  refine h q (by omega) (hs.mono le_rfl (C_mono (subset_trans ?_ hS)))
  exact Set.image_mono (by exact_mod_cast hU)
lemma Acc.const {m n T k k' t b : ℕ} {D : ℕ → ℕ} {S : Finset ℕ} (hn : n &&& m = n) (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n)
    (h : Acc n T k b D S) (hm : Min R m T k' t S) (hk : k' ≤ k) : (S.filter (Cst n)).card ≤ b := by
  obtain ⟨q, hq, hs⟩ := hm.const hn hT0 hT1
  by_contra hc
  exact h S subset_rfl q (by simp only [sdiff_self, Finset.bot_eq_empty, Finset.sum_empty]; omega) hs
lemma Acc.step {n T k b δ c' : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (h : Acc n T (k + 1) b D S)
    (H : ∀ U' ⊆ S', ∀ q, Sol Z0 n (T &&& n) q (C n (Im n U')) → ∃ U ⊆ S, ∃ r, Sol Z0 n (T &&& n) r (C n (Im n U)) ∧
      r + δ + ∑ w ∈ S' \ U', D' w ≤ q + 1 + ∑ w ∈ S \ U, D w)
    (he : ∃ q, q + c' ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S'))) : δ + c' ≤ b ∧ Acc n T k (b - δ) D' S' := by
  have hd : δ + c' ≤ b := by
    obtain ⟨q, hq, hs⟩ := he
    obtain ⟨U, hU, r, hr, hle⟩ := H S' subset_rfl q hs
    by_contra hc
    refine h U hU r ?_ hr
    simp only [sdiff_self, Finset.bot_eq_empty, Finset.sum_empty] at hle
    omega
  refine ⟨hd, fun U' hU' q hq hs => ?_⟩
  obtain ⟨U, hU, r, hr, hle⟩ := H U' hU' q hs
  exact h U hU r (by omega) hr
section sums
variable {g a c : ℕ} {U0 U' : Finset ℕ} {D D' : ℕ → ℕ}
lemma sum_child (hg : g ∉ U0) : ∑ w ∈ insert g U0 \ U', D' w = (if g ∈ U' then 0 else D' g) + ∑ w ∈ U0 \ U'.erase g, D' w := by
  have e : U0 \ U'.erase g = U0 \ U' := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_erase, not_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (fun e => hg (e ▸ h1)) h⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
  rw [e]
  by_cases h : g ∈ U'
  · rw [ite_eq_left h, Finset.insert_sdiff_of_mem _ h, zero_add]
  · rw [ite_eq_right h, Finset.insert_sdiff_of_notMem _ h, Finset.sum_insert (by simp [hg])]
lemma sum_parent {V : Finset ℕ} (hV : V ⊆ U0) (hac : a ≠ c) :
    ∑ w ∈ insert a (insert c U0) \ V, D w = ∑ w ∈ U0 \ V, D w + (if a ∈ U0 then 0 else D a) + (if c ∈ U0 then 0 else D c) := by
  have e : insert a (insert c U0) \ V = (insert a (insert c U0)) \ V := rfl
  by_cases ha : a ∈ U0 <;> by_cases hc : c ∈ U0
  · rw [Finset.insert_eq_of_mem (by simp [ha]), Finset.insert_eq_of_mem hc]; simp [ha, hc]
  · rw [Finset.insert_eq_of_mem (by simp [ha]), Finset.insert_sdiff_of_notMem _ (fun h => hc (hV h)), Finset.sum_insert (by simp [hc])]
    simp [ha, hc]; omega
  · rw [Finset.insert_eq_of_mem hc, Finset.insert_sdiff_of_notMem _ (fun h => ha (hV h)), Finset.sum_insert (by simp [ha])]
    simp [ha, hc]; omega
  · rw [Finset.insert_sdiff_of_notMem _ (fun h => ha (hV h)), Finset.insert_sdiff_of_notMem _ (fun h => hc (hV h)),
      Finset.sum_insert (by simp [ha, hac]), Finset.sum_insert (by simp [hc])]
    simp [ha, hc]; omega
lemma sum_mono {A B : Finset ℕ} (hAB : ∀ w ∈ A, w ∉ B → D' w = 0) (hD : ∀ w ∈ A, w ∈ B → D' w ≤ D w) : ∑ w ∈ A, D' w ≤ ∑ w ∈ B, D w := by
  calc ∑ w ∈ A, D' w = ∑ w ∈ A.filter (· ∈ B), D' w := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun w hw => ?_
        split_ifs with h
        · rfl
        · exact hAB w hw h
    _ ≤ ∑ w ∈ A.filter (· ∈ B), D w := Finset.sum_le_sum fun w hw => by simp at hw; exact hD w hw.1 hw.2
    _ ≤ ∑ w ∈ B, D w := Finset.sum_le_sum_of_subset fun w hw => by simp at hw; exact hw.2
end sums
lemma kpa_le (κ : Kd) (x : ℕ) : κ.kpa x ≤ x := by cases κ <;> simp [Kd.kpa]
lemma kpc_le (κ : Kd) (x : ℕ) : κ.kpc x ≤ x := by cases κ <;> simp [Kd.kpc]
theorem Acc.bi {m n T k k' t b : ℕ} {d : Bool} {a c : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hn : n &&& m = n) (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n)
    (h : Acc n T (k + 1) b D S) (hb : Bi R d a c S S') (hm : Min R m T (k' + 1) t S) (hl : Live R m T k' t S') (hk : k' ≤ k)
    (κ : Kd) (hκ : κ.ok n d a c) (hD : DStep κ D D' (op d a c) a c S') :
    κ.del (if a ∈ S' then 0 else D a) (if c ∈ S' then 0 else D c) + (S'.filter (Cst n)).card ≤ b ∧
      Acc n T k (b - κ.del (if a ∈ S' then 0 else D a) (if c ∈ S' then 0 else D c)) D' S' := by
  have hfr : op d a c ∉ S := fun h' => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h'))
  have hmin := hb.min hl hm.2
  obtain ⟨hac, U0, hS, hS', hal⟩ := hb
  set g := op d a c with hgdef
  have hgU : g ∉ U0 := fun h' => hfr (by rw [hS]; simp [h'])
  have hga : a ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have hgc : c ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have iffa : a ∈ S' ↔ a ∈ U0 := by rw [hS']; simp [hga]
  have iffc : c ∈ S' ↔ c ∈ U0 := by rw [hS']; simp [hgc]
  have hDa : a ∈ U0 → D' a ≤ κ.kpa (D a) := fun h' => hD.ha (iffa.2 h')
  have hDc : c ∈ U0 → D' c ≤ κ.kpc (D c) := fun h' => hD.hc (iffc.2 h')
  have hDg := hD.hg
  simp only [iffa, iffc] at hDg ⊢
  have hDo : ∀ w ∈ U0, w ≠ a → w ≠ c → D' w ≤ D w := fun w hw h1 h2 => hD.ho w (by rw [hS']; simp [hw]) (fun e => hgU (e ▸ hw)) h1 h2
  have hDle : ∀ w ∈ U0, D' w ≤ D w := by
    intro w hw
    by_cases h1 : w = a
    · subst h1; exact (hDa hw).trans (kpa_le _ _)
    by_cases h2 : w = c
    · subst h2; exact (hDc hw).trans (kpc_le _ _)
    exact hDo w hw h1 h2
  refine Acc.step h ?_ ?_
  · intro U' hU' q hs
    have hV : U'.erase g ⊆ U0 := by
      intro x hx
      rw [Finset.mem_erase] at hx
      have := hU' hx.2; rw [hS', Finset.mem_insert] at this
      exact this.resolve_left hx.1
    have hVS : U'.erase g ⊆ S := hV.trans (by rw [hS]; intro x hx; simp [hx])
    have hUi : U' ⊆ insert g (U'.erase g) := fun x hx => by by_cases e : x = g <;> simp [e, hx]
    rw [hS', sum_child (D' := D') hgU]
    by_cases hgU' : g ∈ U'
    · rw [ite_eq_left hgU', zero_add]
      cases κ with
      | N =>
        refine ⟨insert a (insert c (U'.erase g)), ?_, q + 1, ?_, ?_⟩
        · intro x hx; simp only [Finset.mem_insert] at hx
          rcases hx with rfl | rfl | hx
          · rw [hS]; simp
          · rw [hS]; simp
          · exact hVS hx
        · refine .bi (d := d) (Im_mem (x := a) (by simp)) (Im_mem (x := c) (by simp)) (al0 _ _ _)
            (hs.mono le_rfl (C_Im_sub (S := insert a (insert c (U'.erase g))) (hUi.trans (Finset.insert_subset_insert _ ?_)) ?_ (Set.subset_insert _ _)))
          · intro x hx; simp only [Finset.mem_insert]; exact Or.inr (Or.inr hx)
          · rw [hgdef, and_op]; exact Or.inl rfl
        · have : ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ S \ insert a (insert c (U'.erase g)), D w := by
            refine sum_mono (fun w hw hw2 => ?_) (fun w hw _ => hDle w (Finset.mem_sdiff.1 hw).1)
            rw [Finset.mem_sdiff] at hw
            have : w = a ∨ w = c := by
              by_contra hno; push Not at hno
              exact hw2 (Finset.mem_sdiff.2 ⟨by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; tauto⟩)
            rcases this with rfl | rfl
            · have := hDa hw.1; simpa [Kd.kpa] using this
            · have := hDc hw.1; simpa [Kd.kpc] using this
          simp only [Kd.del]; omega
      | K0 =>
        refine ⟨U'.erase g, hVS, q, hs.mono le_rfl (C_Im_sub hUi (Cst_mem hκ) subset_rfl), ?_⟩
        have h1 : ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ U0 \ U'.erase g, D w := Finset.sum_le_sum fun w hw => hDle w (Finset.mem_sdiff.1 hw).1
        rw [hS, sum_parent hV hac]; simp only [Kd.del]; omega
      | KA =>
        refine ⟨insert a (U'.erase g), ?_, q, hs.mono le_rfl (C_Im_sub (S := insert a (U'.erase g)) (hUi.trans (Finset.insert_subset_insert _ (Finset.subset_insert _ _))) ?_ subset_rfl), ?_⟩
        · intro x hx; simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · rw [hS]; simp
          · exact hVS hx
        · have e : g &&& n = a &&& n := hκ
          rw [e]; exact Im_mem (by simp)
        · have : ∑ w ∈ U0 \ U'.erase g, D' w + (if c ∈ U0 then 0 else D c) ≤ ∑ w ∈ S \ insert a (U'.erase g), D w := by
            have key : ∀ B : Finset ℕ, (∀ w ∈ U0 \ U'.erase g, w ≠ a → w ∈ B) → ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ B, D w := by
              intro B hB
              refine sum_mono (fun w hw hw2 => ?_) (fun w hw _ => hDle w (Finset.mem_sdiff.1 hw).1)
              have : w = a := by by_contra hno; exact hw2 (hB w hw hno)
              subst this
              have := hDa (Finset.mem_sdiff.1 hw).1; simpa [Kd.kpa] using this
            by_cases hc : c ∈ U0
            · rw [ite_eq_left hc, add_zero]
              refine key _ fun w hw hne => ?_
              rw [Finset.mem_sdiff] at hw ⊢
              exact ⟨by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; tauto⟩
            · rw [ite_eq_right hc]
              have hcB : c ∈ S \ insert a (U'.erase g) := by
                rw [Finset.mem_sdiff]
                refine ⟨by rw [hS]; simp, ?_⟩
                simp only [Finset.mem_insert]
                rintro (h1 | h1)
                · exact hac h1.symm
                · exact hc (hV h1)
              rw [← Finset.sum_erase_add _ _ hcB]
              refine Nat.add_le_add_right (key _ fun w hw hne => ?_) _
              rw [Finset.mem_sdiff] at hw
              rw [Finset.mem_erase, Finset.mem_sdiff]
              exact ⟨fun e => hc (e ▸ hw.1), by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; tauto⟩
          simp only [Kd.del]; omega
      | KC =>
        refine ⟨insert c (U'.erase g), ?_, q, hs.mono le_rfl (C_Im_sub (S := insert c (U'.erase g)) (hUi.trans (Finset.insert_subset_insert _ (Finset.subset_insert _ _))) ?_ subset_rfl), ?_⟩
        · intro x hx; simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · rw [hS]; simp
          · exact hVS hx
        · have e : g &&& n = c &&& n := hκ
          rw [e]; exact Im_mem (by simp)
        · have : ∑ w ∈ U0 \ U'.erase g, D' w + (if a ∈ U0 then 0 else D a) ≤ ∑ w ∈ S \ insert c (U'.erase g), D w := by
            have key : ∀ B : Finset ℕ, (∀ w ∈ U0 \ U'.erase g, w ≠ c → w ∈ B) → ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ B, D w := by
              intro B hB
              refine sum_mono (fun w hw hw2 => ?_) (fun w hw _ => hDle w (Finset.mem_sdiff.1 hw).1)
              have : w = c := by by_contra hno; exact hw2 (hB w hw hno)
              subst this
              have := hDc (Finset.mem_sdiff.1 hw).1; simpa [Kd.kpc] using this
            by_cases ha : a ∈ U0
            · rw [ite_eq_left ha, add_zero]
              refine key _ fun w hw hne => ?_
              rw [Finset.mem_sdiff] at hw ⊢
              exact ⟨by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; tauto⟩
            · rw [ite_eq_right ha]
              have haB : a ∈ S \ insert c (U'.erase g) := by
                rw [Finset.mem_sdiff]
                refine ⟨by rw [hS]; simp, ?_⟩
                simp only [Finset.mem_insert]
                rintro (h1 | h1)
                · exact hac h1
                · exact ha (hV h1)
              rw [← Finset.sum_erase_add _ _ haB]
              refine Nat.add_le_add_right (key _ fun w hw hne => ?_) _
              rw [Finset.mem_sdiff] at hw
              rw [Finset.mem_erase, Finset.mem_sdiff]
              exact ⟨fun e => ha (e ▸ hw.1), by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; tauto⟩
          simp only [Kd.del]; omega
    · rw [ite_eq_right hgU']
      have e : U'.erase g = U' := Finset.erase_eq_of_notMem hgU'
      rw [e] at hV hVS ⊢
      refine ⟨U', hVS, q, hs, ?_⟩
      have h1 : ∑ w ∈ U0 \ U', D' w ≤ ∑ w ∈ U0 \ U', D w := Finset.sum_le_sum fun w hw => hDle w (Finset.mem_sdiff.1 hw).1
      rw [hS, sum_parent hV hac]
      cases κ <;> simp only [Kd.del, Kd.out] at hDg ⊢ <;> omega
  · obtain ⟨q, hq, hs⟩ := hmin.const hn hT0 hT1
    exact ⟨q, by omega, hs⟩
theorem Acc.un {m n T k k' t b : ℕ} {a : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hn : n &&& m = n) (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n)
    (h : Acc n T (k + 1) b D S) (hb : Un m a S S') (hm : Min R m T (k' + 1) (t + 1) S) (hl : Live R m T k' t S') (hk : k' ≤ k) (κ : Bool)
    (hκ : κ = true → Cst n a) (hg : D' (a ^^^ m) ≤ (if κ then 0 else 1) + (if a ∈ S' then 0 else D a))
    (hka : a ∈ S' → D' a ≤ if κ then D a else 0) (ho : ∀ w ∈ S', w ≠ a ^^^ m → w ≠ a → D' w ≤ D w) :
    (if κ then 1 else 0) + (S'.filter (Cst n)).card ≤ b ∧ Acc n T k (b - if κ then 1 else 0) D' S' := by
  have hfr : a ^^^ m ∉ S := fun h' => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h'))
  have hmin := hb.min hl hm.2
  obtain ⟨U0, hS, hS'⟩ := hb
  set g := a ^^^ m with hgdef
  have hgU : g ∉ U0 := fun h' => hfr (by rw [hS]; simp [h'])
  have hga : a ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have iffa : a ∈ S' ↔ a ∈ U0 := by rw [hS']; simp [hga]
  simp only [iffa] at hg hka
  have hDle : ∀ w ∈ U0, D' w ≤ D w := by
    intro w hw
    by_cases h1 : w = a
    · subst h1
      have := hka hw
      split_ifs at this <;> omega
    exact ho w (by rw [hS']; simp [hw]) (fun e => hgU (e ▸ hw)) h1
  have par : ∀ V ⊆ U0, ∑ w ∈ S \ V, D w = ∑ w ∈ U0 \ V, D w + (if a ∈ U0 then 0 else D a) := by
    intro V hV
    by_cases ha : a ∈ U0
    · rw [hS, Finset.insert_eq_of_mem ha]; simp [ha]
    · rw [hS, Finset.insert_sdiff_of_notMem _ (fun h => ha (hV h)), Finset.sum_insert (by simp [ha])]; simp [ha]; omega
  refine Acc.step h ?_ ?_
  · intro U' hU' q hs
    have hV : U'.erase g ⊆ U0 := by
      intro x hx
      rw [Finset.mem_erase] at hx
      have := hU' hx.2; rw [hS', Finset.mem_insert] at this
      exact this.resolve_left hx.1
    have hVS : U'.erase g ⊆ S := hV.trans (by rw [hS]; exact Finset.subset_insert _ _)
    have hUi : U' ⊆ insert g (U'.erase g) := fun x hx => by by_cases e : x = g <;> simp [e, hx]
    rw [hS', sum_child (D' := D') hgU]
    by_cases hgU' : g ∈ U'
    · rw [ite_eq_left hgU', zero_add]
      by_cases hk1 : κ = true
      · have hc := hκ hk1
        refine ⟨U'.erase g, hVS, q, hs.mono le_rfl (C_Im_sub hUi (Cst_mem (by rw [hgdef]; exact (Cst_neg hn).2 hc)) subset_rfl), ?_⟩
        have h1 : ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ U0 \ U'.erase g, D w := Finset.sum_le_sum fun w hw => hDle w (Finset.mem_sdiff.1 hw).1
        rw [par _ hV]; simp only [hk1, ite_true]; omega
      · refine ⟨insert a (U'.erase g), ?_, q + 1, ?_, ?_⟩
        · intro x hx; simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · rw [hS]; simp
          · exact hVS hx
        · refine .un (Im_mem (x := a) (by simp)) (hs.mono le_rfl (C_Im_sub (S := insert a (U'.erase g))
            (hUi.trans (Finset.insert_subset_insert _ (Finset.subset_insert _ _))) ?_ (Set.subset_insert _ _)))
          rw [hgdef, and_neg hn]; exact Or.inl rfl
        · have : ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ S \ insert a (U'.erase g), D w := by
            refine sum_mono (fun w hw hw2 => ?_) (fun w hw _ => hDle w (Finset.mem_sdiff.1 hw).1)
            rw [Finset.mem_sdiff] at hw
            have : w = a := by
              by_contra hno
              exact hw2 (Finset.mem_sdiff.2 ⟨by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; tauto⟩)
            subst this
            have := hka hw.1; simpa [hk1] using this
          rw [ite_eq_right hk1]; omega
    · rw [ite_eq_right hgU']
      have e : U'.erase g = U' := Finset.erase_eq_of_notMem hgU'
      rw [e] at hV hVS ⊢
      refine ⟨U', hVS, q, hs, ?_⟩
      have h1 : ∑ w ∈ U0 \ U', D' w ≤ ∑ w ∈ U0 \ U', D w := Finset.sum_le_sum fun w hw => hDle w (Finset.mem_sdiff.1 hw).1
      rw [par _ hV]
      split_ifs at hg ⊢ <;> omega
  · obtain ⟨q, hq, hs⟩ := hmin.const hn hT0 hT1
    exact ⟨q, by omega, hs⟩
lemma Kd.out_le (κ : Kd) (la lc : ℕ) : κ.out la lc ≤ 1 + la + lc := by cases κ <;> simp [Kd.out] <;> omega
lemma DStep.le {κ : Kd} {D D' : ℕ → ℕ} {g a c : ℕ} {S' : Finset ℕ} (h : DStep κ D D' g a c S') : ∀ w ∈ S', w ≠ g → D' w ≤ D w := by
  intro w hw hg
  by_cases h1 : w = a
  · subst h1; exact (h.ha hw).trans (kpa_le _ _)
  by_cases h2 : w = c
  · subst h2; exact (h.hc hw).trans (kpc_le _ _)
  exact h.ho w hw hg h1 h2
lemma DStep.sum_le {κ : Kd} {d : Bool} {a c : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hb : Bi R d a c S S') (hfr : op d a c ∉ S)
    (h : DStep κ D D' (op d a c) a c S') : ∑ w ∈ S', D' w ≤ 1 + ∑ w ∈ S, D w := by
  obtain ⟨hac, U0, hS, hS', hal⟩ := hb
  set g := op d a c with hgdef
  have hgU : g ∉ U0 := fun h' => hfr (by rw [hS]; simp [h'])
  have hga : a ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have hgc : c ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have iffa : a ∈ S' ↔ a ∈ U0 := by rw [hS']; simp [hga]
  have iffc : c ∈ S' ↔ c ∈ U0 := by rw [hS']; simp [hgc]
  have h1 := h.hg.trans (Kd.out_le _ _ _)
  simp only [iffa, iffc] at h1
  have h2 : ∑ w ∈ U0, D' w ≤ ∑ w ∈ U0, D w := Finset.sum_le_sum fun w hw => h.le w (by rw [hS']; simp [hw]) (fun e => hgU (e ▸ hw))
  have h3 := sum_parent (D := D) (U0 := U0) (V := ∅) (by simp) hac
  simp only [Finset.sdiff_empty] at h3
  rw [hS', Finset.sum_insert hgU, hS, h3]
  omega
lemma un_sum_le {m a e : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hb : Un m a S S') (hfr : a ^^^ m ∉ S) (he : e ≤ 1)
    (hg : D' (a ^^^ m) ≤ e + (if a ∈ S' then 0 else D a)) (ho : ∀ w ∈ S', w ≠ a ^^^ m → D' w ≤ D w) : ∑ w ∈ S', D' w ≤ 1 + ∑ w ∈ S, D w := by
  obtain ⟨U0, hS, hS'⟩ := hb
  set g := a ^^^ m with hgdef
  have hgU : g ∉ U0 := fun h' => hfr (by rw [hS]; simp [h'])
  have hga : a ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have iffa : a ∈ S' ↔ a ∈ U0 := by rw [hS']; simp [hga]
  simp only [iffa] at hg
  have h2 : ∑ w ∈ U0, D' w ≤ ∑ w ∈ U0, D w := Finset.sum_le_sum fun w hw => ho w (by rw [hS']; simp [hw]) (fun e => hgU (e ▸ hw))
  have h3 : ∑ w ∈ S, D w = ∑ w ∈ U0, D w + (if a ∈ U0 then 0 else D a) := by
    by_cases ha : a ∈ U0
    · rw [hS, Finset.insert_eq_of_mem ha]; simp [ha]
    · rw [hS, Finset.sum_insert ha]; simp [ha]; omega
  rw [hS', Finset.sum_insert hgU, h3]
  omega
noncomputable section core
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
lemma lane_succ (w n : ℕ) (f : ℕ → ℕ) : lane w (n + 1) f = 2 ^ (w * n) * f n + lane w n f := by
  rw [lane, Finset.sum_range_succ, ← lane]; ring
lemma lane_congr {w n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : lane w n f = lane w n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma lane_lt {w n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 2 ^ w) : lane w n f < 2 ^ (w * n) := by
  induction n with
  | zero => simp [lane]
  | succ n ih =>
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [lane_succ, show w * (n + 1) = w * n + w by ring, pow_add]
    have : 2 ^ (w * n) * f n ≤ 2 ^ (w * n) * (2 ^ w - 1) := Nat.mul_le_mul_left _ (by omega)
    have e : 2 ^ (w * n) * 2 ^ w = 2 ^ (w * n) * (2 ^ w - 1) + 2 ^ (w * n) := by
      have : 0 < 2 ^ w := Nat.two_pow_pos w
      conv_lhs => rw [show 2 ^ w = (2 ^ w - 1) + 1 by omega]
      ring
    omega
lemma lane_add (w n : ℕ) (f g : ℕ → ℕ) : lane w n f + lane w n g = lane w n (fun j => f j + g j) := by
  simp [lane, ← Finset.sum_add_distrib, add_mul]
lemma lane_mul (w n q : ℕ) (f : ℕ → ℕ) : q * lane w n f = lane w n (fun j => q * f j) := by
  rw [lane, lane, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
lemma lane_and {w n : ℕ} {f g : ℕ → ℕ} (hf : ∀ j < n, f j < 2 ^ w) (hg : ∀ j < n, g j < 2 ^ w) :
    lane w n f &&& lane w n g = lane w n (fun j => f j &&& g j) := by
  induction n with
  | zero => simp [lane]
  | succ n ih =>
    have i1 := ih (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega))
    have h1 : lane w n f < 2 ^ (w * n) := lane_lt fun j hj => hf j (by omega)
    have h2 : lane w n g < 2 ^ (w * n) := lane_lt fun j hj => hg j (by omega)
    have h3 : lane w n (fun j => f j &&& g j) < 2 ^ (w * n) := lane_lt fun j hj => lt_of_le_of_lt Nat.and_le_left (hf j (by omega))
    rw [lane_succ, lane_succ, lane_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2, Nat.testBit_two_pow_mul_add _ h3]
    split_ifs with hi
    · rw [← Nat.testBit_and, i1]
    · rw [Nat.testBit_and]
lemma lane_mod {w n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) (hw : 5 * n + 6 ≤ w) : lane w n f % (2 ^ w - 32) = pk n f := by
  have h64 : 64 ≤ 2 ^ w := by
    calc 64 = 2 ^ 6 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have base : 2 ^ w ≡ 32 [MOD 2 ^ w - 32] := by
    have : 2 ^ w = (2 ^ w - 32) + 32 := by omega
    conv_lhs => rw [this]
    exact Nat.add_modEq_left
  have key : ∀ n, lane w n f ≡ pk n f [MOD 2 ^ w - 32] := by
    intro n
    induction n with
    | zero => simp [lane, pk]; rfl
    | succ n ih =>
      rw [lane_succ, pk_succ]
      refine Nat.ModEq.add (Nat.ModEq.mul_right _ ?_) ih
      rw [pow_mul, pow_mul]
      exact base.pow n
  have hlt : pk n f < 2 ^ w - 32 := by
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
    have h2 : 2 ^ (5 * n) ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have := key n
  rw [Nat.ModEq, Nat.mod_eq_of_lt hlt] at this
  exact this
lemma lane_testBit {w : ℕ} {f : ℕ → ℕ} {i j : ℕ} (hi : i < w) : ∀ {n : ℕ}, (∀ j < n, f j < 2 ^ w) →
    (lane w n f).testBit (w * j + i) = (decide (j < n) && (f j).testBit i) := by
  intro n
  induction n with
  | zero => intro _; simp [lane]
  | succ n ih =>
    intro h
    have h1 : lane w n f < 2 ^ (w * n) := lane_lt fun j hj => h j (by omega)
    rw [lane_succ, Nat.testBit_two_pow_mul_add _ h1]
    rcases lt_trichotomy j n with hj | rfl | hj
    · have : w * j + i < w * n := by
        have : w * (j + 1) ≤ w * n := Nat.mul_le_mul_left _ hj
        have e : w * (j + 1) = w * j + w := by ring
        omega
      rw [ite_eq_left this, ih fun j hj => h j (by omega)]
      simp [hj, show j < n + 1 by omega]
    · rw [ite_eq_right (by omega), show w * j + i - w * j = i by omega]; simp
    · have e0 : ¬ w * j + i < w * n := by
        have : w * n ≤ w * j := Nat.mul_le_mul_left _ (by omega)
        omega
      have hlt : f n < 2 ^ w := h n (by omega)
      have : w ≤ w * j + i - w * n := by
        have : w * (n + 1) ≤ w * j := Nat.mul_le_mul_left _ hj
        have e : w * (n + 1) = w * n + w := by ring
        omega
      rw [ite_eq_right e0, Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) this))]
      simp [show ¬ j < n + 1 by omega]
lemma laneL_eq (w : ℕ) (L : List ℕ) : laneL w L = lane w L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    change (laneL w L) <<< w + d = _
    rw [ih, Nat.shiftLeft_eq, List.length_cons, lane, lane, Finset.sum_range_succ', Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [List.getD_cons_succ]; rw [mul_assoc, ← pow_add]; congr 2
    · simp
lemma laneL_rep (w n x : ℕ) : laneL w (List.replicate n x) = lane w n (fun _ => x) := by
  rw [laneL_eq, List.length_replicate]
  refine lane_congr fun j hj => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp [hj]
lemma fb_le (x j : ℕ) : fb x j ≤ 1 := by unfold fb; cases x.testBit (5 * j) <;> simp
lemma fb_pk {n x : ℕ} (h : isPk n x) : x = pk n (fb x) := pk_of h
lemma pk_bit {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) (j : ℕ) : (pk n f).testBit (5 * j) = (decide (j < n) && decide (f j = 1)) := by
  have h := lane_testBit (w := 5) (f := f) (i := 0) (j := j) (by norm_num) (n := n) fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
  rw [add_zero] at h
  change (lane 5 n f).testBit (5 * j) = _
  rw [h]
  by_cases hj : j < n
  · have := hf j hj
    simp only [hj, decide_true, Bool.true_and]
    generalize f j = x at *
    interval_cases x <;> rfl
  · simp [hj]
lemma pk_isPk {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) : isPk n (pk n f) := by
  intro i hi
  have hlt : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
  have h5 := Nat.mod_lt i (show 0 < 5 by norm_num)
  have e : 5 * (i / 5) + i % 5 = i := Nat.div_add_mod i 5
  have h := lane_testBit (w := 5) (f := f) (i := i % 5) (j := i / 5) h5 (n := n) fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
  rw [e] at h
  change (lane 5 n f).testBit i = true at hi
  rw [h, Bool.and_eq_true, decide_eq_true_eq] at hi
  refine ⟨?_, hi.1⟩
  by_contra hne
  have := hf _ hi.1
  have hx := hi.2
  generalize f (i / 5) = x at *
  interval_cases x
  · simp at hx
  · exact hne (Nat.testBit_one_eq_true_iff_self_eq_zero.1 hx)
lemma fb_of_pk {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) {j : ℕ} (hj : j < n) : fb (pk n f) j = f j := by
  unfold fb; rw [pk_bit hf]
  have := hf j hj
  simp only [hj, decide_true, Bool.true_and]
  generalize f j = x at *
  interval_cases x <;> rfl
lemma fb_one {x j : ℕ} : fb x j = 1 ↔ x.testBit (5 * j) = true := by unfold fb; cases x.testBit (5 * j) <;> simp
lemma MU_land {n : ℕ} {f d : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) (hd : ∀ j < n, d j < 32) :
    Nat.land (MU (pk n f)) (pk n d) = pk n (fun j => f j * d j) := by
  change (31 * lane 5 n f) &&& lane 5 n d = lane 5 n _
  rw [lane_mul, lane_and]
  · refine lane_congr fun j hj => ?_
    have h1 := hf j hj; have h2 := hd j hj
    generalize f j = x at *
    generalize d j = y at *
    interval_cases x
    · simp
    · rw [mul_one, one_mul]
      interval_cases y <;> rfl
  · intro j hj; have := hf j hj; omega
  · intro j hj; exact hd j hj
lemma shr4 (n : ℕ) : Nat.shiftRight (pk n (fun _ => 16)) 4 = pk n (fun _ => 1) := by
  change pk n (fun _ => 16) >>> 4 = _
  have : pk n (fun _ => 16) = 16 * pk n (fun _ => 1) := by
    change lane 5 n _ = 16 * lane 5 n _; rw [lane_mul]
  rw [this, Nat.shiftRight_eq_div_pow]; norm_num
lemma natHold_eq (x : Nat) (f : Nat → Nat) : natHold x f = f x := by cases x <;> rfl
lemma broadcast_value (N x : ℕ) : broadcastSixteen (WL N) x = x * R16 N := by
  unfold broadcastSixteen broadcastAdd
  simp only [natHold_eq]
  change ((((x + (x <<< WL N)) + ((x + (x <<< WL N)) <<< (WL N * 2))) + (((x + (x <<< WL N)) + ((x + (x <<< WL N)) <<< (WL N * 2))) <<< (WL N * 4))) + ((((x + (x <<< WL N)) + ((x + (x <<< WL N)) <<< (WL N * 2))) + (((x + (x <<< WL N)) + ((x + (x <<< WL N)) <<< (WL N * 2))) <<< (WL N * 4))) <<< (WL N * 8))) = x * ((((((((((((((((((((((((((((((((0 <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1) <<< WL N) + 1)
  simp only [Nat.shiftLeft_eq,pow_mul]
  ring

lemma smearKeep {i s x : ℕ} (h : x.testBit i = true) : (smearStep s x).testBit i = true := by
  rw [smearStep,natHold_eq,no,Nat.testBit_or,Bool.or_eq_true]
  exact Or.inl h
lemma smearMove {i s x : ℕ} (h : x.testBit (s+i) = true) : (smearStep s x).testBit i = true := by
  rw [smearStep,natHold_eq,no,Nat.testBit_or,Bool.or_eq_true]
  exact Or.inr (by simpa only [nsr,Nat.testBit_shiftRight,Nat.add_comm] using h)
lemma gatherSixteen_covers {i j s x : ℕ} (hj : j < 16)
    (h : x.testBit (i + j*s) = true) : (gatherSixteen s x).testBit i = true := by
  unfold gatherSixteen
  interval_cases j
  · apply smearKeep
    apply smearKeep
    apply smearKeep
    apply smearKeep
    rw [show i = i + 0*s by omega]
    exact h
  · apply smearKeep
    apply smearKeep
    apply smearKeep
    apply smearMove
    rw [show s+(i) = i + 1*s by omega]
    exact h
  · apply smearKeep
    apply smearKeep
    apply smearMove
    apply smearKeep
    rw [show 2*s+(i) = i + 2*s by omega]
    exact h
  · apply smearKeep
    apply smearKeep
    apply smearMove
    apply smearMove
    rw [show s+(2*s+(i)) = i + 3*s by omega]
    exact h
  · apply smearKeep
    apply smearMove
    apply smearKeep
    apply smearKeep
    rw [show 4*s+(i) = i + 4*s by omega]
    exact h
  · apply smearKeep
    apply smearMove
    apply smearKeep
    apply smearMove
    rw [show s+(4*s+(i)) = i + 5*s by omega]
    exact h
  · apply smearKeep
    apply smearMove
    apply smearMove
    apply smearKeep
    rw [show 2*s+(4*s+(i)) = i + 6*s by omega]
    exact h
  · apply smearKeep
    apply smearMove
    apply smearMove
    apply smearMove
    rw [show s+(2*s+(4*s+(i))) = i + 7*s by omega]
    exact h
  · apply smearMove
    apply smearKeep
    apply smearKeep
    apply smearKeep
    rw [show 8*s+(i) = i + 8*s by omega]
    exact h
  · apply smearMove
    apply smearKeep
    apply smearKeep
    apply smearMove
    rw [show s+(8*s+(i)) = i + 9*s by omega]
    exact h
  · apply smearMove
    apply smearKeep
    apply smearMove
    apply smearKeep
    rw [show 2*s+(8*s+(i)) = i + 10*s by omega]
    exact h
  · apply smearMove
    apply smearKeep
    apply smearMove
    apply smearMove
    rw [show s+(2*s+(8*s+(i))) = i + 11*s by omega]
    exact h
  · apply smearMove
    apply smearMove
    apply smearKeep
    apply smearKeep
    rw [show 4*s+(8*s+(i)) = i + 12*s by omega]
    exact h
  · apply smearMove
    apply smearMove
    apply smearKeep
    apply smearMove
    rw [show s+(4*s+(8*s+(i))) = i + 13*s by omega]
    exact h
  · apply smearMove
    apply smearMove
    apply smearMove
    apply smearKeep
    rw [show 2*s+(4*s+(8*s+(i))) = i + 14*s by omega]
    exact h
  · apply smearMove
    apply smearMove
    apply smearMove
    apply smearMove
    rw [show s+(2*s+(4*s+(8*s+(i)))) = i + 15*s by omega]
    exact h
lemma zflG_spec {N np q nc : ℕ} {f : ℕ → ℕ} (hf : ∀ j < 16, f j < 2 ^ (2 * N)) (hnp : np = lane (WL N) 16 f) (hw : 86 ≤ 2 * N + 1) {j : ℕ}
    (h : (zflG N np q nc).testBit (5 * j) = true) : j < 16 ∧ q &&& f j = 0 ∧ nc.testBit (5 * j) = true := by
  have hWL : WL N = 2 * N + 1 := rfl
  have hFM : FM2 N = 2 ^ (2 * N) - 1 := rfl
  have pw : 2 ^ (WL N) = 2 * 2 ^ (2 * N) := by rw [hWL, pow_succ']
  have hpos : 0 < 2 ^ (2 * N) := Nat.two_pow_pos _
  set q' := q &&& (FM2 N) with hq'
  have hq'lt : q' < 2 ^ (2 * N) := lt_of_le_of_lt Nat.and_le_right (by rw [hFM]; omega)
  have hqf : ∀ j < 16, q' &&& f j = q &&& f j := by
    intro j hj
    apply Nat.eq_of_testBit_eq; intro i
    simp only [hq', hFM, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < 2 * N
    · simp [hi]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf j hj) (Nat.pow_le_pow_right (by norm_num) (by omega)))]; simp
  let b : ℕ → ℕ := fun j => if q &&& f j = 0 then 0 else 1
  have hb : ∀ j, b j ≤ 1 := fun j => by simp only [b]; split_ifs <;> simp
  have e1 : Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np = lane (WL N) 16 (fun j => q &&& f j) := by
    change (q' * (R16 N)) &&& np = _
    rw [R16, laneL_rep, lane_mul, hnp, lane_and]
    · refine lane_congr fun j hj => ?_
      rw [mul_one, hqf j hj]
    · intro j hj; rw [mul_one, pw]; omega
    · intro j hj; have := hf j hj; rw [pw]; omega
  have e2 : Nat.land (Nat.add (Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np) (MM16 N)) (GG16 N) = lane (WL N) 16 (fun j => 2 ^ (2 * N) * b j) := by
    rw [e1]
    change (lane (WL N) 16 _ + (MM16 N)) &&& (GG16 N) = _
    have hlt : ∀ j < 16, q &&& f j < 2 ^ (2 * N) := fun j hj => lt_of_le_of_lt Nat.and_le_right (hf j hj)
    rw [MM16, GG16, laneL_rep, laneL_rep, lane_add, lane_and]
    · refine lane_congr fun j hj => ?_
      have h1 := hlt j hj
      change (_ + (2 ^ (2 * N) - 1)) &&& 2 ^ (2 * N) = 2 ^ (2 * N) * b j
      generalize hx : q &&& f j = x at *
      have hbx : b j = if x = 0 then 0 else 1 := by simp only [b, hx]
      rw [hbx]
      split_ifs with h0
      · subst h0
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_and, zero_add, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
        by_cases hi : 2 * N = i <;> simp [hi]
      · have e : x + (2 ^ (2 * N) - 1) = 2 ^ (2 * N) * 1 + (x - 1) := by omega
        rw [e]
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (show x - 1 < 2 ^ (2 * N) by omega), Nat.testBit_two_pow, mul_one, Nat.testBit_two_pow]
        by_cases hi : 2 * N = i
        · subst hi; simp
        · simp [hi]
    · intro j hj; have := hlt j hj
      change _ + (2 ^ (2 * N) - 1) < _; rw [pw]; omega
    · intro j hj
      change 2 ^ (2 * N) < _; rw [pw]; omega
  have e3 : Nat.shiftRight (Nat.land (Nat.add (Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np) (MM16 N)) (GG16 N)) (Nat.mul 2 N) = lane (WL N) 16 b := by
    rw [e2]
    change lane (WL N) 16 (fun j => 2 ^ (2 * N) * b j) >>> (2 * N) = _
    rw [← lane_mul, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ hpos]
  unfold zflG at h
  have hbcast : broadcastSixteen (WL N) (Nat.land q (FM2 N)) = Nat.mul (Nat.land q (FM2 N)) (R16 N) := broadcast_value N _
  rw [hbcast,e3,nl,Nat.testBit_and,Bool.and_eq_true] at h
  refine ⟨?_,?_,h.2⟩ <;> have hs := h.1
  all_goals
    rw [nx,Nat.testBit_xor,nl,Nat.testBit_and] at hs
    let W := WL N
    let packed := gatherSixteen (W - 5) (lane W 16 b)
    have bitInfo : U16.testBit (5*j) = true ∧ packed.testBit (5*j) = false := by
      change (Bool.xor (U16.testBit (5*j)) ((packed.testBit (5*j)) && U16.testBit (5*j))) = true at hs
      cases hu : U16.testBit (5*j) <;> cases hp : packed.testBit (5*j) <;> simp [hu,hp] at hs ⊢
    have hj : j < 16 := by
      have hh := bitInfo.1
      rw [U16,laneL_rep] at hh
      change (pk 16 (fun _ => 1)).testBit (5*j) = true at hh
      rw [pk_bit (by intro; intro; omega),Bool.and_eq_true] at hh
      exact of_decide_eq_true hh.1
  · exact hj
  · by_contra hne
    have bj : b j = 1 := by simp [b,hne]
    have hW : 5 ≤ W := by dsimp [W]; omega
    have hb' : ∀ r < 16, b r < 2^W := by
      intro r _; have hr := hb r
      have := Nat.pow_le_pow_right (show 0 < 2 by omega) hW
      omega
    have ht := lane_testBit (w:=W) (i:=0) (j:=j) (n:=16) (by omega) hb'
    have hwj : (lane W 16 b).testBit (W*j) = true := by simpa [hj,bj] using ht
    have off : 5*j + j*(W-5) = W*j := by
      rw [Nat.mul_comm j (W-5),← Nat.add_mul,show 5+(W-5)=W by omega]
    have got : packed.testBit (5*j) = true := gatherSixteen_covers hj (by rw [off]; exact hwj)
    rw [bitInfo.2] at got
    contradiction

end PEqualNP.Outside.L_meta_8399
