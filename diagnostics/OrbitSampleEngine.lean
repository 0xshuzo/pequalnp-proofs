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

def slc0_0 : List ((ℕ × ℕ) × List ℕ) := [((7,5),[]),((19,5),[]),((21,5),[]),((22,5),[]),((26,5),[]),((28,5),[])]
def slc0_6 : List ((ℕ × ℕ) × List ℕ) := [((35,5),[]),((42,5),[]),((49,5),[]),((52,5),[]),((69,5),[]),((76,5),[])]
def slc0_12 : List ((ℕ × ℕ) × List ℕ) := [((81,5),[]),((82,5),[]),((104,5),[]),((164,5),[]),((194,5),[]),((98,6),[])]
def slc0_18 : List ((ℕ × ℕ) × List ℕ) := [((100,6),[]),((152,6),[]),((168,6),[]),((176,6),[]),((200,6),[]),((208,6),[])]
def slc0_24 : List ((ℕ × ℕ) × List ℕ) := [((25,7),[]),((38,7),[]),((50,7),[]),((56,7),[]),((70,7),[]),((84,7),[])]
def slc0_30 : List ((ℕ × ℕ) × List ℕ) := [((88,7),[]),((112,7),[]),((162,7),[]),((196,7),[]),((224,8),[])]
def known0 : List (ℕ × ℕ) := slc0_0.map Prod.fst ++ (slc0_6.map Prod.fst ++ (slc0_12.map Prod.fst ++ (slc0_18.map Prod.fst ++ (slc0_24.map Prod.fst ++ (slc0_30.map Prod.fst ++ (([] : List (ℕ × ℕ))))))))
def slc1_0 : List ((ℕ × ℕ) × List ℕ) := [((129,6),[]),((513,6),[]),((516,6),[]),((544,6),[]),((1025,6),[]),((1026,6),[])]
def slc1_6 : List ((ℕ × ℕ) × List ℕ) := [((1088,6),[]),((2049,6),[]),((2064,6),[]),((2176,6),[]),((4098,6),[]),((4100,6),[])]
def slc1_12 : List ((ℕ × ℕ) × List ℕ) := [((4128,6),[]),((4160,6),[]),((4224,6),[]),((8196,6),[]),((8200,6),[]),((8208,6),[])]
def slc1_18 : List ((ℕ × ℕ) × List ℕ) := [((16386,6),[]),((16392,6),[]),((16400,6),[]),((3,7),[7,19,35]),((5,7),[7,21,69]),((9,7),[25])]
def slc1_24 : List ((ℕ × ℕ) × List ℕ) := [((10,7),[26,42]),((12,7),[28,76]),((33,7),[35,49]),((65,7),[69,81]),((130,7),[162,194]),((132,7),[196,164])]
def slc1_30 : List ((ℕ × ℕ) × List ℕ) := [((8256,7),[]),((16416,7),[]),((32776,7),[]),((32784,7),[]),((32800,7),[]),((32832,7),[])]
def slc1_36 : List ((ℕ × ℕ) × List ℕ) := [((6,8),[38,70,7,22]),((17,8),[25,19,21,49,81]),((18,8),[50,19,22,26,82]),((20,8),[84,21,22,28,52]),((36,8),[38,100,52,164]),((40,8),[56,168,42,104])]
def slc1_42 : List ((ℕ × ℕ) × List ℕ) := [((66,8),[70,98,82,194]),((72,8),[88,200,76,104]),((136,8),[152,168,200]),((144,8),[152,176,208]),((4097,8),[]),((4104,8),[])]
def slc1_48 : List ((ℕ × ℕ) × List ℕ) := [((8194,8),[]),((8320,8),[]),((16388,8),[]),((16512,8),[]),((24,9),[25,56,88,152,26,28]),((34,9),[38,50,162,98,35,42])]
def slc1_54 : List ((ℕ × ℕ) × List ℕ) := [((48,9),[50,56,112,176,49,52]),((68,9),[70,84,196,100,69,76]),((80,9),[84,88,112,208,81,82]),((96,9),[224,112,98,100,104]),((160,9),[224,162,168,176,164]),((192,9),[224,196,200,208,194])]
def known1 : List (ℕ × ℕ) := slc1_0.map Prod.fst ++ (slc1_6.map Prod.fst ++ (slc1_12.map Prod.fst ++ (slc1_18.map Prod.fst ++ (slc1_24.map Prod.fst ++ (slc1_30.map Prod.fst ++ (slc1_36.map Prod.fst ++ (slc1_42.map Prod.fst ++ (slc1_48.map Prod.fst ++ (slc1_54.map Prod.fst ++ (known0))))))))))
def slc2_0 : List ((ℕ × ℕ) × List ℕ) := [((512,7),[513,516,544]),((1024,7),[1025,1026,1088]),((2048,7),[2049,2064,2176]),((32768,8),[32776,32784,32800,32832]),((4096,9),[4097,4104,4098,4100,4128,4160,4224]),((8192,9),[8194,8320,8256,8196,8200,8208])]
def slc2_6 : List ((ℕ × ℕ) × List ℕ) := [((16384,9),[16388,16512,16416,16386,16392,16400]),((1,10),[17,4097,3,5,9,33,65,25,129,513,1025,2049,7,19,21,35,49,69,81]),((2,11),[34,6,18,66,8194,3,10,130,38,50,70,162,1026,4098,16386,98,7,19,22,26,35,42,82,194]),((4,11),[68,6,20,36,16388,5,12,132,38,70,84,196,516,4100,8196,100,7,21,22,28,52,69,76,164]),((8,11),[24,40,72,136,4104,9,10,12,32776,25,56,88,8200,16392,152,168,200,26,28,42,76,104]),((128,11),[160,192,136,144,8320,16512,224,130,132,162,196,129,2176,4224,152,168,176,200,208,164,194])]
def slc2_12 : List ((ℕ × ℕ) × List ℕ) := [((16,12),[24,48,80,17,18,20,144,32784,25,50,56,84,88,112,2064,8208,16400,152,176,208,19,21,22,26]),((32,12),[34,48,96,160,36,40,224,33,16416,32800,38,50,56,112,162,544,4128,98,100,168,176,35,42,49]),((64,12),[68,80,96,192,66,72,224,65,8256,32832,70,84,88,112,196,1088,4160,98,100,200,208,69,76,81])]
def known2 : List (ℕ × ℕ) := slc2_0.map Prod.fst ++ (slc2_6.map Prod.fst ++ (slc2_12.map Prod.fst ++ (known1)))
def andPin0 : List ((ℕ × ℕ) × List ℕ) := [((65552,10),[19,21,22,26,49,81,82,25,50,17,18]),((65600,10),[69,81,82,194,98,70,65,66]),((65540,10),[7,21,22,69,38,70,5,6])]
def andPin10 : List ((ℕ × ℕ) × List ℕ) := [((196672,10),[69,76,81,104,200,88,65,72]),((196640,10),[35,42,49,104,168,56,33,40]),((196612,9),[7,21,28,69,76,5,12]),((196610,9),[7,19,26,35,42,3,10])]
def andPin20 : List ((ℕ × ℕ) × List ℕ) := []
def andPin30 : List ((ℕ × ℕ) × List ℕ) := [((458768,10),[19,21,49,81,152,176,208,25,17,144]),((458756,10),[7,21,69,164,196,5,132]),((458754,10),[7,19,35,194,162,3,130])]
def andPin40 : List ((ℕ × ℕ) × List ℕ) := [((458760,10),[152,168,200,25,9,136]),((524304,10),[19,21,22,26,28,52,82,50,84,18,20]),((524296,9),[26,28,42,76,10,12]),((524416,10),[164,194,162,196,130,132]),((589888,10),[76,82,104,194,98,200,70,88,66,72])]
def andPin50 : List ((ℕ × ℕ) × List ℕ) := [((589828,10),[7,22,28,76,38,70,12,6]),((589825,10),[7,19,35,25,3,9])]
def andPin60 : List ((ℕ × ℕ) × List ℕ) := []
def andPin70 : List ((ℕ × ℕ) × List ℕ) := [((851984,10),[19,22,26,82,152,176,208,50,18,144]),((851972,10),[7,22,164,38,70,196,132,6]),((851969,9),[7,19,35,129,3])]
def andPin80 : List ((ℕ × ℕ) × List ℕ) := []
def andPin90 : List ((ℕ × ℕ) × List ℕ) := []
def andPin100 : List ((ℕ × ℕ) × List ℕ) := []
def andPin110 : List ((ℕ × ℕ) × List ℕ) := []
def andPin120 : List ((ℕ × ℕ) × List ℕ) := [((1441796,10),[28,76,164,196,12,132])]
def andPin130 : List ((ℕ × ℕ) × List ℕ) := []
def andPin140 : List ((ℕ × ℕ) × List ℕ) := []
def andPin150 : List ((ℕ × ℕ) × List ℕ) := []
def andPin160 : List ((ℕ × ℕ) × List ℕ) := []
def andPinKnown : List (ℕ × ℕ) := andPin0.map Prod.fst ++ (andPin10.map Prod.fst ++ (andPin20.map Prod.fst ++ (andPin30.map Prod.fst ++ (andPin40.map Prod.fst ++ (andPin50.map Prod.fst ++ (andPin60.map Prod.fst ++ (andPin70.map Prod.fst ++ (andPin80.map Prod.fst ++ (andPin90.map Prod.fst ++ (andPin100.map Prod.fst ++ (andPin110.map Prod.fst ++ (andPin120.map Prod.fst ++ (andPin130.map Prod.fst ++ (andPin140.map Prod.fst ++ (andPin150.map Prod.fst ++ (andPin160.map Prod.fst ++ (known2)))))))))))))))))
def andRel0 : List ((ℕ × ℕ) × List ℕ) := [((65536,13),[7,19,21,22,26,35,42,49,69,81,82,194,98,25,38,50,70,162,129,513,1025,1026,2049,4098,16386,3,5,9,10,33,65,130,6,17,18,66,4097,8194,34,1,2,65552,65600,65540]),((196608,13),[7,19,21,26,28,35,42,49,69,76,81,104,152,168,200,25,56,88,129,513,1025,2049,8200,16392,3,5,9,10,12,33,65,32776,17,40,72,136,4097,4104,24,1,8,196672,196640,196612,196610]),((262144,13),[16]),((327680,13),[32]),((458752,13),[7,19,21,35,49,69,81,164,194,152,168,176,200,208,25,162,196,224,129,513,1025,2049,2176,4224,3,5,9,33,65,130,132,17,136,144,4097,8320,16512,160,192,1,128,458768,458756,458754,458760]),((524288,13),[7,19,21,22,26,28,35,42,52,69,76,82,164,194,98,100,38,50,70,84,162,196,516,1026,4098,4100,8196,16386,3,5,10,12,130,132,6,18,20,36,66,8194,16388,34,68,2,4,524304,524296,524416]),((589824,13),[7,19,22,26,28,35,42,76,82,104,194,98,152,168,200,25,38,50,56,70,88,162,1026,4098,8200,16386,16392,3,9,10,12,130,32776,6,18,40,66,72,136,4104,8194,24,34,2,8,589888,589828,589825]),((655360,13),[16])]
def andRel10 : List ((ℕ × ℕ) × List ℕ) := [((720896,13),[32]),((786432,13),[64]),((851968,13),[7,19,22,26,35,42,82,164,194,98,152,168,176,200,208,38,50,70,162,196,224,129,1026,2176,4098,4224,16386,3,10,130,132,6,18,66,136,144,8194,8320,16512,34,160,192,2,128,851984,851972,851969]),((1245184,13),[16]),((1310720,13),[32])]
def andRel20 : List ((ℕ × ℕ) × List ℕ) := [((1441792,13),[26,28,42,76,104,164,194,152,168,176,200,208,25,56,88,162,196,224,129,2176,4224,8200,16392,9,10,12,130,132,32776,40,72,136,144,4104,8320,16512,24,160,192,8,128,1441796]),((1507328,13),[16]),((1638400,13),[16]),((1703936,13),[32]),((1769472,13),[32])]
def andRelKnown : List (ℕ × ℕ) := andRel0.map Prod.fst ++ (andRel10.map Prod.fst ++ (andRel20.map Prod.fst ++ (andPinKnown)))
def pieces : List (List ℕ) := [[0], [1], List.range' 2 12]
def andInputs : List ((ℕ × ℕ) × ℕ) := [((0,1),65536),((0,3),196608),((0,4),262144),((0,5),327680),((0,7),458752),((1,2),524288),((1,3),589824),((1,4),655360),((1,5),720896),((1,6),786432),((1,7),851968),((3,4),1245184),((3,5),1310720),((3,7),1441792),((4,5),1507328),((4,7),1638400),((5,6),1703936),((5,7),1769472)]
def andGate (u : (ℕ × ℕ) × ℕ) : Bool × ℕ × ℕ := (false,u.1.1,u.1.2)
def andQ (u : (ℕ × ℕ) × ℕ) := tabE (andGate u) [] (pick andRelKnown [u.2])
noncomputable def andTest (u : (ℕ × ℕ) × ℕ) : Bool :=
  decide (u.1.1 < 8) && (decide (u.1.2 < 8) && (pOk 0 (andQ u) &&
  (fbOk [andGate u] [] (1,0) && (!chkT topC [andGate u] (andQ u) (1,0) 0 13 [0] FF 1 &&
  (!chkT topC [andGate u] (andQ u) (1,0) 0 13 [1] FF 1 &&
  !chkT topC [andGate u] (andQ u) (1,0) 0 13 (List.range' 2 12) FF 1)))))
def andIndex (a b : ℕ) := (a*(15-a)/2+(b-a)) * 65536
def pi1 : List ℕ := [1,0,2,4,3,6,5,8,7,10,9,12,11,14,13,16,15,18,17,19,21,20,22,23,24,25,27,26,29,28,31,30,33,32,35,34,36,38,37,40,39,41,43,42,45,44,47,46,49,48,51,50,52,54,53,56,55,57,59,58,60,61,63,62,78,79,80,83,84,81,82,85,86,87,88,90,89,77,64,65,66,69,70,67,68,71,72,73,74,76,75,91,92,94,93,97,98,95,96,99,100,101,102,104,103,105,106,107,108,111,112,109,110,113,114,115,116,118,117,119,122,121,120,123,125,124,126,127,128,129,132,133,130,131,134,135,136,137,139,138,140,143,142,141,144,146,145,147,148,149,150,153,154,151,152,155,156,157,158,160,159,161,165,166,164,162,163,167,218,219,222,223,224,220,221,225,226,227,228,230,229,181,232,183,215,216,186,234,188,236,237,191,241,242,194,239,196,244,198,246,247,201,251,252,204,249,206,254,208,256,257,211,259,260,214,184,185,217,168,169,173,174,170,171,172,175,176,177,178,180,179,231,182,233,187,235,189,190,238,195,240,192,193,243,197,245,199,200,248,205,250,202,203,253,207,255,209,210,258,212,213,261,267,268,264,270,266,262,263,269,265,271,272,273,274,278,279,277,275,276,280,281,282,283,287,288,286,284,285,289,290,291,292,296,297,295,293,294,298,300,299,301,302,303,306,307,304,305,308,309,310,311,312,314,313,315,316,317,321,322,320,318,319,323,324,325,326,329,328,327,330,332,331,333,334,335,338,337,336,339,374,377,378,379,375,376,380,381,382,383,384,386,385,353,388,389,356,394,358,391,392,361,396,363,398,365,400,401,368,406,370,403,404,373,340,344,345,341,342,343,346,347,348,349,350,352,351,387,354,355,390,359,360,393,357,395,362,397,364,399,366,367,402,371,372,405,369,407,408,409,410,411,412,413,414,415,417,416,418,419,420,421,423,422,424,426,425,427,429,428,430,431,432,437,438,439,436,433,434,435,440,441,442,443,444,451,452,453,454,455,450,445,446,447,448,449,456,457,458,459,465,466,467,468,464,460,461,462,463,469,528,529,472,532,531,533,534,535,478,537,538,539,540,483,542,543,544,545,488,548,547,549,550,551,552,554,555,556,557,553,558,559,561,562,560,505,564,565,566,567,510,570,569,571,572,573,574,576,577,578,579,575,580,581,583,584,582,527,470,471,530,474,473,475,476,477,536,479,480,481,482,541,484,485,486,487,546,490,489,491,492,493,494,499,495,496,497,498,500,501,504,502,503,563,506,507,508,509,568,512,511,513,514,515,516,521,517,518,519,520,522,523,526,524,525,585,587,586,588,589,591,590,592,593,594,595,597,596,599,598,600,601,602,604,603,605,606,608,607,609,610,611,612,614,613,615,617,616,618,619,621,620,622,623,625,624,626,627,628,629,631,630,632,634,633,635,636,638,637,639,640,641,643,642,644,646,645,647,648,649,650,652,651,654,653,655,656,657,660,661,658,659,662,669,670,671,673,672,668,663,664,665,667,666,674,675,676,678,677,679,698,697,699,700,701,702,704,703,705,706,707,708,711,712,709,710,696,681,680,682,683,684,685,687,686,688,689,690,691,694,695,692,693,713,715,714,716,718,717,720,719,722,721,724,723,726,725,728,727,730,729,732,731,733,735,734,736,737,738,739,741,740,743,742,745,744,747,746,749,748,750,752,751,754,753,755,757,756,759,758,761,760,763,762,765,764,766,768,767,770,769,771,773,772,774,775,777,776,792,793,794,797,798,795,796,799,800,801,802,804,803,791,778,779,780,783,784,781,782,785,786,787,788,790,789,805,806,808,807,811,812,809,810,813,814,815,816,818,817,819,820,821,822,825,826,823,824,827,828,829,830,832,831,833,836,835,834,837,839,838,840,841,842,843,846,847,844,845,848,849,850,851,853,852,854,857,856,855,858,860,859,861,862,863,864,867,868,865,866,869,870,871,872,874,873,875,879,880,878,876,877,881,932,933,936,937,938,934,935,939,940,941,942,944,943,895,946,897,929,930,900,948,902,950,951,905,955,956,908,953,910,958,912,960,961,915,965,966,918,963,920,968,922,970,971,925,973,974,928,898,899,931,882,883,887,888,884,885,886,889,890,891,892,894,893,945,896,947,901,949,903,904,952,909,954,906,907,957,911,959,913,914,962,919,964,916,917,967,921,969,923,924,972,926,927,975,981,982,978,984,980,976,977,983,979,985,986,987,988,992,993,991,989,990,994,995,996,997,1001,1002,1000,998,999,1003,1004,1005,1006,1010,1011,1009,1007,1008,1012,1014,1013,1015,1016,1017,1020,1021,1018,1019,1022,1023,1024,1025,1026,1028,1027,1029,1030,1031,1035,1036,1034,1032,1033,1037,1038,1039,1040,1043,1042,1041,1044,1046,1045,1047,1048,1049,1052,1051,1050,1053,1088,1091,1092,1093,1089,1090,1094,1095,1096,1097,1098,1100,1099,1067,1102,1103,1070,1108,1072,1105,1106,1075,1110,1077,1112,1079,1114,1115,1082,1120,1084,1117,1118,1087,1054,1058,1059,1055,1056,1057,1060,1061,1062,1063,1064,1066,1065,1101,1068,1069,1104,1073,1074,1107,1071,1109,1076,1111,1078,1113,1080,1081,1116,1085,1086,1119,1083,1121,1122,1123,1124,1125,1126,1127,1128,1129,1131,1130,1132,1133,1134,1135,1137,1136,1138,1140,1139,1141,1143,1142,1144,1145,1146,1151,1152,1153,1150,1147,1148,1149,1154,1155,1156,1157,1158,1165,1166,1167,1168,1169,1164,1159,1160,1161,1162,1163,1170,1171,1172,1173,1179,1180,1181,1182,1178,1174,1175,1176,1177,1183,1242,1243,1186,1246,1245,1247,1248,1249,1192,1251,1252,1253,1254,1197,1256,1257,1258,1259,1202,1262,1261,1263,1264,1265,1266,1268,1269,1270,1271,1267,1272,1273,1275,1276,1274,1219,1278,1279,1280,1281,1224,1284,1283,1285,1286,1287,1288,1290,1291,1292,1293,1289,1294,1295,1297,1298,1296,1241,1184,1185,1244,1188,1187,1189,1190,1191,1250,1193,1194,1195,1196,1255,1198,1199,1200,1201,1260,1204,1203,1205,1206,1207,1208,1213,1209,1210,1211,1212,1214,1215,1218,1216,1217,1277,1220,1221,1222,1223,1282,1226,1225,1227,1228,1229,1230,1235,1231,1232,1233,1234,1236,1237,1240,1238,1239,1299,1301,1300,1302,1303,1305,1304,1306,1307,1308,1309,1311,1310,1313,1312,1314,1315,1316,1318,1317,1319,1320,1322,1321,1323,1324,1325,1326,1328,1327,1329,1331,1330,1332,1333,1335,1334,1336,1337,1339,1338,1340,1341,1342,1343,1345,1344,1346,1348,1347,1349,1350,1352,1351,1353,1354,1355,1357,1356,1358,1360,1359,1361,1362,1363,1364,1366,1365,1368,1367,1369,1370,1371,1374,1375,1372,1373,1376,1383,1384,1385,1387,1386,1382,1377,1378,1379,1381,1380,1388,1389,1390,1392,1391,1393,1412,1411,1413,1414,1415,1416,1418,1417,1419,1420,1421,1422,1425,1426,1423,1424,1410,1395,1394,1396,1397,1398,1399,1401,1400,1402,1403,1404,1405,1408,1409,1406,1407,1427]
def gvA (v : ℕ) : ℕ := ([0,2,1,3,4,6,5,7] : List ℕ).getD v 0
def gimg (g : ℕ → ℕ) (e : Bool × ℕ × ℕ) : Bool × ℕ × ℕ := (e.1, g e.2.1, g e.2.2)
def swp (e : Bool × ℕ × ℕ) : Bool × ℕ × ℕ := (e.1, e.2.2, e.2.1)
def orbit8 (e : Bool × ℕ × ℕ) : List (Bool × ℕ × ℕ) := [e,gimg gvA e,swp e,swp (gimg gvA e)]
def gtypes : List (Bool × ℕ × ℕ) := [(false,0,4),(false,0,5),(false,1,4),(false,1,5),(false,1,6),(false,3,4),(false,3,5),(false,4,5),(false,4,7),(false,5,6),(false,5,7),(false,1,3),(false,1,7),(false,0,7),(false,3,7),(false,0,1),(false,0,3),(false,1,2),(true,4,5),(true,5,7),(true,0,4),(true,0,5),(true,1,2),(true,1,4),(true,1,5),(true,1,6),(true,3,4),(true,3,5),(true,3,7),(true,4,7),(true,5,6),(true,0,1),(true,0,3),(true,0,7),(true,1,3),(true,1,7)]
def FbOf (i : ℕ) : List (Bool × ℕ × ℕ) := (gtypes.take i).flatMap orbit8
def allGates : List (Bool × ℕ × ℕ) :=
  (List.range 8).flatMap fun a => (List.range 8).flatMap fun b => if a < b then [(false, a, b), (true, a, b)] else []
noncomputable def stageQ (e : Bool × ℕ × ℕ) (cs : List ℕ) :=
  tabE e [] (pick known2 cs)
def ORStage18Restr : List ((ℕ × ℕ) × List ℕ) := [((1,10),[17,4097,3,5,9,33,65,25,129,513,1025,2049,7,19,21,35,49,69,81]),((2,11),[34,6,18,66,8194,3,10,130,38,50,70,162,1026,4098,16386,98,7,19,22,26,35,42,82,194]),((6,8),[38,70,7,22]),((8,11),[24,40,72,136,4104,9,10,12,32776,25,56,88,8200,16392,152,168,200,26,28,42,76,104]),((66,8),[70,98,82,194]),((68,9),[70,84,196,100,69,76]),((72,8),[88,200,76,104]),((128,11),[160,192,136,144,8320,16512,224,130,132,162,196,129,2176,4224,152,168,176,200,208,164,194]),((192,9),[224,196,200,208,194]),((16384,9),[16388,16512,16416,16386,16392,16400])]
def ORStage18Q := tabE (true,4,5) (ORStage18Restr.map (fun r => r.1.1) ++ []) (pick known2 [16,32,2,8,64,128,1,4,24,34,48,68,80,96,160,192,224,4096,8192,16384,6,17,18,20,36,40,66,72])
def ORStage19Restr : List ((ℕ × ℕ) × List ℕ) := [((1,10),[17,4097,3,5,9,33,65,25,129,513,1025,2049,7,19,21,35,49,69,81]),((2,11),[34,6,18,66,8194,3,10,130,38,50,70,162,1026,4098,16386,98,7,19,22,26,35,42,82,194]),((6,8),[38,70,7,22]),((18,8),[50,19,22,26,82]),((24,9),[25,56,88,152,26,28]),((66,8),[70,98,82,194]),((68,9),[70,84,196,100,69,76]),((80,9),[84,88,112,208,81,82]),((4096,9),[4097,4104,4098,4100,4128,4160,4224]),((16384,9),[16388,16512,16416,16386,16392,16400])]
def ORStage19Q := tabE (true,5,7) (ORStage19Restr.map (fun r => r.1.1) ++ []) (pick known2 [32,2,16,64,128,1,4,8,24,34,48,68,80,96,160,192,224,4096,8192,16384,6,18,36,40,66,136,144,8194])
def ORStage20Restr : List ((ℕ × ℕ) × List ℕ) := [((8,11),[24,40,72,136,4104,9,10,12,32776,25,56,88,8200,16392,152,168,200,26,28,42,76,104]),((40,8),[56,168,42,104]),((72,8),[88,200,76,104]),((136,8),[152,168,200])]
def ORStage20Q := tabE (true,0,4) (ORStage20Restr.map (fun r => r.1.1) ++ []) (pick known2 [16,8,32,64,1,2,4,128,24,48,80,4096,17,18,20,34,40,68,72,96,136,144,160,192,4097,4104,25,50])
def ORStage21Restr : List ((ℕ × ℕ) × List ℕ) := [((2,11),[34,6,18,66,8194,3,10,130,38,50,70,162,1026,4098,16386,98,7,19,22,26,35,42,82,194]),((6,8),[38,70,7,22]),((18,8),[50,19,22,26,82]),((66,8),[70,98,82,194]),((68,9),[70,84,196,100,69,76]),((4096,9),[4097,4104,4098,4100,4128,4160,4224])]
def ORStage21Q := tabE (true,0,5) (ORStage21Restr.map (fun r => r.1.1) ++ []) (pick known2 [32,2,16,64,1,4,8,128,34,48,68,96,160,224,4096,8192,6,17,18,24,36,40,66,80,192,4097,8194,8320])
def ORStage22Restr : List ((ℕ × ℕ) × List ℕ) := [((1,10),[17,4097,3,5,9,33,65,25,129,513,1025,2049,7,19,21,35,49,69,81]),((17,8),[25,19,21,49,81]),((4096,9),[4097,4104,4098,4100,4128,4160,4224]),((4097,8),[]),((4104,8),[]),((8192,9),[8194,8320,8256,8196,8200,8208]),((16384,9),[16388,16512,16416,16386,16392,16400])]
def ORStage22Q := tabE (true,1,2) (ORStage22Restr.map (fun r => r.1.1) ++ []) (pick known2 [2,4,16,32,64,1,8,128,34,68,4096,8192,16384,6,17,18,20,24,36,48,66,80,96,160,192,4097,4104,8194])
def ORStage23Restr : List ((ℕ × ℕ) × List ℕ) := [((1,10),[17,4097,3,5,9,33,65,25,129,513,1025,2049,7,19,21,35,49,69,81]),((8192,9),[8194,8320,8256,8196,8200,8208])]
def ORStage23Q := tabE (true,1,4) (ORStage23Restr.map (fun r => r.1.1) ++ []) (pick known2 [16,2,32,64,1,4,8,128,24,34,48,80,4096,8192,6,17,18,20,66,68,96,144,160,192,4097,4104,8194,25])
def ORStage24Restr : List ((ℕ × ℕ) × List ℕ) := [((1,10),[17,4097,3,5,9,33,65,25,129,513,1025,2049,7,19,21,35,49,69,81]),((17,8),[25,19,21,49,81]),((20,8),[84,21,22,28,52]),((24,9),[25,56,88,152,26,28]),((68,9),[70,84,196,100,69,76]),((72,8),[88,200,76,104]),((80,9),[84,88,112,208,81,82]),((192,9),[224,196,200,208,194]),((4096,9),[4097,4104,4098,4100,4128,4160,4224]),((16384,9),[16388,16512,16416,16386,16392,16400])]
def ORStage24Q := tabE (true,1,5) (ORStage24Restr.map (fun r => r.1.1) ++ []) (pick known2 [32,2,16,64,1,4,8,128,24,34,48,68,80,96,160,192,224,4096,8192,16384,6,17,18,20,36,40,66,72])
def ORStage25Restr : List ((ℕ × ℕ) × List ℕ) := [((4,11),[68,6,20,36,16388,5,12,132,38,70,84,196,516,4100,8196,100,7,21,22,28,52,69,76,164]),((20,8),[84,21,22,28,52]),((36,8),[38,100,52,164]),((8192,9),[8194,8320,8256,8196,8200,8208])]
def ORStage25Q := tabE (true,1,6) (ORStage25Restr.map (fun r => r.1.1) ++ []) (pick known2 [64,2,4,16,32,8,128,34,68,80,96,192,224,1,8192,16384,6,18,20,24,36,48,66,72,160,8194,16388,16512])
def ORStage26Restr : List ((ℕ × ℕ) × List ℕ) := [((1,10),[17,4097,3,5,9,33,65,25,129,513,1025,2049,7,19,21,35,49,69,81])]
def ORStage26Q := tabE (true,3,4) (ORStage26Restr.map (fun r => r.1.1) ++ []) (pick known2 [16,8,32,64,1,2,4,128,24,48,80,4096,17,18,20,34,40,68,72,96,136,144,160,192,4097,4104,25,50])
def ORStage27Restr : List ((ℕ × ℕ) × List ℕ) := [((68,9),[70,84,196,100,69,76]),((128,11),[160,192,136,144,8320,16512,224,130,132,162,196,129,2176,4224,152,168,176,200,208,164,194]),((144,8),[152,176,208]),((192,9),[224,196,200,208,194]),((4096,9),[4097,4104,4098,4100,4128,4160,4224]),((16384,9),[16388,16512,16416,16386,16392,16400])]
def ORStage27Q := tabE (true,3,5) (ORStage27Restr.map (fun r => r.1.1) ++ []) (pick known2 [32,8,16,64,128,2,4,24,34,48,68,96,160,192,224,1,4096,8192,16384,36,40,72,80,136,144,4104,8194,8320])
def ORStage28Restr : List ((ℕ × ℕ) × List ℕ) := [((1,10),[17,4097,3,5,9,33,65,25,129,513,1025,2049,7,19,21,35,49,69,81]),((17,8),[25,19,21,49,81]),((34,9),[38,50,162,98,35,42]),((48,9),[50,56,112,176,49,52]),((68,9),[70,84,196,100,69,76]),((80,9),[84,88,112,208,81,82]),((96,9),[224,112,98,100,104]),((4096,9),[4097,4104,4098,4100,4128,4160,4224]),((8192,9),[8194,8320,8256,8196,8200,8208]),((16384,9),[16388,16512,16416,16386,16392,16400])]
def ORStage28Q := tabE (true,3,7) (ORStage28Restr.map (fun r => r.1.1) ++ []) (pick known2 [8,16,32,64,128,1,2,4,24,34,48,68,80,96,160,192,224,4096,8192,16384,17,40,72,136,144,4104,8320,16512])
def ORStage29Restr : List ((ℕ × ℕ) × List ℕ) := [((8,11),[24,40,72,136,4104,9,10,12,32776,25,56,88,8200,16392,152,168,200,26,28,42,76,104]),((40,8),[56,168,42,104]),((72,8),[88,200,76,104]),((8192,9),[8194,8320,8256,8196,8200,8208]),((16384,9),[16388,16512,16416,16386,16392,16400])]
def ORStage29Q := tabE (true,4,7) (ORStage29Restr.map (fun r => r.1.1) ++ []) (pick known2 [16,8,32,64,128,2,4,24,48,80,160,192,224,1,4096,8192,16384,17,18,20,34,40,68,72,96,136,144,4097])
def ORStage30Restr : List ((ℕ × ℕ) × List ℕ) := [((128,11),[160,192,136,144,8320,16512,224,130,132,162,196,129,2176,4224,152,168,176,200,208,164,194]),((136,8),[152,168,200]),((144,8),[152,176,208])]
def ORStage30Q := tabE (true,5,6) (ORStage30Restr.map (fun r => r.1.1) ++ []) (pick known2 [32,64,16,128,2,4,8,34,48,68,80,96,160,192,224,1,8192,16384,24,36,40,66,72,136,144,8194,8320,16388])
def ORStage31Restr : List ((ℕ × ℕ) × List ℕ) := [((20,8),[84,21,22,28,52]),((36,8),[38,100,52,164]),((68,9),[70,84,196,100,69,76]),((4096,9),[4097,4104,4098,4100,4128,4160,4224]),((8192,9),[8194,8320,8256,8196,8200,8208]),((16384,9),[16388,16512,16416,16386,16392,16400])]
def ORStage31Q := tabE (true,0,1) (ORStage31Restr.map (fun r => r.1.1) ++ []) (pick known2 [2,16,32,64,1,4,8,128,34,68,4096,8192,16384,6,17,18,20,24,36,48,66,80,96,160,192,4097,8194,25])
def ORStage32Restr : List ((ℕ × ℕ) × List ℕ) := [((18,8),[50,19,22,26,82]),((20,8),[84,21,22,28,52]),((48,9),[50,56,112,176,49,52]),((80,9),[84,88,112,208,81,82]),((144,8),[152,176,208])]
def ORStage32Q := tabE (true,0,3) (ORStage32Restr.map (fun r => r.1.1) ++ []) (pick known2 [8,16,32,64,1,2,4,128,24,48,80,17,18,20,34,40,68,72,96,136,144,160,192,4097,4104,25,56,88])
def ORStage33Restr : List ((ℕ × ℕ) × List ℕ) := [((24,9),[25,56,88,152,26,28]),((40,8),[56,168,42,104]),((72,8),[88,200,76,104]),((4096,9),[4097,4104,4098,4100,4128,4160,4224]),((8192,9),[8194,8320,8256,8196,8200,8208]),((16384,9),[16388,16512,16416,16386,16392,16400])]
def ORStage33Q := tabE (true,0,7) (ORStage33Restr.map (fun r => r.1.1) ++ []) (pick known2 [16,32,64,128,1,2,4,8,24,160,192,224,4096,8192,16384,17,34,40,48,68,72,80,96,136,144,4097,8320,16512])
def ORStage34Restr : List ((ℕ × ℕ) × List ℕ) := [((1,10),[17,4097,3,5,9,33,65,25,129,513,1025,2049,7,19,21,35,49,69,81]),((17,8),[25,19,21,49,81]),((4096,9),[4097,4104,4098,4100,4128,4160,4224]),((8192,9),[8194,8320,8256,8196,8200,8208])]
def ORStage34Q := tabE (true,1,3) (ORStage34Restr.map (fun r => r.1.1) ++ []) (pick known2 [2,8,16,32,64,1,4,128,24,34,4096,8192,6,17,18,40,48,66,68,72,80,96,136,160,192,4104,8194,25])
def ORStage35Restr : List ((ℕ × ℕ) × List ℕ) := [((24,9),[25,56,88,152,26,28]),((36,8),[38,100,52,164]),((40,8),[56,168,42,104]),((48,9),[50,56,112,176,49,52]),((80,9),[84,88,112,208,81,82]),((96,9),[224,112,98,100,104]),((16384,9),[16388,16512,16416,16386,16392,16400])]
def ORStage35Q := tabE (true,1,7) (ORStage35Restr.map (fun r => r.1.1) ++ []) (pick known2 [2,16,32,64,128,4,8,24,34,48,80,96,160,192,224,1,16384,6,18,36,40,66,68,136,144,8194,8320,16512])
def finalSlices := pick known2 [16,32,64,2,4,8,128,1,4096,8192,16384,24,34,48,68,80,96,160,192,32768,6,17,18,20]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR18 : chkT topC [(true,4,5)] ORStage18Q (259,0x2880040000000400000002000108201010080240188014208a000400402000800) 0 13 (List.range 14) 0x1000000000080000000000000000000000000000000000200 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR19 : chkT topC [(true,5,7)] ORStage19Q (259,0x2880040000000400000002080108601010080240188014208a000400402000800) 0 13 (List.range 14) 0x4000000200000000002000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR20 : chkT topC [(true,0,4)] ORStage20Q (259,0x2880060000000400000002080108601010080240188014208a000400402020800) 0 13 (List.range 14) 0x1000000000000200000000000000000010000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR21 : chkT topC [(true,0,5)] ORStage21Q (292,0x8011010880800808000000000010100011028814200000000200020140801018000500101) 0 13 (List.range 14) 0x400000000000000000000000000000080000000200 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR22 : chkT topC [(true,1,2)] ORStage22Q (259,0x2880060000000400000006080108601010080a40188014208a000400402020900) 0 13 (List.range 14) 0x2000000000000000000000000000000200000000000100000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR23 : chkT topC [(true,1,4)] ORStage23Q (371,0x20000040008902001008001010000901400304000000024000000000000100008004c010200002080000602008448) 0 13 (List.range 14) 0x400400000000000000000000000001000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR24 : chkT topC [(true,1,5)] ORStage24Q (259,0x28800600080004000800060801086010100a0a40188014208a000400402020900) 0 13 (List.range 14) 0x8000080000000080000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR25 : chkT topC [(true,1,6)] ORStage25Q (279,0x60c08012800045000010208124408c08602080120200001004000080a1400000800800) 0 13 (List.range 14) 0x40000000010000000000000000008000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR26 : chkT topC [(true,3,4)] ORStage26Q (310,0x4800c14600800101a12025000800040220310108028000600000080082003004000004000020) 0 13 (List.range 14) 0x40000000000000000000000000000000000000000000208 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR27 : chkT topC [(true,3,5)] ORStage27Q (415,0x120000080010000000040001020100180000800102040100000101000000025020000000004002800821202c01102100001c400) 0 13 (List.range 14) 0x8000000000000000000000100000200 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR28 : chkT topC [(true,3,7)] ORStage28Q (294,0x10001040080810301703e00284a23880000480004020000400820004008010004008010020) 0 13 (List.range 14) 0x80000001000000000020000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR29 : chkT topC [(true,4,7)] ORStage29Q (233,0x2a0488040214006248d000088008019200e200a000400e000410081012) 0 13 (List.range 14) 0x40000000000000000000000000000000000004000000400000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR30 : chkT topC [(true,5,6)] ORStage30Q (231,0x274002a0000039010204200810110130400044501901108614012832) 0 13 (List.range 14) 0x80000001200000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR31 : chkT topC [(true,0,1)] ORStage31Q (225,0x68d080040001182683020410808600000064800281420c99c940000) 0 13 (List.range 14) 0x40240000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR32 : chkT topC [(true,0,3)] ORStage32Q (252,0x800081424800104002138c1810890000001b0110c08000990b00040888088a0) 0 13 (List.range 14) 0x80000000000010000000000000000000000000040000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR33 : chkT topC [(true,0,7)] ORStage33Q (233,0x2a04880c02140062c8d000288008019200e200a000420e000410081012) 0 13 (List.range 14) 0x80000200000000000000000001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR34 : chkT topC [(true,1,3)] ORStage34Q (263,0x20a00800908020800a35902a45025c0810082010308c8400000000600226004) 0 13 (List.range 14) 0x800008000000000000000000000000040000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleOR35 : chkT topC [(true,1,7)] ORStage35Q (299,0x48850094008009000402404004003000300000220e8c0040030007020006241018206110862) 0 13 (List.range 14) 0x10000000000000000000000000002 0 = false := by decide +kernel
end PEqualNP.Outside.L_meta_8399
