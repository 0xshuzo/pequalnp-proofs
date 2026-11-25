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
def NN : Nat := 516
def AA : Nat := 0x7fffbfffdefbeffffbbfffdfffeffff77fffbdfffef7bedfffef7fffbdefb7bdbefbbbbdffdfff7ffdfff7ffdfff7ffdfff7ffdfff7ffdfff0000000000000000
def HX : Nat := 0x2000800200080020008002000800200080020000000000000000000
def HY : Nat := 0x800040002104100004400020001000088000420001084120001080004210484241044442000000000000000000000000000000000000000000000000000000000
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
def zflG (N np q nc : Nat) : Nat := Nat.land (Nat.sub U16 (Nat.mod (Nat.shiftRight (Nat.land (Nat.add (Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np) (MM16 N)) (GG16 N)) (Nat.mul 2 N)) (MD16 N))) nc
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
def segsX : List (ℕ × ℕ) := [(63, 77), (77, 91), (91, 105), (105, 119), (119, 133), (133, 147), (147, 161), (161, 175), (175, 189), (189, 203), (203, 217)]
def segsY : List (ℕ × ℕ) := [(217, 229), (229, 234), (234, 238), (238, 242), (242, 246), (246, 252), (252, 258), (258, 261), (261, 266), (266, 271), (271, 274), (274, 280), (280, 285), (285, 290), (290, 307), (307, 312), (312, 329), (329, 332), (332, 338), (338, 343), (343, 348), (348, 365), (365, 370), (370, 387), (387, 391), (391, 408), (408, 425), (425, 442), (442, 446), (446, 464), (464, 470), (470, 476), (476, 481), (481, 498), (498, 515)]
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
    (Bool.rec (motive := fun _ => Bool) false (F kF kF2) (Nat.beq (edg d l o v) 0)) (Nat.beq n e)) (wst d l v)) (len v)
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
def rawP : List ℕ := [0xffff8000000000ffff00000000000003e0000000000000f80000000003c00044011004401200480120048212084801208482fe73f38cfff987f8010d8086c2082ad8d80046c02368f1b0008d84023610be001361004d842f8084820888bc06c000000000000000000001fff7ffc0007ffdffffe73f38cfff987f8,0x3fffc003e00000000000000000007fff81fffe078000000000000000003c00f8038000083020c0830218086221808602180862218086473f5d4b7ffceb4ad0222ab914013e00a2800914048a0145147a2811e8a07820028a200a28840913c04f8138411400000000000001fff00000000001fff0001fff73f5d4b7ffceb4ad,0x7fff800000f800000000000000000000000000000000001fffe07fff81e007803e003800001006403100c40390184061018406101c4071018b3fae95bffcf4b565743012180f840143001218090c02862014308050c210449f0c027c301e107883e10390821800000000007ffc00000000000001fff7ffc000b3fae95bffcf4b56,0x1fffe00000000001fffef0000000007fffbc0000003efb80000000920250096049012804a812804b012804a0128dfefce6c0d0f9fe70494024a0420806140860a13e50142800a14113e50f0080245042dd43c0202113efb80104a00000001fff00000007ffc0007ffc0000000000dfefce6c0d0f9fe7,0x7fffbfffde000000003fffc0000000007fffbc000000001fffef0000000007bd8000000000192464a19286921a506951a546941a506941a503f8f0fecce39f86057182b8c1e0000818023cc010600830047983c0860401009760f0118100407bd882100200c0000000000000000007ffdfff000000000000003f8f0fecce39f860,0x3fffdfffeffff7000000000000001fffef7fffbdefb000000000000001c607381cc0e3039c0e603980e603980e6039826ac77b55453eaaf18200c1008410302012bd015e80af407142000508002000d780f35e03defb020004002009000007ffc0000001fff00000000000000000000026ac77b55453eaaf,0x3fffdfffeffff77fffbdfffef7bec00000000000000000000000000001f807c01f00fc03e00f803e00f803e00f803e02b4cbbdaa865f5576040302010820c040233e019f00cf80767c03d9f00f7bed1800046000080040010002001201fff00000007ffc0000000000000000000000002b4cbbdaa865f557,0x7fffbfffdefbeffffb800000000000000000000000000000000000000000000000000000001e007801e007001c007001c007001c007001c00fd8ffc0f3cb67e1b7f803fc01efbeff803bc001e000f0004780021e00084209e000878002108200020820001c01fff7ffdfff0000000000000000000000000000fd8ffc0f3cb67e1b]
def TG : ℕ := 0x7fffbfffdefbeffffbbfffdfffeffff77fffbdfffef7bedfffef7fffbdefb7bdbefbbbbdffdfff7ffdfff7ffdfff7ffdfff7ffdfff7ffdfffffffffffffffffff
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def pinMask (Z : ℕ) : ℕ := (List.range 8).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else
  (bif Nat.testBit Z (i + 8) then Nat.lor x (Nat.xor FULL (Nat.land (rawP.getD i 0) (Nat.lor (Nat.shiftRight (rawP.getD i 0) NN) FPM))) else x)) 0
def relationCuts : List ℕ := [0x0,0x8080400020080800004000201010008080020200820000200000800080040008008400400000000000000000000000000000000001fff7271d084ffc884a8,0x1010000800800101000008000402020000100000400040010400041002100800200080800800000000000000000000000000000007ffc000b272e108ffc90350,0x4000200000040400002002100408000040002101008000100004404020000020880100200000000000000000000000007ffc0000000000de63c20c0d0987e0,0x10800840200008080004400020081000088040020001000120100080004008480000020040000000000000000000001fff000000000000003e03038cce398060,0x20000004000200ffff0000000000000000010010040042f8000000000000000400100040020008002000800200080020008026207384545182a8,0x80000004000200ffff0008004020010be00000000000000000000000000000040010004002000800200080020008002000802a40b388a8618550,0x100008002082ffff800000000080000000000000000200000000000000800000000000000040010004001000400100040010004001000400fc03f00c3cb00618,0x202010100104000200001000080004001020004080100002080008200400108041011000100000000000000000000000000001fff000000033f0c013ffce0004,0x200000080000000000040000000020001fffe000000000000800800001004f800000000100040010008002000800200080020008002053e5c4240d0e94a5,0x2003fffc000000000008000000000007fff800800000000200200000000013c0020000000082020808202100840210084021008402100840338504a4ce08b020,0x2008100001000200009000480014010420001080020000280200a0084090200040020010000000000000001fff00000000000000000000022a454b55442a0ad,0x20000002000000008000400010017fff81fffe07820000000000000000000000000000003000c0030018006001800600180060018006023449092a844b405,0x2003fffc013e00800000000000000004000010000040000000000000000000000800000000800200080020008002000800200080020008007185d4073c863409,0x4000000002000000000000080000000000000040020000040007fff800002003e1000000000020010004001000800200080020008002000893eac8480d0f0b46,0x7fff8100000000000001000000000000010008000000001fffe00100000007880800000000100440210084021010404101040410104041010338a0948ce094840,0x10000000004000000001000080002002000000000000001fffe07fff81e1000000000000000006003000c003001800600180060018006001822a8611154434a06,0x40400020008000040001200090002802014008050021044180000600008004001000200020000000000007ffc0000000000000000000000002348a95aa8454156,0x7fff810000f840100000000000000000000000000000000800002000010000002000000000100040010004001000400100040010004001000b18ae80b3c864a12,0x41002080400000100020801040002000210100840400000440401101000021108210000080000000000000000007ffc000000000000000001f8f0e6c0c099860,0x2001fffe04000000000100000000040047fffbc020000004000000000820210084041010804201080420108042010806ac462404038aa7,0x2001fffe04000020011fffef00800000004000000000010000000000090024009004801200480120048012004801200b4c8a4808059547,0x480024004208060008400120001000008000120008000020000280020000000208200004000000001fff0000000000000000000000000000dd8fcc0c0c061e03,0x1000080008000000003fffc100008000040000000000001fffef0100100400200000000000010404201080820210084021008402100840210268c07a44411e820,0x4000200010000000003fffc1000080007fffbc0800401001000000000000040000000000000120048012009002400900240090024009002402b0c0bc88821f040,0x7fffbfffde00008000200000000000004000200000000008000800000000000000000000001800600180060018006001800600180060018003d8f0c0c0c307800,0x3fffdfffeffff704000010000200010000040000800000000000000001c007001c00e003800e003800e003800e00380220c33900041e007,0x18000c000841030001280014000a0004100000400000000c0008300021082000000000008000007ffc0000000000000000000000000000000248c740514126a0b,0x6000300010820c0002300018000c00046000218000842090000040000000000000000001001fff00000000000000000000000000000000000290cb80a28247413]
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

def ORStage32Restr : List ((ℕ × ℕ) × List ℕ) := [((18,8),[50,19,22,26,82]),((20,8),[84,21,22,28,52]),((48,9),[50,56,112,176,49,52]),((80,9),[84,88,112,208,81,82]),((144,8),[152,176,208])]
def ORStage32Q := tabE (true,0,3) (ORStage32Restr.map (fun r => r.1.1) ++ []) (pick known2 [8,16,32,64,1,2,4,128,24,48,80,17,18,20,34,40,68,72,96,136,144,160,192,4097,4104,25,56,88])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem isolatedOR03 : chkT topC [(true,0,3)] ORStage32Q (233,0x4046280200044010003000e633702aa0127282200021000404600a0000) 0 13 (List.range 14) FF 1 = false := by decide +kernel

end PEqualNP.Outside.L_meta_8399
