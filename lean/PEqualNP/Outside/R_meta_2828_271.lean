import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_2828_271
    (normalize : ∀ (C : BinaryCircuit) (b : Bool),
      let z := (fun r : ℕ => ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun e => r &&& e == e))
      (∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) → C.size ≤ 13 →
      (∀ r : Fin 512, (C.eval (List.ofFn (fun i : Fin 9 => r.val.testBit i.val) ++ [r.val.testBit 0 || r.val.testBit 1,false]) != b) = z r.val) →
      ∃ (P S : BinaryCircuit) (u t : Bool) (l : List (Fin 17)),
      let w := fun r : ℕ => P.wires (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [u && (r.testBit 0 || r.testBit 1)])
      P.size = 7 ∧ S.size ≤ 6 ∧ (∀ g ∈ P.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) ∧ (∀ g ∈ S.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) ∧
      l.Nodup ∧ l.length ≤ 7 ∧ (∀ i : Fin 17, 10 - u.toNat ≤ i.val → i ∈ l ∨ ∃ g ∈ P.gates, g.left = i.val ∨ g.right = i.val) ∧ ((List.range 18).map (fun i => List.ofFn (fun r : Fin 512 => (w r.val).getD i false != (w 0).getD i false))).eraseDups.length = 17 + u.toNat ∧
      (∀ i < l.length + S.size, i = S.output ∨ ∃ j : Fin S.size, i < l.length + j.val ∧ ((S.gates.get j).left = i ∨ (S.gates.get j).right = i)) ∧ ∀ r : Fin 512, (S.eval (l.map (fun i => (w (r.val)).getD i.val false)) != t) = z r.val)
    (survey : ∀ (P : BinaryCircuit) (u : Bool) (l : List (Fin 17)),
      let w := fun r : ℕ => P.wires (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [u && (r.testBit 0 || r.testBit 1)])
      let z := (fun r : ℕ => ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun e => r &&& e == e))
      P.size = 7 → (∀ g ∈ P.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) → l.length ≤ 7 → (∀ i : Fin 17, 10 - u.toNat ≤ i.val → i ∈ l ∨ ∃ g ∈ P.gates, g.left = i.val ∨ g.right = i.val) → ((List.range 18).map (fun i => List.ofFn (fun r : Fin 512 => (w r.val).getD i false != (w 0).getD i false))).eraseDups.length = 17 + u.toNat →
      (∀ r s : Fin 512, (l.map (fun i => (w (r.val)).getD i.val false)) = (l.map (fun i => (w (s.val)).getD i.val false)) → z r.val = z s.val) →
      ∃ v : Fin 9,
        let row := fun r : ℕ => r &&& (511 - 2 ^ v.val)
        let sig := fun i : ℕ => List.ofFn (fun r : Fin 512 => (w (row r.val)).getD i false != (w (row 0)).getD i false)
        ((List.range 18).map sig).eraseDups.length + 6 < (((List.range 9) ++ [17]).map sig).eraseDups.length + l.countP (fun i => sig i.val == sig 17) + 12)
    (charge : ∀ (P S : BinaryCircuit) (u t : Bool) (l : List (Fin 17)) (v : Fin 9),
      let w := fun r : ℕ => P.wires (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [u && (r.testBit 0 || r.testBit 1)])
      let row := fun r : ℕ => r &&& (511 - 2 ^ v.val)
      let out := fun r : ℕ => S.eval (l.map (fun i => (w (row r)).getD i.val false)) != t
      let sig := fun i : ℕ => List.ofFn (fun r : Fin 512 => (w (row r.val)).getD i false != (w (row 0)).getD i false)
      P.size = 7 → (∀ g ∈ P.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) → (∀ g ∈ S.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) → l.Nodup → (∀ i < l.length + S.size, i = S.output ∨ ∃ j : Fin S.size, i < l.length + j.val ∧ ((S.gates.get j).left = i ∨ (S.gates.get j).right = i)) →
      out 0 ≠ out 511 → ∃ (D : BinaryCircuit) (b : Bool), (∀ g ∈ D.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) ∧
      D.size + (((List.range 9) ++ [17]).map sig).eraseDups.length + l.countP (fun i => sig i.val == sig 17) ≤ ((List.range 18).map sig).eraseDups.length + S.size ∧
      ∀ r : Fin 512, (D.eval (List.ofFn (fun i : Fin 9 => r.val.testBit i.val)) != b) = out r.val)
    (cofactors : ∀ v : Fin 9,
      let row := fun r : ℕ => r &&& (511 - 2 ^ v.val)
      let z := fun r : ℕ => (fun r : ℕ => ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun e => r &&& e == e)) (row r)
      z 0 ≠ z 511 ∧ ∀ (D : BinaryCircuit) (b : Bool), (∀ g ∈ D.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) →
      (∀ r : Fin 512, (D.eval (List.ofFn (fun i : Fin 9 => r.val.testBit i.val)) != b) = z r.val) → 12 ≤ D.size)
    : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C b hs he
  by_contra! small
  have small' : C.size ≤ 13 := by omega
  let target := (fun r : ℕ => ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun e => r &&& e == e))
  have tab : ∀ r : Fin 512,
      (r.val.testBit 0 && r.val.testBit 1 || r.val.testBit 1 && r.val.testBit 2 ||
       r.val.testBit 2 && r.val.testBit 3 || r.val.testBit 3 && r.val.testBit 4 ||
       r.val.testBit 4 && r.val.testBit 0 || r.val.testBit 0 && r.val.testBit 5 ||
       r.val.testBit 1 && r.val.testBit 6 || r.val.testBit 2 && r.val.testBit 7 ||
       r.val.testBit 3 && r.val.testBit 8 || r.val.testBit 5 && r.val.testBit 7 ||
       r.val.testBit 6 && r.val.testBit 8 || r.val.testBit 8 && r.val.testBit 5) = target r.val := by decide
  obtain ⟨P,S,u,t,l,plen,slen,ps,ss,nd,ll,ul,fr,us,ok⟩ :=
    normalize C b hs small' (fun r => (he (fun i => r.val.testBit i.val)).trans (tab r))
  let w := fun r : ℕ => P.wires (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [u && (r.testBit 0 || r.testBit 1)])
  have sep (r s : Fin 512) (e : (l.map (fun i => (w (r.val)).getD i.val false)) = (l.map (fun i => (w (s.val)).getD i.val false))) : target r.val = target s.val := by
    have er := ok r
    have es := ok s
    change (S.eval (l.map (fun i => (w (r.val)).getD i.val false)) != t) = target r.val at er
    change (S.eval (l.map (fun i => (w (s.val)).getD i.val false)) != t) = target s.val at es
    rw [e] at er
    exact er.symm.trans es
  obtain ⟨v,bad⟩ := survey P u l plen ps ll ul fr sep
  let row := fun r : ℕ => r &&& (511 - 2 ^ v.val)
  have inrange (r : ℕ) : row r < 512 := by
    exact lt_of_le_of_lt (Nat.and_le_right.trans (Nat.sub_le 511 (2 ^ v.val))) (by decide : (511 : ℕ) < 512)
  have val (r : ℕ) : (S.eval (l.map (fun i => (w (row r)).getD i.val false)) != t) = target (row r) :=
    ok ⟨row r,inrange r⟩
  obtain ⟨nc,lower⟩ := cofactors v
  obtain ⟨D,c,ds,cap,ev⟩ := charge P S u t l v plen ps ss nd us (fun e =>
    nc (((val 0).symm.trans e).trans (val 511)))
  have bound := lower D c ds (fun r => (ev r).trans (val r.val))
  let sig := fun i : ℕ => List.ofFn (fun r : Fin 512 => (w (row r.val)).getD i false != (w (row 0)).getD i false)
  let whole := ((List.range 18).map sig).eraseDups.length
  let rawCount := (((List.range 9) ++ [17]).map sig).eraseDups.length
  let constCount := l.countP (fun i => sig i.val == sig 17)
  change whole + 6 < rawCount + constCount + 12 at bad
  change D.size + rawCount + constCount ≤ whole + S.size at cap
  omega
