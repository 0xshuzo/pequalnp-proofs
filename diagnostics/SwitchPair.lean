import PEqualNP.Defs

namespace Research9755.SwitchPair
abbrev W := BitVec 8
abbrev M := BitVec 2
def bank (s : M) : List W :=
  match s.toNat with
  | 0 => [0,15,240,255]
  | 1 => [0,5,10,15,80,85,95,160,170,175,240,245,250,255]
  | 2 => [0,3,12,15,48,51,63,192,204,207,240,243,252,255]
  | _ => [0,1,2,3,4,5,7,8,10,11,12,13,14,15,16,17,19,21,31,32,34,35,42,47,48,49,50,51,53,55,58,59,63,64,68,69,76,79,80,81,83,84,85,87,92,93,95,112,115,117,119,127,128,136,138,140,143,160,162,163,168,170,171,172,174,175,176,179,186,187,191,192,196,197,200,202,204,205,206,207,208,213,220,221,223,224,234,236,238,239,240,241,242,243,244,245,247,248,250,251,252,253,254,255]

def merge (s t : M) : Bool := s &&& t != 0 ||
  (bank s).all (fun x => (bank t).all (fun y =>
    (bank (s ||| t)).contains (x &&& y) && (bank (s ||| t)).contains (x ||| y)))
def inv (s : M) : Bool := (bank s).all fun x => (bank s).contains (~~~x)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem allMerge : ∀s t : M, merge s t=true := by decide +kernel
set_option maxRecDepth 12000 in
theorem allInv : ∀s : M, inv s=true := by decide +kernel

inductive Tree : M → W → Prop where
| context (x : W) (ok : x ∈ ([0,15,240,255] : List W)) : Tree 0 x
| first : Tree 1 170
| second : Tree 2 204
| neg {s x} (term : Tree s x) : Tree s (~~~x)
| conj {s t x y} (a : Tree s x) (b : Tree t y) (disj : s &&& t=0) :
    Tree (s ||| t) (x &&& y)
| disj {s t x y} (a : Tree s x) (b : Tree t y) (clean : s &&& t=0) :
    Tree (s ||| t) (x ||| y)

theorem member {s x} (h : Tree s x) : x∈bank s := by
  induction h with
  | context x h => exact h
  | first => decide
  | second => decide
  | neg h ih =>
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (allInv _) _ ih)
  | conj a b hd ia ib =>
    rename_i s t x y
    have h := allMerge s t
    simp only [merge,hd,bne_self_eq_false,Bool.false_or,List.all_eq_true] at h
    exact List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp (h x ia y ib)).1
  | disj a b hd ia ib =>
    rename_i s t x y
    have h := allMerge s t
    simp only [merge,hd,bne_self_eq_false,Bool.false_or,List.all_eq_true] at h
    exact List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp (h x ia y ib)).2

def graph (x : Fin 10 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def board (side : Bool) (r : Fin 8) : Fin 10 → Bool :=
  let v := r.val.testBit 0
  let y := r.val.testBit 1
  let k := r.val.testBit 2
  if side then ![false,v,k,false,false,false,y,false,k,false]
  else ![false,v,y,k,false,false,k,false,false,false]
def face (side : Bool) : W :=
  BitVec.ofNat 8 ((List.finRange 8).foldl
    (fun a i => if graph (board side i) then a + 2^i.val else a) 0)
theorem both : ∀side,face side=232 := by decide +kernel
theorem impossible (side : Bool) (s : M) : ¬Tree s (face side) := by
  rw [both]
  intro h
  exact (by decide +kernel : ∀t : M,(232 : W)∉bank t) s (member h)
end Research9755.SwitchPair
