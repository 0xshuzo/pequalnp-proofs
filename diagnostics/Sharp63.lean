import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7290.Sharp
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev I := Fin 13
def D : Finset I := {0,1,3,9}
def inputs (P L : I → Bool) := List.ofFn P ++ List.ofFn L
def C : Circuit := ⟨[⟨.or, [3,9]⟩,⟨.or, [1,26]⟩,⟨.or, [0,27]⟩,⟨.and, [13,28]⟩,⟨.or, [4,10]⟩,⟨.or, [2,30]⟩,⟨.or, [1,31]⟩,⟨.and, [14,32]⟩,⟨.or, [5,11]⟩,⟨.or, [3,34]⟩,⟨.or, [2,35]⟩,⟨.and, [15,36]⟩,⟨.or, [6,12]⟩,⟨.or, [4,38]⟩,⟨.or, [3,39]⟩,⟨.and, [16,40]⟩,⟨.or, [7,0]⟩,⟨.or, [5,42]⟩,⟨.or, [4,43]⟩,⟨.and, [17,44]⟩,⟨.or, [8,1]⟩,⟨.or, [6,46]⟩,⟨.or, [5,47]⟩,⟨.and, [18,48]⟩,⟨.or, [9,2]⟩,⟨.or, [7,50]⟩,⟨.or, [6,51]⟩,⟨.and, [19,52]⟩,⟨.or, [10,3]⟩,⟨.or, [8,54]⟩,⟨.or, [7,55]⟩,⟨.and, [20,56]⟩,⟨.or, [11,4]⟩,⟨.or, [9,58]⟩,⟨.or, [8,59]⟩,⟨.and, [21,60]⟩,⟨.or, [12,5]⟩,⟨.or, [10,62]⟩,⟨.or, [9,63]⟩,⟨.and, [22,64]⟩,⟨.or, [0,6]⟩,⟨.or, [11,66]⟩,⟨.or, [10,67]⟩,⟨.and, [23,68]⟩,⟨.or, [1,7]⟩,⟨.or, [12,70]⟩,⟨.or, [11,71]⟩,⟨.and, [24,72]⟩,⟨.or, [2,8]⟩,⟨.or, [0,74]⟩,⟨.or, [12,75]⟩,⟨.and, [25,76]⟩,⟨.or, [73,77]⟩,⟨.or, [69,78]⟩,⟨.or, [65,79]⟩,⟨.or, [61,80]⟩,⟨.or, [57,81]⟩,⟨.or, [53,82]⟩,⟨.or, [49,83]⟩,⟨.or, [45,84]⟩,⟨.or, [41,85]⟩,⟨.or, [37,86]⟩,⟨.or, [33,87]⟩],88⟩
def O (a b : Bool) := GateOp.or.eval [a,b]
def A (a b : Bool) := GateOp.and.eval [a,b]
theorem opO (a b : Bool) : O a b=(a||b) := by cases a <;> cases b <;> rfl
theorem opA (a b : Bool) : A a b=(a&&b) := by cases a <;> cases b <;> rfl
def starRows : List (I × List I) := [(1,[1, 2, 4, 10]),(2,[2, 3, 5, 11]),(3,[3, 4, 6, 12]),(4,[4, 5, 7, 0]),(5,[5, 6, 8, 1]),(6,[6, 7, 9, 2]),(7,[7, 8, 10, 3]),(8,[8, 9, 11, 4]),(9,[9, 10, 12, 5]),(10,[10, 11, 0, 6]),(11,[11, 12, 1, 7]),(12,[12, 0, 2, 8])]
def f (P L : I → Bool) := L 0 && ([0,1,3,9] : List I).any P
def h (P L : I → Bool) := starRows.any fun r => L r.1 && r.2.any P
def val (k : ℕ) (P L : I → Bool) := (C.wires (inputs P L)).getD k false
def answer (P L : I → Bool) := (val 29 P L, val 88 P L)
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 32768 in
theorem eval (P L : I → Bool) : answer P L = (f P L,h P L) := by
  let u26 := O (P 3) (P 9)
  let u27 := O (P 1) u26
  let u28 := O (P 0) u27
  let u29 := A (L 0) u28
  let u30 := O (P 4) (P 10)
  let u31 := O (P 2) u30
  let u32 := O (P 1) u31
  let u33 := A (L 1) u32
  let u34 := O (P 5) (P 11)
  let u35 := O (P 3) u34
  let u36 := O (P 2) u35
  let u37 := A (L 2) u36
  let u38 := O (P 6) (P 12)
  let u39 := O (P 4) u38
  let u40 := O (P 3) u39
  let u41 := A (L 3) u40
  let u42 := O (P 7) (P 0)
  let u43 := O (P 5) u42
  let u44 := O (P 4) u43
  let u45 := A (L 4) u44
  let u46 := O (P 8) (P 1)
  let u47 := O (P 6) u46
  let u48 := O (P 5) u47
  let u49 := A (L 5) u48
  let u50 := O (P 9) (P 2)
  let u51 := O (P 7) u50
  let u52 := O (P 6) u51
  let u53 := A (L 6) u52
  let u54 := O (P 10) (P 3)
  let u55 := O (P 8) u54
  let u56 := O (P 7) u55
  let u57 := A (L 7) u56
  let u58 := O (P 11) (P 4)
  let u59 := O (P 9) u58
  let u60 := O (P 8) u59
  let u61 := A (L 8) u60
  let u62 := O (P 12) (P 5)
  let u63 := O (P 10) u62
  let u64 := O (P 9) u63
  let u65 := A (L 9) u64
  let u66 := O (P 0) (P 6)
  let u67 := O (P 11) u66
  let u68 := O (P 10) u67
  let u69 := A (L 10) u68
  let u70 := O (P 1) (P 7)
  let u71 := O (P 12) u70
  let u72 := O (P 11) u71
  let u73 := A (L 11) u72
  let u74 := O (P 2) (P 8)
  let u75 := O (P 0) u74
  let u76 := O (P 12) u75
  let u77 := A (L 12) u76
  let u78 := O u73 u77
  let u79 := O u69 u78
  let u80 := O u65 u79
  let u81 := O u61 u80
  let u82 := O u57 u81
  let u83 := O u53 u82
  let u84 := O u49 u83
  let u85 := O u45 u84
  let u86 := O u41 u85
  let u87 := O u37 u86
  let u88 := O u33 u87
  let values : List Bool := [(P 0),(P 1),(P 2),(P 3),(P 4),(P 5),(P 6),(P 7),(P 8),(P 9),(P 10),(P 11),(P 12),(L 0),(L 1),(L 2),(L 3),(L 4),(L 5),(L 6),(L 7),(L 8),(L 9),(L 10),(L 11),(L 12),u26,u27,u28,u29,u30,u31,u32,u33,u34,u35,u36,u37,u38,u39,u40,u41,u42,u43,u44,u45,u46,u47,u48,u49,u50,u51,u52,u53,u54,u55,u56,u57,u58,u59,u60,u61,u62,u63,u64,u65,u66,u67,u68,u69,u70,u71,u72,u73,u74,u75,u76,u77,u78,u79,u80,u81,u82,u83,u84,u85,u86,u87,u88]
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  have t26 : step (values.take 26) (⟨.or,[3,9]⟩ : Gate) = values.take 27 := by rfl
  have t27 : step (values.take 27) (⟨.or,[1,26]⟩ : Gate) = values.take 28 := by rfl
  have t28 : step (values.take 28) (⟨.or,[0,27]⟩ : Gate) = values.take 29 := by rfl
  have t29 : step (values.take 29) (⟨.and,[13,28]⟩ : Gate) = values.take 30 := by rfl
  have t30 : step (values.take 30) (⟨.or,[4,10]⟩ : Gate) = values.take 31 := by rfl
  have t31 : step (values.take 31) (⟨.or,[2,30]⟩ : Gate) = values.take 32 := by rfl
  have t32 : step (values.take 32) (⟨.or,[1,31]⟩ : Gate) = values.take 33 := by rfl
  have t33 : step (values.take 33) (⟨.and,[14,32]⟩ : Gate) = values.take 34 := by rfl
  have t34 : step (values.take 34) (⟨.or,[5,11]⟩ : Gate) = values.take 35 := by rfl
  have t35 : step (values.take 35) (⟨.or,[3,34]⟩ : Gate) = values.take 36 := by rfl
  have t36 : step (values.take 36) (⟨.or,[2,35]⟩ : Gate) = values.take 37 := by rfl
  have t37 : step (values.take 37) (⟨.and,[15,36]⟩ : Gate) = values.take 38 := by rfl
  have t38 : step (values.take 38) (⟨.or,[6,12]⟩ : Gate) = values.take 39 := by rfl
  have t39 : step (values.take 39) (⟨.or,[4,38]⟩ : Gate) = values.take 40 := by rfl
  have t40 : step (values.take 40) (⟨.or,[3,39]⟩ : Gate) = values.take 41 := by rfl
  have t41 : step (values.take 41) (⟨.and,[16,40]⟩ : Gate) = values.take 42 := by rfl
  have t42 : step (values.take 42) (⟨.or,[7,0]⟩ : Gate) = values.take 43 := by rfl
  have t43 : step (values.take 43) (⟨.or,[5,42]⟩ : Gate) = values.take 44 := by rfl
  have t44 : step (values.take 44) (⟨.or,[4,43]⟩ : Gate) = values.take 45 := by rfl
  have t45 : step (values.take 45) (⟨.and,[17,44]⟩ : Gate) = values.take 46 := by rfl
  have t46 : step (values.take 46) (⟨.or,[8,1]⟩ : Gate) = values.take 47 := by rfl
  have t47 : step (values.take 47) (⟨.or,[6,46]⟩ : Gate) = values.take 48 := by rfl
  have t48 : step (values.take 48) (⟨.or,[5,47]⟩ : Gate) = values.take 49 := by rfl
  have t49 : step (values.take 49) (⟨.and,[18,48]⟩ : Gate) = values.take 50 := by rfl
  have t50 : step (values.take 50) (⟨.or,[9,2]⟩ : Gate) = values.take 51 := by rfl
  have t51 : step (values.take 51) (⟨.or,[7,50]⟩ : Gate) = values.take 52 := by rfl
  have t52 : step (values.take 52) (⟨.or,[6,51]⟩ : Gate) = values.take 53 := by rfl
  have t53 : step (values.take 53) (⟨.and,[19,52]⟩ : Gate) = values.take 54 := by rfl
  have t54 : step (values.take 54) (⟨.or,[10,3]⟩ : Gate) = values.take 55 := by rfl
  have t55 : step (values.take 55) (⟨.or,[8,54]⟩ : Gate) = values.take 56 := by rfl
  have t56 : step (values.take 56) (⟨.or,[7,55]⟩ : Gate) = values.take 57 := by rfl
  have t57 : step (values.take 57) (⟨.and,[20,56]⟩ : Gate) = values.take 58 := by rfl
  have t58 : step (values.take 58) (⟨.or,[11,4]⟩ : Gate) = values.take 59 := by rfl
  have t59 : step (values.take 59) (⟨.or,[9,58]⟩ : Gate) = values.take 60 := by rfl
  have t60 : step (values.take 60) (⟨.or,[8,59]⟩ : Gate) = values.take 61 := by rfl
  have t61 : step (values.take 61) (⟨.and,[21,60]⟩ : Gate) = values.take 62 := by rfl
  have t62 : step (values.take 62) (⟨.or,[12,5]⟩ : Gate) = values.take 63 := by rfl
  have t63 : step (values.take 63) (⟨.or,[10,62]⟩ : Gate) = values.take 64 := by rfl
  have t64 : step (values.take 64) (⟨.or,[9,63]⟩ : Gate) = values.take 65 := by rfl
  have t65 : step (values.take 65) (⟨.and,[22,64]⟩ : Gate) = values.take 66 := by rfl
  have t66 : step (values.take 66) (⟨.or,[0,6]⟩ : Gate) = values.take 67 := by rfl
  have t67 : step (values.take 67) (⟨.or,[11,66]⟩ : Gate) = values.take 68 := by rfl
  have t68 : step (values.take 68) (⟨.or,[10,67]⟩ : Gate) = values.take 69 := by rfl
  have t69 : step (values.take 69) (⟨.and,[23,68]⟩ : Gate) = values.take 70 := by rfl
  have t70 : step (values.take 70) (⟨.or,[1,7]⟩ : Gate) = values.take 71 := by rfl
  have t71 : step (values.take 71) (⟨.or,[12,70]⟩ : Gate) = values.take 72 := by rfl
  have t72 : step (values.take 72) (⟨.or,[11,71]⟩ : Gate) = values.take 73 := by rfl
  have t73 : step (values.take 73) (⟨.and,[24,72]⟩ : Gate) = values.take 74 := by rfl
  have t74 : step (values.take 74) (⟨.or,[2,8]⟩ : Gate) = values.take 75 := by rfl
  have t75 : step (values.take 75) (⟨.or,[0,74]⟩ : Gate) = values.take 76 := by rfl
  have t76 : step (values.take 76) (⟨.or,[12,75]⟩ : Gate) = values.take 77 := by rfl
  have t77 : step (values.take 77) (⟨.and,[25,76]⟩ : Gate) = values.take 78 := by rfl
  have t78 : step (values.take 78) (⟨.or,[73,77]⟩ : Gate) = values.take 79 := by rfl
  have t79 : step (values.take 79) (⟨.or,[69,78]⟩ : Gate) = values.take 80 := by rfl
  have t80 : step (values.take 80) (⟨.or,[65,79]⟩ : Gate) = values.take 81 := by rfl
  have t81 : step (values.take 81) (⟨.or,[61,80]⟩ : Gate) = values.take 82 := by rfl
  have t82 : step (values.take 82) (⟨.or,[57,81]⟩ : Gate) = values.take 83 := by rfl
  have t83 : step (values.take 83) (⟨.or,[53,82]⟩ : Gate) = values.take 84 := by rfl
  have t84 : step (values.take 84) (⟨.or,[49,83]⟩ : Gate) = values.take 85 := by rfl
  have t85 : step (values.take 85) (⟨.or,[45,84]⟩ : Gate) = values.take 86 := by rfl
  have t86 : step (values.take 86) (⟨.or,[41,85]⟩ : Gate) = values.take 87 := by rfl
  have t87 : step (values.take 87) (⟨.or,[37,86]⟩ : Gate) = values.take 88 := by rfl
  have t88 : step (values.take 88) (⟨.or,[33,87]⟩ : Gate) = values.take 89 := by rfl
  have init : inputs P L = values.take 26 := by rfl
  have final : C.wires (inputs P L) = values.take 89 := by
    change C.gates.foldl step (inputs P L) = _
    rw [init]
    unfold C
    rw [List.foldl_cons,t26,List.foldl_cons,t27,List.foldl_cons,t28,List.foldl_cons,t29,List.foldl_cons,t30]
    rw [List.foldl_cons,t31,List.foldl_cons,t32,List.foldl_cons,t33,List.foldl_cons,t34,List.foldl_cons,t35]
    rw [List.foldl_cons,t36,List.foldl_cons,t37,List.foldl_cons,t38,List.foldl_cons,t39,List.foldl_cons,t40]
    rw [List.foldl_cons,t41,List.foldl_cons,t42,List.foldl_cons,t43,List.foldl_cons,t44,List.foldl_cons,t45]
    rw [List.foldl_cons,t46,List.foldl_cons,t47,List.foldl_cons,t48,List.foldl_cons,t49,List.foldl_cons,t50]
    rw [List.foldl_cons,t51,List.foldl_cons,t52,List.foldl_cons,t53,List.foldl_cons,t54,List.foldl_cons,t55]
    rw [List.foldl_cons,t56,List.foldl_cons,t57,List.foldl_cons,t58,List.foldl_cons,t59,List.foldl_cons,t60]
    rw [List.foldl_cons,t61,List.foldl_cons,t62,List.foldl_cons,t63,List.foldl_cons,t64,List.foldl_cons,t65]
    rw [List.foldl_cons,t66,List.foldl_cons,t67,List.foldl_cons,t68,List.foldl_cons,t69,List.foldl_cons,t70]
    rw [List.foldl_cons,t71,List.foldl_cons,t72,List.foldl_cons,t73,List.foldl_cons,t74,List.foldl_cons,t75]
    rw [List.foldl_cons,t76,List.foldl_cons,t77,List.foldl_cons,t78,List.foldl_cons,t79,List.foldl_cons,t80]
    rw [List.foldl_cons,t81,List.foldl_cons,t82,List.foldl_cons,t83,List.foldl_cons,t84,List.foldl_cons,t85]
    rw [List.foldl_cons,t86,List.foldl_cons,t87,List.foldl_cons,t88]
    rfl
  unfold answer val
  rw [final]
  change (u29,u88) = _
  simp only [u88,u87,u86,u85,u84,u83,u82,u81,u80,u79,u78,u77,u76,u75,u74,u73,u72,u71,u70,u69,u68,u67,u66,u65,u64,u63,u62,u61,u60,u59,u58,u57,u56,u55,u54,u53,u52,u51,u50,u49,u48,u47,u46,u45,u44,u43,u42,u41,u40,u39,u38,u37,u36,u35,u34,u33,u32,u31,u30,u29,u28,u27,u26,opO,opA,f,h,starRows,List.any_cons,List.any_nil,Bool.or_false]

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)
theorem monotone : Monotone2 C := by
  intro g hg
  have all : C.gates.all legal = true := by decide +kernel
  have h := List.all_eq_true.mp all g hg
  cases e : g.op <;> simp [legal,e] at h ⊢ <;> exact h
theorem back : NestedCover.ReadsBack 26 C := by
  have F : ∀ j : Fin C.gates.length,∀ w∈(C.gates.get j).inputs,w<26+j.val := by decide +kernel
  intro j hj w hw
  apply F ⟨j,hj⟩ w
  simpa [NestedCover.gateAt,List.getD_eq_getElem?_getD,hj] using hw
theorem price : C.size=63 := rfl

def active (a b j : I) := decide (j=a ∨ j=b)
theorem rows_ok : ∀ r ∈ starRows, ∀ p ∈ r.2, p-r.1∈D := by decide +kernel
theorem fullRows : ∀ p l : I, p-l∈D →
  (l=0 ∧ p∈([0,1,3,9] : List I)) ∨ ∃ r∈starRows,r.1=l ∧ p∈r.2 := by decide +kernel
theorem exact_pair (p q l m : I) :
    (val 29 (active p q) (active l m) || val 88 (active p q) (active l m)) =
      decide (p-l∈D ∨ p-m∈D ∨ q-l∈D ∨ q-m∈D) := by
  have eq := eval (active p q) (active l m)
  have e1 := congrArg Prod.fst eq
  have e2 := congrArg Prod.snd eq
  change val 29 _ _ = f _ _ at e1
  change val 88 _ _ = h _ _ at e2
  rw [e1,e2]
  apply Bool.eq_iff_iff.mpr
  simp only [f,h,active,Bool.or_eq_true,Bool.and_eq_true,List.any_eq_true,decide_eq_true_eq]
  have zero : ∀ k ∈ ([0,1,3,9] : List I), k-(0:I)∈D := by decide +kernel
  constructor
  · rintro ⟨hl,pp,kp,hp⟩|⟨r,hr,hl,pp,kp,hp⟩
    · rcases hl with hh|hh <;> rcases hp with hq|hq <;> subst_vars <;> aesop
    · have hi := rows_ok r hr pp kp
      rcases hl with hh|hh <;> rcases hp with hq|hq <;> grind
  · have accept (i j : I) (hi : i=p ∨ i=q) (hj : j=l ∨ j=m) (hin : i-j∈D) :
        ((0=l ∨ 0=m) ∧ ∃ u∈([0,1,3,9] : List I), u=p ∨ u=q) ∨
        ∃ r∈starRows, (r.1=l ∨ r.1=m) ∧ ∃ u∈r.2,u=p ∨ u=q := by
      rcases fullRows i j hin with ⟨rfl,hk⟩|⟨r,hr,hh,hk⟩
      · exact Or.inl ⟨hj,i,hk,hi⟩
      · exact Or.inr ⟨r,hr,by simpa only [hh] using hj,i,hk,hi⟩
    rintro h1|h2|h3|h4
    · exact accept _ _ (Or.inl rfl) (Or.inl rfl) h1
    · exact accept _ _ (Or.inl rfl) (Or.inr rfl) h2
    · exact accept _ _ (Or.inr rfl) (Or.inl rfl) h3
    · exact accept _ _ (Or.inr rfl) (Or.inr rfl) h4

theorem exclusive : (f (active 0 0) (active 0 0)=true ∧ h (active 0 0) (active 0 0)=false) ∧
  (h (active 1 1) (active 1 1)=true ∧ f (active 1 1) (active 1 1)=false) := by decide +kernel
end PEqualNP.Outside.L_meta_7290.Sharp
