import PEqualNP.Outside.L_meta_38157
import PEqualNP.Outside.L_meta_36432
namespace PEqualNP.Outside.L_meta_9755.PaidFace
open PEqualNP.Outside.L_meta_36432 PEqualNP.Outside.L_meta_36432.Model

abbrev Ten := Fin 10 → Bool
def board (x : Ten) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def w10 (x : Ten) := !(x 3) && !(x 7)
def w11 (x : Ten) := !(x 3) && !(x 9)
def w12 (x : Ten) := !(x 7) && !(x 8)
def w13 (x : Ten) := !(x 8) && !(x 9)
def w14 (x : Ten) := !(w10 x) && w13 x
def w15 (x : Ten) := w10 x && !(w13 x)
def wire (i : Fin 10) : Wire Ten := fun x =>
  ![x 0,x 1,x 2,x 4,x 5,x 6,w11 x,w12 x,w14 x,w15 x] i
def ws : List (Wire Ten) := [wire 0, wire 1, wire 2, wire 3, wire 4, wire 5, wire 6, wire 7, wire 8, wire 9]
def image (y : Fin 6 → Bool) : Ten := fun i =>
  (([0, 1, 384, 385, 8, 521, 136, 905, 4, 5, 388, 389, 12, 525, 140, 909, 16, 17, 400, 401, 24, 537, 152, 921, 20, 21, 404, 405, 28, 541, 156, 925, 32, 33, 416, 417, 40, 553, 168, 937, 36, 37, 420, 421, 44, 557, 172, 941, 48, 49, 432, 433, 56, 569, 184, 953, 52, 53, 436, 437, 60, 573, 188, 957] : List Nat).getD
    (∑ j : Fin 6, if y j then 2 ^ j.val else 0) 0).testBit i.val
def form (y : Fin 6 → Bool) (i : Fin 10) :=
  ![y 0,false,y 3,y 4,y 5,false,!(y 2),!(y 1),(!(y 0) && y 2),false] i
set_option maxHeartbeats 1600000 in
theorem decoded : ∀ y, board (image y)=posted y ∧ ∀ i, wire i (image y)=form y i := by
  decide +kernel
def face (r : Row) := image (sample6 r)
def atom (i : Fin 6) : Wire Row := fun r => sample6 r i
def helper := combine false (inv (atom 0)) (atom 2)
def off : Wire Row := fun _ => false
def paid := helper :: fullRoots.map observe
theorem rawMem (i : Fin 6) : atom i ∈ fullRoots.map observe := by
  have e : fullRoots.map observe = List.ofFn atom := by
    conv_lhs => rw [←raw6,List.map_ofFn]
    rfl
  rw [e]
  exact List.mem_ofFn.mpr ⟨i,rfl⟩
theorem paidReach : Reach true (fullRoots.map observe) 1 paid := by
  apply Reach.two false Reach.start
  · exact avail_inv rfl (Or.inl (rawMem 0))
  · exact Or.inl (rawMem 2)
theorem hard {s : Nat} (h : Run true board s ws) : 12 ≤ s := by
  have he : restrictRows face board = observe fullWord := by
    funext r
    exact ((decoded (sample6 r)).1).trans (table6 r)
  have nc : ¬Constant (restrictRows face board) := by
    rw [he]
    rintro ⟨b,eq⟩
    have h0 : observe fullWord 0=false := by decide +kernel
    have h1 : observe fullWord 7=true := by decide +kernel
    have e0 := congrFun eq 0
    have e1 := congrFun eq 7
    change observe fullWord 0=b at e0
    change observe fullWord 7=b at e1
    rw [h0] at e0
    rw [h1] at e1
    cases b <;> simp_all
  have e0 : restrictRows face (wire 0) = atom 0 := by
    funext a
    exact (decoded (sample6 a)).2 0
  have e1 : restrictRows face (wire 1) = off := by
    funext a
    exact (decoded (sample6 a)).2 1
  have e2 : restrictRows face (wire 2) = atom 3 := by
    funext a
    exact (decoded (sample6 a)).2 2
  have e3 : restrictRows face (wire 3) = atom 4 := by
    funext a
    exact (decoded (sample6 a)).2 3
  have e4 : restrictRows face (wire 4) = atom 5 := by
    funext a
    exact (decoded (sample6 a)).2 4
  have e5 : restrictRows face (wire 5) = off := by
    funext a
    exact (decoded (sample6 a)).2 5
  have e6 : restrictRows face (wire 6) = inv (atom 2) := by
    funext a
    exact (decoded (sample6 a)).2 6
  have e7 : restrictRows face (wire 7) = inv (atom 1) := by
    funext a
    exact (decoded (sample6 a)).2 7
  have e8 : restrictRows face (wire 8) = helper := by
    funext a
    exact (decoded (sample6 a)).2 8
  have e9 : restrictRows face (wire 9) = off := by
    funext a
    exact (decoded (sample6 a)).2 9
  let rs : List (Wire Row) := [atom 0, off, atom 3, atom 4, atom 5, off, inv (atom 2), inv (atom 1), helper, off]
  have ew : ws.map (restrictRows face)=rs := by
    simp only [rs,ws,List.map_cons,List.map_nil,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9]
  have atomA (i : Fin 6) : Available true paid (atom i) := Or.inl (List.mem_cons_of_mem _ (rawMem i))
  have offC : Constant off := ⟨false,rfl⟩
  have offA : Available true paid off := Or.inr (Or.inl offC)
  have helpA : Available true paid helper := Or.inl (by simp [paid])
  have sup : supply true paid (ws.map (restrictRows face)) := by
    rw [ew]
    intro w hw
    simp only [rs,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact atomA 0
    · exact offA
    · exact atomA 3
    · exact atomA 4
    · exact atomA 5
    · exact offA
    · exact avail_inv rfl (atomA 2)
    · exact avail_inv rfl (atomA 1)
    · exact helpA
    · exact offA
  have low := projected_bound face h nc paidReach sup (L:=10) (by
    rw [he]
    exact fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
  have co : cost off=1 := by simp [cost,offC]
  rw [ew] at low
  simp only [rs,mass_cons,co] at low
  omega
end PEqualNP.Outside.L_meta_9755.PaidFace


namespace PEqualNP.Outside.L_meta_9755.DonorFace
open PEqualNP.Outside.L_meta_38157 PEqualNP.Outside.L_meta_38157.Model
def board (x : Fin 10 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def liftSix (x : Fin 6 → Bool) : Fin 10 → Bool :=
  ![x 3,x 5,x 0,false,x 4,x 2,x 1,false,x 0,x 2]
theorem sameBoard : ∀ x, board (liftSix x) = posted x := by decide +kernel

theorem hardFace {R : Type} (rows : Row → R) {goal : Wire R} {s} {ws : List (Wire R)}
    (run : Run true goal s ws)
    (agree : ∀ r, goal (rows r) = board (liftSix (sample6 r)))
    (avail : supply true (fullRoots.map observe) (ws.map (restrictRows rows))) :
    9 + mass (ws.map (restrictRows rows)) ≤ s := by
  have he : restrictRows rows goal = observe fullWord := by
    funext r
    exact (agree r).trans ((sameBoard _).trans (table6 r))
  have h0 : observe fullWord 0 = false := by decide +kernel
  have h1 : observe fullWord 3 = true := by decide +kernel
  have nc : ¬Constant (restrictRows rows goal) := by
    rw [he]
    rintro ⟨b,h⟩
    have a := congrFun h 0
    have c := congrFun h 3
    change observe fullWord 0 = b at a
    change observe fullWord 3 = b at c
    rw [h0] at a
    rw [h1] at c
    cases b <;> simp_all
  have h := projected_bound rows run nc (p:=0) Reach.start avail (L:=9) (by
    rw [he]
    exact fullBound allgb)
  simpa using h

end PEqualNP.Outside.L_meta_9755.DonorFace
