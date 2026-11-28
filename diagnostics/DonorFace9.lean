import PEqualNP.Outside.L_meta_38157

namespace PEqualNP.Outside.L_meta_9755.DonorFace
open PEqualNP.Outside.L_meta_38157
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
