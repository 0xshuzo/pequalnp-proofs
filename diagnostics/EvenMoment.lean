import Mathlib
namespace EvenObstruction238
theorem finite : ∀ a b : ZMod 19,
   57267942405537375*a^2-37184217741575850*a*b+6035070335795303*b^2=0 → a=0 ∧ b=0 := by decide +kernel
theorem rational (y : ℚ) : 57267942405537375*y^2-37184217741575850*y+6035070335795303≠0 := by
  intro h
  have den : (y.den:ℚ)≠0 := by exact_mod_cast y.den_nz
  have frac : (y.num:ℚ)/(y.den:ℚ)=y := Rat.num_div_den y
  have raw : 57267942405537375*(y.num:ℚ)^2-37184217741575850*(y.num:ℚ)*(y.den:ℚ)
       +6035070335795303*(y.den:ℚ)^2=0 := by
    calc
      _ = (y.den:ℚ)^2*(57267942405537375*y^2-37184217741575850*y+6035070335795303) := by
        have numer : (y.num:ℚ)=y*(y.den:ℚ) := (div_eq_iff den).mp frac
        rw [numer]
        ring
      _ = 0 := by rw [h,mul_zero]
  have integral : 57267942405537375*y.num^2-37184217741575850*y.num*(y.den:ℤ)
       +6035070335795303*(y.den:ℤ)^2=0 := by exact_mod_cast raw
  have z := congrArg (fun k : ℤ => (k : ZMod 19)) integral
  push_cast at z
  have zeros := finite (y.num : ZMod 19) (y.den : ZMod 19) z
  have hn : (19 : ℤ) ∣ y.num := by
    first | exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp zeros.1 | exact?
  have hd : 19 ∣ y.den := by
    have hcast : ((y.den:ℤ):ZMod 19)=0 := by simpa using zeros.2
    have hdZ : (19 : ℤ) ∣ (y.den : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
    exact_mod_cast hdZ
  obtain ⟨k,hk⟩ := hn
  have hn' : 19 ∣ y.num.natAbs := ⟨k.natAbs,by rw [hk,Int.natAbs_mul]; rfl⟩
  have cop := y.reduced
  have bad := Nat.dvd_gcd hn' hd
  rw [cop.gcd_eq_one] at bad
  norm_num at bad

theorem jets (B C D u v w : ℚ) (bn : B≠0)
    (h2 : 7 - 2*u=0)
    (h3 : -51*B*u + 64*B - 51*v=0)
    (h4 : 15*B^2*u^2 - 96*B^2*u + 65*B^2 + 30*B*u*v - 96*B*v - 15*C*u^2 + 96*C*u - 65*C + 30*u*w + 15*v^2 - 96*w=0)
    (h5 : 622*B^3*u^2 - 1482*B^3*u + 651*B^3 + 1244*B^2*u*v - 1482*B^2*v - 1244*B*C*u^2 + 2964*B*C*u - 1302*B*C + 1244*B*u*w + 622*B*v^2 - 1482*B*w - 1244*C*u*v + 1482*C*v + 622*D*u^2 - 1482*D*u + 651*D + 1244*v*w=0)
    (h6 : -80260*B^4*u^3 + 749334*B^4*u^2 - 994854*B^4*u + 315235*B^4 - 240780*B^3*u^2*v + 1498668*B^3*u*v - 994854*B^3*v + 240780*B^2*C*u^3 - 2248002*B^2*C*u^2 + 2984562*B^2*C*u - 945705*B^2*C - 240780*B^2*u^2*w - 240780*B^2*u*v^2 + 1498668*B^2*u*w + 749334*B^2*v^2 - 994854*B^2*w + 481560*B*C*u^2*v - 2997336*B*C*u*v + 1989708*B*C*v - 160520*B*D*u^3 + 1498668*B*D*u^2 - 1989708*B*D*u + 630470*B*D - 481560*B*u*v*w - 80260*B*v^3 + 1498668*B*v*w - 80260*C^2*u^3 + 749334*C^2*u^2 - 994854*C^2*u + 315235*C^2 + 240780*C*u^2*w + 240780*C*u*v^2 - 1498668*C*u*w - 749334*C*v^2 + 994854*C*w - 240780*D*u^2*v + 1498668*D*u*v - 994854*D*v - 240780*u*w^2 - 240780*v^2*w + 749334*w^2=0)
    : False := by
  have hu : u=7/2 := by linear_combination (-1/2) *h2
  rw [hu] at h3
  have hv : v= -229*B/102 := by linear_combination (-1/51) *h3
  rw [hu,hv] at h4
  have hw : w=27613*B^2/7803 - 349*C/36 := by linear_combination (1/9) *h4
  rw [hu,hv,hw] at h5
  have hD : D= -5759782*B^3/350596593 + 63721*B*C/404379 := by linear_combination (2/6167) *h5
  rw [hu,hv,hw,hD] at h6
  have last : 57267942405537375*C^2-37184217741575850*B^2*C+6035070335795303*B^4=0 := by linear_combination (17880426243/2)*h6
  apply rational (C/B^2)
  calc
    _ = (57267942405537375*C^2-37184217741575850*B^2*C+6035070335795303*B^4)/B^4 := by
      field_simp [bn] <;> ring
    _ = 0 := by rw [last,zero_div]
end EvenObstruction238

namespace EvenMoment238
def j2 (A P : ℚ) : ℚ := 7*A^2 - 2*P
def j3 (A P : ℚ) : ℚ := 64*A^3 - 51*A*P
def j4 (A P : ℚ) : ℚ := 65*A^4 - 96*A^2*P + 15*P^2
def j5 (A P : ℚ) : ℚ := 651*A^5 - 1482*A^3*P + 622*A*P^2
def j6 (A P : ℚ) : ℚ := 315235*A^6 - 994854*A^4*P + 749334*A^2*P^2 - 80260*P^3
def det (a b c x y z : ℚ) := (b-c)*x+(c-a)*y+(a-b)*z
theorem exclusion (a b c p q r : ℚ) (ab : a≠b) (ac : a≠c) (bc : b≠c) (positive : a+b+c≠0)
    (v2 : det a b c (j2 a p) (j2 b q) (j2 c r)=0)
    (v3 : det a b c (j3 a p) (j3 b q) (j3 c r)=0)
    (v4 : det a b c (j4 a p) (j4 b q) (j4 c r)=0)
    (v5 : det a b c (j5 a p) (j5 b q) (j5 c r)=0)
    (v6 : det a b c (j6 a p) (j6 b q) (j6 c r)=0)
    : False := by
  let U := p/((a-b)*(a-c))+q/((b-a)*(b-c))+r/((c-a)*(c-b))
  let V := -(b+c)*p/((a-b)*(a-c))-(a+c)*q/((b-a)*(b-c))-(a+b)*r/((c-a)*(c-b))
  let W := b*c*p/((a-b)*(a-c))+a*c*q/((b-a)*(b-c))+a*b*r/((c-a)*(c-b))
  have ab' := sub_ne_zero.mpr ab
  have ba' := sub_ne_zero.mpr (Ne.symm ab)
  have ac' := sub_ne_zero.mpr ac
  have ca' := sub_ne_zero.mpr (Ne.symm ac)
  have bc' := sub_ne_zero.mpr bc
  have cb' := sub_ne_zero.mpr (Ne.symm bc)
  have av : U*a^2+V*a+W=p := by dsimp [U,V,W]; field_simp [ab',ba',ac',ca',bc',cb'] <;> ring
  have bv : U*b^2+V*b+W=q := by dsimp [U,V,W]; field_simp [ab',ba',ac',ca',bc',cb'] <;> ring
  have cv : U*c^2+V*c+W=r := by dsimp [U,V,W]; field_simp [ab',ba',ac',ca',bc',cb'] <;> ring
  let B := a+b+c
  let C := a*b+a*c+b*c
  let D := a*b*c
  let M := (a-b)*(a-c)*(b-c)
  have nz : M≠0 := mul_ne_zero (mul_ne_zero ab' ac') bc'
  apply EvenObstruction238.jets B C D U V W positive
  · have identity : det a b c (j2 a (U*a^2+V*a+W)) (j2 b (U*b^2+V*b+W)) (j2 c (U*c^2+V*c+W)) = M*(7 - 2*U) := by
      dsimp only [det,j2,M,B,C,D]
      ring
    rw [av,bv,cv,v2] at identity
    exact (mul_eq_zero.mp identity.symm).resolve_left nz
  · have identity : det a b c (j3 a (U*a^2+V*a+W)) (j3 b (U*b^2+V*b+W)) (j3 c (U*c^2+V*c+W)) = M*(-51*B*U + 64*B - 51*V) := by
      dsimp only [det,j3,M,B,C,D]
      ring
    rw [av,bv,cv,v3] at identity
    exact (mul_eq_zero.mp identity.symm).resolve_left nz
  · have identity : det a b c (j4 a (U*a^2+V*a+W)) (j4 b (U*b^2+V*b+W)) (j4 c (U*c^2+V*c+W)) = M*(15*B^2*U^2 - 96*B^2*U + 65*B^2 + 30*B*U*V - 96*B*V - 15*C*U^2 + 96*C*U - 65*C + 30*U*W + 15*V^2 - 96*W) := by
      dsimp only [det,j4,M,B,C,D]
      ring
    rw [av,bv,cv,v4] at identity
    exact (mul_eq_zero.mp identity.symm).resolve_left nz
  · have identity : det a b c (j5 a (U*a^2+V*a+W)) (j5 b (U*b^2+V*b+W)) (j5 c (U*c^2+V*c+W)) = M*(622*B^3*U^2 - 1482*B^3*U + 651*B^3 + 1244*B^2*U*V - 1482*B^2*V - 1244*B*C*U^2 + 2964*B*C*U - 1302*B*C + 1244*B*U*W + 622*B*V^2 - 1482*B*W - 1244*C*U*V + 1482*C*V + 622*D*U^2 - 1482*D*U + 651*D + 1244*V*W) := by
      dsimp only [det,j5,M,B,C,D]
      ring
    rw [av,bv,cv,v5] at identity
    exact (mul_eq_zero.mp identity.symm).resolve_left nz
  · have identity : det a b c (j6 a (U*a^2+V*a+W)) (j6 b (U*b^2+V*b+W)) (j6 c (U*c^2+V*c+W)) = M*(-80260*B^4*U^3 + 749334*B^4*U^2 - 994854*B^4*U + 315235*B^4 - 240780*B^3*U^2*V + 1498668*B^3*U*V - 994854*B^3*V + 240780*B^2*C*U^3 - 2248002*B^2*C*U^2 + 2984562*B^2*C*U - 945705*B^2*C - 240780*B^2*U^2*W - 240780*B^2*U*V^2 + 1498668*B^2*U*W + 749334*B^2*V^2 - 994854*B^2*W + 481560*B*C*U^2*V - 2997336*B*C*U*V + 1989708*B*C*V - 160520*B*D*U^3 + 1498668*B*D*U^2 - 1989708*B*D*U + 630470*B*D - 481560*B*U*V*W - 80260*B*V^3 + 1498668*B*V*W - 80260*C^2*U^3 + 749334*C^2*U^2 - 994854*C^2*U + 315235*C^2 + 240780*C*U^2*W + 240780*C*U*V^2 - 1498668*C*U*W - 749334*C*V^2 + 994854*C*W - 240780*D*U^2*V + 1498668*D*U*V - 994854*D*V - 240780*U*W^2 - 240780*V^2*W + 749334*W^2) := by
      dsimp only [det,j6,M,B,C,D]
      ring
    rw [av,bv,cv,v6] at identity
    exact (mul_eq_zero.mp identity.symm).resolve_left nz
end EvenMoment238
