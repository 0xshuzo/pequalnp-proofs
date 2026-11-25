import Mathlib
namespace Obstruction238
theorem finite : ∀ a b : ZMod 11,
   17669503985435881075*a^2-11677408853106621058*a*b+1929338843037258043*b^2=0 → a=0 ∧ b=0 := by decide +kernel
theorem rational (y : ℚ) : 17669503985435881075*y^2-11677408853106621058*y+1929338843037258043≠0 := by
  intro h
  have den : (y.den:ℚ)≠0 := by exact_mod_cast y.den_nz
  have frac : (y.num:ℚ)/(y.den:ℚ)=y := Rat.num_div_den y
  have raw : 17669503985435881075*(y.num:ℚ)^2-11677408853106621058*(y.num:ℚ)*(y.den:ℚ)
       +1929338843037258043*(y.den:ℚ)^2=0 := by
    calc
      _ = (y.den:ℚ)^2*(17669503985435881075*y^2-11677408853106621058*y+1929338843037258043) := by
        conv_rhs => rw [←frac]
        field_simp [den] <;> ring
      _ = 0 := by rw [h,mul_zero]
  have integral : 17669503985435881075*y.num^2-11677408853106621058*y.num*(y.den:ℤ)
       +1929338843037258043*(y.den:ℤ)^2=0 := by exact_mod_cast raw
  have z := congrArg (fun k : ℤ => (k : ZMod 11)) integral
  push_cast at z
  have zeros := finite (y.num : ZMod 11) (y.den : ZMod 11) z
  have hn : (11 : ℤ) ∣ y.num := by
    first | exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp zeros.1 | exact?
  have hd : 11 ∣ y.den := by
    first | exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp zeros.2 | exact?
  obtain ⟨k,hk⟩ := hn
  have hn' : 11 ∣ y.num.natAbs := ⟨k.natAbs,by rw [hk,Int.natAbs_mul]; rfl⟩
  have cop := y.reduced
  have bad := Nat.dvd_gcd hn' hd
  rw [cop.gcd_eq_one] at bad
  norm_num at bad

theorem jets (B C D u v w : ℚ) (bn : B≠0)
    (h2 : 31 - 10*u=0)
    (h3 : -115*B*u + 134*B - 115*v=0)
    (h4 : 365*B^2*u^2 - 2228*B^2*u + 1443*B^2 + 730*B*u*v - 2228*B*v - 365*C*u^2 + 2228*C*u - 1443*C + 730*u*w + 365*v^2 - 2228*w=0)
    (h5 : 12170*B^3*u^2 - 28438*B^3*u + 12173*B^3 + 24340*B^2*u*v - 28438*B^2*v - 24340*B*C*u^2 + 56876*B*C*u - 24346*B*C + 24340*B*u*w + 12170*B*v^2 - 28438*B*w - 24340*C*u*v + 28438*C*v + 12170*D*u^2 - 28438*D*u + 12173*D + 24340*v*w=0)
    (h6 : -84660*B^4*u^3 + 809318*B^4*u^2 - 1066694*B^4*u + 333083*B^4 - 253980*B^3*u^2*v + 1618636*B^3*u*v - 1066694*B^3*v + 253980*B^2*C*u^3 - 2427954*B^2*C*u^2 + 3200082*B^2*C*u - 999249*B^2*C - 253980*B^2*u^2*w - 253980*B^2*u*v^2 + 1618636*B^2*u*w + 809318*B^2*v^2 - 1066694*B^2*w + 507960*B*C*u^2*v - 3237272*B*C*u*v + 2133388*B*C*v - 169320*B*D*u^3 + 1618636*B*D*u^2 - 2133388*B*D*u + 666166*B*D - 507960*B*u*v*w - 84660*B*v^3 + 1618636*B*v*w - 84660*C^2*u^3 + 809318*C^2*u^2 - 1066694*C^2*u + 333083*C^2 + 253980*C*u^2*w + 253980*C*u*v^2 - 1618636*C*u*w - 809318*C*v^2 + 1066694*C*w - 253980*D*u^2*v + 1618636*D*u*v - 1066694*D*v - 253980*u*w^2 - 253980*v^2*w + 809318*w^2=0)
    : False := by
  have hu : u=31/10 := by linear_combination (-1/10) *h2
  rw [hu] at h3
  have hv : v= -89*B/46 := by linear_combination (-1/115) *h3
  rw [hu,hv] at h4
  have hw : w=1739173*B^2/92575 - 5589*C/100 := by linear_combination (1/35) *h4
  rw [hu,hv,hw] at h5
  have hD : D=2781751458*B^3/19384890245 - 242953*B*C/747845 := by linear_combination (10/409689) *h5
  rw [hu,hv,hw,hD] at h6
  have last : 17669503985435881075*C^2-11677408853106621058*B^2*C+1929338843037258043*B^4=0 := by linear_combination (227475752875/2)*h6
  apply rational (C/B^2)
  calc
    _ = (17669503985435881075*C^2-11677408853106621058*B^2*C+1929338843037258043*B^4)/B^4 := by
      field_simp [bn] <;> ring
    _ = 0 := by rw [last,zero_div]
end Obstruction238
