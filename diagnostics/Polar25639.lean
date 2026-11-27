import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25639
abbrev F := ZMod 2
abbrev W (k : Nat) := Fin k → F
def ix {k : Nat} (hk : 0<k) (n : Nat) : Fin k := ⟨n%k, Nat.mod_lt _ hk⟩
def rot {k : Nat} (hk : 0<k) (s : Nat) : W k →ₗ[F] W k where
  toFun x i := x (ix hk (i.val+k-s%k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def mix {k : Nat} (hk : 0<k) (s : Nat) : W k →ₗ[F] W k where
  toFun x i := x i+x (ix hk (i.val+s))+x (ix hk (i.val+k-s%k))
  map_add' x y := by ext i; change (_+_)+(_+_)+(_+_) = (_+_+_)+(_+_+_); abel
  map_smul' c x := by ext i; simp [Pi.smul_apply, smul_add]
def qstep {k : Nat} (hk : 0<k) (x : W k) (i : Fin k) :=
  x i+(1+x (ix hk (i.val+1)))*x (ix hk (i.val+2))
def output {k : Nat} (hk : 0<k) (row col c₁ c₂ key : W k) : W k × W k :=
  (qstep hk (mix hk 1 (rot hk 1 key + row)) + key+c₁,
   qstep hk (mix hk 2 (rot hk 3 key + col)) + rot hk 4 key+c₂)
def obs {D : Type*} [AddCommGroup D] [Module F D] {k : Nat} (hk : 0<k)
    (s t : Nat) (L : D →ₗ[F] W k) (i : Nat) : D →ₗ[F] F :=
  (LinearMap.proj (ix hk i)).comp ((mix hk s).comp ((rot hk t).comp L))
def Compat {A : Type*} [Zero A] (a b : A) : Prop := a=0 ∨ b=0 ∨ a=b

theorem doubleF : ∀ x : F, x+x=0 := by decide +kernel
theorem dichF : ∀ x : F, x=0 ∨ x=1 := by decide +kernel

theorem compat_iff {D : Type*} [AddCommGroup D] [Module F D] (a b : D →ₗ[F] F) :
    Compat a b ↔ ∀ u v, a u*b v+a v*b u=0 := by
  constructor
  · rintro (rfl|rfl|rfl) u v
    · simp
    · simp
    · simpa only [mul_comm (a v) (a u)] using doubleF (a u*a v)
  · intro h
    by_cases hz : a=0
    · exact Or.inl hz
    · have ex : ∃ u, a u ≠ 0 := by
        by_contra! HH
        apply hz
        ext u
        exact HH u
      obtain ⟨u,hu⟩ := ex
      have hone := (dichF (a u)).resolve_left hu
      rcases dichF (b u) with h0|h1
      · right; left; ext v
        simpa [hone,h0] using h u v
      · right; right; ext v
        have hh : b v + a v = 0 := by simpa [hone,h1] using h u v
        calc a v = (b v+b v)+a v := by rw [doubleF,zero_add]
             _ = b v := by rw [add_assoc,hh,add_zero]

def FlatAlong {k : Nat} {D : Type*} [AddCommGroup D] [Module F D]
    (o : W k → W k × W k) (L : D →ₗ[F] W k) (base : W k) :=
  ∃ f : D →ₗ[F] (W k × W k), ∀ u, o (base+L u)=o base+f u

theorem flatDiff {k : Nat} {D : Type*} [AddCommGroup D] [Module F D]
    (o : W k → W k × W k) (L : D →ₗ[F] W k) (base : W k) :
    FlatAlong o L base ↔ ∀ u v,
      o (base+L u+L v) - o (base+L u) - o (base+L v) + o base = 0 := by
  constructor
  · rintro ⟨f,hf⟩ u v
    rw [add_assoc, ← map_add, hf, hf, hf, map_add]
    abel
  · intro h
    let d := fun u => o (base+L u)-o base
    have hd : ∀ u v, d (u+v)=d u+d v := by
      intro u v
      dsimp [d]
      rw [map_add, ← add_assoc]
      have hh := h u v
      abel_nf at hh ⊢
      exact sub_eq_zero.mp (by linear_combination hh)
    refine ⟨{ toFun := d, map_add' := hd, map_smul' := ?_ }, ?_⟩
    · intro c u
      rcases dichF c with rfl|rfl <;> simp [d]
    · intro u
      change _ = o base+(o (base+L u)-o base)
      abel

theorem coordPolar {k : Nat} (hk : 0<k) (s t : Nat) (r c : W k)
    (M : W k →ₗ[F] W k) (b u v : W k) (i : Fin k) :
    let H := fun x => qstep hk (mix hk s (rot hk t x+r)) i + M x i + c i
    H (b+u+v)-H (b+u)-H (b+v)+H b =
      (mix hk s (rot hk t u)) (ix hk (i.val+1)) * (mix hk s (rot hk t v)) (ix hk (i.val+2)) +
      (mix hk s (rot hk t v)) (ix hk (i.val+1)) * (mix hk s (rot hk t u)) (ix hk (i.val+2)) := by
  dsimp only
  simp only [qstep,map_add,Pi.add_apply]
  ring

theorem criterion {k : Nat} (hk : 0<k) {D : Type*} [AddCommGroup D] [Module F D]
    (L : D →ₗ[F] W k) (row col c₁ c₂ base : W k) :
    FlatAlong (output hk row col c₁ c₂) L base ↔
    (∀ i : Fin k, Compat (obs hk 1 1 L (i.val+1)) (obs hk 1 1 L (i.val+2))) ∧
    (∀ i : Fin k, Compat (obs hk 2 3 L (i.val+1)) (obs hk 2 3 L (i.val+2))) := by
  rw [flatDiff]
  constructor
  · intro h
    constructor
    · intro i
      apply (compat_iff _ _).mpr
      intro u v
      have h' := congrArg (fun z : W k × W k => z.1 i) (h u v)
      exact (coordPolar hk 1 1 row c₁ LinearMap.id base (L u) (L v) i).symm.trans h'
    · intro i
      apply (compat_iff _ _).mpr
      intro u v
      have h' := congrArg (fun z : W k × W k => z.2 i) (h u v)
      exact (coordPolar hk 2 3 col c₂ (rot hk 4) base (L u) (L v) i).symm.trans h'
  · rintro ⟨h1,h2⟩ u v
    apply Prod.ext
    · funext i
      exact (coordPolar hk 1 1 row c₁ LinearMap.id base (L u) (L v) i).trans ((compat_iff _ _).mp (h1 i) u v)
    · funext i
      exact (coordPolar hk 2 3 col c₂ (rot hk 4) base (L u) (L v) i).trans ((compat_iff _ _).mp (h2 i) u v)

end PEqualNP.Outside.L_meta_25639
