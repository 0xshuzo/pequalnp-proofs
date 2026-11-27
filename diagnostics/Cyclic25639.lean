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
theorem doubleF : ∀ x : F, x+x=0 := by decide +kernel
def Period {A : Type*} (k : Nat) (a : Nat → A) := ∀ i, a (i+k) = a i

theorem per_iter {A : Type*} {a : Nat → A} {k : Nat} (h : Period k a)
    (s q : Nat) : a (s+q*k) = a s := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, ← Nat.add_assoc, h, ih]

theorem per_reduce {A : Type*} {a : Nat → A} {k : Nat} (h : Period k a)
    (n d : Nat) : a (n+d) = a (n%k+d) := by
  have eq : n+d = (n%k+d) + (n/k)*k := by
    have := Nat.mod_add_div n k
    rw [Nat.mul_comm (n/k) k]
    omega
  rw [eq, per_iter h]

def readAt {k : Nat} (hk : 0<k) (x : W k) (n : Nat) := x (ix hk n)
theorem at_per {k : Nat} (hk : 0<k) (x : W k) : Period k (readAt hk x) := by
  intro n
  simp [readAt,ix]

theorem idx_add {k : Nat} (hk : 0<k) (n d : Nat) :
    ix hk ((n%k)+d) = ix hk (n+d) := by
  apply Fin.ext
  exact Nat.mod_add_mod n k d

theorem ret {k : Nat} (hk : 0<k) (n s : Nat) :
    (((n+s)%k+k-s%k)%k) = n%k := by
  have hn := Nat.mod_lt n hk
  have hs := Nat.mod_lt s hk
  rw [Nat.add_mod n s]
  by_cases hc : n%k+s%k<k
  · rw [Nat.mod_eq_of_lt hc, show n%k+s%k+k-s%k=n%k+k by omega]
    simp
  · have hh : n%k+s%k-k<k := by omega
    rw [Nat.mod_eq_sub_mod (by omega : k ≤ n%k+s%k), Nat.mod_eq_of_lt hh,
      show n%k+s%k-k+k-s%k=n%k by omega, Nat.mod_eq_of_lt hn]

theorem rotAt {k : Nat} (hk : 0<k) (s : Nat) (x : W k) (n : Nat) :
    readAt hk (rot hk s x) (n+s) = readAt hk x n := by
  change x (ix hk ((n+s)%k+k-s%k))=x (ix hk n)
  apply congrArg x
  apply Fin.ext
  exact ret hk n s

theorem mixAt {k : Nat} (hk : 0<k) (s : Nat) (x : W k) (n : Nat) :
    readAt hk (mix hk s x) (n+s) =
      readAt hk x (n+s) + readAt hk x (n+s+s) + readAt hk x n := by
  change _+x (ix hk ((n+s)%k+s))+x (ix hk ((n+s)%k+k-s%k)) = _
  rw [idx_add]
  have hh : ix hk ((n+s)%k+k-s%k) = ix hk n := Fin.ext (ret hk n s)
  rw [hh]
  rfl

def trace {k : Nat} (hk : 0<k) : W k →ₗ[F] W k where
  toFun x i := readAt hk x i.val+readAt hk x (i.val+1)+readAt hk x (i.val+2)
  map_add' x y := by ext i; change (_+_)+(_+_)+(_+_) = (_+_+_)+(_+_+_); abel
  map_smul' c x := by ext i; simp [readAt,Pi.smul_apply,smul_add]

theorem traceAt {k : Nat} (hk : 0<k) (x : W k) (n : Nat) :
    readAt hk (trace hk x) n = readAt hk x n+readAt hk x (n+1)+readAt hk x (n+2) := by
  change x (ix hk (n%k))+x (ix hk (n%k+1))+x (ix hk (n%k+2)) = _
  rw [idx_add,idx_add]
  simp [ix,readAt]

theorem rowAt {k : Nat} (hk : 0<k) (x : W k) (n : Nat) :
    readAt hk (mix hk 1 (rot hk 1 x)) (n+2) = readAt hk (trace hk x) n := by
  rw [traceAt, mixAt hk 1 _ (n+1), rotAt hk 1 x (n+1), rotAt hk 1 x (n+2), rotAt hk 1 x n]
  abel

theorem columnAt {k : Nat} (hk : 0<k) (x : W k) (n : Nat) :
    readAt hk (mix hk 2 (rot hk 3 x)) (n+5) =
      readAt hk (trace hk x) n+readAt hk (trace hk x) (n+1)+readAt hk (trace hk x) (n+2) := by
  rw [mixAt hk 2 _ (n+3), rotAt hk 3 x (n+2),rotAt hk 3 x (n+4),rotAt hk 3 x n]
  simp only [traceAt]
  have h1 := doubleF (readAt hk x (n+1))
  have h2 := doubleF (readAt hk x (n+2))
  have h3 := doubleF (readAt hk x (n+3))
  linear_combination -h1-h2-h3

theorem traceInj {k : Nat} (hk : 0<k) (hmod : k%3 ≠ 0) :
    Function.Injective (trace hk) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hzero : trace hk x = 0 := hx
  let u := readAt hk x
  have eq : ∀ n, u n + u (n+1) + u (n+2) = 0 := by
    intro n
    rw [← traceAt, hzero]
    rfl
  have p3 : Period 3 u := by
    intro n
    have h := eq n
    have h' := eq (n+1)
    linear_combination h'-h
  have shift : ∀ n, u (n+(k%3)) = u n := by
    intro n
    have z := per_reduce p3 k n
    rw [Nat.add_comm k n, Nat.add_comm (k%3) n, at_per hk x n] at z
    exact z.symm
  have p1 : ∀ n, u (n+1)=u n := by
    have bound := Nat.mod_lt k (by decide : 0<3)
    rcases (show k%3=1 ∨ k%3=2 by omega) with e|e
    · simpa only [e] using shift
    · intro n
      have he := shift (n+1)
      rw [e] at he
      exact he.symm.trans (p3 n)
  funext i
  have h := eq i.val
  rw [show u (i.val+2)=u (i.val+1) from p1 (i.val+1),p1, doubleF,zero_add] at h
  change x i = 0
  have hi : ix hk i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa [u,readAt,hi] using h

noncomputable def traceEquiv {k : Nat} (hk : 0<k) (hmod : k%3 ≠ 0) : W k ≃ₗ[F] W k :=
  LinearEquiv.ofBijective (trace hk) ⟨traceInj hk hmod, Finite.surjective_of_injective _ (traceInj hk hmod)⟩

end PEqualNP.Outside.L_meta_25639
