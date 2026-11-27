import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_865_aux

abbrev N (a : Nat) := 2*a+1
def site {a : Nat} (s : Fin (N a)) (d : Nat) : Fin (N a) :=
  ⟨(s.val+d) % N a, Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem site_zero {a} (s : Fin (N a)) : site s 0 = s := by
  apply Fin.ext; simp [site,Nat.mod_eq_of_lt s.isLt]

theorem site_comp {a} (s : Fin (N a)) (i j : Nat) : site (site s i) j = site s (i+j) := by
  apply Fin.ext
  simp [site, Nat.mod_add_mod, Nat.add_assoc]

theorem site_full {a} (s : Fin (N a)) : site s (N a) = s := by
  apply Fin.ext
  simp [site,Nat.mod_eq_of_lt s.isLt]

theorem offsets {a} (s t : Fin (N a)) :
    ∃ d < N a, site s d = t := by
  have hs := s.isLt
  have ht := t.isLt
  by_cases st : s.val ≤ t.val
  · refine ⟨t.val-s.val,by omega,Fin.ext ?_⟩
    change (s.val+(t.val-s.val)) % N a = t.val
    rw [show s.val+(t.val-s.val)=t.val by omega,Nat.mod_eq_of_lt ht]
  · refine ⟨N a+t.val-s.val,by omega,Fin.ext ?_⟩
    change (s.val+(N a+t.val-s.val)) % N a = t.val
    rw [show s.val+(N a+t.val-s.val)=t.val+N a by omega,Nat.add_mod_right,Nat.mod_eq_of_lt ht]

def Mark {a : Nat} {A : Type*} [Zero A] (h : Fin (N a) → A) (s : Fin (N a)) : Prop :=
  h s ≠ 0 ∧ (∀ d : Nat, 0 < d → d < a → h (site s d) = 0) ∧
    (h (site s a) = 0 ∨ h (site s a) = h s)

def Canon {a : Nat} {A : Type*} [Zero A] (h : Fin (N a) → A) (s : Fin (N a)) :=
  Mark h s ∧ ¬ Mark h (site s a)

theorem mark_spacing {a : Nat} {A : Type*} [Zero A] {h : Fin (N a) → A}
    {s : Fin (N a)} {d : Nat} (pos : 0<d) (lt : d<N a)
    (hs : Mark h s) (ht : Mark h (site s d)) : d=a ∨ d=a+1 := by
  have fwd : a≤d := by
    by_contra! small
    exact ht.1 (hs.2.1 d pos small)
  have rt : site (site s d) (N a-d) = s := by
    rw [site_comp,show d+(N a-d)=N a by omega,site_full]
  have rev : a≤N a-d := by
    by_contra! small
    exact hs.1 (rt ▸ (ht.2.1 _ (by omega) small))
  dsimp [N] at rev lt
  omega

theorem has_canon {a : Nat} {A : Type*} [Zero A] (ha : 2≤a) {h : Fin (N a) → A}
    {s : Fin (N a)} (hs : Mark h s) : ∃ t, Canon h t := by
  by_cases ht : Mark h (site s a)
  · refine ⟨site s a,ht,?_⟩
    intro bad
    rw [site_comp] at bad
    have eq := mark_spacing (d:=a+a) (by omega) (by dsimp [N];omega) hs bad
    omega
  · exact ⟨s,hs,ht⟩

theorem canon_unique {a : Nat} {A : Type*} [Zero A] {h : Fin (N a) → A}
    {s t : Fin (N a)} (hs : Canon h s) (ht : Canon h t) : s=t := by
  obtain ⟨d,lt,eq⟩ := offsets s t
  subst t
  by_cases zero : d=0
  · subst d; exact (site_zero s).symm
  have split := mark_spacing (d:=d) (by omega) lt hs.1 ht.1
  rcases split with e | e
  · subst d; exact (hs.2 ht.1).elim
  · subst d
    apply False.elim
    apply ht.2
    rw [site_comp,show a+1+a=N a by dsimp [N];omega,site_full]
    exact hs.1

abbrev F := ZMod 2
abbrev W (n : Nat) := Fin n → F
def lastI {a} (ha : 0<a) : Fin a := ⟨a-1,by omega⟩
def oddSite {a} (u : Fin (N a)) (j : Fin a) := site u (2*j.val+1)
def evenSite {a} (u : Fin (N a)) (j : Fin a) := site u (2*j.val+2)

def loc {a} (u : Fin (N a)) : Option (Fin a × Bool) → Fin (N a)
  | none => u
  | some (j,false) => oddSite u j
  | some (j,true) => evenSite u j

noncomputable def chart {a} (u : Fin (N a)) : Option (Fin a × Bool) ≃ Fin (N a) := by
  classical
  apply Equiv.ofBijective (loc u)
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro i
    obtain ⟨d,lt,rfl⟩ := offsets u i
    cases d with
    | zero => exact ⟨none,(site_zero u).symm⟩
    | succ j =>
      dsimp [N] at lt
      let k : Fin a := ⟨j/2,by omega⟩
      by_cases e : j%2=0
      · refine ⟨some (k,false),?_⟩
        change site u (2*(j/2)+1)=site u (j+1)
        congr 1;omega
      · refine ⟨some (k,true),?_⟩
        change site u (2*(j/2)+2)=site u (j+1)
        congr 1;omega
  · simp [N,Fintype.card_option,Fintype.card_prod,Nat.mul_comm]

theorem next_odd {a} (u : Fin (N a)) (j : Fin a) : site (oddSite u j) 1=evenSite u j := by
  unfold oddSite evenSite
  rw [site_comp]
theorem next_even {a} (u : Fin (N a)) (j : Fin a) (lt : j.val+1<a) :
    site (evenSite u j) 1=oddSite u ⟨j.val+1,lt⟩ := by
  unfold evenSite oddSite; rw [site_comp];congr 1;omega
theorem last_even {a} (ha : 0<a) (u : Fin (N a)) :
    site (evenSite u (lastI ha)) 1=u := by
  unfold evenSite lastI;rw [site_comp,show 2*(a-1)+2+1=N a by dsimp [N];omega,site_full]

def rawValue {a} (ha : 0<a) (b : Bool) (x : Fin a → F) : Option (Fin a × Bool) → F
  | none => if b then x (lastI ha) else 0
  | some (j,false) => 0
  | some (j,true) => x j

noncomputable def model {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) :
    (Fin a → F) →ₗ[F] W (N a) where
  toFun x i := rawValue ha b x ((chart u).symm i)
  map_add' x y := by
    funext i
    change rawValue ha b (x+y) ((chart u).symm i)=rawValue ha b x ((chart u).symm i)+rawValue ha b y ((chart u).symm i)
    rcases (chart u).symm i with _|⟨j,c⟩
    · cases b <;> simp [rawValue]
    · cases c <;> simp [rawValue]
  map_smul' r x := by
    funext i
    change rawValue ha b (r • x) ((chart u).symm i)=r • rawValue ha b x ((chart u).symm i)
    rcases (chart u).symm i with _|⟨j,c⟩
    · cases b <;> simp [rawValue]
    · cases c <;> simp [rawValue]

theorem at_chart {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) (x : Fin a → F) (p) :
    model ha u b x (chart u p)=rawValue ha b x p := by
  change rawValue ha b x ((chart u).symm (chart u p))=_
  rw [Equiv.symm_apply_apply]
theorem at_even {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) (x : Fin a → F) (j) :
    model ha u b x (evenSite u j)=x j := at_chart ha u b x (some (j,true))
theorem at_odd {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) (x : Fin a → F) (j) :
    model ha u b x (oddSite u j)=0 := at_chart ha u b x (some (j,false))
theorem at_root {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) (x : Fin a → F) :
    model ha u b x u=(if b then x (lastI ha) else 0) := at_chart ha u b x none

theorem model_inj {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) : Function.Injective (model ha u b) := by
  intro x y h;funext i
  simpa only [at_even] using congrFun h (evenSite u i)

theorem model_iso {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) (x y : Fin a → F) (i) :
    model ha u b x i * model ha u b y (site i 1)=model ha u b x (site i 1)*model ha u b y i := by
  obtain ⟨w,rfl⟩ := (chart u).surjective i
  rcases w with _|⟨j,c⟩
  · change model ha u b x u * model ha u b y (oddSite u ⟨0,ha⟩)=
        model ha u b x (oddSite u ⟨0,ha⟩)*model ha u b y u
    simp [at_odd]
  · cases c
    · change model ha u b x (oddSite u j)*model ha u b y (site (oddSite u j) 1)=_
      change _=model ha u b x (site (oddSite u j) 1)*model ha u b y (oddSite u j)
      simp [at_odd]
    · change model ha u b x (evenSite u j)*model ha u b y (site (evenSite u j) 1)=
          model ha u b x (site (evenSite u j) 1)*model ha u b y (evenSite u j)
      by_cases lt : j.val+1<a
      · rw [next_even u j lt];simp [at_odd]
      · have e : j=lastI ha := Fin.ext (by have := j.isLt; dsimp [lastI];omega)
        subst j
        rw [last_even ha,at_even,at_even,at_root,at_root]
        cases b <;> simp

def allowed {a m : Nat} (ha : 0<a) (h : Fin (N a) → Fin m → F) (u : Fin (N a)) (b : Bool) :=
  ∀ j : Fin a, h (evenSite u j) = (if j=lastI ha ∧ b=true then h u else 0)

theorem model_sum {a m : Nat} (ha : 0<a) (h : Fin (N a) → Fin m → F) (u : Fin (N a)) (b : Bool)
    (x : Fin a → F) (k : Fin m) :
    (∑ i, h i k * model ha u b x i) =
     h u k*(if b then x (lastI ha) else 0) + ∑ j, h (evenSite u j) k*x j := by
  rw [←Equiv.sum_comp (chart u) (fun i => h i k * model ha u b x i)]
  simp only [at_chart,Fintype.sum_option,Fintype.sum_prod_type,Fintype.sum_bool]
  change h u k*(if b then x (lastI ha) else 0)+_ = _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [rawValue,chart,loc,mul_zero]

theorem model_checked {a m} (ha : 0<a) (h : Fin (N a) → Fin m → F) (u) (b) :
    (∀ x k, ∑ i, h i k * model ha u b x i=0) ↔ allowed ha h u b := by
  classical
  constructor
  · intro checks j
    funext k
    have e := checks (fun t => if t=j then 1 else 0) k
    rw [model_sum] at e
    by_cases last : j = lastI ha
    · subst j;cases b <;> simp [mul_ite] at e ⊢
      exact (show ∀ p q : F, p+q=0 → q=p by decide +kernel) _ _ e
    · cases b <;> simpa [mul_ite,last,Ne.symm last] using e
  · intro ok x k
    rw [model_sum]
    simp_rw [fun j => congrFun (ok j) k]
    cases b <;> simp [ite_apply,ite_mul]
    exact (show ∀ p : F, p+p=0 by decide +kernel) _


end PEqualNP.Outside.L_lib_865_aux
