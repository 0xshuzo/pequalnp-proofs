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

def lastI {a} (ha : 0<a) : Fin a := ⟨a-1,by omega⟩
open scoped BigOperators
abbrev F := ZMod 2
abbrev W (n : Nat) := Fin n → F
def coord {n : Nat} (U : Submodule F (W n)) (i : Fin n) : U →ₗ[F] F :=
  (LinearMap.proj i).comp U.subtype
noncomputable def colors {n : Nat} (U : Submodule F (W n)) : Finset (U →ₗ[F] F) := by
  classical
  exact (Finset.univ.image (coord U)).erase 0

theorem mem_colors {n} {U : Submodule F (W n)} {c : U →ₗ[F] F} :
    c ∈ colors U ↔ c ≠ 0 ∧ ∃ i, coord U i=c := by
  classical
  simp [colors]

def encode {n : Nat} (U : Submodule F (W n)) : U →ₗ[F] (↥(colors U) → F) where
  toFun u c := c.val u
  map_add' u v := by funext c; exact map_add c.val u v
  map_smul' b u := by funext c; exact map_smul c.val b u

theorem encode_inj {n : Nat} (U : Submodule F (W n)) : Function.Injective (encode U) := by
  intro x y h
  apply Subtype.ext; funext i
  change coord U i x=coord U i y
  by_cases z : coord U i=0
  · rw [z];rfl
  · exact congrFun h ⟨coord U i,mem_colors.mpr ⟨z,i,rfl⟩⟩

theorem rank_le_colors {n : Nat} (U : Submodule F (W n)) :
    Module.finrank F U ≤ (colors U).card := by
  have rank := LinearMap.finrank_le_finrank_of_injective (encode_inj U)
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using rank

theorem isotropic_labels {n : Nat} (U : Submodule F (W n)) {i j : Fin n}
    (ortho : ∀ x ∈ U, ∀ y ∈ U, x i*y j=x j*y i) :
    coord U i=0 ∨ coord U j=0 ∨ coord U i=coord U j := by
  let L := coord U i
  let R := coord U j
  have bin : ∀ b : F, b=0 ∨ b=1 := by decide +kernel
  have det (u v : U) : L u * R v=R u * L v := ortho u u.property v v.property
  by_cases hL : L=0
  · exact Or.inl hL
  · have ex : ∃ u, L u ≠ 0 := by
      by_contra! h
      exact hL (LinearMap.ext fun u => h u)
    obtain ⟨u,hu⟩ := ex
    have Lu := (bin (L u)).resolve_left hu
    rcases bin (R u) with z | e
    · right;left;ext v
      exact (by simpa [Lu,z] using det u v : R v=0)
    · right;right;ext v
      exact (by simpa [Lu,e] using (det u v).symm : L v=R v)


theorem site_one_inj {a} : Function.Injective (fun s : Fin (N a) => site s 1) := by
  intro s t he
  have eq : site (site s 1) (N a-1)=site (site t 1) (N a-1) := congrArg (fun i => site i (N a-1)) he
  simpa only [site_comp,show 1+(N a-1)=N a by dsimp [N];omega,site_full] using eq

theorem site_offsets_inj {a} (s : Fin (N a)) {i j : Nat} (hi : i<N a) (hj : j<N a)
    (eq : site s i=site s j) : i=j := by
  have e : s+(⟨i,hi⟩ : Fin (N a))=s+(⟨j,hj⟩ : Fin (N a)) := eq
  exact congrArg Fin.val (add_left_cancel e)

theorem domino {a : Nat} (D : Finset (Fin (N a))) (large : a≤D.card)
    (apart : ∀ i ∈ D, site i 1 ∉ D) :
    D.card=a ∧ ∃ u : Fin (N a), ∀ j : Fin a,
      site u (2*j.val+1)∈D ∧ site u (2*j.val+2)∉D := by
  classical
  let E := D.image (fun i => site i 1)
  have dis : Disjoint D E := by
    apply Finset.disjoint_left.mpr
    intro x hx he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    exact apart p hp hx
  have count : E.card=D.card := Finset.card_image_of_injective _ site_one_inj
  have union := Finset.card_union_of_disjoint dis
  have room : (D∪E).card≤N a := (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have dc : D.card=a := by dsimp [N] at room;omega
  refine ⟨dc,?_⟩
  have one : ((D∪E)ᶜ).card=1 := by
    rw [Finset.card_compl,Fintype.card_fin,union,count,dc]
    dsimp [N];omega
  obtain ⟨u,eq⟩ := Finset.card_eq_one.mp one
  have out : u∉D∪E := by
    have : u∈(D∪E)ᶜ := by rw [eq];simp
    exact Finset.mem_compl.mp this
  have comp {i : Fin (N a)} (ne : i≠u) : i∈D∪E := by
    by_contra h
    have ic := Finset.mem_compl.mpr h
    rw [eq] at ic
    exact ne (Finset.mem_singleton.mp ic)
  have after (d : Nat) (hl : d+1<N a) (pre : site u d∉D) : site u (d+1)∈D := by
    have ne : site u (d+1) ≠ u := by
      intro h
      have bad := site_offsets_inj u hl (Nat.succ_pos _) (h.trans (site_zero u).symm)
      omega
    rcases Finset.mem_union.mp (comp ne) with yes|no
    · exact yes
    · obtain ⟨p,hp,hq⟩ := Finset.mem_image.mp no
      have h := site_one_inj (hq.trans (site_comp u d 1).symm)
      exact (pre (h ▸ hp)).elim
  have odds (j : Nat) (hj : j<a) : site u (2*j+1)∈D := by
    induction j with
    | zero =>
      apply after 0 (by dsimp [N];omega)
      simpa only [site_zero] using (fun hu => out (Finset.mem_union_left _ hu) : u∉D)
    | succ j ih =>
      have hi := ih (by omega)
      have hn := apart _ hi
      rw [site_comp] at hn
      have sub := after (2*j+1+1) (by dsimp [N];omega) hn
      convert sub using 1 <;> congr 2 <;> omega
  refine ⟨u,fun j => ⟨odds j.val j.isLt,?_⟩⟩
  simpa only [site_comp,show 2*j.val+1+1=2*j.val+2 by omega] using apart _ (odds j.val j.isLt)
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
  unfold evenSite oddSite; rw [site_comp] <;> congr 1 <;> omega
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
    · subst j
      cases b <;> simp [mul_ite] at e ⊢
      · exact e
      · exact (show ∀ p q : F, p+q=0 → q=p by decide +kernel) _ _ e
    · cases b <;> simpa [mul_ite,last,Ne.symm last] using e
  · intro ok x k
    rw [model_sum]
    simp_rw [fun j => congrFun (ok j) k]
    cases b <;> simp [ite_apply,ite_mul]
    exact (show ∀ p : F, p+p=0 by decide +kernel) _

def Success {a m} (h : Fin (N a) → Fin m → F) : Prop :=
  ∃ U : Submodule F (W (N a)), Module.finrank F U=a ∧
    (∀ x ∈ U, ∀ k, ∑ i, h i k*x i=0) ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ i, x i*y (site i 1)=x (site i 1)*y i

theorem success_shape {a m} (ha : 2≤a) (h : Fin (N a) → Fin m → F) :
    Success h ↔ ∃ u b, allowed (by omega : 0<a) h u b := by
  classical
  have hp : 0<a := by omega
  constructor
  · rintro ⟨U,dim,checks,iso⟩
    let f := coord U
    have adj (i : Fin (N a)) : f i=0 ∨ f (site i 1)=0 ∨ f i=f (site i 1) :=
      isotropic_labels U (fun x hx y hy => iso x hx y hy i)
    let D := Finset.univ.filter (fun i => f i=0 ∧ f (site i 1)≠0)
    have mem (i) : i∈D ↔ f i=0 ∧ f (site i 1)≠0 := by simp [D]
    have colsz : a≤(colors U).card := dim ▸ rank_le_colors U
    have cover : colors U ⊆ D.image (fun v => f (site v 1)) := by
      intro c hc
      obtain ⟨nz,i,atI⟩ := mem_colors.mp hc
      have diff : ∃ j, f j≠c := by
        by_contra! all
        have sub : colors U ⊆ {c} := by
          intro z hz
          obtain ⟨_,i,e⟩ := mem_colors.mp hz
          simpa using e.symm.trans (all i)
        have sz := Finset.card_le_card sub
        rw [Finset.card_singleton] at sz
        omega
      obtain ⟨j,hj⟩ := diff
      obtain ⟨d,_,eq⟩ := offsets j i
      have walk (d : Nat) (hit : f (site j d)=c) : c∈D.image (fun v => f (site v 1)) := by
        induction d with
        | zero => exact (hj (by simpa [site_zero] using hit)).elim
        | succ p ih =>
          by_cases pre : f (site j p)=c
          · exact ih pre
          · have nt : f (site (site j p) 1)=c := by simpa only [site_comp] using hit
            have z : f (site j p)=0 := (adj (site j p)).resolve_right (by
              rintro (e|e)
              · exact nz (nt.symm.trans e)
              · exact pre (e.trans nt))
            exact Finset.mem_image.mpr ⟨site j p,(mem _).mpr ⟨z,fun e => nz (nt.symm.trans e)⟩,nt⟩
      exact walk d (eq ▸ atI)
    have large := colsz.trans ((Finset.card_le_card cover).trans Finset.card_image_le)
    obtain ⟨_,u,tiling⟩ := domino D large (fun i hi bad => ((mem i).mp hi).2 ((mem _).mp bad).1)
    have zeros (j : Fin a) : f (oddSite u j)=0 := ((mem _).mp (tiling j).1).1
    have alive (j : Fin a) : f (evenSite u j)≠0 := by
      have v := ((mem _).mp (tiling j).1).2
      simpa only [←next_odd] using v
    have edge := adj (evenSite u (lastI hp))
    rw [last_even hp] at edge
    obtain hroot | hroot := edge.resolve_left (alive _)
    all_goals
      have rootChoice : ∃ b : Bool, ∀ x : U, x.val u =
          (if b then x.val (evenSite u (lastI hp)) else 0) := by
        first
        | exact ⟨false,fun x => LinearMap.congr_fun hroot x⟩
        | exact ⟨true,fun x => (LinearMap.congr_fun hroot x).symm⟩
      obtain ⟨b,root⟩ := rootChoice
      let ev : U →ₗ[F] (Fin a → F) :=
        {toFun := fun x j => x.val (evenSite u j)
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl}
      have modelEq (x : U) : model hp u b (ev x)=x.val := by
        funext i
        obtain ⟨p,rfl⟩ := (chart u).surjective i
        rcases p with _|⟨j,c⟩
        · exact (at_root hp u b (ev x)).trans (root x).symm
        · cases c
          · exact (at_odd hp u b (ev x) j).trans (LinearMap.congr_fun (zeros j) x).symm
          · exact at_even hp u b (ev x) j
      have inj : Function.Injective ev := fun x y eq => Subtype.ext
        ((modelEq x).symm.trans ((congrArg (model hp u b) eq).trans (modelEq y)))
      have onto : Function.Surjective ev := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [dim,Module.finrank_fin_fun])).mp inj
      refine ⟨u,b,(model_checked hp h u b).mp ?_⟩
      intro x k
      obtain ⟨y,rfl⟩ := onto x
      simpa only [modelEq y] using checks y.val y.property k
  · rintro ⟨u,b,ok⟩
    refine ⟨LinearMap.range (model hp u b),?_,?_,?_⟩
    · rw [LinearMap.finrank_range_of_inj (model_inj hp u b),Module.finrank_fin_fun]
    · rintro _ ⟨x,rfl⟩ k
      exact (model_checked hp h u b).mpr ok x k
    · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ i
      exact model_iso hp u b x y i

end PEqualNP.Outside.L_lib_865_aux
