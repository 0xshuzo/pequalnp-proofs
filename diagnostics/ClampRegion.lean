import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9752.Engine
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)
def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))
theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))
theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy
theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]
theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega
def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]
theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih
theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

end PEqualNP.Outside.L_meta_9752.Engine
namespace PEqualNP.Outside.L_meta_9791.ClampRegion
open PEqualNP.Outside.L_meta_9752.Engine
theorem runs_respect {R} {p n : R} {v : Wire R} {k ws} (h : Run false v k ws)
    (ok : ∀ w∈ws, w p=true → w n=true) : v p=true → v n=true := by
  induction h using Run.ind with
  | stop => exact ok v (by simp)
  | perm p h ih => exact ih (fun w m => ok w (p.mem_iff.mp m))
  | @two k a b rest d hd ka kb h ih =>
    apply ih
    have aa := ok a (by simp)
    have bb := ok b (by simp)
    intro w hw
    rcases List.mem_cons.mp hw with rfl | z
    · have lim : d<2 := hd.resolve_right (fun z => Bool.noConfusion z.1)
      have cs : d=0 ∨ d=1 := by omega
      rcases cs with rfl|rfl
      · change (a p && b p)=true → (a n && b n)=true
        exact fun q => Bool.and_eq_true_iff.mpr ⟨aa (Bool.and_eq_true_iff.mp q).1,bb (Bool.and_eq_true_iff.mp q).2⟩
      · change (a p || b p)=true → (a n || b n)=true
        exact fun q => Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp q).imp aa bb)
    · rcases mem_kept z with rfl | t
      · exact aa
      · rcases mem_kept t with rfl | l
        · exact bb
        · exact ok w (by simp [l])

abbrev Points := Fin 7 → Bool
def mask (j : Fin 7) : Nat := ([3,12,21,26,38,41,48] : List Nat)[j.val]!
def blocked (q : Fin 64) (j : Fin 7) : Bool := decide ((q.val &&& mask j) ≠ 0)
def legal (q : Fin 64) : Prop :=
    ((!(blocked q 0) || !(blocked q 1))=true) ∧
    ((!(blocked q 0) || !(blocked q 6))=true)
instance (q : Fin 64) : Decidable (legal q) := by unfold legal; infer_instance
abbrev Selector := {q : Fin 64 // legal q}
def lineZero : Selector := ⟨1,by decide +kernel⟩
abbrev S := Selector × Points
abbrev R := S × Bool × Bool
def nb (q : Selector) (j : Fin 7) := blocked q.val j
def hit (r : S) := ∃ j : Fin 7, nb r.1 j=true ∧ r.2 j=true
instance (r : S) : Decidable (hit r) := by
  unfold hit
  infer_instance
def target : Wire S := fun r => decide (hit r)
def fill (q : Selector) : Points := fun j => !(nb q j)
def orig (r : S) : R := (r,r.2 0 || r.2 1,r.2 0 || r.2 6)
def clamp (r : S) : R := (r,true,true)
def lift (a : Wire S) : Wire R := fun r => a r.1
def hA : Wire R := fun r => r.2.1
def hB : Wire R := fun r => r.2.2
def bank (xs : List (Wire S)) : List (Wire R) := hA :: hB :: xs.map lift
def Increasing (a : Wire S) := ∀ (q : Selector) (p t : Points),
    (∀ j, p j=true → t j=true) → a (q,p)=true → a (q,t)=true

theorem helpers_covered (q : Selector) : orig (q,fill q)=clamp (q,fill q) := by
  have facts := q.property
  exact Prod.ext rfl (Prod.ext facts.1 facts.2)

theorem fill_negative (q : Selector) : ¬hit (q,fill q) := by
  rintro ⟨j,edge,h⟩
  change !(nb q j)=true at h
  simp [edge] at h

theorem clamped_correct {k : Nat} {goal : Wire R} {xs : List (Wire S)}
    (run : Run false goal k (bank xs)) (mons : ∀ a∈xs, Increasing a)
    (correct : ∀ r, goal (orig r)=true ↔ hit r) :
    restrictRows clamp goal = target := by
  funext r
  rcases r with ⟨q,p⟩
  by_cases hp : hit (q,p)
  · have t := (correct (q,p)).2 hp
    have order : ∀ a∈bank xs, a (orig (q,p))=true → a (clamp (q,p))=true := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl|hr
      · exact fun _ => rfl
      rcases List.mem_cons.mp hr with rfl|hr
      · exact fun _ => rfl
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
      exact fun h => h
    simpa [restrictRows,target,hp] using runs_respect run order t
  · have pt : ∀ j, p j=true → fill q j=true := by
      intro j hj
      cases e : nb q j with
      | false => simp [fill,e]
      | true => exact (hp ⟨j,e,hj⟩).elim
    have order : ∀ a∈bank xs, a (clamp (q,p))=true → a (clamp (q,fill q))=true := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl|hr
      · exact fun _ => rfl
      rcases List.mem_cons.mp hr with rfl|hr
      · exact fun _ => rfl
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
      exact mons b hb q p (fill q) pt
    have no : ¬goal (clamp (q,p))=true := by
      intro h
      have t := runs_respect run order h
      rw [← helpers_covered q] at t
      exact fill_negative q ((correct _).1 t)
    cases e : goal (clamp (q,p)) <;> simp_all [target,restrictRows]

theorem target_nonconstant : ¬Constant target := by
  rintro ⟨v,eq⟩
  have x := congrFun eq (lineZero,fun _ => false)
  have y := congrFun eq (lineZero,fun _ => true)
  have a : target (lineZero,fun _ => false)=false := by decide +kernel
  have b : target (lineZero,fun _ => true)=true := by decide +kernel
  rw [a] at x
  rw [b] at y
  change false=v at x
  change true=v at y
  cases v <;> contradiction

theorem save_two {k : Nat} {goal : Wire R} {xs : List (Wire S)}
    (run : Run false goal k (bank xs)) (mons : ∀ a∈xs, Increasing a)
    (correct : ∀ r, goal (orig r)=true ↔ hit r) :
    ∃ j bs, Reach false xs j bs ∧ Available false bs target ∧ j+2≤k := by
  classical
  have ident := clamped_correct run mons correct
  have lowered := restrict_run clamp run
  rw [ident] at lowered
  let one : Wire S := fun _ => true
  have mapped : (xs.map lift).map (restrictRows clamp)=xs := by
    clear run mons correct lowered ident
    induction xs with
    | nil => rfl
    | cons a xs ih => exact congrArg (List.cons a) ih
  have re : (bank xs).map (restrictRows clamp)=one::one::xs :=
    congrArg (fun v => one::one::v) mapped
  rw [re] at lowered
  have c : Constant one := ⟨true,rfl⟩
  have sc : supply false xs (one::one::xs) := by
    intro a h
    rcases List.mem_cons.mp h with rfl|h
    · exact Or.inr (Or.inl c)
    rcases List.mem_cons.mp h with rfl|h
    · exact Or.inr (Or.inl c)
    exact Or.inl h
  obtain ⟨j,bs,hb,av,sz⟩ := contraction target_nonconstant lowered xs Reach.start sc
  have oc : cost one=1 := by simp [cost,c]
  rw [mass_cons,mass_cons,oc] at sz
  exact ⟨j,bs,hb,av,by omega⟩

def ordinary : List (Wire S) :=
  (List.ofFn (fun i : Fin 6 => fun r : S => r.1.val.val.testBit i.val)) ++
    List.ofFn (fun j : Fin 7 => fun r : S => r.2 j)
theorem ordinary_increasing : ∀ a∈ordinary, Increasing a := by
  intro a h
  rcases List.mem_append.mp h with h|h
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact fun _ _ _ _ h => h
  · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
    exact fun _ _ _ le => le j

theorem kernel22_forces_region20 {k : Nat} {goal : Wire R} (hk : k≤22)
    (run : Run false goal k (bank ordinary))
    (correct : ∀ r, goal (orig r)=true ↔ hit r) :
    ∃ j bs, j≤20 ∧ Reach false ordinary j bs ∧ Available false bs target := by
  obtain ⟨j,bs,r,a,sz⟩ := save_two run ordinary_increasing correct
  exact ⟨j,bs,by omega,r,a⟩
def maximal : List Nat := [8128, 5761, 6530, 4227, 6724, 5448, 4172, 3280, 2132, 1112, 992, 612, 360, 240, 124]
def negativeRow (q : Fin 64) := q.val + 64 * (List.range 7).foldl
    (fun s j => s + (if blocked q ⟨j%7,Nat.mod_lt _ (by decide)⟩ then 0 else 2^j)) 0
theorem region_maxima : ∀ q : Fin 64, legal q →
    maximal.any (fun n => decide ((negativeRow q &&& n) = negativeRow q))=true := by
  decide +kernel
end PEqualNP.Outside.L_meta_9791.ClampRegion
