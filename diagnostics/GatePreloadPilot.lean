import PEqualNP.Outside.L_meta_17581

namespace PetersenSupportedSeed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_17581
open Petersen7217 SeedCompress

abbrev Point := V → Bool
def rowInput (a b : Point → Bool) (x : Point) := List.ofFn x ++ [a x,b x]
def Fits (C : Circuit) (a b : Point → Bool) :=
  ∀ x : Point, C.eval (rowInput a b x) = pet x

def VanishesOutside (a : Point → Bool) (c : Bool) :=
  ∀ x : Point, (x 0 && x 2) = false → a x = c

private theorem witnessesOff (v : V) : ∃ x y : Point, (∀ j, j ≠ v → x j = y j) ∧
    (x 0 && x 2) = false ∧ (y 0 && y 2) = false ∧ pet x ≠ pet y := by
  have pick (a : V) : ∃ b : V,
      (∀ c : V, c ≠ a → decide (c = b) = decide (c = b ∨ c = a)) ∧
      (decide ((0:V) = b) && decide ((2:V) = b)) = false ∧
      (decide ((0:V) = b ∨ (0:V) = a) && decide ((2:V) = b ∨ (2:V) = a)) = false ∧
      pet (fun c => decide (c = b)) ≠ pet (fun c => decide (c = b ∨ c = a)) := by
    revert a
    decide +kernel
  obtain ⟨b,h₁,h₂,h₃,h₄⟩ := pick v
  exact ⟨_,_,h₁,h₂,h₃,h₄⟩

private theorem internal {C : Circuit} {a b : Point → Bool} {c d : Bool}
    (ha : VanishesOutside a c) (hb : VanishesOutside b d) (hc : Fits C a b) :
    12 ≤ C.output := by
  by_contra! low
  have read (x : Point) : (rowInput a b x).getD C.output false = pet x := by
    obtain ⟨t,ht,_⟩ := wiresFrom_prefix C.gates (rowInput a b x)
    rw [← hc]
    change _ = (wiresFrom C.gates (rowInput a b x)).getD C.output false
    rw [ht,List.getD_append _ _ _ _ (by simpa [rowInput] using low)]
  by_cases h : C.output < 10
  · let i : V := ⟨C.output,h⟩
    have no (j : V) : pet (fun v => decide (v=j)) = false := by revert j; decide
    have e := read (fun v => decide (v=i))
    rw [rowInput,ExtraPetersen.lowRead _ _ _ h,no] at e
    simp [i] at e
  · obtain ⟨x,y,_,hx,hy,hne⟩ := witnessesOff 0
    apply hne
    rw [← read x,← read y]
    rcases (by omega : C.output = 10 ∨ C.output = 11) with hout | hout <;>
      simp [rowInput,hout,List.getD_append_right,ha _ hx,ha _ hy,hb _ hx,hb _ hy]

private theorem primary {C : Circuit} {a b : Point → Bool} {c d : Bool}
    (ha : VanishesOutside a c) (hb : VanishesOutside b d) (hc : Fits C a b) (v : V) :
    ∃ j : Fin C.gates.length, v.val ∈ (normGate (C.gates.get j)).inputs := by
  by_contra no
  obtain ⟨x,y,away,hx,hy,ne⟩ := witnessesOff v
  have ln (z : Point) : (rowInput a b z).length = 12 := by simp [rowInput]
  obtain ⟨t,ex,ey⟩ := same_tail C.gates (rowInput a b x) (rowInput a b y) (by simp [ln]) (by
    intro g hg k hk kl
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hg
    by_cases h : k < 10
    · rw [rowInput,rowInput,ExtraPetersen.lowRead _ _ _ h,ExtraPetersen.lowRead _ _ _ h]
      apply away
      intro eq
      exact no ⟨j,(congrArg Fin.val eq) ▸ hk⟩
    · rw [ln] at kl
      rcases (by omega : k = 10 ∨ k = 11) with rfl | rfl <;>
        simp [rowInput,List.getD_append_right,ha _ hx,ha _ hy,hb _ hx,hb _ hy])
  apply ne
  rw [← hc,← hc]
  change (wiresFrom C.gates (rowInput a b x)).getD _ _ =
    (wiresFrom C.gates (rowInput a b y)).getD _ _
  rw [ex,ey,List.getD_append_right _ _ _ _ (by simpa [ln] using internal ha hb hc),
    List.getD_append_right _ _ _ _ (by simpa [ln] using internal ha hb hc),ln,ln]

private def modes (v : V) (c d : Bool) : List Stat := List.ofFn (pos v) ++ [.inl c,.inl d]

private theorem valid (v : V) (c d : Bool) : ∀ s ∈ modes v c d, s.Valid 9 := by
  intro s hs
  simp only [modes,List.mem_append,List.mem_ofFn,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with ⟨i,rfl⟩ | rfl | rfl
  · unfold pos
    split
    · trivial
    · exact (code v i).isLt
  · trivial
  · trivial

private theorem slice {C : Circuit} {a b : Point → Bool} {c d : Bool}
    (ha : VanishesOutside a c) (hb : VanishesOutside b d) (hc : Fits C a b)
    (f : FanInTwo C) (v : V) (dead : off v) :
    16 + count (modes v c d) C ≤ C.size := by
  have e (y : Y) : C.eval (row (modes v c d) [] y) = nine y := by
    have key : (lift v y 0 && lift v y 2) = false := by
      rcases dead with rfl | rfl <;> simp [lift]
    have equal : row (modes v c d) [] y = rowInput a b (lift v y) := by
      simp only [row,modes,rowInput,ha _ key,hb _ key,List.map_append,List.map_ofFn,
        List.map_cons,List.map_nil,wiresFrom,List.foldl_nil,Stat.val]
      rw [show (Stat.val (List.ofFn y) ∘ pos v) = lift v y from funext (fun i => val_pos_simple v i y)]
    rw [equal,hc,deleted]
  obtain ⟨D,hD,sz,h⟩ := compile_bank (modes v c d) [] C f (by simp) (valid v c d)
    ⟨fun _ => false,(e _).trans nineZero⟩
  have n := nine_bound D hD (fun y => (h y).trans (e y))
  simp only [List.length_nil,Nat.add_zero] at sz
  omega

private def readers (C : Circuit) (v : V) (c d : Bool) :=
  Finset.univ.filter (fun j : Fin C.gates.length => hits (modes v c d) (C.gates.get j))

private theorem hit (C : Circuit) (v : V) (c d : Bool) (j : Fin C.gates.length) (k : ℕ)
    (mem : k ∈ (normGate (C.gates.get j)).inputs) (pick : k=v.val ∨ k=10 ∨ k=11) :
    j ∈ readers C v c d := by
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  apply List.any_eq_true.mpr
  refine ⟨k,mem,?_⟩
  rcases pick with rfl | rfl | rfl
  · have h := v.isLt
    rw [modes,List.getD_append _ _ _ _ (by simpa using h),
      List.getD_eq_getElem _ _ (by simpa using h),List.getElem_ofFn]
    simp [pos,constant,modes]
    omega
  · simp [modes,List.getD_append_right,constant]
  · simp [modes,List.getD_append_right,constant]

/-- Giving two arbitrary additional signals that are constant whenever the nonedge
product is zero still requires at least eighteen gates to compute Petersen. -/
theorem floor {C : Circuit} {a b : Point → Bool} {c d : Bool}
    (ha : VanishesOutside a c) (hb : VanishesOutside b d) (hc : Fits C a b)
    (f : FanInTwo C) : 18 ≤ C.size := by
  by_contra! small
  by_cases h : ∃ (j : Fin C.gates.length) (k : ℕ), k ∈ (normGate (C.gates.get j)).inputs ∧ (k=10 ∨ k=11)
  · obtain ⟨j,k,mem,hk⟩ := h
    have contact (v : V) (dead : off v) : v.val ∈ (normGate (C.gates.get j)).inputs := by
      obtain ⟨i,hi⟩ := primary ha hb hc v
      have bound := slice ha hb hc f v dead
      change 16 + (readers C v c d).card ≤ C.size at bound
      have one : (readers C v c d).card ≤ 1 := by omega
      have eq := Finset.card_le_one.mp one _ (hit C v c d i _ hi (.inl rfl)) _
        (hit C v c d j k mem (.inr hk))
      exact eq ▸ hi
    have h0 := contact 0 (.inl rfl)
    have h2 := contact 2 (.inr rfl)
    let ins := (normGate (C.gates.get j)).inputs
    have sub : ({0,2,k} : Finset ℕ) ⊆ ins.toFinset := by
      intro t ht
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> apply List.mem_toFinset.mpr <;> assumption
    have cap := (Finset.card_le_card sub).trans (List.toFinset_card_le ins)
    have legal := (normGate_nok (C.gates.get j) (f _ (List.get_mem C.gates j))).1.2
    change ins.length ≤ 2 at legal
    rcases hk with rfl | rfl <;> simp at cap <;> omega
  · have standard : ExtraPetersen.good C false := by
      intro x
      have ln : (ExtraPetersen.input false x).length = (rowInput a b x).length := by
        simp [ExtraPetersen.input,rowInput]
      obtain ⟨t,e₁,e₂⟩ := same_tail C.gates (ExtraPetersen.input false x) (rowInput a b x) ln (by
        intro g hg k hk kl
        obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hg
        have avoid : ¬ (k=10 ∨ k=11) := fun bad => h ⟨j,k,hk,bad⟩
        have bl : k < 10 := by simp [ExtraPetersen.input] at kl; omega
        rw [ExtraPetersen.input,rowInput,ExtraPetersen.lowRead _ _ _ bl,ExtraPetersen.lowRead _ _ _ bl])
      rw [← hc x]
      change (wiresFrom _ _).getD C.output _ = (wiresFrom _ _).getD C.output _
      rw [e₁,e₂,List.getD_append_right _ _ _ _ (by simpa [ExtraPetersen.input] using internal ha hb hc),
        List.getD_append_right _ _ _ _ (by simpa [rowInput] using internal ha hb hc),ln]
    exact (Nat.not_lt_of_ge (ExtraPetersen.full C false f standard)) small

/-- In particular a first AND involving the free product, regardless of its
other input, cannot initiate an eighteen-gate solution. -/
theorem after_product_and (C : Circuit) (t : Point → Bool) (f : FanInTwo C)
    (fits : Fits C (fun x => x 0 && x 2) (fun x => (x 0 && x 2) && t x)) :
    18 ≤ C.size :=
  floor (c := false) (d := false) (fun _ h => h)
    (fun x h => by change (x 0 && x 2) && t x = false; rw [h]; rfl) fits f

end PetersenSupportedSeed

namespace PetersenSupportedSeed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_17581
open Petersen7217 SeedCompress

private def remap (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩

private def gateValue (g : Gate) (w : List Bool) :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem synchronized (r : ℕ → ℕ) (p q : List Bool)
    (agree : ∀ (t : List Bool) (i : ℕ), (q++t).getD (r i) false = (p++t).getD i false)
    (gs : List Gate) :
    ∃ t, wiresFrom (gs.map (remap r)) q = q ++ t ∧ wiresFrom gs p = p ++ t ∧
      t.length = gs.length := by
  have go (us : List Gate) (h : List Bool) :
      ∃ t, wiresFrom (us.map (remap r)) (q++h) = (q++h) ++ t ∧
        wiresFrom us (p++h) = (p++h) ++ t ∧ t.length = us.length := by
    induction us generalizing h with
    | nil => exact ⟨[],by simp [wiresFrom],by simp [wiresFrom],rfl⟩
    | cons g us ih =>
      let v := gateValue g (p++h)
      have val : gateValue (remap r g) (q++h) = v := by
        simp only [gateValue,remap,v,List.map_map,Function.comp_def,agree]
      obtain ⟨t,et,eu,len⟩ := ih (h++[v])
      refine ⟨v::t,?_,?_,by simp [len]⟩
      · change wiresFrom (us.map (remap r)) ((q++h)++[gateValue (remap r g) (q++h)]) = _
        simpa only [val,List.append_assoc,List.singleton_append] using et
      · change wiresFrom us ((p++h)++[v]) = _
        simpa only [List.append_assoc,List.singleton_append] using eu
  simpa only [List.append_nil] using go gs []

private def insertPin (n i : ℕ) : ℕ := if i < n then i else i+1
private def movedPin (n l i : ℕ) : ℕ :=
  if i < n then i else if i < n+l then i+1 else if i=n+l then n else i

private theorem insert_agrees (u h : List Bool) (v : Bool) (i : ℕ) :
    ((u++[v])++h).getD (insertPin u.length i) false = (u++h).getD i false := by
  by_cases hi : i < u.length
  · simp only [insertPin,if_pos hi,List.append_assoc,List.singleton_append]
    rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ hi]
  · have right : u.length ≤ i := by omega
    have right' : (u++[v]).length ≤ i+1 := by simp; omega
    rw [insertPin,if_neg hi,List.getD_append_right _ _ _ _ right',
      List.getD_append_right _ _ _ _ right]
    simp

private theorem moved_agrees (u a t : List Bool) (v : Bool) (i : ℕ) :
    (((u++[v])++a)++t).getD (movedPin u.length a.length i) false =
      (((u++a)++[v])++t).getD i false := by
  by_cases hu : i < u.length
  · simp only [movedPin,if_pos hu,List.append_assoc,List.singleton_append]
    rw [List.getD_append _ _ _ _ hu,List.getD_append _ _ _ _ hu]
  · by_cases ha : i < u.length+a.length
    · have h₁ : i+1 < ((u++[v])++a).length := by simp; omega
      have h₂ : i < ((u++a)++[v]).length := by simp; omega
      have h₃ : i < (u++a).length := by simpa using ha
      rw [movedPin,if_neg hu,if_pos ha,List.getD_append _ _ _ _ h₁,
        List.getD_append _ _ _ _ h₂,List.getD_append _ _ _ _ h₃,
        List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by omega)]
      simp
    · by_cases he : i = u.length + a.length
      · subst i
        simp only [movedPin,if_neg hu,if_neg ha,if_pos rfl]
        have left : (((u++[v])++a)++t).getD u.length false = v := by
          rw [List.getD_append _ _ _ _ (show u.length < ((u++[v])++a).length by simp; omega),
            List.getD_append _ _ _ _ (show u.length < (u++[v]).length by simp),
            getD_snoc_eq]
        have right : (((u++a)++[v])++t).getD (u.length+a.length) false = v := by
          rw [List.getD_append _ _ _ _ (show u.length+a.length < ((u++a)++[v]).length by simp),
            show u.length+a.length = (u++a).length by simp, getD_snoc_eq]
        exact left.trans right.symm
      · rw [movedPin,if_neg hu,if_neg ha,if_neg he,
          List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_append,List.length_singleton]
        congr 1 <;> omega

/-- Move an arbitrary internal gate into the input bank and save one gate.
The prefix shifts every old gate index to preserve early or invalid reads. -/
private theorem preload (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ)
    (legal : FanInTwo ⟨pre ++ g::post,o⟩) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = pre.length + post.length ∧
      ∀ u : List Bool, u.length = n →
        D.eval (u ++ [gateValue g (wiresFrom pre u)]) =
          (⟨pre ++ g::post, o⟩ : Circuit).eval u := by
  let r := movedPin n pre.length
  let C : Circuit := ⟨(pre.map (remap (insertPin n))) ++ (post.map (remap r)),r o⟩
  refine ⟨C,?_,by simp [C,Circuit.size],?_⟩
  · intro b hb
    change b ∈ List.map _ pre ++ List.map _ post at hb
    rcases List.mem_append.mp hb with hp|hp
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
      obtain ⟨op,sz⟩ := legal a (List.mem_append_left _ ha)
      exact ⟨op,by simpa [remap] using sz⟩
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
      obtain ⟨op,sz⟩ := legal a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
      exact ⟨op,by simpa [remap] using sz⟩
  intro u hn
  let v := gateValue g (wiresFrom pre u)
  obtain ⟨a,e₁,e₂,hlen⟩ := synchronized (insertPin n) u (u++[v])
    (fun t i => by simpa only [hn] using insert_agrees u t v i) pre
  have agr (t : List Bool) (i : ℕ) :
      ((((u++[v])++a)++t).getD (r i) false) = (((u++a)++[v])++t).getD i false := by
    simpa only [r,hn,hlen] using moved_agrees u a t v i
  obtain ⟨b,e₃,e₄,_⟩ := synchronized r ((u++a)++[v]) ((u++[v])++a) agr post
  change (wiresFrom ((pre.map (remap (insertPin n))) ++ (post.map (remap r))) (u++[v])).getD (r o) false =
    (wiresFrom (pre ++ g::post) u).getD o false
  rw [wiresFrom_append,wiresFrom_append,e₁,e₃]
  change _ = (wiresFrom post ((wiresFrom pre u)++[v])).getD o false
  conv_rhs => rw [e₂,e₄]
  exact agr b o

def hinted (x : Point) := List.ofFn x ++ [x 0 && x 2]
def intermediate (pre : List Gate) (g : Gate) (x : Point) :=
  gateValue g (wiresFrom pre (hinted x))

/-- Every gate output of a correct eighteen-gate circuit must assume both
values already on the assignments on which the free product vanishes. -/
theorem supported_intermediate (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ)
    (c : Bool) (fixed : VanishesOutside (intermediate pre g) c)
    (f : FanInTwo ⟨pre ++ g::post,o⟩)
    (hc : ∀ x : Point, (⟨pre ++ g::post,o⟩ : Circuit).eval (hinted x) = pet x) :
    19 ≤ (pre ++ g::post).length := by
  obtain ⟨D,legal,sz,same⟩ := preload 11 pre g post o f
  have good : Fits D (fun x => x 0 && x 2) (intermediate pre g) := by
    intro x
    have e := same (hinted x) (by simp [hinted])
    simpa [rowInput,hinted,intermediate,List.append_assoc] using e.trans (hc x)
  have low := floor (c := false) (d := c) (fun _ h => h) fixed good legal
  simp only [List.length_append,List.length_cons] at *
  omega

theorem and_reading_product (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ)
    (hand : g.op = .and) (reads : 10 ∈ g.inputs) (f : FanInTwo ⟨pre ++ g::post,o⟩)
    (hc : ∀ x : Point, (⟨pre ++ g::post,o⟩ : Circuit).eval (hinted x) = pet x) :
    19 ≤ (pre ++ g::post).length := by
  apply supported_intermediate pre g post o false _ f hc
  intro x hx
  have hr : (wiresFrom pre (hinted x)).getD 10 false = false := by
    obtain ⟨t,hw,_⟩ := wiresFrom_prefix pre (hinted x)
    rw [hw,List.getD_append _ _ _ _ (by simp [hinted])]
    simp [hinted,List.getD_append_right,hx]
  change g.op.eval _ = false
  rw [hand]
  apply Bool.eq_false_iff.mpr
  intro allTrue
  have bad := List.all_eq_true.mp allTrue false (List.mem_map.mpr ⟨10,reads,hr⟩)
  contradiction

end PetersenSupportedSeed
