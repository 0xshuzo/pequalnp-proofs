import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166_Retired
open PEqualNP.ProofComplexity
abbrev V := Fin 5 × Fin 4
abbrev C := Clause V
def join (p n : C) (v : V) : C := p.erase (v,true) ∪ n.erase (v,false)

-- A cone of an ordinary proof using only the allowed pivot cells.
inductive Cone (allow : V → Prop) : C → Prop where
 | raw {c} : c ∈ PHP 5 4 → Cone allow c
 | step {p n v} : allow v → (v,true) ∈ p → (v,false) ∈ n →
     Cone allow p → Cone allow n → Cone allow (join p n v)

theorem lifts {π : List C} (d : IsDerivation (PHP 5 4) π) :
    ∀ c∈π, Cone (fun _ => True) c := by
  induction d with
  | nil => simp
  | ax prev ax ih =>
    intro c h
    rcases List.mem_cons.mp h with rfl|old
    · exact .raw ax
    · exact ih _ old
  | res prev hp hn step ih =>
    obtain ⟨v,p,n,rfl⟩ := step
    intro c h
    rcases List.mem_cons.mp h with rfl|old
    · exact .step trivial p n (ih _ hp) (ih _ hn)
    · exact ih _ old

def inside (S : V → Prop) (c d : C) := ∀ l∈c, S l.1 → l∈d
def killed (S : V → Prop) (a : V → Bool) (c : C) := ∀ l∈c, ¬S l.1 → a l.1 ≠ l.2

theorem retired {S : V→Prop} {c : C} (cone : Cone (fun v => ¬S v) c)
    (a : V→Bool) (off : killed S a c) :
    ∃ r∈PHP 5 4, inside S r c ∧ killed S a r := by
  induction cone with
  | raw raw => exact ⟨_,raw,(fun _ h _ => h),off⟩
  | @step p n v free pos neg cp cn ihp ihn =>
    have kp {l : Literal V} (h : l∈p) (ne : l≠(v,true)) : l∈join p n v :=
      Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,h⟩)
    have kn {l : Literal V} (h : l∈n) (ne : l≠(v,false)) : l∈join p n v :=
      Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,h⟩)
    cases bit : a v with
    | false =>
      have h : killed S a p := by
        intro l m g
        by_cases e : l=(v,true)
        · subst l; simpa using bit
        · exact off l (kp m e) g
      obtain ⟨r,raw,sub,kill⟩ := ihp h
      refine ⟨r,raw,?_,kill⟩
      intro l m g
      apply kp (sub l m g)
      rintro rfl
      exact free g
    | true =>
      have h : killed S a n := by
        intro l m g
        by_cases e : l=(v,false)
        · subst l; simpa using bit
        · exact off l (kn m e) g
      obtain ⟨r,raw,sub,kill⟩ := ihn h
      refine ⟨r,raw,?_,kill⟩
      intro l m g
      apply kn (sub l m g)
      rintro rfl
      exact free g

-- On a concrete ancestry path from the empty clause, only previously queried
-- cells can occur in the clause at the stopping node.
def names (S : V→Prop) (c : C) := ∀ l∈c,S l.1
theorem parents {S : V→Prop} {p n : C} {v : V}
    (h : names S (join p n v)) (hs : S v) : names S p ∧ names S n := by
  constructor
  · intro l m
    by_cases e : l=(v,true)
    · subst l; exact hs
    · exact h l (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,m⟩))
  · intro l m
    by_cases e : l=(v,false)
    · subst l; exact hs
    · exact h l (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨e,m⟩))

-- All profiles at this physical site falsify its clause. A suffix assignment
-- respecting their jointly fixed live bits produces a common violated raw clause,
-- once the retired bits of each profile are put back.
def glue (S : V → Prop) [DecidablePred S] (x a : V→Bool) (v : V) :=
  if S v then x v else a v
theorem common {S F : V→Prop} [DecidablePred S] {c : C}
    (cone : Cone (fun v => ¬S v) c) (earlier : names (fun v => S v ∨ F v) c)
    {I : Type} [Nonempty I] (x : I→V→Bool) (fals : ∀i,¬ClauseSat (x i) c)
    (a : V→Bool) (live : ∀v,F v → ∀b,(∀i,x i v=b) → a v=b) :
    ∃r∈PHP 5 4, ∀i, ¬ClauseSat (glue S (x i) a) r := by
  have af (i : I) {l : Literal V} (m : l∈c) : x i l.1≠l.2 :=
    fun e => fals i ⟨l,m,e⟩
  have k : killed S a c := by
    intro l m ns
    have f := (earlier l m).resolve_left ns
    cases val : l.2 with
    | false =>
      have all : ∀i,x i l.1=true := by intro i; have h := af i m; cases u : x i l.1 <;> simp_all
      have aa := live l.1 f true all
      simp [aa,val]
    | true =>
      have all : ∀i,x i l.1=false := by intro i; have h := af i m; cases u : x i l.1 <;> simp_all
      have aa := live l.1 f false all
      simp [aa,val]
  obtain ⟨r,raw,sub,fail⟩ := retired cone a k
  refine ⟨r,raw,?_⟩
  intro i
  rintro ⟨l,m,on⟩
  by_cases g : S l.1
  · exact af i (sub l m g) (by simpa [glue,g] using on)
  · exact fail l m g (by simpa [glue,g] using on)
end PEqualNP.Outside.L_pcx_166_Retired

namespace PEqualNP.Outside.L_pcx_166_Retired
open PEqualNP.ProofComplexity
abbrev Site := C × V

-- A topological proof list may be unfolded using the same site for all copies
-- of a shared node. Free pivots may be queried at any time on any path.
inductive Schedule (bank : List Site) (free : V → Bool) (rank : V→Nat) : Nat→C→Prop where
 | raw {k c} : c∈PHP 5 4 → Schedule bank free rank k c
 | step {k p n v} : (join p n v,v)∈bank → (v,true)∈p → (v,false)∈n →
     (free v=true ∨ k≤rank v) →
     Schedule bank free rank (if free v then k else rank v) p →
     Schedule bank free rank (if free v then k else rank v) n →
     Schedule bank free rank k (join p n v)

theorem coneAlong {bank free rank k c} (tr : Schedule bank free rank k c) {P : V→Prop}
    (safe : ∀w,free w=true ∨ k≤rank w → P w) : Cone P c := by
  induction tr with
  | raw ax => exact .raw ax
  | @step k p n w m pp nn ok tp tn i1 i2 =>
    have up : k≤(if free w then k else rank w) := by
      cases b : free w <;> simp [b] at * 
      exact ok
    have more : ∀z,free z=true ∨ (if free w then k else rank w)≤rank z → P z := by
      intro z h
      exact safe z (h.imp_right (Nat.le_trans up))
    exact .step (safe w ok) pp nn (i1 more) (i2 more)

theorem splitCone {v : V} {c : C} (tr : Cone (fun w => w≠v) c)
    {a b : V→Bool} (ag : ∀w,w≠v → a w=b w) (raw : ∀r∈PHP 5 4,ClauseSat a r ∨ ClauseSat b r)
    (ha : ¬ClauseSat a c) (hb : ¬ClauseSat b c) : False := by
  induction tr with
  | raw ax => exact (raw _ ax).elim ha hb
  | @step p n w diff pp nn tp tn ihp ihn =>
    have left {x : V→Bool} (off : x w=false) (hc : ¬ClauseSat x (join p n w)) : ¬ClauseSat x p := by
      rintro ⟨l,m,e⟩
      have ne : l≠(w,true) := by rintro rfl; change x w=true at e; simp_all
      exact hc ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,m⟩),e⟩
    have right {x : V→Bool} (on_ : x w=true) (hc : ¬ClauseSat x (join p n w)) : ¬ClauseSat x n := by
      rintro ⟨l,m,e⟩
      have ne : l≠(w,false) := by rintro rfl; change x w=false at e; simp_all
      exact hc ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,m⟩),e⟩
    cases d : a w with
    | false => exact ihp (left d ha) (left ((ag w diff).symm.trans d) hb)
    | true => exact ihn (right d ha) (right ((ag w diff).symm.trans d) hb)

def earlier (free : V→Bool) (rank : V→Nat) (v w : V) : Prop := free w=false ∧ rank w<rank v
def mayName (free : V→Bool) (rank : V→Nat) (v w : V) : Prop := earlier free rank v w ∨ free w=true
def witness (bank : List Site) (free : V→Bool) (rank : V→Nat) (v : V) (a b : V→Bool) : Prop :=
  ∃ c,(c,v)∈bank ∧ names (mayName free rank v) c ∧ Cone (fun w => ¬earlier free rank v w) c ∧
    ¬ClauseSat a c ∧ ¬ClauseSat b c

theorem locate {bank free rank k c} (tr : Schedule bank free rank k c) {v : V}
    (ex : free v=false) (uniq : Function.Injective rank) {a b : V→Bool}
    (ag : ∀w,w≠v → a w=b w) (raw : ∀r∈PHP 5 4,ClauseSat a r ∨ ClauseSat b r)
    (support : names (mayName free rank v) c) (ha : ¬ClauseSat a c) (hb : ¬ClauseSat b c) :
    witness bank free rank v a b := by
  induction tr with
  | raw ax => exact ((raw _ ax).elim ha hb).elim
  | @step k p n w mem pp nn ok tp tn ihp ihn =>
    by_cases eq : w=v
    · subst w
      have saf : ∀z,free z=true ∨ (if free v then k else rank v)≤rank z → ¬earlier free rank v z := by
        intro z h g
        rcases h with e|zlarge
        · simp [g.1] at e
        · simp [ex] at zlarge
          exact (Nat.not_lt_of_ge zlarge) g.2
      have here : ¬earlier free rank v v := fun e => (Nat.lt_irrefl _) e.2
      exact ⟨_,mem,support,.step here pp nn (coneAlong tp saf) (coneAlong tn saf),ha,hb⟩
    by_cases used : mayName free rank v w
    · obtain ⟨pname,nname⟩:=parents support used
      have lp {x : V→Bool} (d : x w=false) (h : ¬ClauseSat x (join p n w)) : ¬ClauseSat x p := by
        rintro ⟨l,m,y⟩
        have ne : l≠(w,true) := by rintro rfl; change x w=true at y; simp_all
        exact h ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,m⟩),y⟩
      have ln {x : V→Bool} (d : x w=true) (h : ¬ClauseSat x (join p n w)) : ¬ClauseSat x n := by
        rintro ⟨l,m,y⟩
        have ne : l≠(w,false) := by rintro rfl; change x w=false at y; simp_all
        exact h ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,m⟩),y⟩
      cases d : a w with
      | false => exact ihp pname (lp d ha) (lp ((ag w eq).symm.trans d) hb)
      | true => exact ihn nname (ln d ha) (ln ((ag w eq).symm.trans d) hb)
    · have off : free w=false := by cases b : free w <;> simp_all [mayName]
      have no : ¬rank w<rank v := fun h => used (Or.inl ⟨off,h⟩)
      have ne : rank w≠rank v := fun e => eq (uniq e)
      have lt : rank v<rank w := by omega
      have absent : ∀z, free z=true ∨ (if free w then k else rank w)≤rank z → z≠v := by
        intro z h e
        subst z
        simp [off,ex] at h
        omega
      exact (splitCone (.step eq pp nn (coneAlong tp absent) (coneAlong tn absent)) ag raw ha hb).elim

theorem atEmpty {bank free rank k v a b} (tr : Schedule bank free rank k (∅ : C))
    (ex : free v=false) (uniq : Function.Injective rank) (ag : ∀w,w≠v → a w=b w)
    (raw : ∀r∈PHP 5 4,ClauseSat a r ∨ ClauseSat b r) : witness bank free rank v a b := by
  exact locate tr ex uniq ag raw (by intro l m; simp at m) (by simp [ClauseSat]) (by simp [ClauseSat])
end PEqualNP.Outside.L_pcx_166_Retired

namespace PEqualNP.Outside.L_pcx_166_Retired.Column
open PEqualNP.ProofComplexity
abbrev D := Fin 129
def order (v : V) := v.2.val*5+v.1.val
theorem orderInj : Function.Injective order := by
  intro a b h
  change a.2.val*5+a.1.val=b.2.val*5+b.1.val at h
  have e := a.1.isLt
  have f := b.1.isLt
  apply Prod.ext <;> apply Fin.ext <;> omega
def val (x : Nat) (v : V) := x.testBit (4*v.1.val+v.2.val)
def flag (x y : V→Bool) : Prop :=
   (∀ r : Fin 5, ∃ h : Fin 4,x (r,h)=true ∨ y (r,h)=true) ∧
   ∀ (r s : Fin 5) (h : Fin 4),r≠s →
       x (r,h)=false ∨ x (s,h)=false ∨ y (r,h)=false ∨ y (s,h)=false
instance (x y : V→Bool) : Decidable (flag x y) := by unfold flag; infer_instance
theorem safe {x y : V→Bool} (h : flag x y) : ∀c∈PHP 5 4,ClauseSat x c ∨ ClauseSat y c := by
  intro c cMem
  rcases cMem with ⟨r,rfl⟩ | ⟨r,s,k,ne,rfl⟩
  · obtain ⟨k,g|g⟩ := h.1 r
    · exact Or.inl ⟨((r,k),true),Finset.mem_image_of_mem _ (Finset.mem_univ _),g⟩
    · exact Or.inr ⟨((r,k),true),Finset.mem_image_of_mem _ (Finset.mem_univ _),g⟩
  · rcases h.2 r s k ne with z|z|z|z
    · exact Or.inl ⟨((r,k),false),by simp,z⟩
    · exact Or.inl ⟨((s,k),false),by simp,z⟩
    · exact Or.inr ⟨((r,k),false),by simp,z⟩
    · exact Or.inr ⟨((s,k),false),by simp,z⟩
def keys : Array (V × Nat × Nat × Nat) := #[((0,0),541200,541201,0),((1,0),541185,541201,1),((1,0),540930,540946,1),((2,0),540705,540961,3),((2,0),540690,540946,3),((2,0),528450,528706,3),((3,0),525345,529441,6),((3,0),525330,529426,6),((3,0),524610,528706,6),((3,0),67650,71746,6),((4,0),33825,99361,10),((4,0),33810,99346,10),((4,0),33090,98626,10),((4,0),6210,71746,10),((0,1),541200,541202,14),((0,1),540960,540962,14),((0,1),529440,529442,14),((0,1),99360,99362,14),((1,1),541185,541217,18),((1,1),540930,540962,18),((1,1),529410,529442,18),((1,1),99330,99362,18),((1,1),532740,532772,18),((1,1),528900,528932,18),((1,1),98820,98852,18),((2,1),540705,541217,25),((2,1),532545,533057,25),((2,1),540690,541202,25),((2,1),528450,528962,25),((2,1),98370,98882,25),((2,1),532500,533012,25),((2,1),528420,528932,25),((2,1),98340,98852,25),((2,1),135300,135812,25),((2,1),73860,74372,25),((3,1),525345,533537,35),((3,1),524865,533057,35),((3,1),133185,141377,35),((3,1),525330,533522,35),((3,1),524610,532802,35),((3,1),67650,75842,35),((3,1),524820,533012,35),((3,1),133140,141332,35),((3,1),524580,532772,35),((3,1),67620,75812,35),((3,1),131460,139652,35),((3,1),66180,74372,35),((4,1),33825,164897,47),((4,1),33345,164417,47),((4,1),10305,141377,47),((4,1),33810,164882,47),((4,1),33090,164162,47),((4,1),6210,137282,47),((4,1),33300,164372,47),((4,1),10260,141332,47),((4,1),33060,164132,47),((4,1),6180,137252,47),((4,1),8580,139652,47),((4,1),4740,135812,47),((0,2),541200,541204,59),((0,2),533520,533524,59),((0,2),164880,164884,59),((0,2),532800,532804,59),((0,2),164160,164164,59),((0,2),137280,137284,59),((1,2),541185,541249,65),((1,2),533505,533569,65),((1,2),164865,164929,65),((1,2),532740,532804,65),((1,2),164100,164164,65),((1,2),137220,137284,65),((1,2),270600,270664,65),((1,2),147720,147784,65),((1,2),136200,136264,65),((2,2),540705,541729,74),((2,2),532545,533569,74),((2,2),163905,164929,74),((2,2),270465,271489,74),((2,2),147585,148609,74),((2,2),532500,533524,74),((2,2),163860,164884,74),((2,2),135300,136324,74),((2,2),270360,271384,74),((2,2),147480,148504,74),((2,2),135240,136264,74),((3,2),525345,541729,85),((3,2),264225,280609,85),((3,2),524865,541249,85),((3,2),133185,149569,85),((3,2),262785,279169,85),((3,2),132225,148609,85),((3,2),524820,541204,85),((3,2),133140,149524,85),((3,2),131460,147844,85),((3,2),262680,279064,85),((3,2),132120,148504,85),((3,2),131400,147784,85),((4,2),33825,295969,97),((4,2),18465,280609,97),((4,2),33345,295489,97),((4,2),10305,272449,97),((4,2),17025,279169,97),((4,2),9345,271489,97),((4,2),33300,295444,97),((4,2),10260,272404,97),((4,2),8580,270724,97),((4,2),16920,279064,97),((4,2),9240,271384,97),((4,2),8520,270664,97),((0,3),541200,541208,109),((0,3),295440,295448,109),((0,3),272400,272408,109),((0,3),270720,270728,109),((1,3),541185,541313,113),((1,3),295425,295553,113),((1,3),272385,272513,113),((1,3),270600,270728,113),((2,3),540705,542753,117),((2,3),294945,296993,117),((2,3),270465,272513,117),((2,3),270360,272408,117),((3,3),525345,558113,121),((3,3),264225,296993,121),((3,3),262785,295553,121),((3,3),262680,295448,121),((4,3),33825,558113,125),((4,3),18465,542753,125),((4,3),17025,541313,125),((4,3),16920,541208,125)]
def suffixes : Array (Array Nat) := #[#[0],#[0,541200],#[0,0],#[0,270592,540960],#[0,0,540930],#[0,0,0],#[0,266752,266272,529440],#[0,0,266242,529410],#[0,0,0,528450],#[0,0,0,0],#[0,82432,81952,66592],#[0,0,81922,66562],#[0,0,0,65602],#[0,0,0,0],#[0,540674,525314,33794],#[0,0,524354,32834],#[0,0,0,2114],#[0,0,0,0],#[0,540704,525344,33824,540704,525344,33824],#[0,0,524352,32832,540704,262176,16416],#[0,0,0,2112,262176,525344,1056],#[0,0,0,0,16416,1056,33824],#[0,0,0,0,0,524324,32804],#[0,0,0,0,0,0,2084],#[0,0,0,0,0,0,0],#[0,541184,541184,262656,16896,541184,525312,33792,262656,16896],#[0,0,541184,524864,33344,541184,262656,16896,524864,33344],#[0,0,0,525312,33792,541184,262656,16896,262656,16896],#[0,0,0,0,2112,262656,262656,512,524864,576],#[0,0,0,0,0,16896,512,16896,576,33344],#[0,0,0,0,0,0,524804,33284,524804,33284],#[0,0,0,0,0,0,0,2052,524804,516],#[0,0,0,0,0,0,0,0,516,33284],#[0,0,0,0,0,0,0,0,0,644],#[0,0,0,0,0,0,0,0,0,0],#[0,270336,533504,533504,270336,9216,270336,533504,540672,33792,270336,8192],#[0,0,532544,270336,532544,8256,540672,270336,270336,8192,532544,32832],#[0,0,0,533504,532544,10304,270336,533504,270336,9216,532544,8256],#[0,0,0,0,540672,33792,270336,533504,270336,9216,270336,8192],#[0,0,0,0,0,32832,270336,270336,270336,8192,532544,8256],#[0,0,0,0,0,0,8192,9216,8192,9216,8256,8256],#[0,0,0,0,0,0,0,532484,532484,8196,532484,32772],#[0,0,0,0,0,0,0,0,532484,10244,532484,8196],#[0,0,0,0,0,0,0,0,0,32772,532484,8196],#[0,0,0,0,0,0,0,0,0,0,8196,8196],#[0,0,0,0,0,0,0,0,0,0,0,8324],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,147456,132096,164864,147456,132096,147456,132096,540672,525312,131072,131072],#[0,0,131136,147456,163904,131136,540672,131072,147456,131072,131136,524352],#[0,0,0,132096,131136,133184,131072,525312,131072,132096,524352,131136],#[0,0,0,0,540672,525312,147456,132096,147456,132096,131072,131072],#[0,0,0,0,0,524352,147456,131072,147456,131072,131136,131136],#[0,0,0,0,0,0,131072,132096,131072,132096,131136,131136],#[0,0,0,0,0,0,0,131076,163844,131076,131076,524292],#[0,0,0,0,0,0,0,0,131076,133124,524292,131076],#[0,0,0,0,0,0,0,0,0,524292,131076,131076],#[0,0,0,0,0,0,0,0,0,0,131076,131076],#[0,0,0,0,0,0,0,0,0,0,0,131204],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,524292,32772,524292,32772,4],#[0,0,2052,524292,4,2052],#[0,0,0,4,32772,2052],#[0,0,0,0,132,132],#[0,0,0,0,0,132],#[0,0,0,0,0,0],#[0,524352,32832,524352,32832,64,524352,32832,64],#[0,0,2112,524352,64,2112,524352,64,2112],#[0,0,0,64,32832,2112,64,32832,2112],#[0,0,0,0,128,128,524352,64,64],#[0,0,0,0,0,128,64,32832,64],#[0,0,0,0,0,0,64,64,2112],#[0,0,0,0,0,0,0,72,72],#[0,0,0,0,0,0,0,0,72],#[0,0,0,0,0,0,0,0,0],#[0,525312,33792,525312,33792,525312,33792,1024,525312,33792,1024],#[0,0,2048,525312,1024,525312,1024,1024,525312,1024,2048],#[0,0,0,1024,33792,1024,33792,1024,1024,33792,2048],#[0,0,0,0,1152,525312,1024,1152,525312,1024,1024],#[0,0,0,0,0,1024,33792,1152,1024,33792,1024],#[0,0,0,0,0,0,2048,2048,525312,1024,1024],#[0,0,0,0,0,0,0,2048,1024,33792,1024],#[0,0,0,0,0,0,0,0,1024,1024,1024],#[0,0,0,0,0,0,0,0,0,1032,1032],#[0,0,0,0,0,0,0,0,0,0,1032],#[0,0,0,0,0,0,0,0,0,0,0],#[0,540672,540672,16384,540672,32768,540672,16384,16384,540672,32768,16384],#[0,0,540672,18432,540672,16384,540672,18432,16384,540672,16384,16384],#[0,0,0,32768,540672,16384,540672,16384,16384,540672,16384,32768],#[0,0,0,0,16384,16384,16384,18432,16384,16384,16384,32768],#[0,0,0,0,0,16512,540672,16384,16512,540672,16384,16384],#[0,0,0,0,0,0,16384,16384,16512,16384,32768,16384],#[0,0,0,0,0,0,0,32768,32768,540672,16384,16384],#[0,0,0,0,0,0,0,0,32768,16384,16384,16384],#[0,0,0,0,0,0,0,0,0,16384,16384,16384],#[0,0,0,0,0,0,0,0,0,0,16392,16392],#[0,0,0,0,0,0,0,0,0,0,0,16392],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,262144,294912,262144,262144,524288,294912,262144,262144,262144,524288,262144],#[0,0,262144,264192,524288,262144,262144,264192,262144,524288,262144,262144],#[0,0,0,524288,262144,262144,294912,262144,262144,262144,262144,524288],#[0,0,0,0,262144,262144,262144,264192,262144,262144,262144,524288],#[0,0,0,0,0,262272,262144,262144,262272,524288,262144,262144],#[0,0,0,0,0,0,262144,262144,262272,262144,524288,262144],#[0,0,0,0,0,0,0,524288,524288,262144,262144,262144],#[0,0,0,0,0,0,0,0,524288,262144,262144,262144],#[0,0,0,0,0,0,0,0,0,262144,262144,262144],#[0,0,0,0,0,0,0,0,0,0,262152,262152],#[0,0,0,0,0,0,0,0,0,0,0,262152],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,8,8,8],#[0,0,8,8],#[0,0,0,8],#[0,0,0,0],#[0,128,128,128],#[0,0,128,128],#[0,0,0,128],#[0,0,0,0],#[0,2048,2048,2048],#[0,0,2048,2048],#[0,0,0,2048],#[0,0,0,0],#[0,32768,32768,32768],#[0,0,32768,32768],#[0,0,0,32768],#[0,0,0,0],#[0,524288,524288,524288],#[0,0,524288,524288],#[0,0,0,524288],#[0,0,0,0]]

def point (i : D) := keys[i.val]!
def piv (i : D) := (point i).1
def a (i : D) := val (point i).2.1
def b (i : D) := val (point i).2.2.1
def fixed (i : D) (w : V) := order w < order (piv i)
instance (i : D) : DecidablePred (fixed i) := fun w => inferInstanceAs (Decidable (order w<order (piv i)))
def tail (i j : D) := val ((suffixes[i.val]!)[j.val-(point i).2.2.2]!)
def pairOK (i : D) : Prop := flag (a i) (b i) ∧ ∀w : V,w≠piv i → a i w=b i w
instance (i : D) : Decidable (pairOK i) := by unfold pairOK; infer_instance
def clash (i j : D) : Prop := i.val<j.val → piv i=piv j →
    flag (glue (fixed i) (a i) (tail i j)) (glue (fixed i) (a j) (tail i j))
instance (i j : D) : Decidable (clash i j) := by unfold clash; infer_instance
set_option maxRecDepth 8192 in
theorem pairOK_all : ∀i : D,pairOK i := by decide +kernel
def offset0 (t : Fin 10) : D := ⟨0+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test0 : ∀t j,clash (offset0 t) j := by decide +kernel
def offset1 (t : Fin 10) : D := ⟨10+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test1 : ∀t j,clash (offset1 t) j := by decide +kernel
def offset2 (t : Fin 10) : D := ⟨20+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test2 : ∀t j,clash (offset2 t) j := by decide +kernel
def offset3 (t : Fin 10) : D := ⟨30+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test3 : ∀t j,clash (offset3 t) j := by decide +kernel
def offset4 (t : Fin 10) : D := ⟨40+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test4 : ∀t j,clash (offset4 t) j := by decide +kernel
def offset5 (t : Fin 10) : D := ⟨50+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test5 : ∀t j,clash (offset5 t) j := by decide +kernel
def offset6 (t : Fin 10) : D := ⟨60+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test6 : ∀t j,clash (offset6 t) j := by decide +kernel
def offset7 (t : Fin 10) : D := ⟨70+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test7 : ∀t j,clash (offset7 t) j := by decide +kernel
def offset8 (t : Fin 10) : D := ⟨80+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test8 : ∀t j,clash (offset8 t) j := by decide +kernel
def offset9 (t : Fin 10) : D := ⟨90+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test9 : ∀t j,clash (offset9 t) j := by decide +kernel
def offset10 (t : Fin 10) : D := ⟨100+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test10 : ∀t j,clash (offset10 t) j := by decide +kernel
def offset11 (t : Fin 10) : D := ⟨110+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test11 : ∀t j,clash (offset11 t) j := by decide +kernel
def offset12 (t : Fin 9) : D := ⟨120+t.val,by have := t.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem test12 : ∀t j,clash (offset12 t) j := by decide +kernel
theorem allClash (i j : D) : clash i j := by
  by_cases b0 : i.val < 10
  · let t : Fin 10 := ⟨i.val-0,by omega⟩
    have h : offset0 t=i := by apply Fin.ext; change 0+(i.val-0)=i.val; omega
    exact h ▸ test0 t j
  by_cases b1 : i.val < 20
  · let t : Fin 10 := ⟨i.val-10,by omega⟩
    have h : offset1 t=i := by apply Fin.ext; change 10+(i.val-10)=i.val; omega
    exact h ▸ test1 t j
  by_cases b2 : i.val < 30
  · let t : Fin 10 := ⟨i.val-20,by omega⟩
    have h : offset2 t=i := by apply Fin.ext; change 20+(i.val-20)=i.val; omega
    exact h ▸ test2 t j
  by_cases b3 : i.val < 40
  · let t : Fin 10 := ⟨i.val-30,by omega⟩
    have h : offset3 t=i := by apply Fin.ext; change 30+(i.val-30)=i.val; omega
    exact h ▸ test3 t j
  by_cases b4 : i.val < 50
  · let t : Fin 10 := ⟨i.val-40,by omega⟩
    have h : offset4 t=i := by apply Fin.ext; change 40+(i.val-40)=i.val; omega
    exact h ▸ test4 t j
  by_cases b5 : i.val < 60
  · let t : Fin 10 := ⟨i.val-50,by omega⟩
    have h : offset5 t=i := by apply Fin.ext; change 50+(i.val-50)=i.val; omega
    exact h ▸ test5 t j
  by_cases b6 : i.val < 70
  · let t : Fin 10 := ⟨i.val-60,by omega⟩
    have h : offset6 t=i := by apply Fin.ext; change 60+(i.val-60)=i.val; omega
    exact h ▸ test6 t j
  by_cases b7 : i.val < 80
  · let t : Fin 10 := ⟨i.val-70,by omega⟩
    have h : offset7 t=i := by apply Fin.ext; change 70+(i.val-70)=i.val; omega
    exact h ▸ test7 t j
  by_cases b8 : i.val < 90
  · let t : Fin 10 := ⟨i.val-80,by omega⟩
    have h : offset8 t=i := by apply Fin.ext; change 80+(i.val-80)=i.val; omega
    exact h ▸ test8 t j
  by_cases b9 : i.val < 100
  · let t : Fin 10 := ⟨i.val-90,by omega⟩
    have h : offset9 t=i := by apply Fin.ext; change 90+(i.val-90)=i.val; omega
    exact h ▸ test9 t j
  by_cases b10 : i.val < 110
  · let t : Fin 10 := ⟨i.val-100,by omega⟩
    have h : offset10 t=i := by apply Fin.ext; change 100+(i.val-100)=i.val; omega
    exact h ▸ test10 t j
  by_cases b11 : i.val < 120
  · let t : Fin 10 := ⟨i.val-110,by omega⟩
    have h : offset11 t=i := by apply Fin.ext; change 110+(i.val-110)=i.val; omega
    exact h ▸ test11 t j
  by_cases b12 : i.val < 129
  · let t : Fin 9 := ⟨i.val-120,by omega⟩
    have h : offset12 t=i := by apply Fin.ext; change 120+(i.val-120)=i.val; omega
    exact h ▸ test12 t j
  have := i.isLt
  omega

set_option maxRecDepth 16384 in
theorem price {bank : List Site} (tr : Schedule bank (fun _ => false) order 0 ∅) :
    129 ≤ bank.length := by
  classical
  have claimed (i : D) := atEmpty tr (v:=piv i) rfl orderInj (pairOK_all i).2 (safe (pairOK_all i).1)
  choose c site before after oa ob using claimed
  have noShare (i j : D) (lt : i.val<j.val) (same : piv i=piv j) (eq : c i=c j) : False := by
    have mems (l : Literal V) (ml : l∈c i) : fixed i l.1 := by
      have z := before i l ml
      simpa [mayName,earlier,fixed] using z
    have co : Cone (fun w => ¬earlier (fun _ => false) order (piv i) w) (c i) := after i
    let s := earlier (fun _ => false) order (piv i)
    let mask := tail i j
    obtain ⟨r,raw,within,off⟩ := retired co mask (by
      intro l m ns
      exact (ns ⟨rfl,mems l m⟩).elim)
    have safeBoth := safe (allClash i j lt same) r raw
    have kill (k : D) (eqc : c i=c k) : ¬ClauseSat (glue (fixed i) (a k) mask) r := by
      rintro ⟨l,m,on⟩
      by_cases h : fixed i l.1
      · have old := within l m ⟨rfl,h⟩
        exact oa k ⟨l,eqc ▸ old,by simpa [glue,h] using on⟩
      · exact off l m (fun z => h z.2) (by simpa [glue,h] using on)
    exact safeBoth.elim (kill i rfl) (kill j eq)
  let g : D → Site := fun i => (c i,piv i)
  have inj : Function.Injective g := by
    intro i j h
    change (c i,piv i)=(c j,piv j) at h
    have eq : c i=c j := Prod.mk.inj h |>.1
    have same : piv i=piv j := Prod.mk.inj h |>.2
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with less|equal|more
    · exact (noShare i j less same eq).elim
    · exact equal
    · exact (noShare j i more same.symm eq.symm).elim
  have im : Finset.univ.image g ⊆ bank.toFinset := by
    intro t ht
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    exact List.mem_toFinset.mpr (site i)
  have ca := Finset.card_le_card im
  rw [Finset.card_image_of_injective _ inj] at ca
  have cb := List.toFinset_card_le bank
  simpa using ca.trans cb
end PEqualNP.Outside.L_pcx_166_Retired.Column
