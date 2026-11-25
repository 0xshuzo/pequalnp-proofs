import PEqualNP.Defs

namespace PCX150.SmallChart

abbrev Sample := Fin 60
abbrev Var := Fin 12
abbrev Tag := Fin 22
abbrev Key := Fin 48

structure Domain where
  val : Sample → Var → Bool
  tag : Sample → Tag

structure Aut (B : Domain) where
  s : Equiv.Perm Sample
  v : Equiv.Perm Var
  a : Equiv.Perm Tag
  bit : ∀ x q, B.val (s x) (v q) = B.val x q
  label : ∀ x, B.tag (s x) = a (B.tag x)

def Aut.unit (B : Domain) : Aut B :=
  ⟨Equiv.refl _,Equiv.refl _,Equiv.refl _,fun _ _ => rfl,fun _ => rfl⟩

def Aut.thenDo {B : Domain} (f g : Aut B) : Aut B where
  s := f.s.trans g.s
  v := f.v.trans g.v
  a := f.a.trans g.a
  bit x q := (g.bit _ _).trans (f.bit x q)
  label x := (g.label _).trans (congrArg g.a (f.label x))

def acted {B : Domain} (f : Aut B) (u : Set Sample) : Set Sample :=
  {x | f.s.symm x ∈ u}

def branch (B : Domain) (u : Set Sample) (q : Var) (b : Bool) : Set Sample :=
  {x | x ∈ u ∧ B.val x q = b}

def plain (B : Domain) (u : Set Sample) : Prop := ∃ a, ∀ x ∈ u, B.tag x = a

structure Chart (B : Domain) where
  state : Key → Set Sample
  wt : Key → Nat
  root : Key
  start : state root = Set.univ
  rich : ∀ k, ¬ plain B (state k)
  next : Key → Var → Bool → Option Key
  proper : ∀ k q b, match next k q b with
    | none => plain B (branch B (state k) q b)
    | some j => ∃ f : Aut B, branch B (state k) q b = acted f (state j)
  subadd : ∀ k q, wt k ≤ ((next k q false).map wt).getD 1 + ((next k q true).map wt).getD 1

theorem actedChain {B : Domain} (f g : Aut B) (u : Set Sample) :
    acted g (acted f u) = acted (f.thenDo g) u := rfl

theorem branchAct {B : Domain} (f : Aut B) (u : Set Sample) (q : Var) (b : Bool) :
    branch B (acted f u) q b = acted f (branch B u (f.v.symm q) b) := by
  ext x
  have eq := f.bit (f.s.symm x) (f.v.symm q)
  simp only [Equiv.apply_symm_apply] at eq
  change (_ ∧ B.val x q = b) ↔ (_ ∧ B.val (f.s.symm x) (f.v.symm q) = b)
  rw [eq]
  rfl

theorem actedPlain {B : Domain} (f : Aut B) {s : Set Sample} (h : plain B s) : plain B (acted f s) := by
  obtain ⟨a,ha⟩ := h
  refine ⟨f.a a,?_⟩
  intro x hx
  simpa [ha _ hx] using f.label (f.s.symm x)

theorem actedRich {B : Domain} (f : Aut B) {s : Set Sample} (h : ¬ plain B s) : ¬ plain B (acted f s) := by
  rintro ⟨a,ha⟩
  apply h
  refine ⟨f.a.symm a,?_⟩
  intro x hx
  apply f.a.injective
  rw [Equiv.apply_symm_apply,←f.label]
  exact ha _ (by simpa [acted] using hx)

def Classified {B : Domain} (c : Chart B) (s : Set Sample) : Prop :=
  plain B s ∨ ∃ k, ∃ f : Aut B, s = acted f (c.state k)

theorem classifyBranch {B : Domain} {c : Chart B} {s : Set Sample}
    (h : Classified c s) (q : Var) (b : Bool) : Classified c (branch B s q b) := by
  rcases h with ⟨a,h⟩ | ⟨k,f,rfl⟩
  · exact Or.inl ⟨a,fun x hx => h x hx.1⟩
  · rw [branchAct]
    have hi := c.proper k (f.v.symm q) b
    cases e : c.next k (f.v.symm q) b with
    | none =>
      rw [e] at hi
      exact Or.inl (actedPlain f hi)
    | some j =>
      rw [e] at hi
      obtain ⟨g,hg⟩ := hi
      exact Or.inr ⟨j,g.thenDo f,by rw [hg,actedChain]⟩

theorem chartAll {B : Domain} (c : Chart B) (qs : List (Var × Bool)) :
    Classified c (qs.foldl (fun s q => branch B s q.1 q.2) Set.univ) := by
  have walk (xs : List (Var × Bool)) (s : Set Sample) (h : Classified c s) :
      Classified c (xs.foldl (fun t q => branch B t q.1 q.2) s) := by
    induction xs generalizing s with
    | nil => exact h
    | cons a tail ih => exact ih _ (classifyBranch h _ _)
  apply walk
  exact Or.inr ⟨c.root,Aut.unit B,by rw [c.start]; rfl⟩

inductive Tree
  | leaf
  | node (v : Var) (no yes : Tree)

def leaves : Tree → Nat
  | .leaf => 1
  | .node _ l r => leaves l + leaves r

theorem leafPos (t : Tree) : 1 ≤ leaves t := by
  induction t with
  | leaf => decide
  | node q l r h k => simp only [leaves]; omega

def rawValid (B : Domain) : Tree → Set Sample → Prop
  | .leaf,s => plain B s
  | .node q l r,s => rawValid B l (branch B s q false) ∧ rawValid B r (branch B s q true)

theorem rawLower {B : Domain} (c : Chart B) (t : Tree) (k : Key) (f : Aut B)
    (good : rawValid B t (acted f (c.state k))) : c.wt k ≤ leaves t := by
  induction t generalizing k f with
  | leaf => exact False.elim (actedRich f (c.rich k) good)
  | node q l r hl hr =>
    let u := f.v.symm q
    have one (b : Bool) (sub : Tree) (ih : ∀ j (g : Aut B), rawValid B sub (acted g (c.state j)) → c.wt j ≤ leaves sub)
        (ok : rawValid B sub (branch B (acted f (c.state k)) q b)) :
        ((c.next k u b).map c.wt).getD 1 ≤ leaves sub := by
      cases e : c.next k u b with
      | none => exact leafPos sub
      | some j =>
        have hg := c.proper k u b
        rw [e] at hg
        obtain ⟨g,he⟩ := hg
        have hi : branch B (acted f (c.state k)) q b = acted (g.thenDo f) (c.state j) := by
          rw [branchAct]; change acted f (branch B (c.state k) u b) = _
          rw [he,actedChain]
        exact ih j _ (hi ▸ ok)
    exact (c.subadd k u).trans (Nat.add_le_add (one false l hl good.1) (one true r hr good.2))

end PCX150.SmallChart

namespace PCX150.Chart48
open PCX150.SmallChart
abbrev G := Fin 5
abbrev ID := Fin 144
def vars : Array Nat := #[205163979670851,205150245839376,148896472117776,204132939153921,188667281092896]
def samp : Array Nat := #[2162696249821217618215137618282995761805161463866772981130851447475637340800225444037497314043350055714587078,2124316537260600494142276225985762821656081576118724669733229319233394180619356984075646928639684086222827521,2198800641771726253250707320465942554279185016594663310005348741055887738735616140179568159580534921302900994,2162705622156956155524194547248590888843364879373837413591619490913386944305282635826338639645551936198148290,1751495602169449824780452133844769261384469437309448667367654039628175301793608141872959730519764771391422465]
def tags : Array Nat := #[876760607630163527048800059361281,838692637284318602340861100524608,875377867290620207656823162997792,877989843170706854949760033458208,626749673298397928820772366813216]
def rm : Array Nat := #[4296015872,1125902054326274,2155872258,309238177792,12890144768,1125970773803010,1125970782191618,281479272726593,9183121115218432,282575562080321,3231711235,282578784354369,282575564177473,4503917454958720,282853662261313,2322172853895240,36030450582421600,36310276291690593,4503986174435456,4503676940984450,36311375803318369,582090322712985730,4785384918097921,2603647830605897,36311100925411425,38350969872859240,36312200437039201,2330977826258952,281789586743361,36311100925485153,4785384918098113,11821949374219020,4516905440780430,595604368724987922,4503989410865283,14500669728268293,7116327023042761,329045085298696417,326590700467601640,230673451842052101,14500669728269253,331376049949597929,7683709651673549,12099026320933644,13700304749503119,16831647554528205,1094567102241287871,1152921504606846975]
def weight : Array Nat := #[2,3,3,4,2,4,5,5,5,5,3,6,6,6,7,7,7,6,7,7,7,8,8,8,7,8,8,9,9,8,9,11,9,12,10,13,13,13,13,14,14,17,17,15,19,23,29,43]
def words : Array Nat := #[0,1,2,3,4,5,17,25,33,41,10,26,34,42,19,35,43,44,37,81,209,273,337,153,281,345,353,297,202,266,330,154,282,346,354,298,83,275,339,355,299,300,1617,2129,2641,1233,2257,2769,2833,2385,665,2201,2713,2841,2393,2401,1226,2250,2762,2826,2378,666,2202,2714,2842,2394,2402,2131,2643,2835,2387,2403,9809,18001,22097,22609,19025,5329,17617,21713,22737,19153,19217,17049,21145,22681,19097,19225,5322,17610,21706,22730,19146,19210,17050,21146,22682,19098,19226,22611,19027,19219,42577,140881,173649,181841,153169,153681,136401,169169,181457,152785,153809,180889,152217,153753,136394,169162,181450,152778,153802,180890,152218,153754,153683,1091153,1353297,1451601,1222225,1230417,1447121,1217745,1230033,1229465,1447114,1217738,1230026,1229466,11576913,9741905,9840209,9835729,9835722,78685777]
def lab : Array Nat := #[0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,3,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15,16,16,17,17,18,18,19,19,20,20,21,21]
def cols : Array Nat := #[729761264001255936,364805838240031872,58354402365559104,326590701323239464,595657351441551378,230673451842052101,90657122719368468,180640694878079073,881623687009141386,5912485265682627,12099026304418572,1134909993020230704]
def bound : Array Nat := #[538268735057276698148032818307065219936903198283014953358923956780677536819942850242890304553205760,538269256538488514384162552750189572805310722771986366288709298208732214187473396149793011380771008,538269778019701066356742971929272630059099925246598489253571807271743014621838164853091315805585471,538270299500912616876428557405068801697147823820519045138883596591678061623432465554701140674723843,538270820982124235337354173631657741024772027126547668620610255679296665656388669061398013175382020,538271342463336052047768193837752383089907752242692546395786392885910448225350855798839468521148289,538271863944547936346488009801479095892403172781576928675046442073576755926889218454545644415618945,538272385425760867626625862102760796386165762760920307356322518129707788065031296522250603579031559,538272905156500766443108513065369317041708568762534647923702093842356658266821308496139630627913791,538273428388183589711373858776294641910844417093252293990782242762315493497379666978810459928388483,538273949869395936318810126124100462754281549497740041727918895024651978388697535735100951101505599,538274471350608276166304277679751488401409621333068263696017456929647368976690433886918836004831243,538274992831819242604754295200724777820590550881968340029989257580498113508706476668366657917297539,538275514313031127374979499056138697359851683567541417956217325286840594361260696013447673142034445,538276035794243360747015885429852572826124209140990971426163743953392211972732415128892094171561998,538276842588900287613713764195706676224167049845152584474167342240539335744210017514414202831224847,8210935981313464207303642673531011776159086553216937335900125457581773914996661784973199784971059216,73272902932604610420036870157536400652326913083632616291714030090161894913919217964180355688980004881,538278121719090549454486549973880444008146386409356623949437032032239010812143567593609866739957778,538278643200302728876672835513910814295334555055533520541678671153582469755608023022124445167763475,73272905018529455885907656347384293463288078410724482762143185079522703273336082389609338014490673172,12021642714081996388115187691064001916994023436508337678951193881981524391710541908729120294496652232,538280207643938154942151045426220907057630261879816340006700076160044125805351317254509978543194958,538281014437471369034359396148358135313611030222761666854009352164581083121773775918976271943450647,8210773800657187842450702043769927230216753452307810061477961553333273806060039908740084927428542488,73272907389770475404473780227855937336046598631729832801657986665000761855547474412156408208504635417,8210741468822175688784375851528141942691348369779297262523972806564205865176036145723393182467604506,538282829913949782613786499879044261729609061098369591742339269591925191358496908223301606507012762,538283336531209696326906865238153228120465319417122620678190038468416364577908582197572683783217879,57990787607173543562964587864197087933400489757722923477508596161155880340703112137034694538963173405,538284379493634094889820409844606642196500385101432414835725334096532331681857928452251746026129177,538284899956389227892558916924470067998783345048157735682045083732086557518399686318372247782424785,538285612073333914880439379573525300777569415246909905287533586520290764107308491195536593292083232,30190551819297157306895627107820570633510844730208030420894227934123905195516278548573050516125466772,538286465418481162181876574068358400235743343515935276248182275721255525554892449177559713509868126,538287040467347836282951397718802103372519239556242708545061451746137386737772233427339712742507354,538287508670333174588038310469759840636637503503260196428721042124965305636376612286265543067942948,4990481836010083953925990327928264829233735805677075544831425634814654689694087535748976141975666725,4992350824958676661032061808363270825607902639635285870905867626945799892419716024126815405891108902,11474540664384530795261838669345740386371263272951364135411814884895652401053664882877597379849396571,538289788556211066945809738712428459099483457395296971423289575173983144375503294890033704447744288,4989684491526541388212128843925278606681550665566138576901749021922556716775820252848002954007920681,538290664624789112969384686648112981552147623688536516881619820731295230805674216305742156875677738,538291225208098235941059780703506472209378715478932681606304621642847993992222289527826165924201634,538291870566129617220051072053606863194104989936617742843622682016438733782703720838793512483216162,538292329154972782007624731635222049671277488321919676363157486963497117172870256396228987355217962,33654634875485059881322937237765257811134583756154723274761472150882025045230030582607602805856913707,6348845023310766790018526439914031813924028716646621184500080589437918446272198264846895864862065838]

def bits (s : Nat) : Set Sample := {p : Sample | s.testBit p.val = true}
def geo : Domain :=
  ⟨fun r v => cols[v.val]!.testBit r.val,fun r => Fin.ofNat 22 lab[r.val]!⟩
def vs (g : G) (v : Var) : Var := Fin.ofNat 12 ((vars[g.val]! >>> (4*v.val)) % 16)
def rs (g : G) (r : Sample) : Sample := Fin.ofNat 60 ((samp[g.val]! >>> (6*r.val)) % 64)
def ls (g : G) (k : Tag) : Tag := Fin.ofNat 22 ((tags[g.val]! >>> (5*k.val)) % 32)
theorem gInv : ∀ g : G, (∀ q : Var, vs g (vs g q)=q) ∧
    (∀ r : Sample,rs g (rs g r) = r) ∧ (∀ k : Tag,ls g (ls g k)=k) := by decide +kernel
theorem gRule : ∀ g : G, ∀ r : Sample,
    geo.tag (rs g r) = ls g (geo.tag r) ∧
    ∀ v : Var, geo.val (rs g r) (vs g v) = geo.val r v := by decide +kernel
def gen (g : G) : Aut geo where
  s := ⟨rs g,rs g,(gInv g).2.1,(gInv g).2.1⟩
  v := ⟨vs g,vs g,(gInv g).1,(gInv g).1⟩
  a := ⟨ls g,ls g,(gInv g).2.2,(gInv g).2.2⟩
  bit r v := (gRule g r).2 v
  label r := (gRule g r).1

def assemble (w : Nat) : Nat → Aut geo
  | 0 => Aut.unit geo
  | d+1 =>
    let t := (w >>> (3*d)) % 8
    let prev := assemble w d
    if t=0 then prev else prev.thenDo (gen (Fin.ofNat 5 (t-1)))

def backward (w : Nat) : Nat → Sample → Sample
  | 0,r => r
  | d+1,r =>
    let t := (w >>> (3*d)) % 8
    if t=0 then backward w d r else backward w d (rs (Fin.ofNat 5 (t-1)) r)

theorem backApply (w d : Nat) (r : Sample) : (assemble w d).s.symm r = backward w d r := by
  induction d generalizing r with
  | zero => rfl
  | succ d ih =>
    simp only [assemble,backward]
    split
    · apply ih
    · exact ih _

def orient (o : ID) := assemble words[o.val]! 9
def slot (k : Key) (q : Var) (b : Bool) : Nat :=
  (bound[k.val]! >>> (14*(2*q.val+b.toNat))) % 16384
def index (code : Nat) : Key := Fin.ofNat 48 (code%64)
def turn (code : Nat) : ID := Fin.ofNat 144 (code/64)
def mono (code : Nat) : Tag := Fin.ofNat 22 (code/64)
def node (k : Key) := bits rm[k.val]!
def next (k : Key) (q : Var) (b : Bool) : Option Key :=
  let d := slot k q b
  if d%64=63 then none else some (index d)

def pointTest (k : Key) (q : Var) (b : Bool) (r : Sample) : Prop :=
  let d := slot k q b
  let keep := (rm[k.val]!.testBit r.val && (geo.val r q == b))
  if d % 64 = 63 then keep = true → geo.tag r = mono d
  else keep = rm[(index d).val]!.testBit (backward words[(turn d).val]! 9 r).val
instance (k : Key) (q : Var) (b : Bool) (r : Sample) : Decidable (pointTest k q b r) := by
  unfold pointTest; dsimp only; split <;> infer_instance

theorem allSteps : ∀ (k : Key) (q : Var) (b : Bool) (r : Sample), pointTest k q b r := by decide +kernel
theorem allCost : ∀ (k : Key) (q : Var), weight[k.val]! ≤ ((next k q false).map (fun (j : Key) => weight[j.val]!)).getD 1 +
    ((next k q true).map (fun (j : Key) => weight[j.val]!)).getD 1 := by decide +kernel

def witnessRow (k : Key) (a : Tag) : Prop :=
  ∃ r : Sample, rm[k.val]!.testBit r.val = true ∧ geo.tag r ≠ a
instance (k : Key) (a : Tag) : Decidable (witnessRow k a) := by unfold witnessRow; infer_instance
theorem spread : ∀ k a, witnessRow k a := by decide +kernel

def chart : Chart geo where
  state := node
  wt k := weight[k.val]!
  root := 47
  start := by
    ext r
    have h : ∀ p : Sample, rm[47]!.testBit p.val = true := by decide +kernel
    exact iff_of_true (h r) trivial
  rich k := by
    rintro ⟨a,ha⟩
    obtain ⟨r,inside,ne⟩ := spread k a
    exact ne (ha r inside)
  next := next
  proper k q b := by
    let d := slot k q b
    have facts := allSteps k q b
    by_cases hom : d%64=63
    · simp only [next,show slot k q b % 64 = 63 from hom,ite_true]
      refine ⟨mono d,?_⟩
      intro r h
      have both : (rm[k.val]!.testBit r.val && (geo.val r q == b)) = true := by
        have hl : rm[k.val]!.testBit r.val = true := h.1
        simp [hl,h.2]
      have e := facts r
      change (if d%64=63 then _ else _) at e
      rw [if_pos hom] at e
      exact e both
    · simp only [next,show ¬slot k q b % 64 = 63 from hom,ite_false]
      refine ⟨orient (turn d),?_⟩
      ext r
      have e := facts r
      change (if d%64=63 then _ else _) at e
      rw [if_neg hom] at e
      change (_ ∧ geo.val r q = b) ↔ (rm[(index d).val]!.testBit ((assemble words[(turn d).val]! 9).s.symm r).val = true)
      rw [backApply,←e]
      simp [node,bits]
  subadd := allCost

theorem rootWeight : chart.wt chart.root = 43 := by decide +kernel
end PCX150.Chart48

namespace PCX150.Bands

structure Part where
  destination : Nat
  distance : Nat
  down : Bool
  deriving Inhabited, DecidableEq

def readBit (p : Part) (r : Nat) : Option Nat :=
  if p.down then some (p.distance + r) else
  if p.distance ≤ r then some (r-p.distance) else none

def applyPart (p : Part) (m : Nat) : Nat :=
  p.destination &&& (if p.down then m >>> p.distance else m <<< p.distance)

def roll (ps : List Part) (m : Nat) : Nat :=
  ps.foldr (fun p t => applyPart p m ||| t) 0

theorem testPart (p : Part) (m r : Nat) :
    (applyPart p m).testBit r = (p.destination.testBit r &&
      ((readBit p r).map (fun x => m.testBit x)).getD false) := by
  by_cases b : p.down = true
  · simp [applyPart,readBit,b,Nat.testBit_and,Nat.testBit_shiftRight,Nat.add_comm]
  · by_cases d : p.distance ≤ r <;>
      simp [applyPart,readBit,b,d,Nat.testBit_and,Nat.testBit_shiftLeft]

theorem rollBit (ps : List Part) (m r : Nat) :
    (roll ps m).testBit r = true ↔
      ∃ p ∈ ps, p.destination.testBit r = true ∧ ∃ x, readBit p r = some x ∧ m.testBit x = true := by
  induction ps with
  | nil => simp [roll]
  | cons p ps ih =>
    change ((applyPart p m ||| roll ps m).testBit r = true) ↔ _
    rw [Nat.testBit_or,Bool.or_eq_true,testPart,Bool.and_eq_true,ih]
    simp only [List.mem_cons]
    cases h : readBit p r with
    | none => simp [h]
    | some k => simp [h]

def routes (ps : List Part) (r src : Nat) : Prop :=
  (∃ p ∈ ps, p.destination.testBit r = true) ∧
  ∀ p ∈ ps, p.destination.testBit r = true → readBit p r = some src

instance (ps : List Part) (r src : Nat) : Decidable (routes ps r src) := by
  unfold routes
  infer_instance

theorem rollCorrect {ps : List Part} {r src : Nat} (h : routes ps r src) (m : Nat) :
    (roll ps m).testBit r = m.testBit src := by
  apply Bool.eq_iff_iff.mpr
  rw [rollBit]
  constructor
  · rintro ⟨p,mem,y,x,hx,val⟩
    rw [h.2 p mem y] at hx
    have e := Option.some.inj hx
    simpa [e] using val
  · intro bit
    obtain ⟨p,mem,y⟩ := h.1
    exact ⟨p,mem,y,src,h.2 p mem y,bit⟩

end PCX150.Bands

namespace PCX150.Scalar
open PCX150.Chart48 PCX150.SmallChart PCX150.Bands
def quickGen (g : Nat) (m : Nat) : Nat :=
  match g with
  | 0 => ((m <<< 6) &&& 4032) ||| ((m <<< 2) &&& 229739669779120128) ||| ((m <<< 1) &&& 576601524162699264) ||| (m &&& 844631138893824) ||| ((m >>> 1) &&& 288300762081349632) ||| ((m >>> 2) &&& 57434917444780032) ||| ((m >>> 6) &&& 63)
  | 1 => ((m <<< 6) &&& 258048) ||| ((m <<< 3) &&& 4194304) ||| ((m <<< 2) &&& 868280810792288256) ||| ((m <<< 1) &&& 36037595259469866) ||| (m &&& 13514098222301184) ||| ((m >>> 1) &&& 18018797629734933) ||| ((m >>> 2) &&& 217070202698072064) ||| ((m >>> 3) &&& 524288) ||| ((m >>> 6) &&& 4032)
  | 2 => ((m <<< 6) &&& 16515072) ||| ((m <<< 4) &&& 270281964446023680) ||| ((m <<< 3) &&& 1040) ||| ((m <<< 2) &&& 2340) ||| ((m <<< 1) &&& 563087425929216) ||| (m &&& 864902286227275776) ||| ((m >>> 1) &&& 281543712964608) ||| ((m >>> 2) &&& 585) ||| ((m >>> 3) &&& 130) ||| ((m >>> 4) &&& 16892622777876480) ||| ((m >>> 6) &&& 258048)
  | 3 => ((m <<< 12) &&& 281406257233920) ||| ((m <<< 2) &&& 3195660) ||| ((m <<< 1) &&& 768426686428612640) ||| ((m >>> 1) &&& 384213343214306320) ||| ((m >>> 2) &&& 798915) ||| ((m >>> 12) &&& 68702699520)
  | 4 => ((m <<< 12) &&& 1152640029630136320) ||| ((m <<< 2) &&& 12782640) ||| ((m <<< 1) &&& 45802332290) ||| ((m >>> 1) &&& 22901166145) ||| ((m >>> 2) &&& 3195660) ||| ((m >>> 12) &&& 281406257233920)
  | _ => m

def useWord (w : Nat) : Nat → Nat → Nat
  | 0,m => m
  | d+1,m =>
    let z := (w >>> (3*d))%8
    let t := useWord w d m
    if z=0 then t else quickGen (z-1) t

def permute (o m : Nat) := useWord words[o]! 9 m

def parts (g : G) : List Part :=
  match g.val with
  | 0 => [⟨4032,6,false⟩,⟨229739669779120128,2,false⟩,⟨576601524162699264,1,false⟩,⟨844631138893824,0,true⟩,⟨288300762081349632,1,true⟩,⟨57434917444780032,2,true⟩,⟨63,6,true⟩]
  | 1 => [⟨258048,6,false⟩,⟨4194304,3,false⟩,⟨868280810792288256,2,false⟩,⟨36037595259469866,1,false⟩,⟨13514098222301184,0,true⟩,⟨18018797629734933,1,true⟩,⟨217070202698072064,2,true⟩,⟨524288,3,true⟩,⟨4032,6,true⟩]
  | 2 => [⟨16515072,6,false⟩,⟨270281964446023680,4,false⟩,⟨1040,3,false⟩,⟨2340,2,false⟩,⟨563087425929216,1,false⟩,⟨864902286227275776,0,true⟩,⟨281543712964608,1,true⟩,⟨585,2,true⟩,⟨130,3,true⟩,⟨16892622777876480,4,true⟩,⟨258048,6,true⟩]
  | 3 => [⟨281406257233920,12,false⟩,⟨3195660,2,false⟩,⟨768426686428612640,1,false⟩,⟨384213343214306320,1,true⟩,⟨798915,2,true⟩,⟨68702699520,12,true⟩]
  | 4 => [⟨1152640029630136320,12,false⟩,⟨12782640,2,false⟩,⟨45802332290,1,false⟩,⟨22901166145,1,true⟩,⟨3195660,2,true⟩,⟨281406257233920,12,true⟩]
  | _ => []
theorem paths : ∀ (g : G) (r : Sample), routes (parts g) r.val (rs g r).val := by decide +kernel
theorem genAsRoll (g : G) (m : Nat) : quickGen g.val m = roll (parts g) m := by
  fin_cases g <;> simp [quickGen,parts,roll,applyPart,Nat.and_comm,Nat.or_assoc]

theorem genExact (g : G) (m : Nat) (r : Sample) :
    (quickGen g.val m).testBit r.val = m.testBit (rs g r).val := by
  rw [genAsRoll]
  exact rollCorrect (paths g r) m

theorem wordExact (w d m : Nat) (ok : ∀ k < d, (w >>> (3*k))%8 ≤ 5) (r : Sample) :
    (useWord w d m).testBit r.val = m.testBit (backward w d r).val := by
  induction d generalizing r with
  | zero => rfl
  | succ d ih =>
    let t := (w >>> (3*d))%8
    have hr : ∀ k < d, (w >>> (3*k))%8 ≤ 5 := fun k h => ok k (by omega)
    have lim : t ≤ 5 := ok d (by omega)
    simp only [useWord,backward]
    by_cases h : t=0
    · rw [if_pos h,if_pos h]
      exact ih hr r
    · rw [if_neg h,if_neg h]
      let g := Fin.ofNat 5 (t-1)
      have ge : g.val = t-1 := Nat.mod_eq_of_lt (by omega)
      have bit := genExact g (useWord w d m) r
      rw [ge] at bit
      exact bit.trans (ih hr (rs g r))

theorem digits : ∀ (o : ID) (k : Fin 9), (words[o.val]! >>> (3*k.val)) % 8 ≤ 5 := by decide +kernel

theorem actionBit (o : ID) (m : Nat) (r : Sample) :
    (permute o.val m).testBit r.val = m.testBit ((orient o).s.symm r).val := by
  rw [orient,backApply]
  exact wordExact _ _ _ (fun k h => digits o ⟨k,h⟩) _

theorem actionSet (o : ID) (m : Nat) :
    bits (permute o.val m) = acted (orient o) (bits m) := by
  ext r
  change (_ = true) ↔ (_ = true)
  rw [actionBit]
end PCX150.Scalar



namespace PCX150.Sparse

abbrev Point := Fin 60
abbrev Query := Fin 12
abbrev Label := Fin 22
abbrev Box := Sum Label (Fin 2)

inductive TestTree where
  | leaf
  | cut (v : Query) (no yes : TestTree)

def leaves : TestTree → Nat
  | .leaf => 1
  | .cut _ t u => leaves t + leaves u

def half (bit : Point → Query → Bool) (s : Set Point) (v : Query) (b : Bool) : Set Point :=
  {p | p ∈ s ∧ bit p v = b}

def Valid (bit : Point → Query → Bool) (term : Box → Set Point) : TestTree → Set Point → Prop
  | .leaf,s => ∃ i, s ⊆ term i
  | .cut v t u,s => Valid bit term t (half bit s v false) ∧ Valid bit term u (half bit s v true)

theorem coverExists (bit : Point → Query → Bool) (term : Box → Set Point)
    {t : TestTree} {s : Set Point} (h : Valid bit term t s) :
    ∃ f : Finset Box, f.card ≤ leaves t ∧ ∀ p ∈ s, ∃ i ∈ f, p ∈ term i := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,hi⟩ := h
    exact ⟨{i},by simp [leaves],fun p hp => ⟨i,by simp,hi hp⟩⟩
  | cut v t u ht hu =>
    obtain ⟨a,ha,ca⟩ := ht h.1
    obtain ⟨b,hb,cb⟩ := hu h.2
    refine ⟨a ∪ b,(Finset.card_union_le _ _).trans (Nat.add_le_add ha hb),?_⟩
    intro p hp
    cases m : bit p v with
    | false =>
      obtain ⟨i,hi,hit⟩ := ca p ⟨hp,m⟩
      exact ⟨i,Finset.mem_union_left _ hi,hit⟩
    | true =>
      obtain ⟨i,hi,hit⟩ := cb p ⟨hp,m⟩
      exact ⟨i,Finset.mem_union_right _ hi,hit⟩

def box (tag : Point → Label) (A B : Set Point) : Box → Set Point
  | .inl i => {p | tag p = i}
  | .inr i => if i = 0 then A else B

noncomputable def liveTags (tag : Point → Label) (s : Set Point) : Finset Label := by
  classical
  exact Finset.univ.filter (fun k => ∃ p ∈ s, tag p = k)

theorem ofLive {tag : Point → Label} {s : Set Point} {i : Label}
    (hi : i ∈ liveTags tag s) : ∃ p ∈ s, tag p = i := by
  classical
  unfold liveTags at hi
  exact (Finset.mem_filter.mp hi).2

noncomputable def residual (tag : Point → Label) (s A B : Set Point) (x y : Bool) : Finset Box := by
  classical
  exact ((liveTags tag {p | p ∈ s ∧ (x = true → p ∉ A) ∧ (y = true → p ∉ B)}).map
      ⟨Sum.inl,Sum.inl_injective⟩) ∪
    (if x then {Sum.inr 0} else ∅) ∪ (if y then {Sum.inr 1} else ∅)

theorem cheapLower (bit : Point → Query → Bool) (tag : Point → Label)
    {t : TestTree} {s A B : Set Point} (h : Valid bit (box tag A B) t s) (k : Nat)
    (hk : ∀ x y : Bool, k ≤ (residual tag s A B x y).card) : k ≤ leaves t := by
  classical
  obtain ⟨f,hf,cover⟩ := coverExists _ _ h
  let x := decide ((Sum.inr 0 : Box) ∈ f)
  let y := decide ((Sum.inr 1 : Box) ∈ f)
  have subset : residual tag s A B x y ⊆ f := by
    intro u hu
    simp only [residual,Finset.mem_union] at hu
    rcases hu with (lab | fst) | snd
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp lab
      obtain ⟨p,⟨ps,pa,pb⟩,eq⟩ := ofLive hi
      obtain ⟨b,mem,hit⟩ := cover p ps
      cases b with
      | inl j =>
        change tag p = j at hit
        have ji : j=i := hit.symm.trans eq
        simpa [ji] using mem
      | inr j =>
        fin_cases j
        · exact False.elim (pa (by simpa [x] using mem) (by simpa [box] using hit))
        · exact False.elim (pb (by simpa [y] using mem) (by simpa [box] using hit))
    · by_cases hx : (Sum.inr 0 : Box) ∈ f
      · have e : u = Sum.inr 0 := by simpa [x,hx] using fst
        simpa [e] using hx
      · simp [x,hx] at fst
    · by_cases hy : (Sum.inr 1 : Box) ∈ f
      · have e : u = Sum.inr 1 := by simpa [y,hy] using snd
        simpa [e] using hy
      · simp [y,hy] at snd
  exact (hk x y).trans ((Finset.card_le_card subset).trans hf)

end PCX150.Sparse

namespace PCX150.Scoring
open PCX150.Sparse
def bitset (m : Nat) : Set Point := {p : Point | m.testBit p.val = true}
def tags : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,13194139533312,52776558133248,211106232532992,844424930131968,3377699720527872,13510798882111488,54043195528445952,216172782113783808,864691128455135232]
def label (p : Point) : Label := Fin.ofNat 22 (#[0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,3,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15,16,16,17,17,18,18,19,19,20,20,21,21][p.val]!)
def present (m : Nat) : Nat :=
  (List.range 22).foldl (fun n k => if m &&& tags[k]! != 0 then n+1 else n) 0
def apart (a b : Nat) := a ^^^ (a &&& b)
theorem tagBits : ∀ (k : Label) (p : Point),
    (tags[k.val]!).testBit p.val = decide (label p=k) := by decide +kernel
theorem tagSmall : ∀ k : Label, tags[k.val]! < 2^60 := by decide +kernel

theorem tagHit (m : Nat) (k : Label) (h : m &&& tags[k.val]! ≠ 0) :
    ∃ p ∈ bitset m, label p = k := by
  classical
  by_contra no
  apply h
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_and]
  by_cases sm : n < 60
  · let p : Point := ⟨n,sm⟩
    have e := tagBits k p
    change (tags[k.val]!).testBit n = _ at e
    rw [e]
    by_cases bit : m.testBit n = true
    · have ne : label p ≠ k := fun eq => no ⟨p,bit,eq⟩
      simp [ne]
    · simp [show m.testBit n = false by cases z : m.testBit n <;> simp_all]
  · have low := Nat.testBit_lt_two_pow (lt_of_lt_of_le (tagSmall k)
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 60 ≤ n)))
    simp [low]

theorem presentBound (m : Nat) : present m ≤ (liveTags label (bitset m)).card := by
  classical
  let test := fun k : Nat => m &&& tags[k]! != 0
  let ls := (List.range 22).filter test
  have fold (ws : List Nat) (n : Nat) :
      ws.foldl (fun v k => if test k then v+1 else v) n = n+(ws.filter test).length := by
    induction ws generalizing n with
    | nil => simp
    | cons a as ih =>
      cases h : test a <;> simp [h,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have size : present m = ls.length := by simpa [present,ls,test] using fold (List.range 22) 0
  let target := (liveTags label (bitset m)).image Fin.val
  have subset : ls.toFinset ⊆ target := by
    intro k hk
    have hit := List.mem_filter.mp (List.mem_toFinset.mp hk)
    have kt := List.mem_range.mp hit.1
    let v : Label := ⟨k,kt⟩
    have ne : m &&& tags[v.val]! ≠ 0 := by simpa [test,v] using hit.2
    have witness := tagHit m v ne
    have live : v ∈ liveTags label (bitset m) := by
      unfold liveTags
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,witness⟩
    exact Finset.mem_image.mpr ⟨v,live,rfl⟩
  have h := Finset.card_le_card subset
  have nd : ls.Nodup := List.nodup_range.filter _
  rw [size,←List.toFinset_card_of_nodup nd]
  exact h.trans (Finset.card_image_le)

theorem apartSet (m a : Nat) (p : Point) :
    p ∈ bitset (apart m a) ↔ p ∈ bitset m ∧ p ∉ bitset a := by
  change (apart m a).testBit p.val = true ↔ m.testBit p.val = true ∧ ¬ a.testBit p.val = true
  simp only [apart,Nat.testBit_xor,Nat.testBit_and]
  cases m.testBit p.val <;> cases a.testBit p.val <;> decide

theorem countResidual (s a b : Set Point) (x y : Bool) :
    (residual label s a b x y).card =
    (liveTags label {p | p ∈ s ∧ (x = true → p ∉ a) ∧ (y = true → p ∉ b)}).card + x.toNat + y.toNat := by
  classical
  cases x <;> cases y <;> simp [PCX150.Sparse.residual,Finset.union_singleton,Finset.mem_map,Finset.card_insert_of_notMem]

def basic (s a b : Nat) := min (present s) (min (1+present (apart s a))
       (min (1+present (apart s b)) (2+present (apart (apart s a) b))))

theorem numericalLeafCover (val : Point → Query → Bool) (s a b : Nat) (t : TestTree)
    (v : Valid val (box label (bitset a) (bitset b)) t (bitset s)) : basic s a b ≤ leaves t := by
  apply cheapLower val label v
  intro x y
  rw [countResidual]
  cases x <;> cases y
  · have eq : {p | p ∈ bitset s ∧ (false=true → p ∉ bitset a) ∧ (false=true → p ∉ bitset b)} = bitset s := by ext; simp
    rw [eq]
    unfold basic
    exact (min_le_left _ _).trans (by simpa using presentBound s)
  · have eq : {p | p ∈ bitset s ∧ (false=true → p ∉ bitset a) ∧ (true=true → p ∉ bitset b)} = bitset (apart s b) := by ext p; simp [apartSet]
    rw [eq]
    have z := presentBound (apart s b)
    unfold basic
    simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
    omega
  · have eq : {p | p ∈ bitset s ∧ (true=true → p ∉ bitset a) ∧ (false=true → p ∉ bitset b)} = bitset (apart s a) := by ext p; simp [apartSet]
    rw [eq]
    have z := presentBound (apart s a)
    unfold basic
    simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
    omega
  · have eq : {p | p ∈ bitset s ∧ (true=true → p ∉ bitset a) ∧ (true=true → p ∉ bitset b)} = bitset (apart (apart s a) b) := by
      ext p; simp [apartSet,and_assoc]; aesop
    rw [eq]
    have z := presentBound (apart (apart s a) b)
    unfold basic
    simp only [Bool.toNat_true]
    omega
end PCX150.Scoring

namespace PCX150
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev Cl := Clause V
inductive ResTree (F : Set Cl) : Cl → Nat → Prop where
  | ax {C : Cl} : C ∈ F → ResTree F C 0
  | res {C D R : Cl} {i j : Nat} : ResTree F C i → ResTree F D j →
      IsResolvent C D R → ResTree F R (i+j+1)
end PCX150

namespace PCX150.Sparse
open PCX150.SmallChart (Domain Aut)

def renamed {B : Domain} (f : Aut B) : TestTree → TestTree
  | .leaf => .leaf
  | .cut q l r => .cut (f.v q) (renamed f l) (renamed f r)

theorem sameLeaves {B : Domain} (f : Aut B) (t : TestTree) : leaves (renamed f t) = leaves t := by
  induction t with
  | leaf => rfl
  | cut q l r hl hr => simp [renamed,leaves,hl,hr]

theorem smaller {bit : Point → Query → Bool} {base newer : Box → Set Point}
    {t : TestTree} {s d : Set Point} (h : Valid bit base t s) (sub : d ⊆ s)
    (relax : ∀ i, ∃ j, ∀ p ∈ d, p ∈ base i → p ∈ newer j) : Valid bit newer t d := by
  induction t generalizing s d with
  | leaf =>
    obtain ⟨i,all⟩ := h
    obtain ⟨j,hj⟩ := relax i
    exact ⟨j,fun p hp => hj p hp (all (sub hp))⟩
  | cut q l r hl hr =>
    constructor
    · exact hl h.1 (fun _ hd => ⟨sub hd.1,hd.2⟩)
        (fun i => (relax i).imp (fun _ h p hp => h p hp.1))
    · exact hr h.2 (fun _ hd => ⟨sub hd.1,hd.2⟩)
        (fun i => (relax i).imp (fun _ h p hp => h p hp.1))

theorem moveTree {B : Domain} (f : Aut B) {t : TestTree} {s : Set Point}
    {old newT : Box → Set Point} (good : Valid B.val old t s)
    (go : ∀ i, ∃ j, ∀ p ∈ s, p ∈ old i → f.s p ∈ newT j) :
    Valid B.val newT (renamed f t) (SmallChart.acted f s) := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,full⟩ := good
    obtain ⟨j,hj⟩ := go i
    refine ⟨j,?_⟩
    intro p hp
    simpa using hj (f.s.symm p) hp (full hp)
  | cut q l r hl hr =>
    have step (b : Bool) : half B.val (SmallChart.acted f s) (f.v q) b =
        SmallChart.acted f (half B.val s q b) := by
      change SmallChart.branch B (SmallChart.acted f s) (f.v q) b = _
      rw [SmallChart.branchAct,Equiv.symm_apply_apply]
      try rfl
    constructor
    · rw [step]
      exact hl good.1 (fun i => (go i).imp (fun _ h p hp => h p hp.1))
    · rw [step]
      exact hr good.2 (fun i => (go i).imp (fun _ h p hp => h p hp.1))

theorem transferTree {F : Set PCX150.Cl} (vCode : PCX150.V → Query) (bit : Point → Query → Bool)
    (A : Point → PCX150.V → Bool) (correct : ∀ p v, bit p (vCode v) = A p v)
    (term : Box → Set Point) (raw : ∀ C ∈ F, ∃ i, ∀ p, ¬PEqualNP.ProofComplexity.ClauseSat (A p) C → p ∈ term i)
    {C : PCX150.Cl} {n : Nat} (h : PCX150.ResTree F C n) (s : Set Point)
    (f : ∀ p ∈ s, ¬PEqualNP.ProofComplexity.ClauseSat (A p) C) :
    ∃ t : TestTree, leaves t = n+1 ∧ Valid bit term t s := by
  induction h generalizing s with
  | ax hc =>
    obtain ⟨i,hi⟩ := raw _ hc
    exact ⟨.leaf,rfl,i,fun p hp => hi p (f p hp)⟩
  | @res C D R i j _ _ hr ihC ihD =>
    obtain ⟨v,pc,pd,rfl⟩ := hr
    have left : ∀ p ∈ half bit s (vCode v) false, ¬PEqualNP.ProofComplexity.ClauseSat (A p) C := by
      intro p hp sat
      obtain ⟨l,hl,yes⟩ := sat
      have ne : l ≠ (v,true) := by
        rintro rfl
        change A p v = true at yes
        have val : bit p (vCode v) = false := hp.2
        rw [correct,yes] at val
        contradiction
      exact f p hp.1 ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,hl⟩),yes⟩
    have right : ∀ p ∈ half bit s (vCode v) true, ¬PEqualNP.ProofComplexity.ClauseSat (A p) D := by
      intro p hp sat
      obtain ⟨l,hl,yes⟩ := sat
      have ne : l ≠ (v,false) := by
        rintro rfl
        change A p v = false at yes
        have val : bit p (vCode v) = true := hp.2
        rw [correct,yes] at val
        contradiction
      exact f p hp.1 ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,hl⟩),yes⟩
    obtain ⟨l,lc,lv⟩ := ihC _ left
    obtain ⟨r,rc,rv⟩ := ihD _ right
    exact ⟨.cut (vCode v) l r,by simp only [leaves,lc,rc]; omega,lv,rv⟩

end PCX150.Sparse

namespace PCX150.Sparse
open PCX150.SmallChart (Domain Aut acted)

structure Triple where
  points : Set Point
  a : Set Point
  b : Set Point

def admissible (g : Domain) (s : Triple) (t : TestTree) :=
  Valid g.val (box g.tag s.a s.b) t s.points

def restricted (g : Domain) (s : Triple) (q : Query) (b : Bool) : Triple :=
  ⟨half g.val s.points q b,s.a,s.b⟩

structure Embed (g : Domain) (hard easy : Triple) where
  turn : Aut g
  keep : hard.points ⊆ acted turn easy.points
  accepts : ∀ i, ∃ j, ∀ p ∈ hard.points,
    turn.s.symm p ∈ box g.tag easy.a easy.b i → p ∈ box g.tag hard.a hard.b j

theorem embedTree {g : Domain} {hard easy : Triple} (f : Embed g hard easy) {t : TestTree}
    (h : admissible g easy t) : admissible g hard (renamed f.turn t) := by
  let pre : Set Point := {p | f.turn.s p ∈ hard.points}
  have inc : pre ⊆ easy.points := by
    intro p hp
    have w := f.keep hp
    change f.turn.s.symm (f.turn.s p) ∈ easy.points at w
    simpa using w
  have localGood := smaller h inc (newer := box g.tag easy.a easy.b)
    (fun i => ⟨i,fun _ _ hi => hi⟩)
  have eq : acted f.turn pre = hard.points := by
    ext p
    change f.turn.s (f.turn.s.symm p) ∈ hard.points ↔ p ∈ hard.points
    simp
  change Valid _ _ _ hard.points
  rw [←eq]
  apply moveTree f.turn localGood
  intro i
  obtain ⟨j,hj⟩ := f.accepts i
  exact ⟨j,fun p hp ha => hj _ hp (by simpa using ha)⟩

structure Rule (g : Domain) (K : Type) where
  item : K → Triple
  weight : K → Nat
  base : ∀ i, admissible g (item i) .leaf → weight i ≤ 1
  kw : K → Query → Bool → Nat
  fork : ∀ i q, weight i ≤ kw i q false + kw i q true
  child : ∀ i q b, let s := restricted g (item i) q b
    (∀ t, admissible g s t → kw i q b ≤ leaves t) ∨
    ∃ j, Nonempty (Embed g (item j) s) ∧ kw i q b ≤ weight j

theorem soundRules {g : Domain} {K : Type} (rule : Rule g K) :
    ∀ t i, admissible g (rule.item i) t → rule.weight i ≤ leaves t := by
  have count (n : Nat) : ∀ (t : TestTree), leaves t = n →
      ∀ i, admissible g (rule.item i) t → rule.weight i ≤ leaves t := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro t eq i good
      cases t with
      | leaf => exact rule.base i good
      | cut q l r =>
        have pos (u : TestTree) : 0 < leaves u := by
          induction u with
          | leaf => decide
          | cut v a b ha hb => simp only [leaves]; omega
        have left := pos l
        have right := pos r
        change leaves l + leaves r = n at eq
        have each (b : Bool) (sub : TestTree) (lt : leaves sub < n)
            (valid : admissible g (restricted g (rule.item i) q b) sub) :
            rule.kw i q b ≤ leaves sub := by
          rcases rule.child i q b with cheap | ⟨j,⟨emb⟩,hw⟩
          · exact cheap sub valid
          · obtain hg := embedTree emb valid
            have z := ih (leaves sub) lt (renamed emb.turn sub) (sameLeaves _ _) j hg
            exact hw.trans (by simpa [sameLeaves] using z)
        exact (rule.fork i q).trans (Nat.add_le_add (each false l (by omega) good.1) (each true r (by omega) good.2))
  exact fun t => count (leaves t) t rfl

end PCX150.Sparse
namespace PCX150.Scalar
open PCX150.Chart48
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def banksB0 : Array Nat := #[0,4296015872,1075838976,4398046511108,67108868,562949953421316,8796093022216,16777224,2251799813685256,2147483650,1125899906842626,134217744,18014398509482000,281474976710657,274877906945,549755813920,34359746560,35184380477440,576460752311812096,281474976710720,8589934720,134348800,36028797018964000,9007199254773760,70368745226240,562949953421568,4503599627378688,536936448,140737490452480,2199023257600,34360262656,4398047035392]
private def banksB1 : Array Nat := #[72057594038452224,4503599627370624,17179873280,1099511631872,2199023386624,1125902054326274,2155872258,567347999932420,562950020530180,4398113619972,275951648769,281749854617601,2260595906707464,8796109799432,18014398643699728,281476050452481,36029346774777888,309237653504,576460754459295744,576495936683900928,281479271678016,4296015936,281474976710721,2251799813701640,4398047035396,2199157604352,576460752437772288,268452096,4503599627378816,140737490485248,9007199321882624,70373040193536]
private def banksB2 : Array Nat := #[67141636,562950221857024,4503633987117056,4503874505285632,562949953421572,274877915137,36028797020012576,140738564194304,1075838977,549755879456,4432406773760,72057628398190592,72061992084963328,16777736,68719476866,70368745242624,1125899906846722,288239172248928256,8796097216520,35184380477952,1126999418474496,576462951326810112,9147936743129088,36099165764190208,288230376155971584,309238177792,12890144768,3231711232,70875348994,1125970773803010,3221225475,567348067041284]
private def banksB3 : Array Nat := #[844424930131973,281750928359425,2260595910901768,206158430226,824633720865,12884902080,281479272726592,281476050452545,281479271678017,72061992084964352,35184388866568,9147936743129600,8796109799944,576460754459295746,2260595906723848,567348000456708,4398114144260,4432406773764,13510798882112128,4503608221499520,4503676936781952,576462951461027840,52776558134016,36099165764190240,140737557594112,562950020562948,13510798882152448,580542407901440,4503908865024000,562950020530436,52776566784000,844424930132288]
private def banksB4 : Array Nat := #[281749854617665,4432406781952,144255926640050176,281476052549633,144115189151694849,2199056812064,216172782116405248,9042383635218944,72062026444701696,70373040193600,216172782113786880,72061992084963332,2322168558927872,3298535018496,1125902054330370,2199157604368,1126999418474498,288239180838862848,4503874505285760,13194144251904,2322168826314752,1127016598343680,9007199321882628,17592454742272,140738564227072,8804687151232,1125970782191618,2260595927678984,281479272726593,281476052549697,9183121115218432,4503943224762496]
private def banksB5 : Array Nat := #[4503908865024128,77313605762,8804687151240,4503908865024001,310311395329,4432406781956,282575562080321,9042383643607560,4503608221507712,9147936810238464,9147936745226752,2260595923485192,35255247437826,576460823178772482,2322168574656520,281749854625857,9147936759906816,567348067565572,567382360195076,4432473882628,4503676940976256,36099165764206624,70373040209984,4508032034152448,76561228025569280,4503874505285761,36029351070793760,36099715520004128,145135602008068,567348067074052,550292751392,137573303312]
private def banksB6 : Array Nat := #[562950288965892,281754149584961,281480345419841,9007199338660352,72057732014277632,2814750035558656,4707284688896,309238177793,2251800082137352,79456895106,2199157606416,141013442101249,550326304800,324259722926555168,2748812625952,562950020563204,9042383651996160,576462953482682368,11258999085203976,8796113994248,351848016904256,36310276291690560,2330964650901512,2251799830479368,144255926640082944,275953754113,70373308645376,2322168558927880,36029346775892000,1125919234199554,8804703928328,576460752446160912]
private def banksB7 : Array Nat := #[576462951469416448,4503633987641472,138110043152,9011597368393732,4398114177028,4785349481996289,288230934501720064,580542139728132,2260595910918152,288230925911785504,567348000456964,140738631335936,144255925633449984,140737557594116,72062026444701700,288230376692843520,3231711235,282578784354369,282575564177473,281750930456641,4503917454958720,4503977584500864,4503676940976258,2260604500836488,4512404314521736,54043195529756720,576460823178772610,281785288105985,567382360203268,4508032034152452,9042385782735360,288239730594742272]
private def banksB8 : Array Nat := #[4503676940984448,18033107387289600,36099170059157600,576462953482684416,281754149593153,567382427303940,4503679084265602,36099170059173920,52776566784768,9015995368735240,2885118779736320,2322172853895232,4508306912059392,76561502903476224,4503883099414656,4503908865024129,4503875579027585,4503883095220353,12890144960,422213540937729,708085555429380,206158431378,72062026511810564,805389568,567348335476996,4503909938765825,211106235727872,844424930132293,2322173122330624,9147936810238468,281784214888449,4503908865548289]
private def banksB9 : Array Nat := #[703687508918532,72057765837145104,824633794593,144255925599864864,288230926478016544,576495936818249744,216172782116408320,4503875581124609,9147936762003968,2322168575705096,2322172853895176,36029351070859296,292742780466233472,2260604517613576,144117388174952449,13510798882153088,144256201517957121,13194144251916,201490452,144115737867323424,288239180855640072,864691128467914752,144117387132799008,576462951494584320,576462951368755200,2260596179353608,9147937886076928,153263124888190976,288239172785865728,2322168574657032,50334248,282853662261313]
private def banksB10 : Array Nat := #[2322172853895240,36030450582421600,36029351070859360,36310276291690593,4503986174435456,4503670502727810,6764204128206984,8873406627978,4785349481996481,2748812822560,310314016769,2814750035558668,5070981987573764,4707284688901,70373308645696,281480348565569,72062164420527104,4503951818891392,4512679192436864,4503883099414657,144117387269113856,720578139413153792,9147936829112832,2322168575705608,11258999085253128,576495936818250256,2330964936114184,2260596196130824,576498135707290112,35255247438466,292742780466233480,38350965577891880]
private def banksB11 : Array Nat := #[43980494471688,2603647830605888,351848016920641,76565900949987328,288239731131613184,4503909938765953,4503917454958721,4503884168962177,4503676940984450,4503943224762499,4508032034152580,4503642581770368,4512404314529928,145135604629508,140738631335941,687731704880,648518483914654736,2260604500852872,141013442142209,4432473923588,4785384915476481,18032008009875728,567382360203524,567348268908804,4785383842258945,2322168827363592,2260596179353864,2885118780784896,9183121131995656,76565626072080388,633318967099652,720578139570440192]
private def banksB12 : Array Nat := #[2199191160880,72057765971362832,288239722004807720,703687511015684,72057766374016016,35186544738826,144256475355678752,576496074257203216,576498135841505296,292733984373284992,2336596560912,550326307872,2260595927695880,2330964667679240,144255925633452036,138110239760,8804703928968,144255925599897632,580964422806143106,585503135955419656,4785350557835265,144117388208637952,281784214888513,9183121199104512,9042385799512576,9183121182327300,9046781740483076,9011597368918532,9051179736662536,9042383652028936,9007199338660364,422488418811969]
private def banksB13 : Array Nat := #[9147937835745792,9147937886077440,9147937818968577,9147936812335620,2322173122330632,9147936762003976,281754150641729,567348067598596,1125919242850306,576463022202159106,576498137854771202,9570149275304708,281750930464833,4508306912059520,2330964919337224,72062026981573636,144117936890578976,9715284810170372,72057903276106753,72062163883664384,72057765837153296,2251800098915080,81069191406845956,562950289015044,144117388175083521,576462953482684418,144117388309301248,576462951502972928,576495938848293376,144258125696862208,576498137988988928,2260604517629960]
private def banksB14 : Array Nat := #[2260604769288200,288230926482210848,288230934535274528,288230935038591008,567382427304196,567348336001284,567382628630788,9429412795678721,288239172785865736,72058144331203616,79469478018,288239722541679616,585503138086126082,585503138102903296,2330964656144392,324259722931798048,36311375803318369,4785350555738305,144117936888678432,582090322712985730,281785290727425,4508306912059397,4512747911913600,720578139446708224,9183121192813056,281789583073345,576498137854773760,4503679096848514,38350969872859176,4503918528700545,4503977584500867,4503917459677312]
private def banksB15 : Array Nat := #[9147937886076933,38913915799748864,144256201517998081,144255926740748288,9187519228838404,72062301322616837,288239722541678632,9051179749212680,576495938848162314,144258674378934304,567348335526148,576498273280458768,288239180855640712,9042385866621440,9191917225017864,9147937902854656,2322173139107848,72062679816668160,4503909941387265,576498206574247938,144258400541214721,4503713444012162,4508375631536256,72062027048682500,72062438761571328,576462953650456576,288239181392576520,72057766508233744,2260604786065416,567382695739652,4785384918097921,2603647830605897]
private def banksB16 : Array Nat := #[36311100925411425,38350969872859240,360288108170249232,4503986179154048,288239730594742440,4785362366898369,864693877267957792,144117936890775584,637717014135044,2330964924580104,567348336050436,2827944175091980,849132214820869,914798238777664,2260604769288584,720578139580925952,4503679096856706,9429412795679297,281788510904385,281755226480705,576498135757621760,292742849185710218,9710886765757188,2322168844141320,72061992689042436,4503884175253633,4503986174435459,4503946445987971,4508306912059525,4508100753629318,4512679192436873,1178695800983554]
private def banksB17 : Array Nat := #[4512473034006666,4503917459677313,9715284812791812,72062542377714724,360288657921344560,352122894835777,76561434184000640,76561502903477377,72057765971502096,6764204128231560,81069191406847492,288239172802643464,576496074257204752,422488418852929,2260596196131592,13651812324253697,2885118780784908,76565900949987333,144117388309301265,567382628655364,576462953516238882,720578139570440240,2322173122330952,576463022202161282,148619063656982657,72062164420527124,288230934535276704,144255926673639457,288230926482213920,153263124888193540,576498137854773762,576498135841507856]
private def banksB18 : Array Nat := #[567382427345156,290490972868001800,585503138102903306,288239249558405258,288231003221196962,292742849185783936,594477487409466384,72057732148691984,432346114023295008,576463088908373008,13519603586040456,2322172870672968,9046781749395972,9042385849844230,9147937886077445,9042385799512586,9147937835745801,9183124346929664,2260604517630600,9183121142481416,11267795182469640,11470105317786120,576460960752074770,19140521754890258,576498137988988946,9574547322340100,580964422806282370,4503704862990466,144256475355777056,72062301322617861,281785290727489,72058040715060241]
private def banksB19 : Array Nat := #[72062163883664404,3395309355159808,153263125961935360,648518483923567632,144117387269113904,72062026511852548,144258125696862241,576495936835027480,13515231356035076,4503909941387393,144258124791056384,144258125697026048,144258125663471617,72062130060854292,288239310224819224,576496007550993026,153263125961932805,72058281770157104,288231063887610928,72062164420600832,72062026981647364,72057766374089744,585503138086289922,2330977541046280,360288657926063104,9156732859220488,324259735816699936,36312200437039201,4785396726636737,18035306544893968,1008809065343813664,2845536361136396]
private def banksB20 : Array Nat := #[5352731842191365,12420085520007690,576498135891839488,576498137905105408,873742308204347912,4503980805726339,4516905440780416,4517111599210624,1179795312611330,9992362816208901,126101477298078768,157767000400109569,13933287300964353,2898312919269644,198160582795462704,3166598052462912,36943595257741632,288239730645073960,144118212842227745,90072181660976144,144256751307327521,778454568059140,292734877726482560,234189517219826704,792635871013768208,504403708591803424,936748860603302928,882705665074856976,590006806432973442,301749979737752200,720578142667933696,9055577850282508]
private def banksB21 : Array Nat := #[220676692055171073,11478901410808328,19141621266518034,85572825393963012,492861459005505,72062130262115348,153263124938525184,153263125945158144,76561709061907584,76565832230511744,72624977203430660,720578142768596992,869194807551983746,72058591007810560,585503136156910080,585503138287616512,225325116973154308,2330977826258952,493960970633281,281789586743361,36311100925485153,4517180318687360,4503946456473731,4516836721303692,288239799314219178,4785384918098113,2330977541046472,18035443983847440,324259735816700128,38913915799748908,54131156728430896,72062027048788996]
private def banksB22 : Array Nat := #[914798238777669,720578142802151424,36382569181216865,9020393482912268,9042385866621454,576495938982511130,864735108949803528,576498138039323136,576498137988991506,296120548906238090,38350970191626280,9768061368304388,2330964941357832,576498135757621800,2322173139108680,290490972868003080,18032128940131600,4503989395660931,4508375631536263,4512747911913611,774056524693764,4503713457119362,4503986179154051,954763259112784912,72058453568857121,414331853449790512,72062679816668212,76565900949988485,576460960752075922,76561434184000658,288239731131614376,4785362372141249]
private def banksB23 : Array Nat := #[144258674379163680,216173332442713120,324259723502226464,158048475376820225,288239181392578184,39759444268044352,2902710967091468,2827944179810572,492586581147713,849132214821189,9196315338637836,72062129725408276,72062164621853716,288239731181944872,577589952901158978,153263125961935365,588880837823431178,985163561468229,576498206574250626,796046754103556,292743673819504768,292742849185783946,4503918535516289,216173092427803649,216317917718416388,810650269523250192,567382695796996,540432505610767392,292734809007005857,288230935072148640,591132706339816066,216175118712966160]
private def banksB24 : Array Nat := #[144255926740748325,72057766508438544,576498273280462352,9183124430815744,9183124346929667,9187519239848452,144258125697026081,9191917239697928,9183121209590284,9147937902854669,864691266577957904,220958167031881729,3449172272369738,594530263976247312,18594958097535252,13651812324254337,13519603586081416,576498344147419154,72624942843774212,282906274574401,9622925842088708,9715284812792580,2260604786066312,864693877280540704,72062438761571349,2383741494248200,20003432224264512,153263124871416360,76566107108418688,153263126012267008,720578142634379267,36032099883554912]
private def banksB25 : Array Nat := #[720578139580926000,144117388342855729,576462953650456626,18594940850700564,144258950330583073,864691207924809858,288239722055141928,144258125898352640,360301164870829068,144258124791056404,54043883261461552,360288657926063152,72062989054321664,144258400541386753,72062164420600852,290490981474713608,55451691399778368,585503138304393728,585503138103067146,585503136140132884,360301852065596416,11821949374219020,364791613308347520,145445916024837,326590687582699560,2886922865712,44059951366794,4516905440780430,4517111599210637,292743605100028073,4785363447980225,3166598052462925]
private def banksB26 : Array Nat := #[36943595257741669,590006806433145474,5352731842191813,2330977809482184,9161130973364748,585503136156910108,13933287300965057,2330977557824200,576498137905105450,9992362816209733,576498135891839544,14078181309457284,4503955050602627,360301714626642988,72062851615368229,126101477299913776,72058591007810609,866986908763505160,288239387534230682,288231141197022386,36099720620361056,873742308204577288,85572825393964676,576496145124165266,290490972884780808,2898312925036812,720578142768597011,144258125864798229,144118212842432545,492861459062849,9763663332541188,145100351637326149]
private def banksB27 : Array Nat := #[72062164085154836,157767000400112257,288239730645076648,791648711000324,778454571729156,252202129462725664,220676692055174273,576463159775333522,792635871024778256,36099716358950176,11478901418148360,292734877726482595,225325116973157892,9183124414038535,9183124363706891,9055577863389708,288239722592013864,39477969291333738,54325791492935793,936748860616410128,504403708598619168,15771403399783048,90072182063707152,19141621266519250,72062130262344724,144256751307434017,153263125945158185,153263124938525228,577590021620635842,630506147032729648,301749979737858696,869194807552188546]
private def banksB28 : Array Nat := #[18017851797806160,360301302309782556,342274259417367600,1008809065358493728,144258124824610868,585503138287616534,595604368724987922,595653846748237842,13656244798136325,729761260578703872,326590688388005928,4503989410865283,4517180318687375,292743673819504811,4785397808242881,1044837862378506272,2915905111343372,56945906495537468,39195395071426925,9196315353842188,9183124430815759,585503138304393758,9768061379576580,2383741508141832,576498138039323194,2330977826259912,414331853455819824,76566107108418711,288239937290044602,77410325880120773,144258950330820641,180357840143370272]
private def banksB29 : Array Nat := #[86135775347386244,290490981474715528,774621335110682672,158048475376822977,796046758035716,154107550892067653,38350970191629160,72624977270662404,870320707459035266,810650269534522384,540432505618631712,954763259126154256,220958167031884993,324259736387128544,36099720653917536,576498344147422866,288239731181948584,225888066926579460,144540975029729345,594530263976251152,11514085798625800,36382569181311073,39759444268044395,55451691399778419,5629630544097410,1127100364099778,584992061976836,21972657818063134,72062164622091284,588880837823615498,591132706339992194,282906278506561]
private def banksB30 : Array Nat := #[1179864032089026,90072182198055952,18032146254353680,153263126012267053,720578142802151475,875994108018278920,304001779551560328,144258125898352693,360301852065596476,18035443983850832,72062989054321717,296120548906332298,14500669728268293,7116327023042761,595654052906668050,329045085298696417,326590700467601640,7331586756862348,13554858833519242,90657122518041876,12085832164885260,11874725941003020,596779727612953368,604098076789342996,363115914906387724,864693956737435810,308523101002745112,217162652959940613,229829026911920133,364804807447880844,864691346034853010,653022188777645202]
private def banksB31 : Array Nat := #[364791819466777746,364792437942068385,864735188406698634,54131844460135728,369308364209489420,864735247059846680,729761260729698836,95701749780460690,725082085859141763,436849998192257185,919505523466565,729761260780030464,326590700517933096,864737857762429480,13524036059964044,216175429024361489,216320254314974228,216173642754108449,216318468044721188,1080866797491784752,918737210906446896,1055536870113605,878245987288613514,867841092628805,13687067571692163,13550486603473542,13660617028182665,595601276348535954,216175669039270960,325386803954651362,364805013606311040,230673451842052101]
private def banksB32 : Array Nat := #[326590701323239464,881623687009141386,12099026304418572,364805838240031872,180640694878079073,729761264001255936,1134909993020230704,14500669728269253,364805013606311070,364805632081601709,364792644100498611,729761263799929387,326590701272909288,729761263950924311,729761260780030524,878245987288851082,217162652959944005,229829026911923845,5912482050486467,5912472392052931,57509977435427194,1080866797506989104,12085832176681740,12046249754149644,11887920085254924,595654052906669970,180639870244542561,595604574883421394,331376049949597929,13559291307401870,606349876888257308,12314535955317581]
private def banksB33 : Array Nat := #[381148043041129756,941252574060422290,401102714233758945,344622816522749240,367619557483439500,373812006786541196,864735326516741786,676160206313260820,191895570794728041,734265206974360195,864737937219324586,216320564626369557,216318778356116517,252483919045799009,508907627127319713,864694094847478962,1060244154802501,864737995872472632,1018000982583511592,13695872275620491,1008579723964741,13665049502065293,15095541966877379,3493232223736522,216175979350666289,216320804641279028,3475655313609162,7683709651673549,16264264858788553,109006446873109861,945804438466692636,662068970518128278]
private def banksB34 : Array Nat := #[885019037837772568,1013313020394416291,198952231506463028,446006731045186217,632881092433955640,797139851830504595,252980584030784804,513564839565168172,126384382500746353,8475164749361550,12913771612787275,309649095398872474,615976107196439146,234472419202317393,12099026320933644,364805838240031935,729761264001255999,1134909993036745776,230673451842056133,326590701323243496,5912485282197699,58354402365559167,90657122719626516,180640694878337121,595657351441555410,13700304749503119,417247758561133884,376626756822099852,1056351948161403432,192458521083693933,545217903419010273,864738075329367738]
private def banksB35 : Array Nat := #[820418330902826772,332503118087549163,607475796122456862,776029834201929843,216321114952674357,16831647554528205,404001027153028589,950308151910704798,966651179198039836,1022504937619434155,484639175894756073,786707167275567932,1085370786902650035,271014911323131188,253262373613858149,1090063112845626940,518068758093868717,552478755364917036,921120952414588728,8828387155800527,17426519524700875,13494331267928911,420244335500276979,127039691699352949,386777671424374174,345749914725471738,886145034381383578,904215906510658282,1094567102241287871,557264153165295597,18011511586616271,423160240605591039]
private def banksB36 : Array Nat := #[1062264381887478507,271297817597705589,922248052764794874,1152921504606846975]
private def banksTable : Array (Array Nat) := #[banksB0,banksB1,banksB2,banksB3,banksB4,banksB5,banksB6,banksB7,banksB8,banksB9,banksB10,banksB11,banksB12,banksB13,banksB14,banksB15,banksB16,banksB17,banksB18,banksB19,banksB20,banksB21,banksB22,banksB23,banksB24,banksB25,banksB26,banksB27,banksB28,banksB29,banksB30,banksB31,banksB32,banksB33,banksB34,banksB35,banksB36]
def banks (i : Nat) : Nat := (banksTable[i/32]!)[i%32]!
private def nodesB0 : Array Nat := #[2685010207,2416836895,2416967967,2424310303,3225813025,2971271201,2954101345,2685796961,2685928033,2957378145,2957509217,2685797025,2957378209,2957509281,2688812385,2957378913,2695365985,2957510881,2690386145,2689337697,2703231329,2963934817,2702839393,2167017057,2702839457,2702840865,2434407777,2703105377,2434540385,2176459617,2445157217,1934631777]
private def nodesB1 : Array Nat := #[3221880995,3222929571,3224240291,3224633507,3224895651,2956722339,2956853411,3222929635,2954625251,2958950627,3222929699,2958426403,3222929763,3492675939,3493069155,3229352291,3229876579,3230007651,2962096483,3232498019,3237216611,2969043299,3226470883,2965375459,2428635619,2965375523,2428635683,2965375587,2965376547,2969965027,2696943587,2967345123]
private def nodesB2 : Array Nat := #[2968655843,2972456931,2699171875,2968786979,2972456995,2705725475,2439387171,2452756515,2723026979,2195986467,2212763683,1952323619,1147044643,1691386659,3222274084,3496476708,3496607780,3228303396,3233021988,2978086948,2980577316,2988704996,3221356581,2959736869,3228303397,2977169445,2451832869,2965900709,3222274086,2958557222,3496607782,2988703782]
private def nodesB3 : Array Nat := #[3234467174,2451838054,2720277094,2183409382,1925072038,3225157799,3493855399,3231187111,3491365223,3761111399,3761504615,3497787751,3498312039,3498443111,3499491687,3505652071,3237478759,3494906343,3233810919,2697071079,3233811047,2965379047,3235780583,3239450599,3237222439,3238533159,2974160935,2720798759,2991462439,2479101991,2232817703,1427538727]
private def nodesB4 : Array Nat := #[1967169575,3503161384,3242197032,3493986472,3498574120,2989886056,3230535080,3774746024,3529379240,3258325480,3258326888,2721459432,2992522984,2459191016,2464433896,1981695720,4295098409,4295753769,4565106729,4565237801,4297588777,4298113065,4301258793,4033478697,4302176297,4034789417,4304011305,4304142377,4304535593,4036886569,4038328361,4308074537]
private def nodesB5 : Array Nat := #[4040949801,4042129449,4311744553,3776053289,3781820457,3517579305,3788111913,3791519785,3523477545,4060610601,3524132905,3528720425,4065722409,3260547113,3800301609,3533963305,3802529833,3535667241,3540254761,3550216233,3550347305,3283615785,3288989737,3035496489,3304325161,2507407401,3049127977,3264217513,3264217641,4034397033,3281781673,4034397161]
private def nodesB6 : Array Nat := #[3044541673,3765175721,3778545193,3508800297,2995784489,3768454569,3768847785,3769503145,3769634217,3771207081,4039773609,3772517801,3508669865,3520073129,3525578153,3265531305,3013348777,3020426665,3520074729,2744916265,3781040681,3003393833,2776116969,2243833577,3518509929,2186818921,2780706153,3786814889,3267245865,2723693737,2997109929,2730378409]
private def nodesB7 : Array Nat := #[3013365801,2476495081,3534115369,2780714153,3281803241,1975408617,3015209897,4563796010,4297064490,4058906666,3268149290,3539075114,3556638762,3561619498,4035575914,4057202794,3784311018,4311613994,4316201514,3781035050,3507620970,4302048618,3765964138,3519155562,3777498602,3529643690,3518244650,4062455594,3798083370,3542886762,3019778410,3798084778]
private def nodesB8 : Array Nat := #[2756325738,3295031658,3805827498,3025295786,3490578731,3768844587,3502506283,3773564011,3505783915,3777889387,3766094315,3772778987,3529640491,4034530859,4036890155,3768847915,3773828651,4043050539,3775794731,3776450091,4045803051,3516927531,3792703019,3519551467,3519944683,2975996075,3529644203,3261212395,3261213163,3524274859,3526640171,2997633579]
private def nodesB9 : Array Nat := #[3270394411,2752791083,2501526059,2508603947,1723630315,2261164011,4834852908,4571267116,5112332332,4578345004,4863295532,4595908652,4337565740,4095737900,4096917548,4099801132,3597533228,3339714604,3080978476,2547777580,4337828012,4615831724,4591059244,4331798828,3800960108,4573630316,4305850220,4326428524,4066250604,4337831788,4072279916,4072673132]
private def nodesB10 : Array Nat := #[3543011180,3821539180,3822849900,3555331948,3555463020,3829010284,3829403500,3316256620,3806729964,3806074668,3538167916,4860946604,4623444140,3540658476,3086231852,3535420716,3804249644,3806740396,3809100204,3535422380,3535424492,3535819244,3540668908,4347417068,4357247468,3285864940,3592442348,3269874796,3538179948,4088813420,3827324780,3829421932]
private def nodesB11 : Array Nat := #[3037615980,2783729516,2493019564,5906497581,5910691885,5644353581,5649727533,6187384877,5659426861,5662572589,5394792493,5400559661,5400690733,5669519405,5941493805,5410652205,4874829869,5145100333,5417730093,5423628333,5174067245,5191368749,4663279661,4403757101,4901830765,4660789357,5918818477,4866048173,4871291053,4871815341,4633526445,4638900397]
private def nodesB12 : Array Nat := #[4136501421,4137025709,3870425261,5125701869,4858446125,5404623149,4385538349,3608936749,5125702061,4606657005,4611244525,5117182509,5120197165,5926814253,4855300653,4857791021,4858446381,4862640685,4606657069,4607050285,4607836717,4611244589,4611375661,4611899949,4612031021,5152703725,4654892269,5396366957,5152704109,4394321517,5123738093,4608494061]
private def nodesB13 : Array Nat := #[5657201325,4589226669,5404625581,4586867437,4620946285,5129375021,4889120045,5644488045,5644881261,5645667693,5646847341,5649599853,5922229613,5123738989,5664804205,5408427373,4875226477,5168434541,4135849325,5122297261,4884270509,4373089709,4853468653,4338224621,4342943213,4403498477,5120855597,5137239597,4875750957,5378150125,5378805485,5385359085]
private def nodesB14 : Array Nat := #[4858449645,5136322285,4876799725,5152706285,4347924205,4623044333,4359851757,4633005805,4633792237,4641001197,4394323693,4128378605,3860729581,3599503085,4852420717,5129375853,5404627053,4875489389,5147857005,4093382765,3852211821,4394849965,4136113837,4340062189,4322498669,4875491437,4343601261,3831240813,4847573165,4866054573,4602861997,4886108589]
private def nodesB15 : Array Nat := #[4887812525,4855306733,4619377197,4618722029,4857928493,5124136045,4866710701,5135277229,5404630189,4606794925,4607188141,5144190125,5156510893,4091419821,4634188973,4909964461,4389084333,4135460013,4136115373,3868335277,4594476781,3340510957,5121517357,5127939885,4860946221,4606797613,4879427373,4615841581,5154678573,4368115501,4124190509,4404553517]
private def nodesB16 : Array Nat := #[4586874733,4589234029,4598146925,4603127661,5141440365,4340066157,4610991981,4343605101,4615317357,4615841645,4353566573,4353697645,4093257581,4634453869,4099680109,3857983341,4052101357,4332071213,4342950189,3559794989,3318622509,4608502125,4617677165,4620953965,4361955693,3846318445,4591987309,4130089581,4591987373,4338363053,4879690413,4589497069]
private def nodesB17 : Array Nat := #[4125895405,4053150637,4057344941,4320144365,4322503661,4592511981,4880477229,4588842221,4323159277,4600376557,4332203245,4334431469,4068093165,4336921837,4338887917,3535023341,5147864301,4879690989,3823119597,4650052845,4394331373,4671941869,3889442029,3831246317,4338626349,4600377197,4095488109,4592513197,4329189549,4331679917,4334432429,4603392173]
private def nodesB18 : Array Nat := #[4071895213,4342558893,4343607469,4344131757,4344524973,4347408557,4391317677,3589550253,3610390701,4321063277,4323422573,4324733293,4062196077,4331024749,4342952301,3538432365,3822989677,4630131053,4904989037,3575132525,4658311533,4394856813,3062641005,4139397485,4323160557,4065473005,4602474989,4067570157,3803460077,4344394221,4081201645,4082905581]
private def nodesB19 : Array Nat := #[4069798893,4879823853,4120654829,5144065453,3589551533,4871568685,3309452589,3861658925,4137041197,4075175405,4875238957,5416304173,4074913517,4607065901,4347412269,4612046701,3824697645,4871831917,4338237805,4875501933,4342956397,4404560237,4069802605,4338369133,4876943981,5144068781,4340073133,4610998957,4349379245,4350952109,3306701485,3868607149]
private def nodesB20 : Array Nat := #[4606674093,5143807149,5144069293,5683561645,4880876717,4613096621,5151016109,4886774957,4625417389,4359865517,5167269037,4631839917,4632364205,4901455021,4365108397,4637213869,4378346669,4111615149,4922950829,4123935917,4126426285,4666836141,4403512493,3621536941,4347413805,4603135661,4603397805,4875241133,4875634349,4339943085,4608509613,4071900845]
private def nodesB21 : Array Nat := #[5146560173,4342040237,4610868909,4342564525,4879566509,4611393197,4611917485,4347020973,4617291437,4886120109,4619388589,4351346349,4620961453,5159929517,3820635821,4097328813,4120659629,3855500973,4394862253,4130096813,3598206637,4135470765,4342564717,4607199149,4879435693,4347414445,4338763757,4875765741,3831252973,3299493869,4607330349,4611000365]
private def nodesB22 : Array Nat := #[4620961837,4612049453,4117123117,4343484845,4619653549,4372320685,4394340781,3331477933,3608957357,4875768493,4881142445,4634202797,4100346541,3857994413,3867038381,3330822829,3065139885,4074525421,4075049709,4615852781,4081341165,4354233069,4089336557,3827454701,3827585773,3828503277,4097594093,4635906797,3835712237,3306705645,4657533677,4121449197]
private def nodesB23 : Array Nat := #[3866645229,3086242541,4875637549,4125905709,5144204205,4342961069,5149709229,5418800045,5155345325,4887303085,4619391917,4619522989,4622799789,4896084909,4631712685,4903818157,4905653165,3843183533,4649014189,4385559469,4660941741,3856815021,4394865581,3868611501,4407841709,4408759213,4343616941,4372845997,3874117037,3589559789,3321124525,3538310893]
private def nodesB24 : Array Nat := #[3334100717,4612053165,4887829357,4344142765,3807533997,4076231597,4888615853,4354497453,4089076653,4093270957,4094712749,3827063725,4096023469,4099038125,4105984941,4107426733,4113193901,3587070893,4129184685,3065142189,4407843757,3080870829,4107427245,3591528045,4126433005,3323092717,4140326637,3830081581,3321132141,3066590509,3605689645,3556275821]
private def nodesB25 : Array Nat := #[4901336685,4904875629,4111365741,3321132653,3591534189,3056367213,4372854765,4142561261,4099570669,4909202413,4372593645,4654006189,3854466989,4403527597,5174493165,5177245677,4114776045,4383604717,4924145645,4139417581,3878846445,3331490157,4637229613,4403921453,4642210477,3859972781,3331490541,2797241069,3068822381,4905272237,4112155565,3311829933]
private def nodesB26 : Array Nat := #[3589571501,3859973357,3867051245,4380591597,3320612333,4385572653,3583805229,3858007853,3870983981,3877406509,4386365229,3054673709,4403535917,4922974701,4662796781,3858014701,4120423533,4136021101,4386368749,2781785325,2787945709,4135365869,3330190573,4407864557,3335040493,4135104109,3321147053,2797252845,3858020845,3591552685,4398431917,3329801901]
private def nodesB27 : Array Nat := #[2793193133,4137074349,4404594029,2530529069,3605712685,3608989485,3621572397,3868381485,7809663022,7548960814,7290355758,7295074350,7295991854,7070285870,6525288622,6281494702,7519731950,7519994094,7279214830,7300055278,6286475502,6022758638,6031933678,4703781102,7251297326,7272399918,7277380654,6482953262,7289439278,6755714094,7025067054,6220678190]
private def nodesB28 : Array Nat := #[7027426350,7029654574,7300187182,6763447342,6765675566,6767510574,6768952366,6769738798,6774719534,6506546222,6506939438,6507201582,6785205294,6785336366,6786909230,6522930222,6257640494,6535250990,6267077678,6805652526,6270485550,6274286638,6279398446,6279529518,5748950062,5754979374,6025643054,6026167342,6026691630,6029313070,6031803438,4167304238]
private def nodesB29 : Array Nat := #[7269254318,7271220398,7272400046,7274366126,7284065454,6480987310,7027819694,7027950766,7031620782,6508905646,6510478510,6518867118,6031803566,7797606830,7262701998,7287867822,7557876142,7295863214,7300057518,6263802286,6534597038,6538267054,6023154094,5764024750,5500570030,4698802606,4435610030,7290620526,7295863406,6258297454,6266423918,6537611886]
private def nodesB30 : Array Nat := #[6538267246,5735320174,5497817710,4433513070,7265193070,7274368110,7008947310,7285771374,7025462382,7307791470,6507990126,6258429038,6271011950,6272846958,6005853294,5757733998,5758258286,7538740398,7274106030,7031753902,6506548398,6508121262,6269832366,6004804782,5482089646,5751966894,5763370158,7000820974,7008423150,7279217902,7015632110,7017336046]
private def nodesB31 : Array Nat := #[7030967534,6240472302,6263540974,6001396974,6004804846,5754326254,6024465646,5764287726,5232659694,6754012974,6493572910,6762663726,6259347246,6010441518,6011883310,6026956590,6994268014,6471815022,7279218542,6749163374,6751653742,6236540782,6797135726,6261182318,6278877038,6024466286,5756292974,5757734766,5758259054,5760749422,5760880494,5230038894]
private def nodesB32 : Array Nat := #[5230169966,7296390766,7269258990,6512842478,6515070702,6026172142,5760882414,7265851182,7274108718,7027300142,7299536686,6996891566,7284201390,7017207726,7291017134,6486497198,7027955630,6507861934,6514677678,6786652078,6267213742,6537484206,6278485934,6548756398,6555703214,6026696622,5495592878,5229385646,4705884078,6497639022,6019881582,6996368046]
private def nodesB33 : Array Nat := #[7265065646,6997154478,6736583342,7287741102,6482696878,6762666670,7031757486,6253320878,6255286958,5990259374,6269049518,6004677294,6274816686,5748038318,6018964142,6029318830,5763504814,4693564078,6224485102,6233004782,6011099886,7000955758,6736976750,7279221614,6270622574,4161149806,6460546222,6751394990,6483090606,7025073326,7025466542,6758997166]
private def nodesB34 : Array Nat := #[6762536110,6504979630,6507863214,6515072174,6247554222,6516382894,6250568878,6262103214,6533684398,6537092270,6273244334,6005071022,6010444974,5476850862,6017391790,5752888494,6024600750,4693564590,4166786222,4438236334,6735797486,6752574702,6737370414,6737894702,6757031214,6759390510,6493707566,6225403182,6494100782,7300193582,7307795758,5969026350]
private def nodesB35 : Array Nat := #[5467151662,6005202222,6007168302,5741616430,6547578158,5743451438,6012149038,6014770478,5749742894,6018964782,5755116846,5760752942,5494021422,3892976942,6463956910,6751004590,5987510190,5463877550,5733754798,6278227886,5219428270,6270101486,6004418542,6005860334,5738473454,5475018734,5227161582,6733441070,6469199918,6226585646,5735327790,5760755758]
private def nodesB36 : Array Nat := #[6470772846,6742091886,6480603246,6482045038,6751135854,7022585966,6758738030,6758869102,7027959918,6226847854,6495545454,6496462958,6230517870,6500395118,6232352878,6248867950,6522677358,6255421550,6525429870,5994326126,5997733998,6535391342,6002059374,5735196782,6004025454,6005205102,6007040110,6007302254,5741619310,5742930030,6012151918,5748041838]
private def nodesB37 : Array Nat := #[5749090414,5755119726,5494024302,5495859310,4964100206,6757034222,5727070446,5466892526,6543124718,6007040238,5741619438,4413597934,5763508462,4434700526,6469855534,6740125998,6472608046,6741436718,6741829934,6742223150,6744189230,6749169966,6480865582,7019309358,6751267118,6751791406,6483880238,7291414830,6488205614,5952252206,6224226606,7030319406]
private def nodesB38 : Array Nat := #[6768568622,5964048686,5965752622,6502885678,6237464878,5969291566,6774860078,6240348462,6256601390,5994457390,5995637038,5998651694,5999569198,6272461102,5735983406,6275606830,6011234606,6280587566,5744240942,5744634158,6020671790,5486815534,5756299566,5220477230,5220870446,6031943982,6032337198,5770324270,6307457326,4161415470,4431030574,3902810414]
private def nodesB39 : Array Nat := #[6256994862,5724318254,5744372270,6269053806,6016740206,4435749742,5971520558,5972044846,6246771758,6255291438,5455883310,5944126766,7019310382,5959200046,5970341166,5708983598,6231698926,5724450286,5754465774,4436536814,5701512750,5462044206,5467156014,5484588590,5756300846,5488651822,5226507822,5769014830,7291416174,6758739566,5970996846,6006910574]
private def nodesB40 : Array Nat := #[6007172718,6012153454,5744242286,5751975534,5216153198,5495598702,7552511982,6750613486,7025078254,5736247278,6014119918,6284390382,6018969582,6758740398,5746864558,5747257774,5221396910,5223887278,5224018350,7284079662,6749436974,6482181166,7019183150,6750878766,7019445294,6752189486,7022591022,6487161902,7025081390,6757039150,6491094062,7029668910]
private def nodesB41 : Array Nat := #[7031110702,7031503918,7032028206,6764379182,6764641326,6765034542,6498171950,6500793390,6770801710,6505380910,6774209582,6507609134,6508395566,6777093166,6781156398,6514293806,6247300142,6784564270,6785874990,6517570606,6788103214,6253984814,6258179118,6260538414,6261193774,6262897710,5995379758,6266174510,6266436654,6535396398,5998787630,6267354158]
private def nodesB42 : Array Nat := #[6269713454,6538935342,5735201838,6272859182,6274300974,6006127662,6543785006,6544178222,6008486958,6278233134,6011501614,6280330286,5743590446,5476203566,6015695918,5479480366,6017399854,6286752814,5484461102,5756304430,6025788462,5489835054,5492456494,4958731310,4693179438,4962532398,4963580974,4437457966,5963398446,4695801134,6214532462,7031766382]
private def nodesB43 : Array Nat := #[6231833966,6233800046,5206588782,5218123118,4434181486,4434967918,6494764462,5963267502,6777224622,6253198766,5456018862,5208423854,5495602606,6485589550,6763200046,7031766574,5479874094,5481184814,5484461614,6022905390,5764038190,6490963630,7031111342,7039368878,6266175150,5724323758,5484461998,6754156590,5466505262,5480529966,5226512430,5968117998]
private def nodesB44 : Array Nat := #[5480136942,5762466030,5227167982,6756647342,6761890222,6763332014,5172117934,6255821230,5724193198,5995774382,6002065838,6004425134,5473190318,5741756846,5474501038,5208424878,5752111534,5757747630,6295142830,3901637038,3634381230,6494241582,5739135790,5472928558,5217862446,4437721902,5474370414,5220483950,4692525934,6262113262,5735597038,5469783022]
private def nodesB45 : Array Nat := #[5218124782,5489837038,7291028526,7300203566,5730354222,6274827310,5743461422,7027967086,6230525038,5738480750,5483676782,5501895790,3900458094,6213749166,6216894894,6754027950,6754159022,6219778478,5420239278,6235507118,6241929646,6001412526,4940122542,5209475502,5749098926,5756045742,5219436974,5758536110,5763910062,6220173614,5432168750,5701259566]
private def nodesB46 : Array Nat := #[5187457326,5737435438,5204496686,5204758830,5473587502,5477912878,5748052270,6017536302,4679160110,5230055726,4705898798,6758748526,6494245230,6002069870,6547591534,5483024750,5484597614,4961489262,6754030062,6487691758,6756782574,6490313198,6495162862,6497391086,6499357166,6504075758,6505386478,7048548846,6781424110,6518624750,6787715566,5724197358]
private def nodesB47 : Array Nat := #[5729309166,6536974830,6537105902,5195715054,5198336494,6004429294,5206069742,5206725102,6283612654,6018978286,5757227502,5494952430,5230186990,5768368622,6756127342,6757044846,6489920110,5955408494,6223975022,6761108078,6761501294,6224892526,6762156654,6762287726,6762680942,6763598446,6766744174,6767530606,6499488366,6499619438,6768317038,6500668014]
private def nodesB48 : Array Nat := #[6501323374,6233150062,6502765166,6504600174,6504731246,6237606510,6506828398,6238524014,6507614830,6239965806,6240096878,5167796846,6243242606,6244291182,6244422254,6244946542,6246388334,6246650478,6246912622,7053660782,6517183086,6517838446,6249796206,6518362734,6250451566,6519149166,6251106926,6251500142,6251631214,6521115246,6252941934,6253073006]
private def nodesB49 : Array Nat := #[6253597294,6253728366,6522557038,6522819182,6523081326,6523998830,6792565358,6524392046,6524523118,5987783278,5990011502,5453402734,6261068398,6261592686,5726425710,5728260718,5997744750,5998662254,5731799662,6269719150,5732979310,6269981294,5464805998,6539072110,5737304686,6005871214,6274568814,6009410158,5473063534,7084331630,6548116078,6012818030]
private def nodesB50 : Array Nat := #[5476995694,5477257838,5746348654,5478306414,6284399214,5480534638,5480665710,6289379950,6022910574,6023697006,5488923246,4952838766,5758276206,5760897646,5764305518,4962669166,4695282286,4696724078,4429861486,4437463662,5187327086,5204497518,5742023790,5218129006,5490103406,5232153710,5742023854,5746349230,5494953134,5495084206,4695807150,5971530990]
private def nodesB51 : Array Nat := #[5711746286,5718299886,5742023918,5475816686,5478831342,4952052974,5226517742,4963980526,4434842862,4703409390,6249927982,5713974574,5719479598,5219439918,5684221294,5456811374,5461398894,5730227566,5735601518,4965160302,4434711918,6251108142,5488662318,5224027950,3898103598,5977954222,5188114350,5467166638,5482108846,5482764206,5486565294,5226518446]
private def nodesB52 : Array Nat := #[5227042734,5230843822,4167194542,5432826094,5435054318,5442787566,5446719726,4915484910,6537500910,5197289710,5737306350,5208430830,5216164078,5220227310,5220882670,5232417006,4168898798,5738486126,5470312814,4939995502,5210003822,5495085422,5233596782,5978479022,5470706094,5473589678,5216950702,4949957038,5220882862,5492332974,5764307374,5233465774]
private def nodesB53 : Array Nat := #[5987916270,5738617326,5475031534,5210003950,5478832622,5480536558,5483026926,5218130414,5764307438,5738486318,5738748462,5475031598,4939995694,5746350638,5216164398,5217081902,5486565934,5488925230,6026582574,5490104878,5495085614,5495478830,5998926446,5747268206,5489318510,5758540398,5473327790,5473589934,5475031726,5216033454,5220489902,4952971950]
private def nodesB54 : Array Nat := #[6032743086,5487746094,6026189870,4430388270,3901119534,5737444526,5484606638,5217612974,4950750382,5219447982,5489849518,6300398766,4434719918,5475300718,5751469422,5216171374,5488801134,4416107886,5465208238,4928468398,4951799214,5489325486,5492340142,5227050414,4965037486,5199525358,5213681134,5213812206,5215122926,5217613294,5219186158,4960974382]
private def nodesB55 : Array Nat := #[5443975022,5982812014,5178029934,5721585518,5456033646,6532134766,5193496430,6002603886,6541703022,5737445230,6006404974,5469665134,6008239982,5204506478,5207652206,6013482862,5209487214,5748062062,5748324206,5214599022,4951930734,4952455022,4952979310,5221676910,5226657646,5227050862,5232162670,4964120430,4698961774,5236750190,3631380334,4706432878]
private def nodesB56 : Array Nat := #[5737445294,5469665198,5743736750,5478840238,5226657710,5468094638,5221679278,4958093486,4958617774,5500731566,4965564590,4928471278,4933583086,6024757486,4953243886,4433019118,3361898734,3363602670,5467570478,5227053358,5709529518,5719490990,5719622062,5185634734,5456429486,4933190062,4945248686,5218402734,4951015854,5495882158,5232558510,5232689582]
private def nodesB57 : Array Nat := #[5725651438,5732205038,5482775022,4950884846,4951802350,6026199534,6029214190,5492474350,5227446766,5500994030,4699095534,5445813230,5195334638,4939744238,4946822126,4951016430,4690314222,5199791406,5481334062,3894576430,5465212270,5196907886,5199922542,6274188654,6292931950,6293063022,5220369774,4688741742,6034720110,4962944366,5188126254,6002607662]
private def nodesB58 : Array Nat := #[5736007214,5738497582,5205165614,5205820974,5474780718,5483038254,5483431470,5219190318,5488805422,5488936494,5220894254,4689790510,6300927534,4165109294,4933584558,4938172078,6013486766,4946167470,5767464622,4963731118,5236491950,4936337134,6016501486,5479892718,5738104622,4949706542,4951934766,5495490350,5727356782,5465212782,5736269678,5737449326]
private def nodesB59 : Array Nat := #[5743740782,4943677294,5214603118,5216175982,5220239214,5489330030,4953245550,5492344686,5207525486,5750425710,5215520878,4947609710,4951804014,4683499630,5758158958,5223909486,3630336110,3632040046,5187340718,5213817262,4951804334,4955605422,5232167342,4695820718,3901131182,5732207278,5746363054,5748066990,4951018158,5492345518,4920352686,5195341742]
private def nodesB60 : Array Nat := #[6272884654,4931231662,5469020078,4934508462,4939751342,4671709102,5747285934,5747548078,5212118958,4675379118,4945911726,4680621998,6023585710,4682457006,6026993582,5224046510,5494972334,4431060910,4169572270,4170096558,3902840750,4931231918,4401438894,5475311790,5218279598,4414021806,4682588334,4147683502,4955611310,4699365550,3626148014,3362431150]
private def nodesB61 : Array Nat := #[4438270126,4920877422,5201895790,6013493614,6022930798,4951941486,4952465774,5223915886,5224046958,5196129710,4936738222,6014018990,4943816110,4945257902,4415595950,4688749998,4698711470,3632965038,6269087086,5200588142,6282456430,4683378030,4684557678,4684819822,4960988526,4698713454,3358240110,3093474670,4169051502,5737459118,5201636782,5746372014]
private def nodesB62 : Array Nat := #[5478854062,4948536750,5220380078,5220904366,4952993198,4165643694,5469023726,5211205102,4415073774,4683640302,4953255406,4694126062,4696616430,3630345710,5460897326,5733658158,4933201454,5206879790,6013890094,6014021166,4943818286,6824439342,4957187630,5501660718,4698713646,5236502062,4167216686,5193379822,5732216814,5464961006,5196787694,5198098414]
private def nodesB63 : Array Nat := #[5198491630,5198753774,5736542190,4936478702,6011531246,6549188590,5745061870,4941066222,5478330350,5211729902,4675252206,5749125102,6287306734,5213827054,5751222254,5483966446,5487767534,4951814126,4951945198,4952076270,4684034030,4958105582,4152930286,4426739694,5769572334,5502054382,4698845166,4438536174,4171149294,5730513006,4928090222,5747290222]
private def nodesB64 : Array Nat := #[4675252334,4414943342,4687179886,5497860206,3620253806,4968853614,4674335150,5480296878,4675383726,4947751342,5219332526,5487899054,4684820910,5492486574,4688753070,3357716910,3901403566,5196132910,6010221102,5745324590,4950897198,5220250158,5220381230,4952863278,5766296110,4699107886,4968067630,4437357102,5745063022,6553121902,5480821870,6293075054]
private def nodesB65 : Array Nat := #[4683510894,4684035182,4953257070,4955616366,4961907822,4698715246,4972786798,4169053294,4706186350,4171150446,5468894958,6013499118,6014023406,6014154478,4406818542,4947752686,6024509166,4951815918,4952471278,4955485934,5500614382,5769180910,5211731822,4947752814,4683511662,3884365678,4692555630,3632052078,4950773166,3878079918,5746773486,4406824430]
private def nodesB66 : Array Nat := #[6017568238,5487644142,5487775214,5758176750,3888434670,3359821294,4434087406,3900493294,4673556206,4676177646,4679323374,4680240878,4681289454,4681420526,4687056622,5224058606,5769055982,4675391342,4945923950,4947758958,4683386734,4415606638,5758308206,4953263982,4150185838,5760929646,4689809262,5749264494,4409315438,4946710638,4948283502,4679979118]
private def nodesB67 : Array Nat := #[4950773870,4950904942,4951036014,5488693358,5488824430,5757390958,5489348718,5492363374,3621965934,5770498158,2824654958,4972793966,3901411438,5225632046,4959031598,6024651502,5487911662,4415087342,4415611630,4684571374,4684833518,4418757358,5228520174,4693091054,5230224110,4693484270,5230617326,3620528878,4962968302,3352748782,4965065454,4161200878]
private def nodesB68 : Array Nat := #[4430291694,4430553838,4699644654,2825183982,4704363246,3900629742,4437762798,3902726894,5487911726,4689814318,4961526574,4424786734,4426097454,4158317358,5233632046,4697416494,4429636398,4699644718,4434092846,4169327406,4962050926,4698858350,4435272558,4706198382,3629315694,4971755310,3904042798,3621844910,2824271790,3632199598,4430299374,4701488110]
private def nodesB69 : Array Nat := #[2827682798,3635610606,3899066222,10779492399,10784604207,10022813743,10232004719,10235150447,10272112751,10274603119,10291904623,10025828463,10034217071,10034479215,9783869551,9785049199,9517269103,9519104111,9969076591,9995159919,10018097519,10020456815,10021898607,9756215663,10025306479,10039069039,9514518895,9783740783,9247525231,9784658287,9516484975,9517795695]
private def nodesB70 : Array Nat := #[9518713199,9520941423,8195934575,9964751279,10017966511,10019539375,10024520111,9783085487,9246345647,9517009327,9517664687,9517795759,8187546031,8456898991,10242233967,9747699311,9749403247,9768408687,9768932975,9788724847,9252902511,8190170735,10212480687,10217068207,9951123119,10233190063,9966720687,10236860079,10505557679,9707722415,10249442991,10262156975]
private def nodesB71 : Array Nat := #[10270021295,10272249519,10276837039,9754646191,10292434607,10026620591,9758971567,9760282287,10031994543,10032125615,9764214447,9514653359,9515439791,9247135407,9515833007,9785448111,8458475183,7922652847,7654610607,7655528111,7118919343,7387879087,7925536431,8195806895,7122589359,7392466607,6052386479,6321739439,6053435055,6322001583,9749534575,9749665647]
private def nodesB72 : Array Nat := #[9755694959,9488832367,9506920303,9782564719,8978044783,9246742383,9515308911,9248577391,7650285423,8191088495,8192005999,7926847343,7928026991,9696323247,9480447663,9217255087,9217648303,9487525551,9487918767,9494996655,9514657455,9249367727,8457561775,7924885167,9470879535,9488443183,9488967471,9495258927,9503778607,9515968303,9249367855,9249498927]
private def nodesB73 : Array Nat := #[9251596079,8983422767,9252382511,7654352687,9968428975,9431820207,9481627567,9229969327,9506269103,9509152687,8977524655,8977917871,8978048943,9515837359,9248319407,9517541295,9249236911,9250809775,8982767535,8985257903,9524094895,8187160495,7918856111,7919380399,7651207087,8457824175,7921215407,9475074479,9486346671,9220008367,9488837039,9220532655]
private def nodesB74 : Array Nat := #[9225382319,9502075311,9511512495,9517279663,7920560559,6590048687,9427893295,9965812783,9966730287,9968041007,10237131823,10240277551,9175448623,10015489071,9488972847,9760947247,7892646959,7634959407,9245965359,9514531887,8709487663,8978185263,8979102767,9248062511,8980020271,8711715887,9517284399,7912045615,7644134447,7376092207,8450489391,8450751535]
private def nodesB75 : Array Nat := #[7379369007,7113554991,7919123503,8188345391,6312442927,7655406639,6855998511,5783174191,6054231087,9197993071,9205202031,9214770287,9221192815,9223683183,10029251695,9225780335,9230498927,9238101103,9245703279,8980937839,8181922927,7651474543,8190966895,7658552431,6051740783,9205333167,9212411055,9224993967,9497623727,9244523695,9247538351,9517546671]
private def nodesB76 : Array Nat := #[8980937903,9518464175,9788079279,9522396335,8187034799,7659994287,9221061935,9225125167,9232989487,8171437359,9250422063,8714599727,8983559471,7653571887,8194112815,8194506031,6048464175,7659601199,8197389615,8942538735,8945291247,8961413103,8967573487,8969801711,9244921839,8977534959,8978321391,8979238895,8981467119,8983826415,8984874991,9253834735]
private def nodesB77 : Array Nat := #[9253965807,8991166447,8992215023,8458227695,8463470575,7661965295,6324113391,8939393071,8978452527,9247805487,8980025391,8981205039,7643877423,8718798895,7920832559,8191234095,6322278447,9200095343,8966787183,8977535087,8977666159,9514930287,8978583663,9248985199,9249378415,8981074031,8189792367,7386058863,7658557551,7659475055,6052270191,6053056623]
private def nodesB78 : Array Nat := #[9211760879,9215955183,9222377711,9232863471,9505493231,8977535215,9246232815,9249247471,9250296047,7650300143,7650693359,8193593583,7927910639,6320181487,6054367471,6054760687,6323458287,8941883695,8681574703,9220411695,8952107311,8953680175,8961675567,8704381231,8978059567,8710410543,9248067887,9248461103,8444465455,8981729583,8988152111,7113822511]
private def nodesB79 : Array Nat := #[7114346799,7383437615,8463601967,7926862127,7391433007,7392874799,6051877167,6054236463,3640807727,8967445039,9514539567,9246235183,8978061871,8978586159,8978848303,7385930287,7386192431,7389993519,7390911023,5783575087,5785803311,8683680815,8975840303,8979248175,8980558895,8980689967,8713040943,8981607471,8982656047,8985539631,7386330159,7121695791]
private def nodesB80 : Array Nat := #[7659746351,5785547823,5786203183,8950936815,8699540719,8705570031,8979641583,8711992559,8712123631,8712910063,8714482927,7377155311,8720905455,7393146095,5517243631,6323336431,5786989807,3908990191,8676081583,8686698415,8960638895,8698363823,8703606703,8709767087,8979382191,9248079791,8443297711,8443428783,8713568175,7641399215,8447360943,8717762479]
private def nodesB81 : Array Nat := #[6845136815,7117111215,7118684079,7122747311,5783191471,5516591023,6590857135,8977809391,8710160367,8710291439,8710553583,8710815727,9248079855,8711602159,8712257519,8980955119,8712781807,8713568239,8984494063,7380303855,7650705391,5516460015,5516722159,6054772719,8943337519,8943992879,8680800303,8949891119,7072809007,8953954351,7615971375,8958410799]
private def nodesB82 : Array Nat := #[8968765487,8970993711,8973746223,8712126511,8991178799,7113834543,7659094063,7659356207,7392493615,4711284783,8679358575,8952905839,8699674735,8972042351,8705704047,8706097263,8711602287,8711864431,8711995503,8714092655,8716845167,8187314287,7392624751,5784895599,5516722287,6055297135,8673468143,8678186735,8153505519,8692866799,8693915375,8425610991]
private def nodesB83 : Array Nat := #[8433082095,8702303983,8434523887,8435703535,8709119727,8173035247,8711216879,8712003311,8712265455,7102045935,8444616431,8713445103,8714886895,8179195631,8179588847,8448155375,8717115119,7376379631,7385292527,8459165423,7118036719,8197021423,7392108271,7124066031,6856679151,5514895087,5784248047,5517516527,4713389807,3908869871,3909394159,8413949039]
private def nodesB84 : Array Nat := #[8416832623,7075310703,9492671599,8687889519,8690510959,8691166319,8440687727,8709516399,8442129519,8174087279,8443047023,8444095599,8444750959,7640099951,8445668463,8446454895,7910632559,8720657519,7380184175,7113976943,7383329903,8457333871,7115287663,8189946991,6848687215,8463494255,7928458351,7928720495,7929113711,6855502959,6587198575,6855765103]
private def nodesB85 : Array Nat := #[6856158319,7661595759,6857075823,6589164655,4710771823,5516471407,5248691311,5248953455,5518437487,8433347823,8433609967,8441081071,8173300975,8443309295,8712400111,8715545839,8448158959,6845148399,8457858287,8458251503,7927934191,6855634159,7929638127,5248167151,6054522095,8698506543,8709123375,9246125359,8977820975,8173432111,8711875887,8443702575]
private def nodesB86 : Array Nat := #[8444226863,8714235183,8446586159,8446848303,7376383279,7381364015,6845410607,8187850031,6847114543,7116598575,7116729647,7926492463,7659498799,7391194415,5516995887,5785955631,5518306607,8424042095,8431251055,8433741423,8710041199,8710434415,8710696559,7639182959,7376514671,9259888239,7382150767,6845410927,8456941167,8195321455,7929245295,7124069999]
private def nodesB87 : Array Nat := #[6857862767,5248167535,6322040431,6591131247,5518306927,7920340335,6318640495,7392513391,5245160815,6053219695,8434667247,8437026543,8706903791,8438599407,8439516911,8440958703,8441351919,8443186927,8711753455,8712539887,8981106415,8445153007,7909068527,8177635055,7104024303,8447512303,7911689967,8985693935,7387664111,6853807855,6855118575,7124471535]
private def nodesB88 : Array Nat := #[6588255983,5247520495,6591401711,5787406063,5787537135,7651910063,4441432495,8977441519,8172659439,7904486127,8173708015,8174232303,8174756591,6564930287,7371285231,8176853743,6839395055,7376659183,7109796591,6843589359,6308291311,6845686511,6581969647,8194417391,7658726127,8195859183,7660823279,6587212527,7392781039,6050734831,6588130031,6589047535]
private def nodesB89 : Array Nat := #[6857876207,5785314031,4980138735,5248967407,5250671343,4177584879,7646278447,7383348015,7384396591,7654535983,6315635503,6855389999,5782041391,6857093935,5247922991,7377580911,7380071279,7386755951,4980929391,4981060463,7377581039,7389770735,4442878959,4980405231,7123825711,6050346031,4710265903,5516227631,5516489775,7114653679,7386103791,4702273519]
private def nodesB90 : Array Nat := #[4974510063,6586957807,5513609199,6589972463,4979490799,4177068015,7114785263,6586958319,6855524847,5782569455,6588662255,5250286063,5781653295,7123961647,5245044527,5782046511,4976871215,7392921391,6857492271,6055724847,5780344559,6319574767,5244916655,6318789551,6319969199,6051795887,4173140911,4441707439,6321542063,4979495855,4711453615,3908768687]
private def nodesB91 : Array Nat := #[4172617327,6588667503,5246621295,5784671855,4711716463,3101365871,4442888559]
private def nodesTable : Array (Array Nat) := #[nodesB0,nodesB1,nodesB2,nodesB3,nodesB4,nodesB5,nodesB6,nodesB7,nodesB8,nodesB9,nodesB10,nodesB11,nodesB12,nodesB13,nodesB14,nodesB15,nodesB16,nodesB17,nodesB18,nodesB19,nodesB20,nodesB21,nodesB22,nodesB23,nodesB24,nodesB25,nodesB26,nodesB27,nodesB28,nodesB29,nodesB30,nodesB31,nodesB32,nodesB33,nodesB34,nodesB35,nodesB36,nodesB37,nodesB38,nodesB39,nodesB40,nodesB41,nodesB42,nodesB43,nodesB44,nodesB45,nodesB46,nodesB47,nodesB48,nodesB49,nodesB50,nodesB51,nodesB52,nodesB53,nodesB54,nodesB55,nodesB56,nodesB57,nodesB58,nodesB59,nodesB60,nodesB61,nodesB62,nodesB63,nodesB64,nodesB65,nodesB66,nodesB67,nodesB68,nodesB69,nodesB70,nodesB71,nodesB72,nodesB73,nodesB74,nodesB75,nodesB76,nodesB77,nodesB78,nodesB79,nodesB80,nodesB81,nodesB82,nodesB83,nodesB84,nodesB85,nodesB86,nodesB87,nodesB88,nodesB89,nodesB90,nodesB91]
def nodes (i : Nat) : Nat := (nodesTable[i/32]!)[i%32]!
private def refsB0 : Array Nat := #[6570244,21267668214987600449691932644451041540,42535336429975200899383865288895512836,63803004644962801349075797933339984132,81129715785932924078719836882500,101412144732416155098399795840580,128519731842570110450750419537102915140,149787400057557710900442352181547386436,171055068272545311350134284825991857732,192322675640304100844814945628682470980,213590323572882097642836454325875656260,236519547065010446585328569742921844292,256125619438038091238879471720262026820,277393267370616088036900980417455212100,300073240331125161601553208063447549508,328983928957056821017101183410001430084,344934705471314361626848311760575809092,344801292090214927334559303337540,390959245107815363040934246635449370180,404999215813312879780041304442368181828,435571459716385287688389462561523779140,456589816552524801805230235593160541764,446213436822631082432959098127940,466495865769114313452639057086020,520392821197487603154306033526493955652,507060723662080775491998975002180,527343152608564006511678933960260,578878853012081930056755331376952133188,567908010501530468551038851876420,588190439448013699570718810834500,608472868394496930590398769792580,628755297340980161610078728750660]
private def refsB1 : Array Nat := #[689952670234051713360786934477669599568,711220297884220106507138019227594721616,732487824122340481395136984241313745232,753755472054918478193158492938506930512,775023119987496474991180001635616229712,793881562460123915421233783983302576464,815149291522340326825936988469500905808,838826246326916898250278336930215168336,856936957487096116198482879911991249232,881361562474482495497991777447219104080,896896894392828438942445195074285406544,918164562607816039392137126894163265872,895912390539935722200230659164480,963274994325890063671886183925310097744,984542642258468060469907691797852784976,1005810452450322886481292592073324693840,1024502680576248401472222127521339083088,1045770389356055209225254908060269349200,1070361208690143513963888060466578131280,1090880983333406062718367355020276468048,1112148529853936041258036743980928010576,1133416461740248489179444188764625242448,1152108791278222022428725843123910019408,1124485736107856819706263968483648,1144768165054340050725943927441728,1159583812101712814783535763228992,1179866241048196045803215722187072,1258447091788340817373844658451780798800,1223600225441733081346317398116672,1306714602255680846065103654326762539344,1260995937491315856047868762720576,1349250040097704065222839633029682497872]
private def refsB2 : Array Nat := #[1364785392298459612318963473779416697168,1386053040231037609116984982476593105232,1345294741092193125962196765968704,1428587889883182322376278672206532249936,1385146448808465639792880811837760,1402972843402632904015294498933056,1426424398849686708538716215904576,1443537681952786252220587621550400,1466276183937211677705667442968896,1489569283059236953553902072039744,1504384949449422831445560703125824,1450712367044679953079601472,1470055198605275685787273536,1489398030165871418494945600,1508740861726467151202619649,1528083693287062883910291713,1547426524847658616617963777,1566769356408254349325635841,1586112187968850082033307905,1605455019529445814740979969,1624797851090041547448652033,1644140682650637280156324097,1663483514211233012860850433,1682826345771828745568522497,1702169177332424478276194561,1721512008893020210983866625,1740854840453615943691538689,1760197672014211676399210753,2787593151682311355768424918682434929956225,2787656954646391460676807532669706764031361,1906548320969424795130529966986625,1926830749915908026150209925944705]
private def refsB3 : Array Nat := #[1947113178862391257134705512813953,1876254661377786072644195585,1895597492938381805351867649,1914940324498977538059539713,1934283156059573270767211777,793799155031142219904179413125378935120,684719423191881111218912189868299848016,812325331069661981500908687335188662608,892664558133911763578653572663616,958291220921650948760620037096993786192,979558868854228945558641543663866415440,999829352401053011631940111829271906640,1025001648136068406109957399530220620112,1043361548980638088480990558441279916368,1655857779918802746377051466065230224755024,1107164756449677583515210002519533095248,1128432505794303598571583628547968797008,1149700234856520009976286833033697364304,1116722053181006257752723326830912,1137004482127489488772403285788992,1256038575931419326561625304790873475408,1258699017120688860175685799446848,1341109269073740646348942272385939212624,1341109289356169592832173292065881393488,1429087303655878207529839104156156102992,333524182522249135043279498260842816,1399725223767424070236790774106432,1420007730085159756592737914259776,1461523306585465830087487651907904,1481805754874762174941234406164800,1450713307829524914610637120,1470056139390120647318309184]
private def refsB4 : Array Nat := #[239173886513743729160653703488,2495526119265947648371198272,2517815855085806629368629568,2533909108210377687463627072,2553252327152598968071883072,2705960538766144588314491066845504,2591938082507510802034985280,2746525338932608015850128539715904,2901208161164473229201428047145717533008,2787090196825722051842078134044992,2809353310190035769307946312337728,2829635739136740361256510785915200,2986278772860494940932379330242246936912,2870992859312073246325886767139136,2888502283227707218207578473433408,2637886918225473569088,1663484584123409635778498817,2674780441557294125313,1642876880066032548940828552204545,5235420907511151375475032121995694337,4438440585456713361537889210625,2748567488220943618305,1990428685060776432684916088680782771143316865,2785461011552768364801,2803907773218680738049,2822354534884593111297,1903158727924048962606752338177,2457775208355459921494267662593,5309969716074309002460966949121,2896141581548242604289,5310047087363657862059972890881,6036025148237856458282986041034688175491088329513112961]
private def refsB5 : Array Nat := #[2951481866545979724033,2969928628211892097281,1685897791654386346274844310507777,3006822151543716843777,3025268913209629217025,3043715674875541590273,3062162436541453963521,3080609198207366336769,3099055959873278710017,3268937150234873299380212993,3135949483205103456513,1663485082185974615412576513,7132062711692626281232716534017,3191289768202840576257,1547428258843255212381049089,3228183291534665322753,3570102049282947526036068799354241,2457775208761288678144339874049,3283523576532402442497,3301970338198314815745,3320417099864227188993,3338863861530139562241,3520393739161688940065330433,5310047087824826903707782222081,1586114069538540005095379201,3412650908193789055233,3772530023849888688440118888895873,2658455995186941250518135712738709889,2658455995206284082078713853260337537,3486437954857438548225,3646158961088833975570769383681,3523331478189263294721]
private def refsB6 : Array Nat := #[1644142656454135532780261633,3560225001521088041217,3578671763187000414465,3597118524852912787713,2658516842589837689574857109791838593,3634012048184737534209,3652458809850649907457,3670905571516562280705,3689352333182474653953,3707799094848387027201,1995687696858556112803011910316332289,1702171298710016058199118081,3763139379846124146945,1702171335603539390023864577,3800032903177948893441,3818479664843861266689,3836926426509773639937,3855373188175686013185,3873819949841598386433,3892266711507510759681,4100678114130494636299392257,3929160234839335506177,3947606996505247879425,3966053758171160252673,3984500519837072625921,4002947281502984999169,4021394043168897372417,4039840804834809745665,4058287566500722118913,4076734328166634492161,4095181089832546865409,4113627851498459238657]
private def refsB7 : Array Nat := #[4132074613164371611905,4150521374830283985153,4584222529466453384437117680096641,4187414898162108731649,2457775209702073523105870909697,4224308421493933478145,4242755183159845851393,4261201944825762414849,4279648706491674788097,4298095468157587161345,4316542229823499534593,4334988991489411907841,4353435753155324281089,4371882514821236654337,4390329276487149027585,4629733999238660612717285633,4427222799818973774081,4445669561484886147329,4464116323150798520577,4482563084816710893825,4501009846482623267073,4519456608148535640321,4537903369814448013569,4556350131480360386817,4574796893146272760065,4593243654812185133313,4611690416478097506561,4863358950772886954582229249,4874994935573671647429804289,4667030701475834626305,4685477463141746999553,4703924224807659372801]
private def refsB8 : Array Nat := #[4722370986473571746049,4740817748139484119297,4759264509805396492545,4777711271471308865793,4801847785908638842880,4822095987425499414528,4840542749091411787776,5337286542993042245009932252626948,4876139482021158453248,4895883051681334951936,4916059230788529684480,4930326687184614326272,5705547371171981458972175289774393016580,5726233258749895497076684227178934845700,5747500926964883097507929399806734385412,5001807662140631547904,5022055898841864208384,5811885387728363384907825357374471028996,5059453807739768406016,5077396166247415283712,5603493052984330535152533392081152,5114794110329691570176,5918223749085710990715721636214382805252,5151687704030260494336,5169630062537907372032,5186275296391941324800,5204722022873481609216,5223168819723766071296,5243921494767636316160,5263521142753783447552,6089112805835650412993411877138275254532,5297964707888318644224]
private def refsB9 : Array Nat := #[5316411469554231017472,5339109629268381138944,5353304992886055763968,5635258916701020595069140992,5389189692309163474944,5407636453975075848192,5172107633754128,5189699836575760,6011360702371827431465195929620560,5224884242219024,5771565787591553906521424144,5523793647408034873424,5543609538545039966480,5295253053505552,5312845256327184,5868280775498473283826762000,5887624030902576019440422928,5906966032358896786846273552,6206813581612090345099700788529488,5400806270435344,5689815100535571742800,7236716709637142398081806164324925837958048515184976,6006476419613365916294713424,5471175081721872,5488767284543504,5506359487365136,5523951690186768,5541543893008400,5559136095830032,5850503693569976434768,6158422547930413193851060496,5611912704294928]
private def refsB10 : Array Nat := #[5629504907116560,5647097109938192,5664689312759824,5682281515581456,5699873718403088,5717465921224720,5735058124046352,5752650326867984,5770242529689616,6074098003249589125392,5805426935332880,6724732160848667133624840911606032,6745014652960581420755374095483216,5858203543797776,6471232341330588790727655504,6184778397323202920720,5910980152262672,5928572355084304,5946164557905936,5963756760727568,6277012698233974030608,5998941166370832,6016533369192464,6962020740146120265378993612525904,6663980820629486055756661072,6069309977657360,6385459377261156237392,6104494383300624,6738706941345822226306318608,6447500314816978878736,6157270991765520,6789705274279904871868008528]
private def refsB11 : Array Nat := #[6192455397408784,6210047600230416,6227639803052048,8310190863446914576869764469182710908976684392010004,9604377086020454432882158335731553088141063573200257335782657751337301,6280416411517184,8784169930872627185261455833327117582697472979109440477504,8018253954570710057850442488304561722107171141,6333193019982080,7333124236201747504972908726391044,6368377425625344,6697685442401178489088,7040790693169575772574187793,7413144868404419045396475564544260,8571436693695266627936235809458379778211331109376277,6456338439733504,6473930642555136,6491522845376768,6509115048198400,6526707251020032,6544299453841664,8326019178183149455714628949505293209391419648,6579483859484928,7261869400203975895933796612,6935982396070405603585,7300555331304944719770964224,9732927176078968797530426362973075715562719290045608321681021269,7000903921258349990144,7019925507603263717632,6702629279236352,7388955199787144091780778304,7074690897553255305472]
private def refsB12 : Array Nat := #[7427640826014847409743464768,6772998090522880,6790590293344512,7148043804249700712704,6825774698987776,6843366901809408,7203385004041112142080,7217217511229436723456,7239052545519687581952,6913735713095936,6931327915917568,6948920118739200,7304917619698720309505,9743703701397347094569374436050775111591234136660334891285,7351391882737289793792,7019288930025728,7036881132847360,7397151428028198289665,7072065538490624,7089657741312256,7107249944133888,7124842146955520,7142434349777152,7160026552598784,7177618755420416,7554016359428500029696,7563172283019463491904,8347244387178534305795694196232512,7610221282778134151424,7618512573859245326596,7283171972350208,7300764175171840]
private def refsB13 : Array Nat := #[10702110264836369152229833098172797872744150007582888235903572308,7335948580815104,9333998566705845786619586725680210687750654288,7735675102110655975680,7757364437916089061632,8153981105138482559274008832,8170981764128951714562720064,8589524161339927606904568370188560,8609966484702582518218867817402624,9486267906498593208038941134563598322001858816,9974479181344544469514042945130176818458307655194960,10984929593083184922166414281918721518655860298589348339544054096,11014054582910432866720736755020927965386966808309597226651701573,7915170674412418502912,9601606722185489965744116470730409362914890001,8741726881294736497401905400512789,7976922924195252289792,8381865016166773996956684560,7635016028782848,8024341329408816054532,8052943193324124176640,7687792637247744,7705384840069376,7722977042891008,7740569245712640,8539930849596419596296978692,8559122040054085911853420800,7793345854177536,8199508339597403767040,7828530259820800,7846122462642432,7863714665464064]
private def refsB14 : Array Nat := #[7881306868285696,8282595997680700227841,7916491273928960,8733358667140285972132987152,7951675679572224,7969267882393856,8374829796870353584385,8401197562901934653696,8022044490858752,8430170081868040372481,8448616847725186515204,8467063605199831564545,8092413302145280,8110005504966912,8530324912155507310848,8965472554999056671862493440,10859049878019152292671740906321134467154705213903120,9439006784705096350160921383145728,10400598459638346300187073601981926509159665924,9040423969185255361509327104,8233150924718336,8657652105787712999680,8669977982975111856385,8285927533183232,8303519736004864,9598571994523838467738422571438336,8745274263283219566848,8356296344469760,8373888547291392,9234836413112733650837852416,8827706761079978787072,9273522166958728499574096129]
private def refsB15 : Array Nat := #[8444257358577920,9313492009748031549458108672,8479441764221184,8497033967042816,8514626169864448,9382855539468373787035046160,8965126174507735712016,8983572936173631308048,9449949446717512586528620816,8602587183972608,9038913221171318096144,10452301926572750288203903135170219491588,10982333690156480335840888228435360595740786949,9094253501840348938497,8690548198080768,10039793624243301221559614801185092,9149593791166691672336,9621693374857129524495139088,8760917009367296,8778509212188928,8796101415010560,9248809475866296844544,9719842403346712127829262592,9739185215235531911624474880,9758528028349207648762151168,9323535241577274294528,9795778969582956522489528580,9361797771234889498880,9832951759882429885181067536,8954431240405248,8972023443226880,10879486244122394227481309884217062150401]
private def refsB16 : Array Nat := #[9454320847879579635968,9471109897854526701824,9042392254513408,9059984457335040,10981584526156016556738304772399484387585,9095168862978304,10027892726949175330754019588,9130353268621568,9147945471443200,9620916844211141148928,9183129877086464,9200722079908096,9675681776764295581952,10162306832189785452153405696,9253498688372992,9731022008985474568448,9288683094016256,9306275296837888,9323867499659520,9341459702481152,9359051905302784,9376644108124416,9394236310946048,9411828513767680,9429420716589312,9447012919410944,10406443384710084259756376337,9482197325054208,9961251299587820355841,9517381730697472,9998144830478619771137,9552566136340736]
private def refsB17 : Array Nat := #[10533147257794362197097382148,9587750541984000,9605342744805632,9622934947627264,9640527150448896,9658119353270528,10644974390295093737768882433,10667488924618115604532973824,9710895961735424,9728488164557056,10219505967788267143440,11266961196268796459425272711696640,9781264773021952,9798856975843584,10302437410292809875712,9834041381486848,11368374227975337348381752386720004,10354752578162721296640,9886817989951744,10395248928419884306688,10403973584310002254084,13217730740801848797698017197633985507072296830193924,9957186801238272,9974779004059904,9992371206881536,10009963409703168,10027555612524800,11055402998426616286247207168,11072403663899243053764858112,11632996080796558169964939309043968,11113431438993238322816565504,10614807801727140512000]
private def refsB18 : Array Nat := #[10133108829454592,11169118700666423210602938628,10168293235097856,10687154400197473210624,10203477640741120,10727721330305046479104,10238662046384384,10256254249206016,10773187719410378344704,10291438654849280,10309030857670912,10326623060492544,10344215263314176,10361807466135808,10379399668957440,10396991871779072,10920482914598167511297,10940292587315460575488,12057975012895601981341322853814592,10467360683065600,10484952885887232,11014079563610365890816,10520137291530496,14017903182028513427488300570255358651960830529388821,10555321697173760,10572913899995392,11104950532011594875152,10608098305638656,10625690508460288,10643282711281920,11178737573866088956161,10678467116925184]
private def refsB19 : Array Nat := #[10696059319746816,11234077862093624705281,10731243725390080,11828209945948172125233807632,10766428131033344,12433128949551602779878783086231829,10801612536676608,10819204739498240,10836796942319872,10854389145141504,10871981347963136,13172733432680680289990455432795251884288,10907165753606400,10924757956428032,11483173251752487092480,10959942362071296,10977534564892928,12686729944611259046620512372478208,11554151195740750221568,12722063423319007414024152182690048,11047903376179456,12176834113647293332663046401,11083087781822720,11100679984644352,11118272187465984,12252316105914902855427309888,11153456593109248,11713693662588153364740,12310344545256462712863473936,11206233201574144,11223825404395776,11241417607217408]
private def refsB20 : Array Nat := #[12387715926839077727434195204,14300266902785888561818649565485202189444206852,12427837152477577814514663696,16541921773250057554959884680260426799776129802475648637741648212,11881076693405177745664,11898161283645071950096,12497048635265923031534407937,11935054797838665908481,11962644799140644536576,11971948321170457100545,13833113594586621382842446533442215627088,12010203901921262047488,12036576541534509400320,12639171316727528576780353796,12064182134378598498576,12083990878216167362816,11540485055185152,11558077258006784,14681731559764378001519459438310309674608836868,11593261663650048,12176224598584799006976,12787190831973697916254556417,14770934540558500494143630750742475689762832644,11663630474936576,12258801123608703860992,11698814880579840,11716407083401472,13535499159090140375518224155164928,12322436797699979215120,11769183691866368,11786775894688000,11804368097509632]
private def refsB21 : Array Nat := #[14302413098858354502617054684860362277141,12414670605892840325380,12433117367558735921412,12451564129224631517444,12470010890890527113476,11909921314439424,12506904414359304274192,11945105720082688,11962697922904320,14493155865337892760763373974027231297797,11997882328547584,12015474531369216,12033066734190848,16026280128766954479047375403272888729435546145014037,12068251139834112,12085843342655744,12103435545477376,12121027748299008,12729771035984664727808,12156212153942272,12765159077544856649988,13412884154876244325377786128,12802052600876043862276,12820499366939885306128,13470913461214770629064016132,12867543748410416890112,12875839651937672757520,13530225203648045433420267780,12314541979336960,12332134182158592,12958768539317215183104,12968073455869137780996]
private def refsB22 : Array Nat := #[12384910790623488,13004966982019870359809,12420095196266752,12437687399088384,13704462688864574392984731908,13723804782555402437545492737,13744054234693737588000358660,12508056210374912,13141072317092877828352,13801024587241968659159073028,12560832818839808,12578425021661440,13214358162376119816448,13232804906449846145280,16024222765707708125503288712951054610286594384,12648793832947968,12666386035769600,12683978238591232,12701570441412864,13995510794644634783650496768,12736754847056128,13380378823855284687104,13392348974184837153028,12789531455521024,12807123658342656,12824715861164288,12842308063985920,12859900266807552,12877492469629184,12895084672450816,14887289519520456414470594115930448,12930269078094080]
private def refsB23 : Array Nat := #[13576816590843793113348,12965453483737344,14285049682669913692409172240,13000637889380608,14321995873165182307259138320,13669050399310693269776,13696783508169878995200,16581741331868254679912352926786220884230232384,13733676996317331652864,14411986949069800861576728848,13761284207640120918288,14457395564962148181860172048,14470015388411355838520758544,14489358201525207497502101776,14516860968773552723757957392,14534766817417554816745357584,14547386640866766735053689104,13246928728883456,16824348130190749465135540378559253323607726416,14613423494340249755691532560,14631480882986808852084703504,13317297540169984,14663443519549872428468408592,14001092109297065656592,14708852135442215487338987792,14726307828190586846071230736,14056432396975919333633,14768316543129439982617428225,14093325917077542797569,13458035162743040,13475627365564672,13493219568386304]
private def refsB24 : Array Nat := #[13510811771207936,14185559725955820290320,14895557332256320229136666881,13563588379672832,13581180582494464,13598772785316096,14277793536966666486017,14302356091415132377344,13651549393780992,14339249579562585035008,13686733799424256,13704326002245888,13721918205067520,13739510407889152,13757102610710784,13774694813532416,13792287016354048,13809879219175680,13827471421997312,13845063624818944,15992603742467401663655449584484625,13880248030462208,13897840233283840,14591388477727363301633,14611194499657325613312,13950616841748736,13968209044570368,14665175524390979240193,14003393450213632,14020985653035264,14730665075778636546304,14056170058678528]
private def refsB25 : Array Nat := #[14766549423358023319808,17040620751352089315219674802043255800065,16273625675692229283207867003060484,14126538869965056,14144131072786688,14161723275608320,15600057285664137725045965060,15619400098777988283844591876,14904983434431750471937,14232092086894848,14249684289716480,15696620272399431239330709764,14284868695359744,19019435412592131664973467335406290165375859406754052,18164048892120448124986145401194517238122633536,17342274834139282369847085950224501328208,14355237506646272,15811392575165480418494398736,18253251022208470773520830247897945484713613632,15850078201393183735785996560,17450192789556465653774263791030213085520,14443198520754432,15164741095386865733888,16702489419661564138145367510241552,15206246269552745779456,15220081239647114498304,14531159534862592,14548751737684224,14566343940505856,18499604356058640074895661463870169961228998992,14601528346149120,14619120548970752]
private def refsB26 : Array Nat := #[14636712751792384,15374067315351696195840,16140220803929332503394926864,14689489360257280,14707081563078912,17806256075181179998768171851745283293444,15458386280903102955792,14759858171543808,15495279804097069318404,17891326666911414615556352777657447104772,14812634780008704,14830226982830336,19741874008207305480615880698449017512624210214998276,18851970911889603578519487974195319848133021952,17166051698252902782635602178490628,16390167674427663208037748996,14918187996938496,16431799467044866964118896912,16450990112966854455569957124,14970964605403392,14988556808225024,16507735120089481090460303620,15023741213868288,19072626329911679880821176379052731917423362324,15790427990751499518212,18233852247497529554592339516571823390980,15094110025154816,15111702227976448,15873931900724417925376,16655753178042868606628270337,16679931786668899150856196353,15182071039262976]
private def refsB27 : Array Nat := #[15199663242084608,15966021699419020202240,16761080821630137060930097409,15252439850549504,16799312049211076882188009732,18489064022688233402189870683252838383876,16837998579329239811885170948,15322808661836032,1013888946847361798631154796811227941676464570811853743629314902640116831,964353158776952463375853432953771395723572394851965004441686659167,7240221937261996129436895681035015424306867124457738656044374,870637449707155045723304685003642373823494130953704784,4986549559159912131608552048626496581396116952663790658207021719092482399,4749601877994632210437932856507058673971160629682795923520831444310,7490801519557799015772883092915256391396544780785963350,2510167626047169620430969471938594947383737558021460310,1271358871605510358331250002370070490480750210723971928299345823065,1397873863109382882156907300854707735090763757617016840959501712736012190635351,1052481984475843399054295890317649268178898153943151567192354527833495264646487,1271358880874034457239632270996412233950180845407120936637109126486,5657522022247288407683613059746644305,5455467270052108638879824,3755516640055194078029696678488981777,8165937732310470796247312,219139465103846388647536272596432640550802585020416033627988837721,11820497519286550984884183641865937422923057723431162121247982462399853454709087,208986244269019254400634585339559054172434061820670086759764,4392785073298306077032784,519115875151660646881228102002930480290101561659246956341906888811029518844886415171736927,6904533654065371501740281524147415641498434186551510297,4991615390901109622790519558444040844028607168934087424204700193215829337,6564225170326683728]
private def refsB28 : Array Nat := #[208990257362427942815428604611725186248529682651603260429648,229787218036171957133650962986947926206628668123438317381524647172134233,472163056239387413626605193130181984415283460969487599012633459936965715907926,2756820394236476489221961069029263993532952367129,4128628434204769210248994271391988664738226913561,199306182706609391486287749575509995059049790059073561,208987672772781898656628230419930431837766477677714434441561,190073181041945561663495832838773898269418586452,7960393440674722833563459712587969767929158555458059616353965166189434201,5156836054041242005505729552393119138598937,2072377442129832322545370857552,6279636778352358560169755171973109648723993,2498983029562418549981011566302936777532170587376734553,4464556241918370760638480,4910253885447843000290259696896708944,8980418869948367998009891587140701336653849,199302889351988638179833124890761181967387363623845977,6281238247822935184746142289774448727114000,802202975281914820119772288669983370708304,802090241406510899439851160577210557206608,9777683921429907690488740649757362201960665160044789849,2628619658337280108110723462440954472169558,4690115069061619885199790985232,6803933221847510896417099730337081560728912,695799304046974440833104,15451815952,2883206055971563076145133791337955047176520066976204057,4120688848283883194505295198618887693358869793049,6497149058838824175716094901236275280,472161406991614307965206304693462726791459440145647124344034465619923441113430,2629112301654201141811209159245463710351641,15552479248]
private def refsB29 : Array Nat := #[8756961912223651364682236424095722553212118025899898076205472912749779961738496922975,1114639569734606136405099197883846938689059087732451689010915351533239958163082794335,7591725607031763242924912476878105107021429997411397784266155054417,1061250411084581692543371852163338604483786933499073379421491194214914891011415,12514907851734599206815049347980667563893946468251797817991141174404685759860831,7721926771502453188743184,4982397721478809929044583774916407265793389003115230513121457987145520473,7972792374917882856222032619758272232394982388401457475117338919278302550,967078526605136276781313262619163292311109378094990777572144795990,839000831858338203541624501419720090185135837462,5657275706369414136222687974706397465,7486801111261509524132112,3574769783589522923710325997840,9471459427781958321663253449679870989223413854100886994458352708828597599099703088215,4979968693088931529802606827649506502256688826560741951144378109221163359,12514508091227945597115115457835892614554712676772640724240290024933538311525718,450663427360385012482185239993798584319538188001300230976137621258195286,7981104368011632462264984503618843488043808393227170479132454117790038,8368801749499159666028930481100406063667877907065276961302960354949357458774,2388195441172261244766880826197053763720543736150,7242968650229668271311042045064492092280093350390284086695254,2383802196428448733412617690654671406128601240662,2187621927559052861261708824540383178412118,9452932046747105128091728,693174316704722091835408,8573218359968295708721172971606,16005464080,1334009871152080988955364022569396931268866739973356524650232389223929172,1271358871728100842552763532676721958672290933843701994252320134484,801349365996934865520419759300479835719953,802072464245996682753910287951492868489553,841055451685580613370804583374383305783646622804]
private def refsB30 : Array Nat := #[4918042322651491336188453151867932756,6564717752643223632,2311718815492211728,16156459024,252683363496088126218802603303458210737753225527022225485183826187537748827441485151,4991208989427075043944366528076395908544524840186747868874463182551535967,219165171551853321502060922912663193962116650535705396056960554324,230104108381540199883816121474797951555193147278733472809481384305644889,7962415434849277513743443466092158701386692535808503572257512463552304473,11934630156407217259657801522290301836730583373225648041742502791235065174,5400800403859180826873780985714676877458736959577,798349886767423551604334645520439943955536,2282236963410130631343358311680660891517014,9425128688713398469107015462325721487371569205593,3936877753259267408792843931721103096152150,3174596612070068027656464,6196163870604610875765446412368,450636477291171933987873649091143285084923634811243532768682076057916503,7972768046262672910501501288752278179237820040308137697697620032681693535,7251190304050594279267740386531027991110988198027590179770710,6813160476087238576405506030207026063495441,2759190982103496465596706626453754872243990839574,4916504510820246268504530243606024214,4473506733095650354004048,16508780560,16525557776,5714216688517222184337630314768,8756961912138842705570223129638152763568555863950374072508216207049858365315091879263,7972763423276766424853999322908020398179617493504864414989117460653035871,1011170617798611798199257806020256722277782911098874355981621228893197654,4760784871125135884644249289939883577107700699170372978720678105183,4987490522142843137947461598202934886894060790679438015177247606965555551]
private def refsB31 : Array Nat := #[8116657837321446096303416482651258574866797517069504451690544582745,8233263418034261947562287619349942550,1903969095859947939315984,4916504510820246512491630174052552726,4918672669972894741200173513201418326,4392785078611148040831312,3336277298207858735683723421230221753791837392060691026250539715861501270,4416177391456736581158602156336484438,16777216016,6904874322479337948108558078578439161776211601147216,1971371551918790728237072,7589277873430211099118637422104078042124772209195819558528962646,5905191975925240373198864,1902564482597760096289040,6196241550950710210177540558928,241510123788663701237280916328912985436353406153116471296469408789341282915673,4749268249327945832337272568121766174526342998031057079018607432025,5446866541985469400350992,1003729672643518116814363344229693581378579338375195933219684428690052438,1213323951790923767195049601493938824543456487152216731566425,1052390778267544765031332222585636643684688,2281519183277313955725328,1213620784714342590692361779847028142366596519139477307004241,1003636862160093404065152519774421072,3581713849550938568432852943120,1016535647313930113287970640548839485482715321519359470529921564286473558,1978126886145613074006096,3581632859803609592255275352336,6568605626748895312,3932070761010265034626106072452900032889113,2384084232372883482304746373200,4187063441036411152]
private def refsB32 : Array Nat := #[17179869200,219450701098650923987745245187005219267453766855299735191677063510,5228794623969193985551488059416873933609932960929154069925570556954139369231711,4602428971258271201769665069334,2278655834832377157259280,5998828477359467733491498175507220752,7339461950673205836905405099539430428887261722900406051363158,8777754235564875578560657352612045376438880894836761477579118011795168203113845087,6915273866346245407140564704480173966034992122702090582,7599001822940879024039449023925237248834418310649264879246379406673,7981104342306379232155998933367473509828032058272780439949534880420182,1011599344218133197996893642436246699040280484742820226687620814934005081,1060256119216333889018692892291659941878940078511756586329863027514330460804445,919695984318467116150301493184835652210269510844624751972692,4755561006325553855629743501233083097244038780699178095185929262422,8980315349298256735446301138978001964650516,4986576512833073973299834838068792791707419295027685242372891068123731286,2275897953632038536018388544523659733373265,2067620782497547719947432759316,836416899507722153153601315451647275216879829328,6285874591272856171667740650886337387579664,881976602548628679152007113357825150922354286532841750,2505329993445316104825032372229783824,6344256314638612898797247407469757730900,8925268266581745451169329984075346656167360982031873410649770876696287073686870,6812755145962156255005733243014808093333588,4013612247930823050793040,17632854032,4013758811229916695105808,2273380565205575655231504,9460032173042963209785616,4528323388674404493707916838688972505886844450359809370576208]
private def refsB33 : Array Nat := #[4528323388677600525006044254457723866863446801324378871387472,5476363484726253531218364774466823251578862915909224023192386975855711439117463410015,409878009484826550054852065947539351398005397039889689956374,11944745627505457142256687467333386234580016624440651949576132797228617140884831,2391218103424970105574439010321,429788252949475262664092260829842170092878900591454781005744132182,4530066703280433791286458640699630679436657907674039964684630,3830417054029058064,2273507314390343252721680,4123728983861542409776826828056606309000211140630,2759188804337960956681430598296893057155131064342,6288122568641964162203784793800135547289686,372445537533816978197532073900664894892780048406,3830417054129721360,6480902768897972171424572993961213968,8512201929947837868230860845065303402924417635087026901416279415566192982,3581542338771194427323915976976,19803377241317806440470,686886290048986859442192,2273606826068447304089680,2384064218446401565759477383440,1013758783060080651338467384412596301240687125566920747677437967149126998,8565593952258799629781568997877354832,1011197577822411979073093521192683885959893394550765668823805175184840022,6601289279889280934871837067010020370513219920,19946195394144088621078,2759387864954562178912546621328065783321662345237,6319000881788944123479315868774175080784,6281465288625309163632364329938192249671705,7251190305570561557283900045022207278964506053584827742179673,4529257545634858189941574061980008188697085658355637553484121,7640699037619627826248694051578593126689809207533310782618292310]
private def refsB34 : Array Nat := #[8011853582649113975129309016588781400309279752860050013082923138634073,2630410451991493049881005506259720835694870,5664293124798162535717033988510883663114826815140860249,3415400048550868365086736,5908532854215216340406288,3935154989179117986982425045474269002219801,5150376569693884567797840,764851742451088715999097102334771216,2175147647279819467412077034336489552,3936005771319463851125992273686948591440976,8573424703888823291976462081223557206,4918870810560041710480865198342492176,5662937430729161804855492927463375129,5224897731100688,2393194020853281073146002407504,18505269264,881907548275614552765829907166512227230551036067647574,20391078977878829826070,18555600912,7794252990445536044908816,5993640766371771461262715357991538768,6911084189436626995892497581229105157563068428653449302,8439178300543978650581410827218555890775596815319668379929,8435728532347879750453369896544542312443662404648044941334,912813266813701005207567427270385245646249503187656802324825,7973172445515297156654876165311400399468175416131950679591799540086560089,6285615720248471695457016737531505822400793,6487474024398754089341445345839939865,8437747762380108893710033805659662127108707788621184569625,12515476218631606823224704285325106564680412529434377581635438076628843416015199,3335630164051808736633125717713709946045989378599300943513818607368820063,686721207121393512349712]
private def refsB35 : Array Nat := #[18790481936,765074839809241349754512005861281808,830194999126080193565843292015290628414899556377,6590925151989899434834301937157060935445430685721,8048227619102588988872798325547889769844831088296217,5909200251369721205886992,6495179993208064810606543967401295897,6289405026227792507832486352508407547953433,6492076788871496279568114335596429337,7471968883132075670908749369739554425168488977195618329,794119201577194036552526110734704056746009,2631833805475459763226648825699668526891289,6288915864969827462241218469254138208456726,20902108685401172475929,2748372946407142542758029784856821390083779462233,2883489671481395187548739686403934486094512497301393750,2384122240871739268557087969296,695706136937994575413264,2277732054101867650875408,687957787721377147535376,1978440480654130694848592,1972445578890138607685648,7796283426885023505318160,6285102564436865005340088953743625239658582,3413940814101880291721232,5635445712306307088,6196067468252125860135906316368,4991609913324970405475322905434321970612348669694444741596427106261488982,180626892293152729628905196076611736436820,1971331206403939209854992,6196146875614048445275685781588,8217068194030824689804347331680474164949434871485465626969]
private def refsB36 : Array Nat := #[6195837012971478939021057740816,6802394558344823964102616184007741577449552,2067094211010484567844554297360,4681642916794321577682688823312,7067346609975178623345325501309339848784,961130341177212921929195886452439265011202092199365211222596212054,4530064307093047266330437195269243852545380113262178014156112,7251558095521261142159177150708512628903303468651889909126480,12514879571559341985823263553589024850194722197969445891785129906406309775103318,5455186097995254112452624,4909061175134758817320871792730263568,3573592520265475145745340567568,9013567645617754128,4914632664269812322903620986647892240,4911994201691694069984697946485379088,4906443115180605456,7404642608177521664738490775050665214761783568,4472938623072590358646800,3747183350542579517983183826698178576,8176854867461124256165873848340,9910522434255099196573378154518,391098676755953841054620613804509737045058810574881104,1971408445600455079510032,9451410707767957563379732,3409384034615512016109584,2802027360916148855050256,4906443115365154832,3573586702967705130869749776400,689636440235816753578000,1812804422946799632,6194289587922087765621784985680,4690229468742101112391230296144]
private def refsB37 : Array Nat := #[7145435817710718992,1812804423013908496,8568374694813893637015932681985462294,8176868246577557331504986853456,1812135919994552336,3322635573379319555721044199855688883240917959046846732902013249521014105,6588362744101459781165098117240844298524919333209,5266590348284526672,209157882321517682765252806884574280276420645962897318757657,4917938296610199352663228869094162457,2629262006243247144769616964267777962819609,22048184724896557826073,6282741770592721066835018091414587549171993,4691297624286140936783499952208,2167522808262000559329291632063546704,2167299701717674766024049547966416208,5148772540095495445777433310727857368204628,5398878800235535612953453442433343666171937047892,4539479959694585706128721636463719915459969037960701321433433,2383129165482489985025685755416257870166218773844,4755565527137302807169382817540046822553111559411494092499773113689,229809759494576905312074366270144362575799444976904138175199149659800925,4909037644003661326912618530913650000,3168653044450320293099913105114846737496540817080650188443992020308,2627041984721296019395210097381921386452222897194144606016852,229809759674554279651582841421305372622338688754871657456352987620722009,2272725580989888587834248346569507355231572,881793641175926080743222098398852907463237354728477012,6803904561081191923969651537182853630854480,2664949701047612588399878486041298260,5153544871365554187813136,9418747735020097122742879858778805588785868568284546158053262369206658487641]
private def refsB38 : Array Nat := #[5934687453685677233327883383490292510378822607593316697789785,877705315336090818221470385488,8730104752790044752,7593319694988369431433994187969286870396741824203034497294875837785,2499629131922222733327984153645548624,8730104752840376400,7595453711408337522443677597631818952954216360343676809194235053401,2664969983515244679411982823281657172,6588005933773359786520551546340192598113205354841,2629113132707718924707416287404920761761817,2886790843317762931429071574222657074049822749296428377,1169792892732483027318891006820156752,9421709786447144840579240971796547635919083290969,3937371229148511164641727691791074048884761,7796282132592713321939216,3021866198096425657110207178943091765960355084904454434395225,8730104753024925776,6810693427874116741676741273033085531996249,2387892805319091289211970519376,2177223112250011121728941754583093332,3933713188937743678075509276132153532629017,3182883738943167471288656,1978218184806112679952464,2277456506319665145839888,4190792988118483216,2625790555335357674585491811580783191146777,219319442313751317718938048104192937385269979082748549593920980313,2277477547770442985766928,8590509543180457332723942867462487223118012797473955466104362320,22973043735259961622553,22991490479333671174169,21943986142838808]
private def refsB39 : Array Nat := #[2273421069401951032311824,2074516729507699057487941730326,5202466831143534608,8981669683369061617419146471764494949564694,9875099486676113998073662456911293047949083543014232406,21021851664,2276258257281077717504016,2281663153294674632904720,686873241080175839412304,2273507675856993145339920,2171632242987630608,21122514960,957146341436559885968019139477000860986090307935471889498208817497,686724374013951052349456,755055337746405043498278158205259792,5634759619030286352,1524867039300547275411472,3830944822999388176,21239955472,21256732688,3033033632819183888,3033033632835961104,21307064336,21323841552,8170001551392292174705732096080,4124592010106528310132545571575243336421788107801,2280760350559926309896208,3411066861351080656371728,4329183703312144905703356030200222040216207742303818064,4318732787690882185352599745177519268737114606128157008,1974029828620448558219536,3745899458770552019456714493413033040]
private def refsB40 : Array Nat := #[3406878089022255066775568,5907334888182128727834640,2387471876203088802464828490000,2393384955570449063735828156432,21541945360,6196067466942405992965883564112,12514910828970802934710506642273518355926722024897375084884555982840067461042271,6724324092291068472527990688475839205648,429194792334879433379877660232787776008154865119129750064015429721,4916199636111907831972413509684428886,8986206254430263480616021876998375576178774,429792473756741974428336476784808985167825582190459476474351341913,1052709786699068762273837620787017038450704,6586353498986274439594155311097856298928265515344,693639740223056014999632,4394554663481590056747344,5271604123068792912,4185955137912570128,7221252443736811063412705460310,12995900883613394465486998491296968076471958092000839898223380244392809700571897908723799391,10355238748573540726872269477184633356872321173745307243336022,3412099878086822967115792,3491948624563249415071278711799248488548513763340438190655417655482426932417879,1003721561949245372278593536211299424943280115796125188256026761304036693,964319714452463740740258029756288602375861919263923125242912068950,2888448822881253784882794684821039371920789243667173654,4755561006325560216084867685158089955973223472667359322826874115414,1903966436484373228306704,7968128302684763425544894249591919434669456991980225356791786967160673625,1003729680694578994922126051707571623355154373056807299474298847806969173,8981013119013557442546462791417612873241936,7666415803529786833610543590549525440035399844939129097576338768]
private def refsB41 : Array Nat := #[8427657196794517618193744773703539354322094533960455143956972791545055237462,8614595814303426089357346012037791124539780962832458920519687171220985174,8355417020184888949282785503820591751461542086934698085750239694233553289433439,791803105949973802011807197453693220110608,870594438329765026022667041345480092362246130003887441,791803105949973802011807197453693253665040,7185929177101436008268049,5150605047405552495393360022594496600822032,5670141511789649560733744453314260386441271734322876758,791799441428005470176740682149010253038864,2888444073183509008619009366479427937229534378012792080,7489653042011789482203573306220095051865611649681805398,7339601689054509342516591998661779436782065175764035258373462,6975031017323602266472293740063857577011483514258768,3330260606367759090788078626605678262637402994902983683169343183487587670,7314428621356074186860697996798992519285613543030419378518,4681486435715850243792959702288,797881994470530431945634367731723901620496,8427657196794517618193744867239644143691284349902575283103204834565263021398,2754661761549374711907278702646501215008571277590,791801029051205249746705398278735556527376,2389264865688996955982299939088,836688342899287374880971234149045553883021328662,5145869874598238297800976,6970831563903627411768230076198030780976196187603286,2754639459209094922364238884713658587821905297686,2277562815043045515727809645245215394762838,2405239017442514660281467889907985169526304096393385302,729477413618740567146299932944,760717844383621619375649850402095376,5716963370692207421323423531280,1903969095859953794564368]
private def refsB42 : Array Nat := #[8574069931375061197113549836769366096,8912877868506995744980500474240532656394308674113211868351528733929452622175,3826634738777460752,9425122243919817446890843336428267950965583532313,2888864989842987984013663366386071020475659692725780822,3488025240995909200777488,912879453875349821452465124542877999804338555857404710622553,755116185919094328139938673582162192,6853036096285049104,2754639451191191649330593851306809145966114131990,2293858672625235251044073443988851903158093369686,7490794484537804691520330445653947268578507824774271318,6811804086616618234180212349596757437714518,9455347635917359258013776,5148896289976617889972496,3488118555703333787537488,2754994611983155422664399680941696608921921585238,6591529451087126496934647236523649072846119125273,4192710538444144912,2280731698867361494191630780606899326029910,725473075322634068053669724432,9460770980135181442093136,6071054526608542410619825814520287312,3488118555720926107799632,22951231504,22968008720,5272307811752083536,23001563152,1971355053474143273222416,23035117584,5901471707295419237400656,12515016951006461680311510994531972407432433364674341381978515526930279028839766]
private def refsB43 : Array Nat := #[1971355050923276363890960,1971282200572558733213776,5635445716215398416,1886885121701969936,23152558096,23169335312,8441769768119782531734541618681790364341462191418260066646,4906443118804484112,3026865102021560341770685823281621916467379497752049323692372,1971371552112311200399376,23253221392,6051735273472016,6196073439573861735318872658000,6361533761430931646595974469595516125264,7694837297362543654528076503207444074542475849767955181786698070,912810864202478320333641762943791717890731979290575176487254,8176949622417398771459270381648,5557477147917943056,23387439120,4473507018124255557845264,6196067470449808907774864920656,9875076563287133266491655582110445228162460615247676761,11935149031860314548548262397442645837998584765236608063139023391783473494,7251190296539941894344809062636509436630374462830990926827862,10392105742532683165510617174137377046,657507976915976208,23521656848,3177342158793087971959548779206725111844918391215220381883747620182,5455187473369955327803408,2282549032786255714451472,2279619101224471542906896,1971355058628654371438864]
private def refsB44 : Array Nat := #[5790296277357486314103936975184,218581840565261066383385874100436465725671887353263677474183730518,7491711114910021277716560,6915271665632655550110545888923433848111039003137167641,6915271665632655533242903048552162326856714964595659033,2893219158962086153330093106376341641877529296612118614,23722983440,4531236277186984787228524068366912375170595961104813530567961,2626431826735237747175283062999656374206745,6587820820498386433687568573215915105001858749456,2167589205595748199554859288372723737,8572100083462078383324949731092988185,3576371609585193000146587111440,1995191856093641141988173561881,694761534940510763892752,6051735877451792,797800578203720598382038803921037899858201,7906554894202569147960230625140320493653978657390873,8051248705147983904133315227650715852789030238622036,23941087248,25123499093786648,12562642654452241747875107882303504056204508995981239769109590,4681754666409856907306091152464,24008196112,24024973328,1452393311682707472,9601114800519256499663589605462,3411821741174639928803600,24092082192,5901410393390137179652112,3415125152418425445023760,2278691289701925503893520]
private def refsB45 : Array Nat := #[24159191056,5909124587799761939333200,4539473819563753294211543310431329017030156171707203540046166,11820324932817487774186968499112276700871868557705285799716649653211604716967254,2388922583659481016502007890192,2631089447030836802001702376466064092696598,5909193128527636065419284,14483597867587903499730630463887183896040570071791119895414805113451172666430806,1971241343934332605304848,3581033685943320942154167354384,3412175470672319345852432,5630942117812764688,24360517648,2509648643312686707679446615809347600,232506084677355000893456,2889031689072981991938888904059972197715663336328418640,190100533805760310433028362174270270891350053200,243798335782375622592375640080,24461180944,1980095284585446643077136,1671582647439409116335446962722591824,4470313500815867597033488,221731937432174608,24545067024,2389961202095261917750899003408,7232497117814335193622226487011855322010725644667335304630294,24595398672,1003189852878869920564887180850254864,1523151492172064453840912,729502649948459750557031399440,695704771485295952789520,4472842284778563366567952]
private def refsB46 : Array Nat := #[2074516733621322985925171740694,1103268754839489209310136827834412942878452219990,5627124613827002384,6481085305984742989739451876352737296,1885125904724918288,7436516132917608464,4472951382298105464754192,3739367175362318445675450236230963216,24830279696,4681754665689353130074821625104,4685419076664376494484829245712,7240227501274900540337904903534767991360810955806627341882704,7019335751707877794120778959297092782868667695431766,1971404986818354290638864,6386290227197015515370066187684999872784,4187133817565217040,24964497424,27476646276883174916118,10854973289181938887320119077985828440839626937174287338262864,8986410945019158827257597451610386315153744,2631369572294020875019467963861266320331088,4320205979090939161938014848442891620435753168161543504,4918697070800617735993136282404655440,3929204452343746181168813486109889685426256,4914577990139097031784458447986430032,2167279815369176302823401923843264592,7251555710327204995676281815892792832335815318352388926297424,7603416381303936643345738669822726315707581789475897239034104403286,924747087960992450371175106158112624780671944491734052197712,2075680766595730851458724401232,7251555699472735586365137999513559006095381043974907689718102,1063408475447604059115536]
private def refsB47 : Array Nat := #[4210582271994795425806294192150,7604316266607656549759749681555315977594062321404828177331693901140,2278603095495304371354764985687112753157200,3325908350096379920,3829502267820609552,1252874641022104513597841914583912784,25333596176,3830557799033606160,4320204237603445863482328365311049159394306473227261264,7471975186211115754136219310839849940221825661817672784,6285740594300692586968581239094354925392912,723136219960018344028679458832,25434259472,2068309566608475599289545146448,409853497794388993315332335637785170978688886268542231789913,472557183756276025205494464947783686915045626149813555380789720141580096329049,11979639377295802882463987405052103101765845642323973200,181053995972676112002807305329210440286233,3750609096170860665995708101129687056,7251158411632649298893187024805943629961478634617097900282201,371979060785518184309604324670128762235678638416,9909247309088397851308905746448,7740650125071816906776252044762695208417752153880906756800857,8116664168808382143026092307312714090070062749715709559852932288857,4128055331535634396993776236998979556692616040784,10351340850924529138767063679936356160690077102805172560,8510934824148568459783504303505286374669878272015112922337841347399340377,7251925903318465296943078662706864162922383428693495356069209,199304811747657141423335499553005123640959678312371280,181266670322343900835281357718930144382992,11271714238544033057663663229828652237567645784124176202666236891186353497,8117585546715744605929556716004855133155620272368360142663989936473]
private def refsB48 : Array Nat := #[8095650119574965486603405902160,1990692148031614035554532868432,409068862556168398270004630874660115515469017773058261533017,390866756692859563980246970493573618389852755810337113,8046861520061149393411368059685924822109864003453264,11980387666247281335781347628804886670078492863458726992,7382065887918153746526984154153231713485710830044725593,6572956101568673123371845852363476783184,1051651227618934374441166010834307699200080,181269828804307481680015359247871522133264,11980387666247277270095411397199313463558947552516920400,1886674018288009232,6715153328499736948966566123201581213826762768,8087676573796032719285443907600,6127678628724505243988605659267088,8562485361288774380170272571408,172869368063459759496700732476772368,2389754328645555204541925036048,323317100923790564139737547024,11935144607774778106568991925843899451993084070643602103429422862031999321,7048164355426433615863386482755993092432,390870593313054012550023613594534569575448672390365529,8117894078820242215142325609478124759171490321154254012068213899609,10352110789186984113869664081819129249889690155745628496,7721926769989535708237840,1993144672450234170673977114960,354874482527458927048068618741510057492505,8116788505445792006448726973211734285041679243659297771501749881113,7040214077267625833057447063257437162199149985817,7040079845356246352245790587046635991638927753561,5903662120864755577258256,172281178121181799372339603829964816]
private def refsB49 : Array Nat := #[181287938031123688300202828126926180470800,164860321170560595140263563280,8097027084884761921173229424912,208444787985984410693505647749938650290587271132656904197456,409878017723043003651813277833798976051756538766118465323353,390054982782511540959976647913147777813950783042179408,450045567884181731585714236276508456148772934645251935258791473422094681,8572794446612139966076699839752851536,9425856241660553131738878533752688929273547149648,164860700085130613208297525264,877701447979499493348474440648048697617858480888430681,1884949984592527376,7859939959586645746650479333712,229029504178612058649099086977024954604008970980564340030950130899571033,2391029061619283009569836765200,2390734991764740530926534262864,189581263637355027088218176356825192250211325200,1194849396562184506191563014224,4259824731961950224,956471143599045303712689967120,696038181409961471639568,8979008169804172928607407894531424528,26675773456,2890625824329660416205600267636737820235999185116353872,1886674019042983952,5267769031493943376,7713679203703138285539344,10391329076137884308878288143662470160,2391029061619284065101234311184,228839205554036560216378575358395719484797736344252532333986438591042905,6714688117214219539373831067799995349483856,2758808045894427313044661069690581626275369337113]
private def refsB50 : Array Nat := #[156724624354779534000144,2393365614348221964010996891728,323607543603913504901951651856,2176311770263584784,390893977339260837815644089961234002820687742098227545,5272923542206283856,173173604014161332214452968760807440,6714694181104372254293114150343556670439760,2756731197929319808902075364157436598374158911760,9776723805379622437951872012075356283963759825039671577,2756447998078749103498552737192452774960091644185,27028094992,8563063598466065791523299065936,6272659321189315785535095402676560,9909944032872179213345501499408,29792142053436194553881,5665324789666667298832,27128758288,29847482285657323208729,355555045395319323297090614699791964442896,4261302476160106512,5627124616293253136,1885125907174391824,1886885125795610640,1971408445600462629257232,663471731743129616,27279753232,8168859635344329532605869654096,2390290103053842107614081859600,1524129527925619113869584,27346862096,4690214125214749484981005062164]
private def refsB51 : Array Nat := #[4472936749663114070593552,5907334888375648679903248,27413970960,5715654329004901471081496576272,7432417156236836880,27464302608,2280668116857156055089168,1980560270339820319150096,27514634256,1522412099858193388160016,3665119655714417072791632555212924621246800,2385899210345229874549922746384,727891304922036897406858055696,27598520336,27615297552,27632074768,3572385498769823757444129488921,4906548676383490064,3041372335413133584,27699183632,27715960848,755141933000734836605679523664494873,755140503450788861942316151096738073,4397875078523171536634192,27783069712,3658306274793334892554870591510,27816624144,27833401360,27850178576,27866955792,7795080071978418256,5451884784056712911929360]
private def refsB52 : Array Nat := #[1813068313840861200,5199353021176217616,27950841872,1452287762492309520,5531403813801330726666324,28001173520,3253727613491871760,28034727952,1016425172897601645032461686379424028539005586672810506179681718690469206,5800097285552777892194659860566,5275157750991552592,9013250994846302224,28118614032,3577513294382102636660887127056,4190968917327347984,1980556446291156143443984,3253833166775910416,3754965695863384319599662956790678608,3415123783623209980788752,149410464315473936,5197329920099876880,1902564482773693365240080,5634829994871226384,4464781703550650909196560,4258030330696695824,28336717840,5900469605642470051561488,3035637283450519824,3581445701406034352309724774672,11425726188654618993602560138874886847514532905241,7798073054392292697444368,5630942121906405392]
private def refsB53 : Array Nat := #[4681567895998561403762792206356,4472842282227700181778448,5909193132960866948612116,5197347512537579536,7793461080125897072443664,761345494689743171104368102340821328,4264785730372632592,28571598864,8176872251082452888522796044308,5998037938748540501117683386979520528,5998040553277903877669527847091638288,5635445721735102480,5295276659048464,7436516136809922576,28689039376,3251739697156718608,1886885127288782864,762846390459544386894665939781222672,4688840792406442597280494391376,1971408445600464155983888,1902693609806287991750928,2393060060373577235758732034064,1979434724634052838818064,7793458413906957057655056,7796502126679119150448912,1971408445406950210158608,28890365968,28907143184,3322301955597930512,28940697616,693954924167995763720464,8730474197236580432]
private def refsB54 : Array Nat := #[8574065726831254217968680658295722064,8986208406272225165736540594124727033008214,7741534281740649943802367446047192556247648392808853304070425,31939101059014855753750,6462023858202845441698054224,7796804107401953360,29091692560,29108469776,1978322876204338517393424,1886674021475680272,8166382331676717507149904,6975035321282058653876940624281953246545159824359769,29192355856,29209133072,4689190927344033542980883451984,29242687504,2505551596474287524297274570644390992,8730474197538570320,1978490417692709052747792,29309796368,2279908775338561099792400,355795054605104679178361241106619746814224,8988687580526024111927529007857809030973776,7791888063059156193787920,4266281067025268752,29410459664,29427236880,7796804107771052112,29460791312,29477568528,7789397754315647568068624,5198103977544122384]
private def refsB55 : Array Nat := #[7796283434783925407580432,10896566994289845678690893259979513654412560,5630942123030478864,3930606538971746364572709070346312127676752,4689046101977270417830019596310,3334470981858293208380770140248648275343420551148269671668538607620412758,2392307575955551821068636520720,2176513940726108949148578132646953046,3033537673630934299909968294898694216444695859853458673046868,2630448676060828868697543818709354451042390,372536579014139300375262837457258318429020229654,4464819901816054279831824,2282509757826297433948176,5900469605642471444070416,7789417421922248656421136,729423389747609826585950290960,7436516137933996048,4690233473248294462565789208596,2071429348579414010809263853588,4264785731664478224,2278691290388026480656400,2392423636489359449637042520336,5909128046423543992549456,1971408448151332273274896,1902933417831091077660944,5907552795465834016555024,2176681209240748048,1811361873858150416,5909193134544163692609556,2631554588392191265339136266526401037095952,30031216656,1900558328107325750001744]
private def refsB56 : Array Nat := #[2630299802526337152618711174563304643493974,4464819894110677161476368,5907331789881515564089360,7432417158904414224,30131879952,4688968731333557597374874124310,1156599147633863919805293556842606678588352477995880729,30182211600,1511992289564055337844752,7194053513483351647846736,30232543248,1880129729374453776,694982971427840748421136,2074307426698626704604949385296,1971404993485798186958864,30316429328,30333206544,30349983760,1194847438939664641840157622608,1900889432171388224946256,157228740003952062369808,7140263725566529552,157228740003952095924240,1813156277304442896,912290300289383191806032,30484201488,1813156277354774544,30517755920,1886885129100722192,9450864430049260726128656,4914799414540779536,30584864784]
private def refsB57 : Array Nat := #[390213368988036734247430866738584770462579064541828176,5720644775801612998875112816656,696034003125042427215888,1884949988753276944,2392880101226577992257289322521,7741536870113679876133866936178509692996730197239666941380953,471911622298435152348151810736866655417730381566986651069378908805379390789977,5144841610936922411122768,9909944032866991260092474609680,1451601670021595152,1601004675264024714225469374489,3581708738142322486296072683545,1814774758772850704,1446447159577674768,30836523024,30853300240,4018592873580628115722320,30886854672,2090188047178378832392909733796790550,30920409104,1978492357512697070485584,30953963536,30970740752,2075680765894754576663566356560,3335522418004251943511241209581753964803405165428802683320556969109312854,2759429587233679204709629059514609590045731263568,5452069532180781483491344,3660182531239721779652422799382,9872809789437256425089415275458728446204722889040,31088181264,31104958480,6595142085184920373896898729045286814664818184278]
private def refsB58 : Array Nat := #[7487134443164843340992784,2273582981654680194519056,31172067344,31188844560,3325099115460694032,9021783208194215952,8567557139656377985740610668815716374,5156947131449154089322790204967655125029910,2278655836486056671186960,693770456568931325837584,8097355912930353517778540974352,31323062288,5157068759423343155983733554507143811698774,31356616720,695702394446716528230416,5635445724486565904,2509548734428439724779113131063706640,4264785733241536528,4311362437480027922210076120882164348542009671626851664,695706133701044724826128,4311362437480032005598479172143725927484060518774539600,5633756874726965264,4918068314539914762848434094988333140,2071431313231446613982139650068,4916910159193571441733194496126226768,31557943312,3412171286722719649891344,6495422978595421763005709030850446352,1980096428394206009230352,5633827243605360656,2072357807285023110557398732880,2176819213084007256857288663512645718]
private def refsB59 : Array Nat := #[6194285962281834112698638681104,31692161040,31708938256,31725715472,5720194073740403677272938446864,5902946513679000354947344,5907497451398518158934032,4689130934899879850057369129232,31809601552,8564478412334494326625964119063531542,5451125434340161357086736,31859933200,5715919312040444908660363363344,3254097053274341392,4688840793734608170590736224336,4909121397972452778322460492484051225,31943819280,31960596496,31977373712,3838919730605339974084504104145522774,4311410573394890367398112613991242175986273215057252377,7217693377394826224158906515542,3257281239099375632,32061259792,1678294064600109499479775288481562713,729249305735495071505963040784,7147089495446261776,3411105272200469515603984,32145145872,801522089723534040461013682939476415877401,32178700304,1883401877924872208]
private def refsB60 : Array Nat := #[450043358508184252343179794969216883474288984463919243429208971338404185,32229031952,7793356042108141648,1813156279116382224,1520198418230283975279632,32296140816,1994017748233550866522218447184,323340293965474655764643578192,32346472464,3255486836441612304,32380026896,32396804112,1157137911288768786949064691212893141925025397750382681,7433490284568379408,1333473526296884323158596824386713005795949224556220291273692343870707033,7793356042326245456,2629406055990955825971497662843449011880217,35740136184907948883993,7793461595492843600,32531021840,34137226497490968,4187591222019227920,32581353488,2093452247628710887239187015835599129,32614907920,32631685136,1886744393726296080,32665239568,4397875078523176452358480,3041231602941165840,32715571216,32732348432]
private def refsB61 : Array Nat := #[2177669007681865930908282599638302998,5633756876002033680,729344584795326818810227654672,3755679698067194702803086799610905616,2759701721498794809810581344911499502528023037264,692123726096418334834704,7796502126802268445737232,4464819894075495574405392,11382778699849876676602581554232055972634088497057720822179669823574,32900120592,32916897808,2278583665875774154738898337642261820739673,32950452240,32967229456,32984006672,9919806999212955618163357126678,9022011908407955472,33034338320,8224087864245829921639735026329112129321182550649521900198482498902,6493419233758575496078483184817537110,802090241548487992810169313171919456243792,694982971269513909370896,5271604134443745360,1973157430900656825450512,4259666408830664720,3329602717050998800,33185333264,33202110480,33218887696,6595893689921809333474631147788632823873114751062,1888380467632406544,7436516141406879760]
private def refsB62 : Array Nat := #[7793455678286847224856592,5627124622400159760,3407668921187201914765328,7796502126802268932276496,5909127109903523374170192,33369882640,9602372093628621789511324532822,5275157756309930064,659777378831040528,6858788751875768592,1840170998307554943379932580729588912161946617177,33470545936,2072312689866398256500723483664,33504100368,3838696632204340179059937143271985238,2074595973598996550691278045264,5273539275344838736,7495953867120107738632272,1138833465409925466357840,2072359771811385756802091323472,5267839407133556816,9254865334124936590950742631642786330838836123963357226445450834694486,9427800163056622355337115215119713898469565666390,1138834764241021209477200,9022152646567399440,6289590036746552132343448269341057868955984,5998969167544336,761691014235335327548675142066393360,4918045975497567844709781545354006550,4419584843252924296702947525746757718,1904559687219049303920656,3413927626911275079962640]
private def refsB63 : Array Nat := #[3491255801959356953530448,33839644688,5407448735680145928760533243299921234229568214294,5557705856839057680,8633267810215092411287556268693668015116630,218572317879056206027553659923770753606957699375101931552765134166,3489368460695406995575824,33940307984,3413924304574164184862736,7855077757261708617511992299542,33990639632,9014781520933556240,218570210145989214254825119856197621475081562425443048052137149782,4128875488971235986859284306681018466634789032278,1598764365789020481539136312336,3413929500408720334524432,4914721720583622533503142540637114390,3413924304609348707946512,3254044278947577872,694010264347445518401808,5153658216395285081374992,2280409862334577699209232,34191966224,6569872281240076368,8480787336700433731489877802025505808,7144186786879639568,5800232692053368848900075552854,34275852304,5157068179872347471513345072611090862706774,1903967797609412052402448,7795484698699890768,2393268450528985889832260616464]
private def refsB64 : Array Nat := #[34359738384,729475548761206163762616205337,8485661675619659798515350114528151888,1995428339927420865056214106448,34426847248,5766061278233906332385165584,34460401680,6922091759716400221001641837527376,34493956112,8734045416540078160,3566277609483159765455009546256,2074556530958749064885795356752,5144897887460473037668432,243665814671339217904247832912,3829537461487276048,34611396624,4473705459495775794167824,4190968923820130576,1903969095859965924491536,308342888697824989413648,7794471833967798098592016,801330930262943535801481425982683752710425,5452217475463728667296016,4471903738873538444267536,8979247033124433088517332192507003216,7722587387537759573917968,5720560746641987375629268484368,6855428645717016848,3755679698067194700569917112976737296,7604315061020244409222346982598805128885104101734292144758765737302,4464783008327912011333904,4329975746004078387514529369841971655117451970139722836]
private def refsB65 : Array Nat := #[3415767041835561984983056,7796504792898065540579600,1971408453305847800676368,6190726505317154491989798223952,4471749054551707661631508,6487602303158115657952717947795673172,5720854222885776925673278210064,4261355260553199632,1978543885483022095761424,6497053906265531093736356537182720084,5275157757970874448,5908532349266717067972624,4686889134704863772308387663952,4686887169628557832250999443536,35131490320,35148267536,5211917162848285159580173340823357187562567212586624461175346024261746639066454,3739370027881725970125148743166854160,4190968924373778704,4689130934897213982964179013904,3566138432945536892022375321616,5155811212499835453061507918940878773048336,35265708048,35282485264,3412261728133585531060240,35316039696,35332816912,35349594128,6186914870229871162863506423830,35383148560,3413815424828294690767888,4473657762139603984]
private def refsB66 : Array Nat := #[3921012420738210826668115845083945000652816,764754448274304773172572621863453712,6192214994418727512305876403216,4688782763927243693026839893008,3566273371707455107993121653776,798034371050210320,35534143504,798509360106963984,35567697936,1454539569922850832,35601252368,35618029584,35634806800,35651584016,3036903928143806736,6493423036981178441476069585221582934,3576762845209062965882029146128,35718692880,7789855200574963792,35752247312,5711725775525051232708660822352,35785801744,6196170156483690650067758485584,1518101982593792690110544,35836133392,6595942815642814606988696627899967240511042109526,35869687824,5556017008992059664,35903242256,35920019472,7494272044757628772946192,1448786925455425552]
private def refsB67 : Array Nat := #[7436516144108011536,4263044111386542096,1978532714708767655329872,7125830304923456696803195233837430806398792696144,6480904904888632486276662205099540752,727584381203572402490128466192,308618219269309490790672,339330432946355743174734529254654224,36104568848,339082053353214226025278292018594064,36138123280,6180674898705286756201673326608,36171677712,686923681413609691287568,3414145670481639598198800,1016527536616141926664431577938342139335416394368327854294503631843841366,2280731698867356078218660962094943154999382,695536373750058024435728,7796502126960601542689040,6497153967422687921424149155122774102,1971405347176704616185872,6190726505317149566179081519184,764756430352538588156696788234208272,2067862818727264539153487101974,4682844521834259812077380309264,4688968738193584750598258163734,4311362437747636857198876543353207230258267477314438480,36423335952,5627107033351454736,36456890384,695540116241348587421712,2076354313831811647066299695126]
private def refsB68 : Array Nat := #[6802744072636324284155107828629829025271894,6196238107423564524144799514646,4311362437747640940587279594611973701036890353174906192,36557553680,729325241982212984747224006672,36591108112,1978543885483023672819728,6812654796816285532147427786367162256724054,2072353802573194509545466237008,2072719727790981688347536408848,1880710277939593232,36691771408,36708548624,4263061704310784016,764938968905436375827238864536536080,7433472696710856720,1888433247713755152,3921163699585060688499885372630076844475472,36809211920,4915239225449791504,3329444391050809360,3491180718315808376229968,36876320784,2074657260068843158362613104720,36909875216,5903578174754033841899312144,765318238315950747547484930335638544,36960206864,36976984080,36993761296,3833970694786387984,3921159549655027607678784333426572198479120]
private def refsB69 : Array Nat := #[37044092944,3921161294554301462120115896403398493537296,37077647376,9744005907947983052653883777761043237471129168998713607097678383849739605,5060850191849429861116861866895704071349435484731868332447057,6779170041443895005423515870847102087256577910197357869652399506100393301,8953603326131959046298154519206992933243513709737222276648129986958032358168021,11439332567767070371455712659828860183018032789314906237247153074302642843592936510805,7807454687902162436164002083314128675573344978305775049993428769887834314350895797118522845,13777112283600196297813988428533831919365755099724062383788675557548260233614553445135906165,9002086603918182843107072599386403749403358899488561464029557163964937188177022208077825190360535,12580156208004306469057723764213012908895967140465533390789377287164628535266856687529530041554389,9442138495486883808742831734639090643858683641007942470637176651731733627239857070260815844952725878263,13193919207090868021420180188571521681283686734314736316121748656055810015705350414873037431864093562357,12950969987336826774466534962164240025721789496256605706231502046728569207850436668527790165328686937049789941,12577711104416109295687001486560684114157865912921951629235040746091828606893540031159106113181565,1872423929786360381735199901950933771610127054043328532073954629831385318943138479186467752465781,7798759666487414943538839628933953574395543769025731633538187051786811187433735505074148725,10117034386402803636190740987366222199913111242250868938890505028950412922119936890709,12011584321010963452525255093853505611890458926361631443144443681561662879104247148030818133,10314652135959727841029259101313222056507966076226076937598683314497988524889317247914498233694037,5908431829510386666541553137702860063481945347260283411270411246606698520335445,13018941553048436175125905656055228687501798071459817873750320229220209256577968473556473813,10311390478538557871519938566605135593516856162059222850640302333049344594163306053909934788534101,9833639135958886177824349603098088728306648372959495429412925227356386270945111025223816533,14825999676659969246609507698984937824079443055531242969652624323882317138800377568645576021,10311588434155342372133737477844574067680412210440650418453888519577152535535603314554485192357847,11684787083320335823464717928345750838450909557745988864918635761011075465443373405168827866727644493781,11476833816741445176992287683740699265284002029594355082180374795989424553637094716757,16741902419879275926539871225108117679558131801870379348342725076264957348744397613042455132100437,5183008486062360832160864378588819220109697319246887638427063200784067100877355459609096505938350135157,10826632931807581832871423962750617104052905081343028774866548948440364193083082777193945573351753603031]
private def refsB70 : Array Nat := #[10826558442518579676360794710798352245737721938181904720241817526500837975022293723604499260267411896151,14834849603202236181448033247024225850131381659447294974355510416205291875257654618956592599,9842165057706714321931451741915991450644619558769248283413432963392965501150810626796246357,7782732126007280026353297110214700633269505815151623739865672206554143969858901,9844775392098927344890743839363467135877667571256741069432576217837814580047661241866745175,8557208706108775500019738803958465978261063127072318386936386331905455520805364473553311189,7794436716760536513979971039383965741879823282393642816693564595336032076258644,9408743673818381508048684099003476550555104245480036630978181145899602907933884001607640207438756404597,9832810124689002825645448284310475552014037460457065537728792683110039588588157896794428765,13660574883823722680462519955938404771286233262162202894151838016976866504817810408629353318282583,10626815103387404929447590551729674743146612341448625181855908892770561998839250782391203157,10323095142939135014359744286538746150770062170691421512226726404458948449687031345082641535555031,9209153212771834109216140334929496680822441618044588986719443057169470801,16755719380465472235971502854780468970076118518830612920087638784893754525023561275907975761220951,14457523209750238202218372980307595693058421872095465577675848004992266757197748499560004665046485,15958396041899758078724377842033617817542529342300647415287859824327337799590825757997626837,4837824510570186578513222800986187314958417771256651741736688781801029123620605718479466120705493,11252632274263739085005992937877829378619573159077532478725305617992750036170717300989982549,15211881452430213644073687186952334336950984119876843063797072032020476009342886565207,13651834730480382788276309511605767853640989370349341541900021593057692482540684437815912736576983,13651514815093060198828879120940994160877254327440088179276099736640304649816943865864216177890775,13149959671205653116005796350489154583068372184201146008046304726591425043205260662357,11782100645219857046724214345441395484480649063949386138426194658827484068856170587115638366494589,8583573136871964396126529886250350985478745950118607133789688514867118333935405257454569418589042242911,6792110301778516527660530739158972297216405048985976699538015324311213333,10105499766531476055813698503062346076939780953641223270525560691960915421203315250517,7806714290265495153171621790469063706919693212186999922915800085176615081981082838404289885,7445208938117385674492757563639585871459403146805212560830950502809689213431610463573,7092671758178932812177308945547611240051902546855671208507704473524616945825045,11791293558271105284268588829116206807744739585156064368944689583573704882996361877073610032010613,8990954408158946483467660290622520529138807702428095376123072719990648983636872145930997275421914253086938589,7437296857398716624223996074810823323757666999296738622827102506312777087381155468629]
private def refsB71 : Array Nat := #[7445831437294206947951139751494995026968901337671060793716513762680989447448175932885,8583430532483718118500311805736818851422492854022880164454761490623818665957144801693202105786999231861,12216799579260135057119216336807099035862677388046065282049981904920872492148496475618128737230671847307597309,7808424215665718776979188196316383558128848170940824595284453557282756402856691969228363255,2058746105749487281292139014370005377684328406288692646116401285093563102338573992708736851675626415880363485,7798661566557124208553716014845235947715441636072912208413470457939500726163244309028100085,11111117290945851943004252658072585802042336108419319347809589459684695305270611197783544291644789,10596384548687708308686983716976776031494821545289568610819817928131963204613586586156094837,12965302810790037620560020407447756617649477387003754934203717899570070430370929873400681549699095108616443351,11650848021060671237459363181402434569764022876329593129913071164532206221089267104060743797959940339063,11111114499501247687435379398181886237249440394942875184492266906308344776740615854213627939085685,10596384525087662543451663741665620443141604061615641416069923243209323154432242219769748853,13594768797801918185743571083659347503744187336696643228805615527774123238661262313688953062456438754599847038154237,7798850366590244479267805377521136977575903390110245833433038573868429384999805690391680349,12954266902328511365893167327538574628531443050585159304976564682770137319251865546826307226840341410052142589,8177521943146117633064956186202902186965647228385780988072656847785560912639845212252201881040151,10105502336178875496489968830726118464354114694337817232081246655789832212851744660821,14012602490094266492128725098643907048938056520319613745091860,9763793449724027661527638580290162756,9574157971500336563555887772343103417304946313188134865719621,6959071756289,7665813589827010564,12488873136985636505423525510966807743213493056746902609,7446693617274759362058899730608849982918563922807112696252613478535413102766057674101,5881918407905015805288719581248694660629765,7827133348944950896426855876491399573982993080624476701452442119930617942874855971497534845,9170688199767363585,2236245520097373317936814587940,8449202362396971008,2344893465470489175323197003683414113,10924526410061844746071188692516219018542176357158884056239935550540859565233493,12011647462845628087123682339592349572816390084084734177245565039345266494234609697361982805]
private def refsB72 : Array Nat := #[2931700851072891083496847508806278319037501272059219498327633730892272048176603362737214805,3073980772107872325445176780556155101476408111264606214672656093086088184576118469922896668481365,15963186673139539164657263494741958980686601553196642466580997987534609484960204202110711637,14478188949547456280373100648216049552971278244550561318055572063060551176111101320217317533120471,3074111142445210669490798894593838008677379333001337057910809107170296569198184477262919163665749,15547294540771175034179038884888784755142870401172009881646127801999005406244133671942064411367261,12585799956848743979073428877018536160766220889989623613868739408942541864651049342761987129308629,12585505471967340962570852612846785973321793736240308023301480672928887800748814559239362393765207,12975863772033047313658967325556912517652430891400695702491618845408974661,12868990649010018620182154772042775409818171397967247343260875540615484693,13167954716456153167077093456621857280020932276496731006764636158684053464187789465429,10736830324470673927003146580960750260114191037937590552875032527026726849942484637524,12585766213094161203100081773601961219445807250550015875142834766901360251156334561547222897350485,14503312934189140996231588949842234825873009602706665113775783484334803149739349,16721179177353958853461519103635469893077203841348866080483051093340306527998442402259318788183383,14119665631939406007214259272524957807840972107182794058676964960216785922249859618261,15239243615063735872601434249770758684042981378094471371880500906955590114911876109781,14826775752282324537306489270944977488058912281291228993415555201896847835068560989536738647,12011895148027315249601613692922970630169696566124448086877758499235527607608172520589317469,16721179177478289661521835194191826167084145004830109622541384750057698954628979457086877442364765,17533427177268660208691460473809277746212089820465479054070241458943357732831175560566417785985188191605,12011675509566706145287103736322623579543988358041092097612485861451543367218016279580202453,15524803504114247266022153522992768900005324149352838897789778241783486381806721433802766083257813,11976078665032785448067533158103009244718832632933280813399736227781231957,5732499661115168793615345145956628705559933057280415312792743357792531564624412878440848725,13023377126180974460265849270187682418472306843286278347143825277458475577666097395409444181,8569948347565116041668514466969346302604207349444963417841039943514400393149954261693978069,8986049418886872287109384955275084673723423063631846407621927183311803873864626274781866354900311,8198278620378560328528700084430854377623454556225769969363318208802436362698245887317,8583593054900693460200375535403440361667095713584312549150340319611608021188131205099648343,8569889959599351010659185261512644208121728864382820974421028703327758756357859490709984727,3950215561905300613940322962017518051559681588236886524583245203096958130305647212846472533]
private def refsB73 : Array Nat := #[8173032154196635585441141428118935036085831062013676205917477828877024844733305943383,10633868927918014670434849843055501260687356245512994579144179677983976299307188148147410391,3767043122869048422214054492336710581176366203725194087783644532905559365499290473813,11991902068009131888361695854456521923885771542801,4416191633384917481372237545277315270899679353224721080663394719932551877281726158173,8954930110339853561495467378828940461720370827076838274995351918330131193877845,6101920562742123761077046319870245830824986541214867046373177714710838320118843659637,13040476303318365308825082350995192339073532183874502843037041303935725403091990241053333341,10307972846339610576887466168621865080275127878943768285406304485911990401223515077718580124933493,9830444590021307589047759910918447975103178904805215595068960784297925248077158607398327669,13021677836007978795179362061828310904812205549437247593559386286634148659613863338441037653,9838871507025173693532129911242966095410607505515142286439933200452144667782897144619718493,3074108978863902983817029391074966316093453030396071583664840251973860951024937034094734436949333,10616779148396592173760692680238313386988424705349666759634539664337034643746207396915934676,8571284318432342611991539769534502061950345920014269990413371886304822342352428329103349597,1872419473769788532651560011532208978082178865124988059739570139943177674624511100153402687444341,10316701650895240983503809550707581081271826322384843088217443902521741898541086768781427811906903,13021617734687033782623496366606754760422563235205476255823282713545474846763184679919376221,9856745420615803151667422118613836730992377006706136658141401139687721106819632551949588317,12543747127407766529656219011572487769068954844128409069864874687852667580274005,8948255741650932331558719521968152886081461378972822038215299809387672151348565,12901515159452570716326537961151935176447236618937312254711624455493,6794347977342379858363326952941625994245883821654767564635801338879495509,7454704909214928619958690821069959397986410939183711279582019727702578257,7395602073922396275097659779740251890205115864625205573,1785869108099503031780626588885407904848980767349312822608915446726581047521168667583010165,11500569523268833185071494736922570141555225935534100697130133,10625389069325185147883217504777418840243146759828439605985835179087289239676376457946684885,10626094330430408561683430114172602469835946941494736315859674777154211658162715299941799285,13023354713106852407884035738570495759046988173545414298112878896526320112805121100283731317,2931569473314943030673205079020892672909533407256378952349067795894132402202101125284844885,14145156571540274680348456676591183752313144252281865734500728052047939985360513619285]
private def refsB74 : Array Nat := #[4408306662966522620327011456719069462412849267057119653839953380258208912827850513749,5466932240297276793925077512920880703911665147606126604200520734358027119067168855381,4408282106389909232369229921855546484626749960689762504927726544844771720610935297373,1872419467771822456984528046028476499887992507506787218666408374722465085414153872697543292835189,10490786036541773784849750134158897697316611192371045649,13343192943406295542408918472448015974080023492350465108,7794436695889963423565981683961514533205653711858350169357337888001398767179093,13040170442850699889799628995714126072902116795472899026956506370831327232881986063710909783,10921189615180762196703763109738175332446255322886928108524077499386226659382613,10723346670178141132472102515684467281770909599765099210094094415838203766195425990103,10823624805772701151733662998069248385827933944886708906707531329964632943683496662812430888401167545815,8952781631778768400343080633724765942032967485078663817618890091604125517436245,8953033287136408931427895980927010762013124678572354300657982914971091055498581,9844806483035490241240914602865776338405646102797730448240281653623017648870895795255727479,13028482252145037841382975139132557771763638828742968069443173949508059121765130284528653685,9845364877504198438685169962252821498759437146201214014736107163253628536858356148606948695,1808516776000,1808516776000,12424536337060111409949027031281074054318271691736882780430593520771904553970860119381,13028515059814838965305346183067427532555719679427739020926664698910518490237378876134225367,8954646427753722727073330106612606979322402847943428248109587030682726737204565,1702959621364517388214299955095529423754920325919159738730057163084122886016043668821,9389599658825932334626524877506362268236908161120197523085585780109226551720812049749,12424842989568394366975251660355072552267632227702512077392120712558367037602418480501,4713924619770824245154347580966148884176778868816979088704046356091145835176406972034798965,11848658106239325246754806439866342069830733978407385453010046049791448171504981,1785682606340084438904978770159127009537321517945942957834190801112262805252509841780725109,11259182102452147391524526729876210945,1808516776000,4076259512320,8954279918979406839647074012727101345879850986724775342549804856395930610783573,11848799454380766016666449932223177968089132861580182932271889329972475346638165]
private def refsB75 : Array Nat := #[4344971211564314429308992,4344971211564314429308992,8977488226601235512363904866946595236341061149497172034386702487932155882984785,13177019797753469410004741402442504835291188139508179447566414112347986948350930146647,4078843203584,10933915244207892634457374755204013347652868,3426565761536811880204879355968,4277119635469373504,5494322636869616640,11475326225932146012516531273700394472966148687350274801033850645468604231321671529813,14823481491310980069935689169105942453003258149075865659985541158522795433000314851089022293,10620503373408669549189864377962180054097898589315599787263850488637279654637899707896395221,13159717600777160308310528014908888187931141636028327626781233266583553488850217424341,12448291487827621315430730022932885511990702034611965325926233563589434910490584503645,8574765774687877966429207529211044559035301316241253339852484306209479749210081440744955717,8177591710889791359185463554702715511736796810742446789666610322054246889766031545687,9852890668035010215061360018931316153959385068871482237273842821245993586429856908859366741,3767220299207904111129653514231876839060782909537958391762041330732440172598520010069,8177656432750495144770232192041753017690651511667521976558675326486350011235036132695,10128151021845923230020089611196540321273678242713767979891692532797999103295756784983,7805689860912130870199286234021550145270946150331410063113804173744978745709973,9818045375588530954555194846035375258556553030124523540,14964399951661204277260540971328828795587995803788571296956346088604128597,8378104409561988871318285644252809239602734234268741135585301,9463945547880595460,6496388164570159445026274688256182013275721879274097471667482130999456745528327955405034837,10617954591823346224959455088352466275258283166733602667020603032175689069836989145741219159,11241189925640787887623153411913900955533635940722270262809797366001160157616188685102175605,11443929085283411742417647813510197623781557511395746815828462298818682386909909964117,9852890658552911821825594371129753648034817746799239066773558595169449141531912395688465751,10127793681039240936703957587484521628393914381497285390683554022406807296873579509077,1785678361793703086354151145863693279843833898998713620637275197998794570413263990864434517]
private def refsB76 : Array Nat := #[10612178909624495216739428266076607440413881438487265796722146413473251798978719225834984919,1872617064614690987368570640567420376976806316929441436379058084521472581667524726232175032620405,12614805784176335911688831234699092907529091101256694614744753370033672206067774352146855623989087,12234929020900478822889333462320460346793380667527912704826030247136024058212307645537724563361415949314283383,11869296223285196620205552315248906629335882943001211696222053167834862090278007,9204678822812710628843449684059291114783764743604497875419924947732354326,13153819620350724968714229739116510283986325762720450341651975708676957446270283511125,13153847290559627345115509845987545858543105355812711039621927729423764801345167938901,11253351800658044577840609006996886732339288918824836518059858388079645797829183975613357429,11610009249212869508421613722700919923487365060450585941,15165273800897455757539844094013438890815699971918639378355941203821700501677255308511932048301582835037,2931702549809439921445123281118479104168038623844197492036771855886772080055519444156636501,4495546849173559552454153155486343249375137357427617810514510989996942709347843396949,12105759234765694595211115891879702832677878668878747156,12544600413976828328241580406387609257674565749815241356206051898133011099899221,13153936218939722035413703473303805728919591162587859764382361451703036858350639078741,0,14523468122162778269424887330717373592508812754346971578031541978209927000642901,8194314631367848729798217942697285950658618814497814018810546517125554810233447470421,13783202452995740723457184725820025009146301345144670876266558313345511472859773909394087381,14125389242540891360397645247874179879476081524845805364558810544308090133435108382165,9773532226227728020532310100926751991265928396384082946589583610891031637,3950029072864169643523129524084971670817031207573900113004560656909868024294840892772406741,6724537636011915179491322363829615538542452254698886606575765642553292627452554977879593045024597,8184949022332479556969091713931817508078897227471876101483365762759483822003088348629,8187368457972630471479302190996127848048228349307764736418497755034490720161163990357,8582691648680059312487605318166615965190576062546788720517470608670198687027525341312014173,14811544150535813703541929287365204557464252690874497093526839333676707157617929286449583477,14125389242710836995965575517082562371206632440276069750531965318282585823744861099349,3767041278418095015582197811466921783321219395680033706794447573262640905819526616405,3767219132523450213782102832267186633663937567845950413166704403285175712098060424533,13033576137810276293487054999029186970622890029594517758387336549457523383072422966737589597]
private def refsB77 : Array Nat := #[11251262906624427746568891021244878922116624710884134976209661218162014714042075238452516693,7806000383740554869234248533122063549705427961628090539997668598124056247883093,7805972118853051656392776164365417469824089742482034681379419172998853573301589,8196746402619610983400274630002566798713956573627502673576299933213259659732061353303,7808714270461181380645171817569679541064282668163252880421270007698543233815893,11268012597990944140591330226711036756366670989378051936743483345498560603539956142799412697,11093858844761557558731564799408478288,15231330941243089854437939360211915731103403058221942954891345616543079724207537341781,11470015968153325763173730775867992133024089046488730423696526691069809425580528334165,10728706338288121096696688369914284407064738945531780634166413411265540666894406997845,4713920107815002810185225394738457108835379700208983646568730109177753030145038916582331733,11776426733131092483201172824328152860263661061150174418827748723414187258860223651837720485911893,7093282059962998074288984097104,4426210881243181627542488974753667829105635394552759555860574954696367569889709086037,3426269328866528095204570141315965348766392026797983353955166403975006549,10231807733497341401278656771473627215813196853282083342652953211437635692482901,8344779504903053238641454530550054929,7826327086429630391530719141129558328417240894207531633177232162097786012261164093925578077,11884925896896076085020935790659764679326564241418450713923742557653532606762499465483823388907349,14815263829608435519532459239621229840810187890006715723034800965574196986297582366234072917,11884923890139933075297533911208211060058334727415197322466682422904860903060666235468357945357655,1963681674277805871830504200630956005651673750276286944538639687840784397148145927711445349814864141653,6398950188824409766833855669473815695000689594239111882652348537893456195430618939059434837,11884925907093167776906951533523210238302553614475141625598464521907471825359001626296265546749789,9396063411193526353741346697645850035399294654871672425556289103196578874382364267863,9396507484823780512746778064456229098432165388980437421156211840302670772460351479125,11334346664248490298174917919334741797022801305425994657157285733176172058797383341831451990,9465833765106368512,8771394625704201549181019763980669930563160807564002794083955593301,9644193843744478753047795700987776495076778237246216298499712317378564600452437,8395874673459527680,7568233513433227633150141678656]
private def refsB78 : Array Nat := #[12032751672681646550983063570022103589477726806271895776287731532005500385477839372934282581,1785802692034155956185940741820518383876781617803871264358298573656955337822312546665190741,8172765393656094102028825378867595985279008737314399131661176918376804302133673680213,14130572324504757445249907492542991683880802008903141439216247832686351490388933834069,1785678356748994960288426880486792421708789593484383000105549467240032565140136130961167701,12025249390647247714309999340974042301605839561268172778228116443582977291691688245312444245,8569763947476599856713089510989857443526401678332906419720349402109275110254798396966002005,8569917279505915459188947506604626761824263039107272108551999130562649123341306578544719191,15961723849628941919451959995251689957232155029094231606909104271513835197421772446648071511,8088403438915987326271762920995706711959370415083902021,1477081808003411053593932968497191816737171549121885487993378395217,11985565420826651199606146190480500734113682593925752549225171630809240916,7818406524685696201097854265601386997290849515695284440218814815005954824033621,6376379561577551114551300,6609154879721424286833845489665,4860988557805748288,1165214801276237520745625110924574784,12005303575078212824428724834820046724051871631558560149393286541468178981014758552008873303,11449150601600546641195707448885601946845956246742663876542168834051646047945798016341,2795772825091494234261468344612147938401901097676021932613076836258262284884533138773,13795850056059322423835399530555268218399729242453853145548853225121047745645567972176516469,14466815927297608560017835426268764819885135910596117435218880002408756468206081065264759476411863,12547224262886672310086266387747826545601931347643564038454058546564793745364309,11785947225062780769050744313553821472941232715497222361506162364821863508531598361148804459623767,2795889427868252879499963001062554683649142870666145355278398812124687310208982406485,7121788183234777070996992227493423121988125805170100656812997108696991397156437,4942896891212060846586681187983589913082739927994148306409625394124198465621270053716746778924405,4713924599910170131150314201677706186795008499562892399469137779763183947028358048821630325,13157492794475546741766040233332371037818780307405967215612778321482970918114595001717,11244710816713955298716243531381907805332457738739260167173777797379076540798352547426694487,13157493358904007101183675411289496715241527544959559665668197790629115355531851423061,6999611398054079522492801764501554192]
private def refsB79 : Array Nat := #[8585663292134659430934108176389,11712906659577826238504440367606687175361541,12547456072864330875025379276859968214767110120998666557649191312755792058602837,14529879359918306769174566538376829823344530715569042033879086202483032821552213,3334552590478162928344161446441220934200075833364,15238831151794194348872916981010270610881132434740093140571114663445808055605492280662,5789649684372914241,7936954757016737370056831574866019332,1445105631232,1872425707899427381988298002069765319313552640201235772520743805489149998287109254709534669496149,13803281880611660190667565036122250333961369814171232120736989277139791859904856409104283095,6415390393973795281102426846626374549644006983546520075466351435147588933052335406278073717,2795889434653829112661190952960674834833702933228713818594796493310904247772362659157,13163601272428285546635937127777077241719789439670591316155641488222840077036400506197,15232930732043789905760813714075332380867236039162977249849039091139190500777329546581,5955440923119936828617347207888341715718404,9967243254058636459301712147947842438500420,13534211844292419913144397637732407720910183149783569492,13212461779514249518821515760718274106364907504308546210632907950421,8244616226401173504,2301474836224852501742596,1702961261792575521410594517830863376916974023224575100988287762014729958533048521813,14830841899642121985368123670521463924526058565365262332341749280190846620456950150680894813,9852884962160155455341466710736925145461762667632336996384981330339257137144758918062759253,1963375446789859562103175849569453562895072684054956629976323551847472519904905763329059003973779183453,1785678353575364359898400444536227848994942887511398601127663672062779905166073871117800789,9852884964829265191298794638241817010881087341018586842667194179693908794213099933412056405,10139735912780166341679433880269694804047248187436247156124099589702057471361735415125,1872419462426680070714710481140939963864056085784343199432789052612528886573342310202872574629717,10731344743271023445759090167399795296708038677453720845473490818579619878533749626197,8929487291836653357726665113729490080776468,7619837479448820334815457685675191344428802461701]
private def refsB80 : Array Nat := #[9211818267897513417337724578082672895057700938706001232657290870194984277,5336168458659475950450044583940,6378928526888907511447616,11884923877833478509598776613933872772470490940787626062732965746192679451944199123176888475147607,13167870290226332093410638566251823928644610472634137652610546371893401203130288690517,2666367071812136534102440642645093234277714025690725461695943086909250854017365,4713922541275745942120035768902716332495468931546594250068793594024204465479259066979407221,1702951995087759284621814645575213148981131575972370843863511363994971474150208918885,12552601560689698959473634597988341744096657480138185649299996663448054416119125,7798632812572727064202108308593040331647314948253910548423396846213102231167125108016110965,1624072072708105816036548855507446643770640252851318143509900195689027857634645,9856280420833806327743744,7124081349901159863572080919586871202230395932427444407967343503605776178828629,2931701599371410667984299604995492102839055037370403259130029386766299181880762731576252767,7811499836527611904,10322795475972841519069325673514730514,8242595964839697103655821242060247122,8248132370434,11242277820223572749097642348642764169767478480727736429433253367599373982981135385775928662,4198013878994845292847896289490014606513855000084737116860731518957289282626918,15231807781353548600109135314276303099789392650303977330210075741918956715966809335127,12564812149524565946338617977265205525812328490561535408442949395505150785050198,8189779288708229194555244473240390549058814376516607045427102286713529976921028646741,1624066870544386350194289848564970567519310730148124559916856010047106865059157,13175154387022157032931206603743172895854823567984814100535527323514046852416021026133,4713913813733956632166168291971510302507764652388452268315106362347169130152651824093942133,7810212557392198981158355392032784761379313413169576252296573146374266156311894,4198012448774096969028174432035796143419491194577410202900087627562865005057381,4417192853797232305635739116095736272128829623902237584345436911147572102743756985685,3718629308377627622229519941019830537520070356786121087931728,8189799165683712257604470890077795564630594271736264418499384033857427582837564200277,8587512770447341867038734646668373191722831468305377463576428566272457259464278425512277335]
private def refsB81 : Array Nat := #[8433583219670613519317331887172,5344099595721896962226873697536,11509242425352683389738517724450264321,10900811895781984865300170438512236831933931113917079685977412,9829446104087793728,6695171080334387654381729223936,12015868845810923939988152653958150971224642670310016261,8558356595744335709858293103801289882130674832966602256982568815301044039388772186797333845,10938663618772733217557688691756399166117381010490088593932771006826671934629205,4642897576660463079387404532394030635189665812328058020952723027182370000860351470599755613,10124025235156054472898989989075653524655255681096614226568248299071108448304659529041,7783780515678608638374697765823038837679699524827819501969964878173006523160917,4713913806767895752925906953713691239654192744461217024088413766006950182875123625676461397,4495543975908535681262734005026041510216818061815951176519803517410335344064424400213,1624065104559411953665917012639545270766888084641923289218331527516811290826069,4868337152548373965287753071551236854663117261436007897208436479614142708283992393557870000952791,8161886480137021340307334092596633638680896388111490904629419911940018751954549692757,4212427147668850606506139976520991392494844377203979824502235502970579872732505,14469099551180883128008440585844976832390908892072141462523083792304169208570895586507795427974487,5079150472938640998678592,10068728311276354083439775093806179155610404632335294406153297,753880248063426564,11920743681324527539148685295927771201,6018607176086454336,8589063635461563066285624821698572096774618241131836405577437393137226500390088451737091413,11334353705416290131401769320895413124249287501138391414807290828445756007726075452319028565,15241137050275912671342365969077131889861233324127578815295240419591234938698928059733,11334348606710219082982116549018600780485337014486976208181807740701539992604994529811324245,8179668699800928320,7815854701723371581023736885833831366746190033544937770116015761509965256231216540793790293,4863819153323574636339190321152,7815850334839517213626750641717128703463135686824042081241472258861147837572405953966732631]
private def refsB82 : Array Nat := #[9839115327304193602626027910517021321408580743684791424681620130009385139580449910452223317,14131995185584510877201964756202924973564934036530827749494384844292506666408860808533,7802116147938088472999021815843524964601949019097887859107429706776632424555366871968609623,11884919944318469096555868326564418430773268932853801726461538757734533995155585441757672135579477,10809275289016619592935639900297594273125411097039326125526091372302548129667167376725,8941228223968251881608380131175058129800706188536142814860368,7799070155856150553628390287234779260016159530635277905342762160864846440420689,9216563220642424803310585284004338791534552704953624001923213685767362897,7805942427351571327145807250785867910627124127675356690710140753031741771707729,0,1548916698892483081983791273634118359220217261147123770050652733378549076,1785674589363276671306866190301039600374455214065467299154127656347019855284017245883553621,10246593278836434904979730117307774128308169779677672951446622148251964589565269,16747019223462844451700186166968844530964119950898741799035658630615587374349497444494904800532309,10214418997962098463707038474118347218101262871049140425129016514926568174934357,15971241358384259711514414248877443307963207796482719970055143957533735052984066548701287765,10231778266199226500467520864672184316642572439234419242969968037578937967465813,10214422534352222687190639016655032591735361341564490790625519263430335037856085,10728767491719273808612821393730947324111738990425672697816111711526781240061172602197,12009560198128252876485823082385312766459702033281615658464318318631535828190369052064830813,15956161396413371888060551054576652099478102245387280667542890051452893924722019447183595349,8388744440466809306621984130928457861803215356654500426630420,10214425411275091485502684748891897162546843260662195486016781341424297837222229,4469994866233141869501975953732,5823702325360131779353703956545,10647799540297102683164970844244,13035977460110987253410375646235374254363322933669115726019211148918587724030060265645366615,10308528231078511902970025640846494090321449744155676929738471039378544078968145,9375556529133239234251703068202272001660692621668082628345443209553,14120612363040678614452445111357373225707111730074866083797807650170984565607526399313,11334346655357627269335168260421976033500856663853616834362962417094955666797648205789363283,9830981572109432034999370985792851090256294541290215175298392538884692305]
private def refsB83 : Array Nat := #[6115936729883446037855608372595902840383939272630676197303195926926643175415998667605,10809275295774043710588127933215537146303963648624831871208740435270009947061218530645,10809275295802313264778566268498763640856423409478727630439680803717892155118334596437,10917371476008068288744788632195215599073052024205768768616303841100428714792281,8585078068187108971596042837738106066673028919711222665378387640374119768905805746691987285,7805916576292979126396633500028687734820696617933439162512525242790596048148305,4434659106053757297034080640324176378757462439059820498306735417319421702514390029653,12448286857588575415028403403730454910434746800548063650586848468032048410300794754389,9933977672424687296646670390988645171335248864820015949664813731948569535954429860132640085,9606760639926386688,14125384850215937762471888594771677183675357471327319771085472440017955883610436752725,14517470785459406941405303120183836753594500625318091208780529248433185198797909,11884926560950866940373801866600343730870037680074226739261057308314826556952250081670634184998230,13158230035018855040763854121745611545207444656859066620218002665236257128159915629910,7099359511635576048542906276170438077965708910595823250069840548177,10809277153618365258248174041910633207713924369298787836142544450256011479215355811157,9758914949255034775745878349312767297526795068757809221999816944602404436,7755280005117959218375015068755553980530960,9773442990666425875044456936948896018861086743909635493534041258896742737,8198932035137583851400973806741259883508597140323370550095522565573634845474913851221,2775572283396,11334348607002842764635432892956315146562319067121004967865379769894308019661547830869611861,6782005235602831905345911914523490291602369543815770767971664,9669612711495490692232799378684440056673299299762840172798719565691065180976465,9773442990670766170509138840676122596374749386712968177953102964782881105,5804733235200,6692386855534648113644543426832,5341020709163048380356922200065,7517310750104631313174532,6117836980224,2956732663808,11299950482328602434744172526015478996115801152972677918489953984654169429]
private def refsB84 : Array Nat := #[7122046253489082308788744609467338169613490507981484934941103616811548907001173,0,6432175030234569927503194762334932267321487727380045499095654242598258025383644564756485469,4405846305700220959212292996779059161793807503543850369858576645062964570298114233685,7468004233503339789353369918354774430313462577572316124955517415523117022948361592149,7468184628926887740761769402553898162753729163321573870350221059607037606742289896797,13488858474441929519713564817896101914561407685088480712994555187834242054051413,10748720527821839762391385987646349365703263129785239995262547187980531119782391830101,9662487215757679794440905221488702540943341085177052250894886003447911773988181,10746408750604048158776117708184851849807370600742564266661426880440671762791513052757,10117685516949490556785652245787089931961653947585580726670795777821636136307713726293,9865909929333499847883191284673554706149492653652214352570680046844211758695870192980448599,1703135298800009464680867252544818674686529384449373446414037835940202145774396855637,1477235578477455728089511857961273348946360892826704090226266035285,7124361927377564223865340668806516471572729066981217227785773069772793453040981,7122128651340359666274489961381474685867035523905883147696956149966287536477525,4011706355899894322309815031423639900370972850289576671220010021075113301,7451048581104386438665893997433926682062889098863979106636854924299072794676377802069,3652595801673730937216555512357362380242698097705754599441748,7352988175253103902315126283149771860,8889220992198926074395613331857691178256621054759850831316564,10746256733817634064086900818371203249606274657763184829637925467187809580142508733717,6792272043167071653727465314912035756934482304157229399455250371922978137,2931700145190443675488045696231747516357890964306740903633311271778397537428187282402530653,5111519114364563357745057294599651664,10248744201696858984005804577720303036599992053599723644610817402896075086714197,7122328957359243696503563501382196927221673731109784690883238611243550847096149,10248687088935996826875483544528544082882976670680091577304411769072224816158037,7122385153937198278880017562738951028963589733682182371631211825175642366104917,8889220992198476669775841692636168472677147328876496901441108,6792272058439410826364908893663973964370827963418248507323980568796947801,7122043852109783646833081458940801102954503897192042119351225546688555461467477]
private def refsB85 : Array Nat := #[9625903146269144933571692845608870970838854332423947348,10749257027031647202054846757705953463150351329078141861154709850491011645042058417501,7564495061474783833162614063172,7012238250821185780249476005968,0,2039431303031488516,4873170948434975074947770090564,6833044487721763844670528,10838907152962364851355716,3767222943914055491485651261879784755962786618945262420602253503373613783451497231701,4214033392038693985456190905867045233141513464211550150897338470468551761548693,7919024164531472905547826912632117609346263552324439103176435572641608884377429,14530565211282499298071774142740413308266791257881154132141508636748129945085333,14530593922790362717394450083705150363887771413166103427587741221446052933363030,14530533076778047335509874881388450744858500931584545270696265989782056048354646,4141913079186270539170353683387400437839502857758842066115767227208390062551182123160156612425173,7530967121788653338171987754194136527823745817611062682911766670725013813997511994709,8433583219670613519317331887172,1785871895912511081408231912032986189339413046203799978428802156772116848493886096142587349,15236638643278363051015677982906871794324772540870645755417838760316376252300057998679,14530650036358524422169551073405086678683809661319621638333267416848873565803925,9023136335152863636374529,15976803590849846253817016592866636280192055838243319016209227687886937693574950752934647253,4938364702134636544,10417772917802308886864690430980,15241135138519702285585585852543830367802342365927921844666057270956348440390720116053,15981486818993212751520201331710745202766973010012580107891856688473395424796003649409341269,7820264077317290221731482628695842564819353136102108033292000539241217317290604078845752663,7453777342593381323528251036168722715909434242412731964710952909625663221917453604181,8183462832812862333923351802001045627381703235141051802750922122900581237044228216413,7815852030757550823465379887454798370389133016518457465702614208873568883616687746566280541,4435934308618961876297826971940075645201886528949215860484649514741080241063438145365]
private def refsB86 : Array Nat := #[14533106612707872837721851655976365243355707634453458167714184141052387526006101,12025567789562858921288676473044386656233372883762413076584187337853980584151759768148891477,10133686920440674724613520047018960961078678599482761858274861450966330379201351603543,10928256471655371186364030601171294957916157948194065758952646399089761437701462,7585139354726379342020864,7501800279648958620647680,7953595086469723966050543879232,6782001117628233702887169192042914228591974961776966198694997,5290800234937532416,8339950186468233796601928663423796544,9169867419409920068268031026201367867173018621504,7804471415689263641881470343631873539720049869926749849899654804859047676040533,14530647161697957146737491512385351303218078366046525475649352226414437382575445,3847559204041706423041787860850019010022713095279548366759891653716,8675684064252752821538836725769,7483546746535830097363107598337,6883297199121235984,4287290559250271346602173946231007653135695297049008603963402783129344627070358,11864406120457303395285106508638176885910787999681741689880588770828157298501029,9221203790271152201980973548555095490872343919715803728080169111469253958,13815186541187263986690509272999622205941262980752478956980330958917184424260186525532509685,10139799573804058219435896202034406491380442758350750661992194463614245527868931397461,9670091725611200740072153795079003431530287556584470246984055731898655670887766,5342495365552547350199476174852,6089171707888664832,10632408062284066633587010308776364775394633286229043058548145184949097740011217196632462679,9331740331867825493794731469133868916487587355493133848490102654428865893,9235758776078842637583360,14486233154802054907776742269662812378978400556321408371412812033601078710580452255134052970222967,13815314053941658108592434214605321076096413523559756951553004210491041216891689660220659031,15189916416529719903728599672530658677400790260508799986779356659794177935409116795039698206280838895479,12564841856472975640684088037171184124608645077140318765354999939761687112279461]
private def refsB87 : Array Nat := #[9430514241949130911023279650220811330,6089222625027952640,13173466557715943610616904064114146823502843850411828261,3669737818378559075706699546571486926917714532081936412857428,8675919424859554361140143457296,8559793123047148691798959297280915836846541923767451308169385211139282257,6752506502743295452012501513946575028896004,8559794593382603684429435149584454867722653549413034266475760040279627089,2630740208304259072,5693865203451455275002882343564231748,1785685404708484578849753782551347547695672256894903046750077739792844684508596344133605205,1702953619910914769942104356895754291611605660093284681353147285032990376435438146901,14827481031620757792768261630604855098169416656992681337307662023297000092091797469796881749,12029913496003593419647556201409712068950916927712801809965060478731536330757341790269166965,11853547759889950832743300151485655819687382826587228837135228119500191666885973,12029913496007972792784956376689958424166147577103278887806011482805416742511534455468283253,1785680304131087423953762421513901126145974915318647610023455692297214191183481577143621461,4287289565667234533898964647706969148751299915714719433046444464106893374477653,13049032662207236549604603037550895230440767517834237868167555310190536926745067327990355799,9409313732848659604989578771017827586270827654670234103661381215525805115588453160279,15239243615063745529213484325593832683350814208957038839691782825020322392378753504629,4425257309814741013575820232361639460222709510772881092748213913018583418662702929237,10941828455350010490266485658395937649727561585909402519657416252243167406282069,1702958022356678689983217332634814672767816749488094219028588556173792277811397219669,5225282837921928582397486801037472031411586104543035057852756,6408047300816412019867678869442902101108140379143274630617912732939815394043790206770173271,13035940366027439239562323567313137298076450328209071100385308383831237057327348651562227029,7530961572869750583616507651320907852203531097791574568879303771944134658930884564309,12607424199469627189626081631627854457882861020478826864792645,5073697450689924585592401626208508600932908381804169825178645,13893418307220580017984090736749362243724115609186192694006101,11321815020268171401066467852480524880736222013025639624319196685441254998]
private def refsB88 : Array Nat := #[12483478284187460141923898274255695931493652309662339349,5513517654293364992,12607668173224929007769794649404914896569114142028716202608197,11256137041208861665569592226882851076,7452143841773158464,13325360838524413998088372218700118484850224060218805084839298291089,3266758836480,12566591686177921465231288299440894488167583500492205740703848628484453315204437,13177797156073556208380843103900897821067708683318644726628115105576286663526174774615,1702962308128354942258333138109494889087723156420276911091595315156813609777086420310,9656379796119142995541727297918247582787998820116231480662383093297347898463637,12566592249292119456469994009824305256311598325362813014087583358183176305726806,14534663306745847523404495392521027681817471174764779394511591847469609313981845,0,14525673596940877501435200281568296178937497753273024508133011317635482524144981,8182718070704665206126946397550339643832994881317603158013075586941933486313125016918,9090647409264156663656001303907468304,7916705626992531684568421449311156819831603588715070801506017550512223784621526,4227832300678322199617295041873560435512215592355415845938095818066493940520278,9009799030827082391130929365399110916,5876589002816,8266729335972444793855196164188889104,10344682482217985366188656544683749376,13818202195676258040367217608886352103091491495306871386183654624091317727412210207372441045,14535934871139504307968261704910441303760154961517956137646823052013490504291797,13167837775685521828326428135098458367837620814038413795893451234913424218747510814037,13177019797754459027097372065497922112141765856282367453700277148584736870954340537687,6753614829654870294888907380735604171277317,14536021250493537544918980935411122524643486569085753016942097084963295826630037,4340525042594414160052292,6782099191546530010506113729725146081038462187543576178942997,4214914294963257348]
private def refsB89 : Array Nat := #[9888610901765812662244935731541981511558226,834376006322839905303170998336,7892723652507992065,4215124640533595136,1407152199716372544,8670951198677127514291569753055796960518209,13220048647297149840449552902532903256064014562892794987362716505669,4031335098311300025604693342048977402952155016337880426647725332738954821,13609676956748586473907758557594140456495988489990162257085845,11177413516722237074367544750165998059192820450388,2629382518742189056,12289694405095670994755021515016165247058247320859360028333649,3495057623908991354962331825150246205080219399518967109,10173336776464880753818371254517777476,1625182402796586486727748,10379807464808733672423719729529171897093544267750901060,6153879006947866446962112122099450072561752491076,12304751463091942321180372110270763506266271153195564462789717,9704370072093121770090218405956,4228600823808,6467238604464719239269867547342439218087743394638283076,12980202697656495776305144407388890081000954017164313940,6091351285612679168,6310121378619101636726785,7125040392060457085274292426247878604306050891704184796401412580191739001263701,10874911785485903541963516511506473811998255477585962305,5468894762689057402093922947137,7214632902613196004656192,1469014787666032946380868,13862225730593944250321823239616414159397014976318613094661554493816395333,11177525020469499829587370706890325013827700409428,586632135680]
private def refsB90 : Array Nat := #[584786641920,13528219159660074164045853709083918899122542288262696943986512404013209173,2629381415271138304,11735777174325259213099623226953115077315313594887652436,1625182402811981713114180,8518638063100832206945498826931241989,12379733891766314766901896512059757403412957774949,11165347244690506932816351435176393783921452844624,14535597207683804468173425266441869131650925209291021480809899614712940134225509,1913025267306676979114969555686130704,9097294099762348682816695398179030084,8955637687430468241200132,9706997977484647173508989716032,11984681125545156469944382352206439119519255311287743239298369465678648916,10371123978162236548456148917351223901628641141057,4854552023145644096,3711601232649913408,6794671499202071824557048893585265098385759770431658914113268274032890965,7936956615685495356939710778609517636,11093859403230463966933501704405258324,0,4034219811267614981792012814912122624471277565696826518571542416066876759,7357332578931216244646509405915399674991684,8977715392028491102201787110651999475062579203229184950631382553719588718728537,9090646695417639380139947862229582864,4937072222491639812,8322503387520721174122113560467336959379012,0,12298251860195866157343281656407282783001806252256206764983892,5430089793608843495836312666692,8652115394087044477157377,8322503387520721174122113560467336959379012]
private def refsB91 : Array Nat := #[3447765429368440339012119499840,9627566543572272193309052575282347268611861630011380805,3351913253453169728,10738052199593185274382737540112,8678135235397071342818049459201,0,4290013483187049472]
private def refsTable : Array (Array Nat) := #[refsB0,refsB1,refsB2,refsB3,refsB4,refsB5,refsB6,refsB7,refsB8,refsB9,refsB10,refsB11,refsB12,refsB13,refsB14,refsB15,refsB16,refsB17,refsB18,refsB19,refsB20,refsB21,refsB22,refsB23,refsB24,refsB25,refsB26,refsB27,refsB28,refsB29,refsB30,refsB31,refsB32,refsB33,refsB34,refsB35,refsB36,refsB37,refsB38,refsB39,refsB40,refsB41,refsB42,refsB43,refsB44,refsB45,refsB46,refsB47,refsB48,refsB49,refsB50,refsB51,refsB52,refsB53,refsB54,refsB55,refsB56,refsB57,refsB58,refsB59,refsB60,refsB61,refsB62,refsB63,refsB64,refsB65,refsB66,refsB67,refsB68,refsB69,refsB70,refsB71,refsB72,refsB73,refsB74,refsB75,refsB76,refsB77,refsB78,refsB79,refsB80,refsB81,refsB82,refsB83,refsB84,refsB85,refsB86,refsB87,refsB88,refsB89,refsB90,refsB91]
def refs (i : Nat) : Nat := (refsTable[i/32]!)[i%32]!
private def tagMaskB0 : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,13194139533312,52776558133248,211106232532992,844424930131968,3377699720527872,13510798882111488,54043195528445952,216172782113783808,864691128455135232]
private def tagMaskTable : Array (Array Nat) := #[tagMaskB0]
def tagMask (i : Nat) : Nat := (tagMaskTable[i/32]!)[i%32]!
def pop4 : Array Nat := #[0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
def pop24 (x : Nat) : Nat :=
  pop4[x%16]!+pop4[(x>>>4)%16]!+pop4[(x>>>8)%16]!+pop4[(x>>>12)%16]!+
  pop4[(x>>>16)%16]!+pop4[(x>>>20)%16]!

def pickRef (i t : Nat) : Option Nat :=
  let z := refs i
  if z.testBit t then some ((z >>> (24+20*pop24 (z % (2^t)))) % 2^20) else none

def mask (i : Nat) := rm[nodes i % 64]!
def one (i : Nat) := banks ((nodes i >>> 6)%2048)
def two (i : Nat) := banks ((nodes i >>> 17)%2048)
def wt (i : Nat) := nodes i >>> 28
def classOf (i : Nat) := Fin.ofNat 48 (nodes i%64)
def sw (i : Nat) (q : Fin 12) (b : Bool) : Nat :=
  (((next (classOf i) q b).map (fun j => weight[j.val]!)).getD 1)
def homogeneous (m : Nat) : Bool :=
  let k := lab[m.log2]!
  m &&& tagMask k == m

def present (m : Nat) : Nat :=
  (List.range 22).foldl (fun n k => if m &&& tagMask k != 0 then n+1 else n) 0

def apart (a b : Nat) := a ^^^ (a &&& b)

def baseScore (s a b raw : Nat) : Nat :=
  if homogeneous (s &&& a) && homogeneous (s &&& b) then raw else
  min (present s) (min (1 + present (apart s a))
    (min (1 + present (apart s b)) (2 + present (apart (apart s a) b))))

def fits (rotated a b : Nat) : Bool :=
  homogeneous rotated || rotated &&& a == rotated || rotated &&& b == rotated

def dirMask (q : Fin 12) (b : Bool) : Nat := if b then cols[q.val]! else (2^60-1) ^^^ cols[q.val]!
def sideScore (i : Nat) (q : Fin 12) (b : Bool) : Nat :=
  let s := mask i &&& dirMask q b
  match pickRef i (2*q.val+b.toNat) with
  | none => max 1 (baseScore s (one i) (two i) (sw i q b))
  | some h =>
    let j := h%4096
    let o := h/4096
    if j < 2919 && o < 144 && permute o s == mask j &&
       fits (permute o (s &&& one i)) (one j) (two j) &&
       fits (permute o (s &&& two i)) (one j) (two j)
    then wt j else 0

def nodeOK (i : Nat) : Bool :=
  let s := mask i
  !homogeneous s && s &&& one i != s && s &&& two i != s &&
    (List.range 12).all (fun v => decide (wt i ≤ sideScore i (Fin.ofNat 12 v) false + sideScore i (Fin.ofNat 12 v) true))

def panel (beginAt count : Nat) : Bool :=
  (List.range count).all (fun j => nodeOK (beginAt+j))

open PCX150.SmallChart PCX150.Bands
open PCX150.Sparse (TestTree Triple Valid box leaves)
namespace Local

theorem labSame (r : Sample) : geo.tag r = Scoring.label r := rfl
theorem labelSame : geo.tag = Scoring.label := funext labSame
theorem tagSame : ∀ k : Fin 22, tagMask k.val = Scoring.tags[k.val]! := by decide +kernel

theorem numSame (m : Nat) : present m = Scoring.present m := by
  have go (xs : List Nat) (n : Nat) (sub : ∀ i ∈ xs,i<22) :
    xs.foldl (fun v k => if m &&& tagMask k != 0 then v+1 else v) n =
    xs.foldl (fun v k => if m &&& Scoring.tags[k]! != 0 then v+1 else v) n := by
    induction xs generalizing n with
    | nil => rfl
    | cons k xs ih =>
      simp only [List.foldl_cons]
      rw [show tagMask k = Scoring.tags[k]! from tagSame ⟨k,sub k (by simp)⟩]
      exact ih _ (fun i h => sub i (by simp [h]))
  exact go (List.range 22) 0 (fun _ h => List.mem_range.mp h)

theorem subsetIf {s u : Nat} (h : s &&& u = s) : bits s ⊆ bits u := by
  intro p hp
  have e := congrArg (fun m : Nat => m.testBit p.val) h
  change s.testBit p.val = true at hp
  change u.testBit p.val = true
  simpa [Nat.testBit_and,hp] using e

theorem useAnd (s t : Nat) (r : Sample) :
    r ∈ bits (s &&& t) ↔ r ∈ bits s ∧ r ∈ bits t := by
  change (s &&& t).testBit r.val = true ↔ _
  rw [Nat.testBit_and,Bool.and_eq_true]
  rfl

theorem subsetBack {s a : Nat} (range : s < 2^60) (h : bits s ⊆ bits a) : s &&& a = s := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases sm : i<60
  · cases v : s.testBit i
    · simp
    · have w : a.testBit i = true := h (show (⟨i,sm⟩ : Sample) ∈ bits s from v)
      simp [w]
  · have hn : 60 ≤ i := Nat.le_of_not_gt sm
    have small := Nat.testBit_lt_two_pow (lt_of_lt_of_le range (Nat.pow_le_pow_right (by decide : 0 < 2) hn))
    simp [small]

theorem rangeGen (g : G) (m : Nat) : quickGen g.val m < 2^60 := by
  rw [genAsRoll]
  have bs : ∀ (i : G), ∀ p ∈ parts i, p.destination < 2^60 := by decide +kernel
  have eachPart (xs : List Part) (h : ∀ p ∈ xs,p.destination<2^60) : roll xs m < 2^60 := by
    induction xs with
    | nil => decide
    | cons p ps ih =>
      apply Nat.or_lt_two_pow
      · exact lt_of_le_of_lt (Nat.and_le_left (x := p.destination)) (h _ (by simp))
      · exact ih (fun y hy => h _ (by simp [hy]))
  exact eachPart _ (bs g)

theorem rangePerm (o : ID) (s : Nat) (range : s<2^60) : permute o.val s < 2^60 := by
  have go (w d : Nat) (ok : ∀ k<d, (w >>> (3*k))%8≤5) : useWord w d s<2^60 := by
    induction d with
    | zero => exact range
    | succ d ih =>
      simp only [useWord]
      split
      · exact ih (fun k h => ok k (by omega))
      · rename_i h
        let t := ((w >>> (3*d))%8)-1
        have lim := ok d (by omega)
        have small : t<5 := by dsimp [t]; omega
        have z := rangeGen (⟨t,small⟩ : G) (useWord w d s)
        exact z
  exact go _ _ (fun k h => digits o ⟨k,h⟩)

theorem homTag {m : Nat} (range : m<2^60) (h : homogeneous m = true) : plain geo (bits m) := by
  have lo : m.log2 < 60 := by
    by_cases z : m=0
    · simp [z]
    · exact (Nat.log2_lt z).mpr range
  have small : ∀ r : Sample, lab[r.val]! < 22 := by decide +kernel
  let k : Tag := ⟨lab[m.log2]!,small ⟨m.log2,lo⟩⟩
  have sub : bits m ⊆ bits (tagMask k.val) := subsetIf (eq_of_beq h)
  refine ⟨k,?_⟩
  intro p hp
  have be := sub hp
  change (tagMask k.val).testBit p.val = true at be
  rw [tagSame k,Scoring.tagBits] at be
  exact of_decide_eq_true be

theorem admits {m a b : Nat} (range : m<2^60) (h : fits m a b = true) :
    ∃ j, bits m ⊆ box geo.tag (bits a) (bits b) j := by
  unfold fits at h
  simp only [Bool.or_eq_true,beq_iff_eq] at h
  rcases h with (hom | sub) | sub
  · obtain ⟨i,hi⟩ := homTag range hom
    exact ⟨Sum.inl i,fun p hp => hi p hp⟩
  · exact ⟨Sum.inr 0,by simpa [box] using subsetIf sub⟩
  · exact ⟨Sum.inr 1,by simpa [box] using subsetIf sub⟩

def triple (s a b : Nat) : Triple := ⟨bits s,bits a,bits b⟩

theorem embedded {s a b m u v : Nat} (o : ID) (range : s < 2^60)
    (eq : permute o.val s = m)
    (f : fits (permute o.val (s &&& a)) u v = true)
    (g : fits (permute o.val (s &&& b)) u v = true) :
    Nonempty (Sparse.Embed geo (triple m u v) (triple s a b)) := by
  have eqSet : bits m = acted (orient o) (bits s) := by rw [←eq,actionSet]
  obtain ⟨i,hi⟩ := admits (rangePerm o _ (lt_of_le_of_lt Nat.and_le_left range)) f
  obtain ⟨j,hj⟩ := admits (rangePerm o _ (lt_of_le_of_lt Nat.and_le_left range)) g
  refine ⟨⟨orient o,eqSet.subset,?_⟩⟩
  intro k
  cases k with
  | inl l =>
    refine ⟨Sum.inl ((orient o).a l),?_⟩
    intro p _ h
    have z := (orient o).label ((orient o).s.symm p)
    change geo.tag ((orient o).s.symm p) = l at h
    change geo.tag p = (orient o).a l
    simpa [h] using z
  | inr k =>
    fin_cases k
    · refine ⟨i,?_⟩
      intro p hp h
      apply hi
      rw [actionSet]
      apply (useAnd _ _ _).2
      exact ⟨eqSet.subset hp,by simpa [box,triple] using h⟩
    · refine ⟨j,?_⟩
      intro p hp h
      apply hj
      rw [actionSet]
      apply (useAnd _ _ _).2
      exact ⟨eqSet.subset hp,by simpa [box,triple] using h⟩


def treeRaw : TestTree → SmallChart.Tree
  | .leaf => .leaf
  | .cut q l r => .node q (treeRaw l) (treeRaw r)
theorem rawLeaves (t : TestTree) : SmallChart.leaves (treeRaw t) = Sparse.leaves t := by
  induction t with
  | leaf => rfl
  | cut q t u ht hu => simp [treeRaw,SmallChart.leaves,Sparse.leaves,ht,hu]

theorem positive (t : TestTree) : 1 ≤ Sparse.leaves t := by
  rw [←rawLeaves]
  exact SmallChart.leafPos _

theorem rawIf (s : Set Sample) (term : Sparse.Box → Set Sample) (t : TestTree)
    (v : Valid geo.val term t s) (plainHere : ∀ i, ∃ j, ∀ p ∈ s, p ∈ term i → geo.tag p=j) :
    SmallChart.rawValid geo (treeRaw t) s := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,hi⟩ := v
    obtain ⟨j,hj⟩ := plainHere i
    exact ⟨j,fun p hp => hj p hp (hi hp)⟩
  | cut q l r hl hr =>
    exact ⟨hl _ v.1 (fun i => (plainHere i).imp (fun j hj p hp => hj p hp.1)),
      hr _ v.2 (fun i => (plainHere i).imp (fun j hj p hp => hj p hp.1))⟩

theorem rawAfter (s a b : Nat) (range : s < 2^60) (t : TestTree)
    (v : Sparse.admissible geo (triple s a b) t)
    (ha : homogeneous (s &&& a) = true) (hb : homogeneous (s &&& b) = true) :
    SmallChart.rawValid geo (treeRaw t) (bits s) := by
  apply rawIf (bits s) (box geo.tag (bits a) (bits b)) t v
  intro h
  cases h with
  | inl i => exact ⟨i,fun _ _ z => z⟩
  | inr i =>
    fin_cases i
    · obtain ⟨j,hj⟩ := homTag (lt_of_le_of_lt Nat.and_le_left range) ha
      exact ⟨j,fun r hr z => hj r ((useAnd _ _ _).2 ⟨hr,by simpa [box] using z⟩)⟩
    · obtain ⟨j,hj⟩ := homTag (lt_of_le_of_lt Nat.and_le_left range) hb
      exact ⟨j,fun r hr z => hj r ((useAnd _ _ _).2 ⟨hr,by simpa [box] using z⟩)⟩

theorem scorePaid (s a b raw : Nat) (range : s<2^60) (t : TestTree)
    (v : Sparse.admissible geo (triple s a b) t)
    (paid : SmallChart.rawValid geo (treeRaw t) (bits s) → raw ≤ Sparse.leaves t) :
    max 1 (baseScore s a b raw) ≤ Sparse.leaves t := by
  apply max_le (positive t)
  unfold baseScore
  split
  · rename_i h
    have u := Bool.and_eq_true_iff.mp h
    exact paid (rawAfter s a b range t v u.1 u.2)
  · have vs : Valid geo.val (box Scoring.label (Scoring.bitset a) (Scoring.bitset b)) t (Scoring.bitset s) := by
      have bset (x : Nat) : bits x = Scoring.bitset x := rfl
      simpa only [Sparse.admissible,triple,labelSame,bset] using v
    have h := Scoring.numericalLeafCover geo.val s a b t vs
    have sameApart (x y : Nat) : apart x y = Scoring.apart x y := rfl
    simpa only [numSame,sameApart,Scoring.basic] using h

abbrev NodeID := Fin 2919
theorem rankOK : ∀ i : NodeID, nodes i.val % 64 < 48 := by decide +kernel
theorem maskEq (i : NodeID) : Chart48.node (classOf i.val) = bits (mask i.val) := by
  change bits (rm[(nodes i.val %64)%48]!) = bits (rm[nodes i.val%64]!)
  rw [Nat.mod_eq_of_lt (rankOK i)]
theorem maskRange (i : NodeID) : mask i.val < 2^60 := by
  have h : ∀ k : Key, rm[k.val]! < 2^60 := by decide +kernel
  exact h ⟨_,rankOK i⟩
theorem dirBit : ∀ q b (r : Sample), (dirMask q b).testBit r.val = decide (geo.val r q = b) := by decide +kernel

theorem branchBits (s : Nat) (q : Var) (b : Bool) :
    SmallChart.branch geo (bits s) q b = bits (s &&& dirMask q b) := by
  ext r
  rw [useAnd]
  change (_ ∧ geo.val r q=b) ↔ (_ ∧ (dirMask q b).testBit r.val=true)
  rw [dirBit,decide_eq_true_eq]

theorem rawHalf (i : NodeID) (q : Var) (b : Bool) (t : TestTree)
    (v : SmallChart.rawValid geo (treeRaw t) (bits (mask i.val &&& dirMask q b))) :
    sw i.val q b ≤ Sparse.leaves t := by
  let k := classOf i.val
  have square := chart.proper k q b
  have eq : SmallChart.branch geo (chart.state k) q b = bits (mask i.val &&& dirMask q b) :=
    (congrArg (fun s => SmallChart.branch geo s q b) (maskEq i)).trans (branchBits _ _ _)
  rw [←eq] at v
  change (match Chart48.next k q b with | none => _ | some j => _) at square
  unfold sw
  change ((Chart48.next k q b).map _).getD 1 ≤ _
  cases track : Chart48.next k q b with
  | none => exact positive t
  | some j =>
    rw [track] at square
    obtain ⟨f,hf⟩ := square
    rw [hf] at v
    have w := SmallChart.rawLower chart (treeRaw t) j f v
    change Chart48.chart.wt j ≤ Sparse.leaves t
    simpa only [rawLeaves] using w

def item (i : NodeID) := triple (mask i.val) (one i.val) (two i.val)
theorem noLeaf (i : NodeID) (h : nodeOK i.val = true) :
    Sparse.admissible geo (item i) .leaf → wt i.val ≤ 1 := by
  intro v
  obtain ⟨u,hu⟩ := v
  unfold nodeOK at h
  simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne] at h
  cases u with
  | inl j =>
    exfalso
    apply chart.rich (classOf i.val)
    rw [show chart.state (classOf i.val) = bits (mask i.val) from maskEq i]
    exact ⟨j,fun p hp => hu hp⟩
  | inr j =>
    fin_cases j
    · exact False.elim (h.1.1.2 (subsetBack (maskRange i) (by simpa [box,item,triple] using hu)))
    · exact False.elim (h.1.2 (subsetBack (maskRange i) (by simpa [box,item,triple] using hu)))

theorem pivotPay (i : NodeID) (q : Var) (h : nodeOK i.val = true) :
    wt i.val ≤ sideScore i.val q false + sideScore i.val q true := by
  have all := (Bool.and_eq_true_iff.mp h).2
  have pick := List.all_eq_true.mp all q.val (List.mem_range.mpr q.isLt)
  have eq : Fin.ofNat 12 q.val = q := Fin.ext (Nat.mod_eq_of_lt q.isLt)
  simpa only [eq,decide_eq_true_eq] using pick

theorem childPay (i : NodeID) (q : Var) (b : Bool) :
    let s := Sparse.restricted geo (item i) q b
    (∀ t, Sparse.admissible geo s t → sideScore i.val q b ≤ Sparse.leaves t) ∨
    ∃ j : NodeID, Nonempty (Sparse.Embed geo (item j) s) ∧ sideScore i.val q b ≤ wt j.val := by
  dsimp only
  let s := mask i.val &&& dirMask q b
  have r : s<2^60 := lt_of_le_of_lt Nat.and_le_left (maskRange i)
  have eq : Sparse.restricted geo (item i) q b = triple s (one i.val) (two i.val) := by
    change Sparse.Triple.mk (SmallChart.branch geo (bits (mask i.val)) q b) _ _ = _
    rw [branchBits]; rfl
  rw [eq]
  cases h : pickRef i.val (2*q.val+b.toNat) with
  | none =>
    left
    intro t v
    simpa only [sideScore,h] using scorePaid _ _ _ _ r t v (rawHalf i q b t)
  | some w =>
    let j := w%4096
    let o := w/4096
    let okay : Bool := j < 2919 && o < 144 && permute o s == mask j &&
       fits (permute o (s &&& one i.val)) (one j) (two j) &&
       fits (permute o (s &&& two i.val)) (one j) (two j)
    by_cases hg : okay = true
    · have pack := hg
      unfold okay at pack
      simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at pack
      obtain ⟨⟨⟨⟨jt,ot⟩,same⟩,f⟩,g⟩ := pack
      right
      refine ⟨⟨j,jt⟩,embedded ⟨o,ot⟩ r same f g,?_⟩
      simp only [sideScore,h]
      change (if okay = true then wt j else 0) ≤ wt j
      rw [if_pos hg]
    · left
      intro t v
      simp only [sideScore,h]
      change (if okay = true then wt j else 0) ≤ Sparse.leaves t
      rw [if_neg hg]
      exact Nat.zero_le _

theorem bankSound (checks : ∀ i : NodeID, nodeOK i.val = true) (i : NodeID) (t : TestTree)
    (valid : Sparse.admissible geo (item i) t) : wt i.val ≤ Sparse.leaves t := by
  let rule : Sparse.Rule geo NodeID :=
    {item := item, weight := fun i => wt i.val, base := fun i => noLeaf i (checks i),
     kw := fun i q b => sideScore i.val q b, fork := fun i q => pivotPay i q (checks i), child := childPay}
  exact Sparse.soundRules rule t i valid

end Local
end PCX150.Scalar

namespace PCX150.Scalar
open PCX150.Chart48 PCX150.SmallChart
def full : Nat := 2^60-1
def len : Nat := 7056
def big : Nat := 2^7056-1
def R (a : Nat) := if a=0 then 0 else rm[a-1]!
def weightR (a : Nat) := if a=0 then 0 else weight[a-1]!
private def testMaskB0 : Array Nat := #[51539607552,52776558133248,844424930131968,805306368,50331648,54043195528445952,216172782113783808,864691128455135232,3221225472,3377699720527872,13510798882111488,211106232532992,12884901888,824633720832,201326592,206158430208,3298534883328,13194139533312,8804687151104,3231711232,844424930131973,54043195528446000,13194139533324,18014536082653200,201326612,36029346808332320,50331688,52776558134016,211106232582144,52776566784000,144117387132667904,824633794560]
private def testMaskB1 : Array Nat := #[216172782116405248,72062026444701696,51540393984,288239180838862848,51539619840,13194144251904,36099170059157504,54043195529756672,2260595927678984,9007199338660352,16515072,3231711235,54043195529756720,63,18033107387289600,577586723085615106,5629576843624578,52776566784768,12890144960,206158431378,805389568,18032007875658000,211106235727872,844424930132293,824633794593,288230926478016544,216172782116408320,9042383710749184,258048,4032,3377699720548362,51540406272]
private def testMaskB2 : Array Nat := #[13510798882153088,13194144251916,201490452,90072130120582160,9574547321815044,864691128467914752,3298535020608,576495938831516160,585503138086126080,50334248,72062164420527104,5629578991108226,72339378252816385,36099170059173984,144255926707193856,580542408179972,2278188361203976,162131785742944272,288239180838928520,578747736514363912,9147937835745792,72062542377714688,594477487409463312,576463022202159106,4508100753629312,38350970141294592,584940521521412,1127016598605890,576495938831516162,297246371520446984,576498137988988928,288239310224819200]
private def testMaskB3 : Array Nat := #[38913915799748864,36029351641284640,293859952999530626,37437275710165056,3386573127155850,864693877267957792,281788510904385,4516836721303680,1178695800983554,9715284812791812,72062542377714724,54043883260150832,1127087465304258,54045394719606832,720578139570440240,288239722055139368,144399962663290945,36099716325392416,594477487409466384,216173332440091680,13546054129549954,11470105317786120,576460960752074770,19140521754890258,492586581098561,594527927514038288,9622925833437956,3449172272369728,72062129725244436,3395309355159808,13515231356035076,144258124791056384]
private def testMaskB4 : Array Nat := #[324259735816699936,18035306544893968,900722674286921760,2845536361136396,12420085520007690,576498135891839488,14671954036392578,38350969923190824,866986908763292168,1179795312611330,126101477298078768,14078181309456388,18594958030405908,2898312919269644,198160582795462704,3166598052462912,288239730645073960,90072181660976144,90072182063629328,36102468627597408,791648707592452,778454568059140,234189517219826704,9055577850282508,9161130966549004,11478901410808328,1408481911377987,1408494796279875,19141621266518034,577590021620633602,492861459005505,594528064952991760]
private def testMaskB5 : Array Nat := #[594530126537293840,9627323879949060,1178764520460290,144258125864798208,153263124938525184,2313372750070536,2374945401225992,76561709061907584,76565832230511744,72624977203430660,144258124824610816,72058591007810560,585503136156910080,288239387534230656,360301302309782528,360301714626642944,324259735850254368,2330977826258952,493960970633281,4517180318687360,4503946456473731,4516836721303692,4785397800378561,4785384918098113,18035443983847440,584992061915396,38913915799748908,54131156728430896,914798238777669,38350970141294952,720578142802151424,36382569181216865]
private def testMaskB6 : Array Nat := #[11302979562947080,9020393482912268,576498138039323136,296120548906238090,38350970191626280,9768061368304388,2330964941357832,875994108018033160,2322173139108680,290490972868003080,4503989395660931,36099716325393696,954763259112784912,72058453568857121,414331853449790512,288239859980633144,216173332442713120,324259723502226464,18594958298841364,90072181526770704,2902710967091468,2915905105314060,2827944179810572,77410325880119301,9196315338637836,1044837862362777632,39195395071426880,72062129725408276,72062164621853716,288239731181944872,90072182197847056,56945906495537408]
private def testMaskB7 : Array Nat := #[144540975029553217,577589952901158978,36103018383411296,588880837823431178,36099720653914144,796046754103556,292743673819504768,810650269523250192,540432505610767392,292734809007005857,594477487418117136,304001779551437448,9183124430815744,144258125697026081,9147937902854669,864691266577957904,220958167031881729,1179864032088066,11514085782897160,3449172272369738,594530263976247312,5629579003703426,5629630530728066,577625205992722434,13546054129590914,1408499091247171,1408477626896451,86135775347384324,3412886265287178,576498344147419154,72624942843774212,282854738112577]
private def testMaskB8 : Array Nat := #[282906274574401,9622925842088708,9715284812792580,1127081028096194,1127100350206146,18032145448965392,864693877280540704,3386573127176330,19159213452562450,2383741494248200,20003432224264512,2304576665699080,153263126012267008,36032099883554912,180357840143124512,72624977270539524,18594940850700564,18032146254136592,144258950330583073,144258125898352640,144258124791056404,154107550892064773,870320707458826370,54043883261461552,360288657926063152,11470105320931848,72062164420600852,290490981474713608,55451691399778368,585503138304393728,585503138103067146,585503136140132884]
private def testMaskB9 : Array Nat := #[225888066926575620,288239937290044544,324259736387125280,364791613308347520,180425465476941921,44059951366794,595601070190104594,89082186453312,4516905440780430,4517111599210637,3166598052462925,590006806433145474,2330977809482184,585503136156910108,9992362816209733,576498135891839544,14078181309457284,288239387534230682,288231141197022386,324259736353572064,873742308204577288,576496145124165266,290490972884780808,2898312925036812,144258125864798229,492861459062849,9763663332541188,72062164085154836,791648711000324,38350965896661800,252202129462725664,216454567404514369]
private def testMaskB10 : Array Nat := #[9183124414038535,288239722592013864,55170216423067762,5629628388225154,936748860616410128,18877532317421909,1408494807027779,579873638568841738,18032129074480400,594528064952993552,90072182063707152,19141621266519250,153263124938525228,72624977203520772,577590021620635842,630506147032729648,18035306544896336,18594941119152404,18017851797806160,360301302309782556,342274259417367600,291616949278953610,144258124824610868,585503138287616534,180357290387490848,595653846748237842,11874725932352268,13656244798136325,364791819466777728,180426290110662753,180428764011825249,326590700467601448]
private def testMaskB11 : Array Nat := #[13554858833478282,3421759671894666,864735188406502026,595601276348534802,933507116585280,3466781906981184,54132277714899264,90657070374454548,90657070978434324,180636571709474913,364792437942068352,364804807447880832,4503989410865283,4517180318687375,292743673819504811,4785397808242881,1044837862378506272,2915905111343372,56945906495537468,39195395071426925,9196315353842188,9183124430815759,585503138304393758,9768061379576580,2383741508141832,576498138039323194,2330977826259912,414331853455819824,76566107108418711,288239937290044602,77410325880120773,144258950330820641]
private def testMaskB12 : Array Nat := #[180357840143370272,86135775347386244,290490981474715528,774621335110682672,158048475376822977,796046758035716,154107550892067653,38350970191629160,72624977270662404,870320707459035266,810650269534522384,540432505618631712,954763259126154256,220958167031884993,324259736387128544,36099720653917536,576498344147422866,288239731181948584,225888066926579460,144540975029729345,594530263976251152,11514085798625800,1408499103043651,36382569181311073,39759444268044395,55451691399778419,5629630544097410,1127100364099778,584992061976836,18594958299025684,21972657818063134,20003432224264535]
private def testMaskB13 : Array Nat := #[72062164622091284,588880837823615498,591132706339992194,282906278506561,1179864032089026,90072182198055952,18032146254353680,19159213452563922,153263126012267053,36103018383628384,493960970694721,720578142802151475,875994108018278920,577625205992725186,304001779551560328,144258125898352693,360301852065596476,18035443983850832,72062989054321717,296120548906332298,14500669728268293,7116327023042761,595654052906668050,329045085298696417,326590700467601640,7331586756862348,90657122518041876,12085832164885260,11887920071885580,596779727612953368,604098076789342996,363115914906387724]
private def testMaskB14 : Array Nat := #[864693956737435810,308523101002745112,217162652959940613,229829026911920133,108724658363778340,108368729860547681,364792644100498560,864691346034853010,653022188777645202,54131844460135728,369308364209489420,657565265664050708,864735247059846680,180429588645546081,95701749780460690,725082085859141763,436849998192257185,162853065440266516,180918041653070116,54133355919591728,919505523466565,326590688438337576,326590700517933096,326590701272907816,864737857762429480,13524036059964044,216175429024361489,216320254314974228,216173642754108449,216318468044721188,1080866797491784752,918737210906446896]
private def testMaskB15 : Array Nat := #[270218864565095472,1055536870113605,878245987288613514,868112888127029898,54045004247929968,933507116585285,1003872439275845,867841092628805,11751585666351689,6214559980073350,3404182761787786,13687067571692163,13550486603473542,13660617028182665,10591598742114883,3484358817108554,10748845076288262,3430495899898634,307370907037668498,5912472380780739,3458045678997706,162414378487257169,613618754249693282,54046515707385968,191614090449308200,90657121914062100,721986617029564483,325386803954651362,614849101335513640,441502846876224040,364805013606311040,364805632081601664]
private def testMaskB16 : Array Nat := #[230673451842052101,326590701323239464,881623687009141386,12099026304418572,364805838240031872,90657122719368468,180640694878079073,729761264001255936,1134909993020230704,595657351441551378,5912485265682627,58354402365559104,14500669728269253,364805013606311070,364805632081601709,364792644100498611,729761263799929387,326590701272909288,729761263950924311,729761260780030524,878245987288851082,217162652959944005,229829026911923845,5912482050486467,5912472392052931,4311206837113167,54976702645031285,57509977435427194,16932558554067594,90657122518136084,90657121914238228,1080866797506989104]
private def testMaskB17 : Array Nat := #[918737210920340528,270218864569027632,12085832176681740,12046249754149644,11887920085254924,868112888127246986,595654052906669970,180429588645754977,180639870244542561,180637396343318625,595604574883421394,331376049949597929,479853812454115880,13559291307401870,606349876888257308,12314535955317581,381148043041129756,941252574060422290,401102714233758945,399215630426391852,126756786498520372,344622816522749240,367619557483439500,373812006786541196,864735326516741786,676160206313260820,473160274483947745,181199521998489957,768112226156595752,191895570794728041,734265206974360195,864737937219324586]
private def testMaskB18 : Array Nat := #[748356201378908948,192177040738274092,216320564626369557,216318778356116517,90939971078993237,252483919045799009,508907627127319713,864694094847478962,234915194964184340,903088823340321320,54134043651296560,1060244154802501,864737995872472632,1018000982583511592,8243395160993995,330172153436647651,327717768605552874,13695872275620491,938214401274181,1008579723964741,1074245747921221,372123114245048076,13691500045574791,13665049502065293,597905646847152922,15095541966877379,3493232223736522,13000645175202574,3501968451720010,3439369306526602,605223996023542550,383932135063237778]
private def testMaskB19 : Array Nat := #[672162504374105234,883831661631313042,95984599146706131,54132965446604144,96286689966437782,216175979350666289,740001032853395539,758015418378098787,198443179835791473,631633170073524338,726490560254326979,16338786095522700,216320804641279028,54134476906060144,731169738144782915,6497409346318791,801823390253616660,3475655313609162,54047203439090800,7683709651673549,16264264858788553,109006446873109861,945804438466692636,662068970518128278,885019037837772568,1013313020394416291,198952231506463028,446006731045186217,632881092433955640,797139851830504595,252980584030784804,513564839565168172]
private def testMaskB20 : Array Nat := #[126384382500746353,8475164749361550,12913771612787275,11172158128821063,15256945829917574,343401357620090098,901849757470890210,309649095398872474,163135658182220117,615976107196439146,234472419202317393,12099026320933644,364805838240031935,729761264001255999,1134909993036745776,230673451842056133,326590701323243496,5912485282197699,58354402365559167,90657122719626516,180640694878337121,881623687009399434,595657351441555410,13700304749503119,417247758561133884,376626756822099852,1056351948161403432,192458521083693933,545217903419010273,864738075329367738,820418330902826772,332503118087549163]
private def testMaskB21 : Array Nat := #[1078953032610117,3510841858347978,960392889656882322,96569539332683223,607475796122456862,776029834201929843,216321114952674357,735673681369545411,54135164637764976,16831647554528205,404001027153028589,950308151910704798,966651179198039836,1022504937619434155,484639175894756073,786707167275567932,1085370786902650035,271014911323131188,253262373613858149,1090063112845626940,806327371059342999,518068758093868717,552478755364917036,921120952414588728,8828387155800527,17426519524700875,13494331267928911,17517550615982990,15680533760357319,420244335500276979,127039691699352949,386777671424374174]
private def testMaskB22 : Array Nat := #[345749914725471738,681789828254054294,886145034381383578,1050750296104581347,199234828543383925,769520708067973739,904215906510658282,749764696175188823,634008115474750330,270501770843602033,816562741915303123,919864311270546674,235198096943791445,1094567102241287871,1147009019341164348,557264153165295597,18011511586616271,423160240605591039,972280809728767902,1062264381887478507,788115666366815103,1140822478302428403,271297817597705589,826330803283607511,922248052764794874,1152921504606846975]
private def testMaskTable : Array (Array Nat) := #[testMaskB0,testMaskB1,testMaskB2,testMaskB3,testMaskB4,testMaskB5,testMaskB6,testMaskB7,testMaskB8,testMaskB9,testMaskB10,testMaskB11,testMaskB12,testMaskB13,testMaskB14,testMaskB15,testMaskB16,testMaskB17,testMaskB18,testMaskB19,testMaskB20,testMaskB21,testMaskB22]
def testMask (i : Nat) : Nat := (testMaskTable[i/32]!)[i%32]!
private def staticFlagsB0 : Array Nat := #[544777605266688,457456971942092,557533999661056,559252338966528,422229644935168,427436456411136,368202968708352,544165919735808,380435318177792,547561085600256,422212465065984,422212465065984,281492156579840,544786009833488,383321888587776,548729316704768,427436219039744,422229644935168,299084342624256,557566757175312,383594252439842,548762074228736,559557198741536,475040567003272,545362330779648,422212465065984,548729316704256,422229644935168,378236563357696,422212465065984,531169888185344,457448380958924]
private def staticFlagsB1 : Array Nat := #[366002066395426,541965013237792,281492156579840,539974571671568,457439792595136,422212465065984,544777586655248,427436386942976,281492293071872,422229644935168,557529704693760,559247960047616,299067162755072,474989023199744,383317593620480,548725021737472,368821385082112,381603549282304,281492160774340,383321888587776,544784403415040,548729316704768,281492156579840,286698968055808,423311976693760,423311976693760,427435145297920,422229649129472]
private def staticFlagsTable : Array (Array Nat) := #[staticFlagsB0,staticFlagsB1]
def staticFlags (i : Nat) : Nat := (staticFlagsTable[i/32]!)[i%32]!
private def oveB0 : Array Nat := #[21794070892,31457747312,1929847153,38437069172,49174487436,8372298134,26625909113,44342649213,31994618241,16425361796,6761685383,1392976295,5151072674,14277878190,319234455,2466718109,41121423791,57764422066,81962,81965,81980,81981,22302634193,9954603242,290926775,6733377728,1364668661,2438410498,9417732294,7270248703,8880861445,71723063661]
private def oveB1 : Array Nat := #[61522516341,64743741829,32531487119,29310261659,28745085165,13712699674,8909166971,7298554238,21257197955,18572843398,9446037921,3003586995,37334237261,9416949839,54514106450,7269466203,37871108188,45416386930,22330937727,15888486786,4614197640,35752710544,23941550488,12130390431,50785096101,19692186251,364833420,2512317069,36872055438,5196671631,4659800720,36335184529]
private def oveB2 : Array Nat := #[3049187986,15934089875,5733542548,16470960789,901704342,13204132207,47026999672,33068355968,36289581454,856101267,19646583188,66891223460,20691107916,21227978833,27670429780,73304457301,10519777646,26089034099,23404679542,4077326711,54006321530,3540455804,65280610697,13741003146,28773388683,53469450637,19109712273,36826452370,15351615893,60985643417,30920872346,65817481628]
private def oveB3 : Array Nat := #[40584548766,9982906784,49711354275,14814744998,11593519528,29847130537,73870545322,44879516075,51321967020,5687939501,27162775984,50248225201,15866738739,378061481,13799834283,28832219821,29905961647,2525545148,14873576125,5666191433,18631672497,29369090751,4136157892,47085830853,10041737930,3062416075,14792996926,9961158720,834353218,8965112481,22389768886,9504866999]
private def oveB4 : Array Nat := #[13262963390,4055578667,29288511532,32509737015,4592449592,21772318778,13182384193,51375043115,8962241081,73923621442,8425370181,50838172248,81935,8350545969,1908095026,297482292,17477351478,6203062335,35194091589,2444965958,29363335725,15941562927,25068368433,25605239356,22384013898,909177422,60501848658,19146269305,26125591166,1429529217,2503271043,3040141957]
private def oveB5 : Array Nat := #[1985790620,912048804,5207016102,81924,81929,81930,81934,13794075184,50301297228,47080071761,16478429794,49227555430,30973944425,22367494783,8428241566,4670145183,81920,81921,81922,81923,81925,81926,81927,81928,81931,81932,81933,81936,81937,10036240849,3056919023,13796946583]
private def oveB6 : Array Nat := #[13260075672,375173785,17555042970,5743882907,16481301149,18091913888,6280753826,15944430243,4133270181,2522657447,3059528360,37546,37548,37550,37552,37554,37555,37556,37557,37560,37561,37562,37563,37568,37569,37570,37571,37574,37575,37576,37577,37580]
private def oveB7 : Array Nat := #[25293,25294,25295,25296,25297,25298,25299,25300,25301,25302,25303,25304,729,63133131122,291447158,291578239,47539364222,29310263707,51296149883,299966850,856234417,319234455,291838354,5145827694,53443633539,47538053525,23913767328,291707268,71173607836,51297460653,32531487119,12130394527]
private def oveB8 : Array Nat := #[317133164,297480234,297480237,297480252,297480253,49711358371,15323312317,69045653928,23922286993,5126689162,306254217,51315673456,18084465016,75494918521,20190398886,291055813,23941554584,3516725798,290926775,2982883535,39496645160,355793523,33113959051,12175993487,36335184529,61031246478,4659800720,3049187986,23913507057,72845295996,43296293281,27199339134]
private def oveB9 : Array Nat := #[900530548,72287322542,3040148101,3041190540,36294156941,74948862611,10557383317,290795630,6761679239,8372298134,45994410397,6789071269,45940670891,901704342,18080399745,26674397616,5733542548,29847128489,23920978166,77065945477,11630082676,23912853562,291318004,32558874997,15400108427,50833588642,4662690220,71227343279,47054389682,3535208883,290664553,26089032051]
private def oveB10 : Array Nat := #[12130517382,7342981516,5736432013,856097171,23913890206,301511339,301773485,18082083503,914930362,13262961342,23924093631,10045010634,10498027593,23913246828,53444276868,33667330743,3062414027,1908092978,23928570221,73897935229,37377081736,15396045200,1985788572,4670143135,1991422630,52457812662,2528817852,4136155844,47085828805,297087020,290533425,13180547123]
private def oveB11 : Array Nat := #[43782189120,2981441601,10497634373,47557575025,36289577358,60985639321,69628654193,58874720892,7351890563,18049053342,378057385,290402347,297480244,23919407158,2981703735,21249994808,38429863998,7274967106,10497896518,6767313358,335598198,54049559161,5741269642,8965108385,40109257380,1371484194,47024373937,49708728498,360251574,14863237390,324860350,22927954476]
private def oveB12 : Array Nat := #[300339760,65867010609,56743746098,2984825416,57280617052,28826458727,34732306696,74995790147,8969310665,26686050776,14864273881,57824563676,35742472673,7358697959,32537104875,38426827255,41623,41624,41625,41626,5743880859,41629,41632,41634,41635,41637,41639,3059526312,35498,33452,35502,33456]
private def oveB13 : Array Nat := #[33457,35506,33459,33460,33461,35512,33465,33467,33469,35520,33473,33474,35523,35526,33479,35528,35529,33484,21197,21198,21199,21200,23249,21202,23251,23252,21205,23254,21207,21208,729,293413244]
private def oveB14 : Array Nat := #[293151093,38410985880,38411247997,61499580830,23918617003,65280614793,293673352,5157755284,293935523,9487061368,38411508107,38411112836,66891227556,29317206437,38410852782,293804431,16439118199,9446035873,23917963306,23917963309,23917963324,23917963325,66894367104,8403876375,66931063314,5727779355,1438575244,30918904177,29316946353,5155519101,9477878390,5148453111]
private def oveB15 : Array Nat := #[26662468230,29314710151,21839669901,3049187986,16470960789,293017967,294056570,901704342,42759422331,6798244482,56191410836,38411639186,47040758172,51863413390,74981892747,17503675027,293542270,65278640511,50833326446,29310263707,61535476367,23954512528,38410594570,38411377041,5151072674,36335184529,293273978,40097087893,70697810327,43828576690,21293759113,38410070180]
private def oveB16 : Array Nat := #[65277995254,52969142903,38410332334,62107613571,70139838854,8413313427,54599142044,51914787488,1448921753,17555049114,3059534504,292104288,3588684189,21850016414,55609206840,38410725661,5158009228,38422903322,20756888193,46009207447,11649469087,41177369251,912050852,4133276325,3577019012,3553536664,43868793499,23997493917,8965110433,6280755874,62072466086,2522659495]
private def oveB17 : Array Nat := #[62114265805,3595336401,11648400084,76010301484,291973174,38410461400,60983027961,31509246338,5691079045,39538192775,65868984717,51375305102,5687943597,19146273401,23917963316,61498927162,44394148234,30920876442,12718764454,21845569960,70698725802,40097467006,40098114217,37954562743,14876848829,64802568903,22860079170,44375931016,292366492,49764690305,34664804863,38421457535]
private def oveB18 : Array Nat := #[28835490477,70699887282,7361571529,2521594578,374110931,1447852759,23917963265,23917963271,23917963273,23917963274,23917963276,59904172052,25544433690,74399684673,24531759237,3055087759,50301561049,43833157852,13257468130,49234629063,50845241806,16485503467,22320699889,54066467316,1919605242,33451,31409,31414,33464,33465,35515,35516]
private def oveB19 : Array Nat := #[35521,35522,35523,35526,35528,35530,35531,19150,19151,21200,21205,19158,23256,729,294723952,7274045815,21794070892,41633784216,1392976295,294984066,7274437024,26625909113,7293311379,67940585842,5151072674,7274172795,41651999125,67958673802,67476588926,41652132264,7274568079,312936814]
private def oveB20 : Array Nat := #[29310263707,67940850076,7811835946,7292389795,7811835949,7811835964,7811835965,7274305958,1438575244,3049187986,305068563,66936826507,16470960789,2503277187,65326213774,54582641018,66930672017,901704342,36335184529,10019469949,23402064099,77119160703,21284585857,26662468230,2512317069,23994888833,5687943597,313983364,11109986940,65320059293,40101016182,372955791]
private def oveB21 : Array Nat := #[52960352912,21284969107,7352277652,7273654443,70697810327,65277995254,23404683638,67940067476,6810171794,10031397248,3588948377,51898284453,6798244482,41634427396,294594750,7273523265,30918256918,295106951,295238024,1387461038,41634560547,17555049114,21850016414,11649469087,41177369251,3059534504,313063791,3048012171,6200947209,13796952727,10033474226,8967992002]
private def oveB22 : Array Nat := #[11111529166,3595336401,294201388,294332559,5190908429,13189970470,1448921753,4133276325,5209895600,49697192485,3024792216,2522659495,373598894,914928314,21852895937,7352920780,45940942906,7273785509,70139834758,9473421709,41634165134,52959965609,35780096426,67941102091,14876846781,21316025030,3516868660,23918354620,3517259981,12715489616,30920876442,2998991300]
private def oveB23 : Array Nat := #[18562613703,22320710129,59974003375,42257263283,4676299448,7811835920,73321357366,11105138830,39001321685,19159239227,2516240963,64796809814,17552175713,10032695925,19146273401,26680785613,21848947408,11648400084,8427174613,7811835908,7811835914,7811835916,7811835918,7811835919,17550602403,2516502977,1919605242,39579,39580,41629,39584,41633]
private def oveB24 : Array Nat := #[41634,41636,39590,35499,35501,33460,35513,35515,33468,33475,33477,35527,35528,35530,35531,19151,23250,23251,19158,23255,23256,729,21794070892,296296860,57764422066,16425361796,5673523594,74394179991,16425490862,7285576100,3547533686,57805443467]
private def oveB25 : Array Nat := #[13209244039,16470960789,10565380756,296423846,76552802706,43282665899,74394571133,7298556286,296546850,41644128791,49756957331,363659640,49711358371,10559226271,74448568744,76045418896,364833420,36327187086,8901435437,8901435452,355793523,36335184529,73338249867,12689146240,5196671631,57796260470,59419459954,8901435434,8901435453,52980810121,68541282702,5741664914]
private def oveB26 : Array Nat := #[12166953610,76045802125,71723065709,13264278160,12727407254,44928008600,57771749920,49211046519,7285969325,295772292,74446860674,66398777748,16470831739,29369090751,73373122933,5199296943,1966404213,59421278905,66400600771,295903374,13204136303,16464802215,7335115392,60438931971,1988674226,8431125196,3540459900,53496836510,16446833339,39555232121,76554770824,16481305245]
private def oveB27 : Array Nat := #[23959872175,5672607813,59421401792,44930081480,45435089614,23926218806,53469454733,30437339535,13796952727,5209897648,49732829889,374108883,1978333388,68492663047,296034573,296165648,47617206650,6276311441,30974208433,49767301784,41626,10575725211,73393423013,2522663591,10037787350,4607516721,295641161,13237418183,32565041436,52985655891,1979630204,31519320729]
private def oveB28 : Array Nat := #[1985792668,18091913888,15944432291,13267149480,55679951539,49212990146,65868984474,20747708633,11032785412,14867821157,41631,5750956730,8427172565,1447850711,8901435395,22324645932,5204406392,7883911307,43859108058,70702653762,1453117902,37534,37537,37538,37540,39590,35497,35498,33451,35508,35509,33464]
private def oveB29 : Array Nat := #[35516,33469,33482,21197,23247,19152,21201,17106,17108,17112,729,13204136303,299966850,29310263707,2984321423,299571574,23922153864,10500381094,2983926191,23921760625,10499987835,5145827694,850860440,299700599,2984055178,299440496,5145432444,2983795093,850465183,5144777092,3534819746,297480234]
private def oveB30 : Array Nat := #[297480237,297480252,297480253,299833721,12124230051,10499598574,10500514183,23922286993,3534293402,10500114845,23921887648,298266738,298528954,850200966,298135658,356182667,3040537230,23920193634,36335184529,2983012601,12124094846,12124881279,5145166224,12125145495,907084196,4662690220,12124488113,5204533903,4659798672,909566614,26674397616,3535210931]
private def oveB31 : Array Nat := #[3041190540,301259405,356835986,10501806739,23979156116,10557383317,299182312,2983536905,43846926701,11642012018,43847582069,14863237504,3534553473,12124750227,29352067484,13245940133,25057100203,3040148101,26662468230,297742389,10498289735,298004582,54006319482,23920062542,2983141605,67469248883,5202051469,36289579406,51315933586,33062322580,850592158,3534946721]
private def oveB32 : Array Nat := #[2984182184,29351412138,36330736046,5145559474,5144904044,51316064628,74985441661,33062453635,47557968268,25056444825,54047476137,378059433,301513387,301775533,10502189743,2528817852,10502322878,23924095679,10045010634,23919669312,2981441601,36321423998,33667330743,2985867972,2986130117,10497896518,10498027593,13245284745,3534160295,849805741,1985788572,4670145183]
private def oveB33 : Array Nat := #[8965110433,1992602278,52457812662,3062414027,297087020,1908092978,297349171,23919407158,2981703735,21249994808,38429863998,1922510914,10497634373,297607242,2984442402,300474937,54038164088,2985357954,8971924132,297480244,3532990527,300214829,23922534961,21310270010,10500891196,2984825416,10501417554,67459936895,23923317377,10501673610,296693779,296824861]
private def oveB34 : Array Nat := #[47556141086,2981179424,2981308454,298918096,2982748410,2983665921,300601918,300735045,59972047434,909173326,10500758100,54049428059,301380254,297480192,296953874,51373338950,4674343359,50845241806,26686050776,5204400621,4663728631,44939661818,41623,41624,49772931737,41626,35277417115,17560677021,41632,41634,41635,41637]
private def oveB35 : Array Nat := #[41639,30982449832,37546,33452,37550,35504,33457,35506,33459,33460,35509,35512,35513,35514,35515,35517,37568,33473,35522,35523,37574,33479,35528,35529,33484,23245,21198,23247,21200,25297,23250,25299]
private def oveB36 : Array Nat := #[23252,21205,23254,21207,23256,729,302588268,37883552161,34662326695,304814448,7284136311,38420814232,34664806926,21839669901,303108482,37884072330,62608181651,302713202,5149100448,5687943597,7284265359,38420423091,7281910166,38422649244,1438575244,3049187986,33589105045,29308291451,901704342,5148971375,25544433709,34662449576]
private def oveB37 : Array Nat := #[7282430374,33590811009,30920876442,16470960789,23953471866,33588584848,36335184529,34664552846,25544433724,303753854,38420681111,19146275449,61535476367,305068563,63682960011,62609218196,62072347278,3553417875,29310263707,2503277187,23954512528,25544433725,38420943245,30918898033,62597952109,38421457535,25544433706,37883810205,5151072674,59433861816,71245021885,62071304588]
private def oveB38 : Array Nat := #[47039703676,11115479723,33590940032,34663232084,21815542469,34662584702,61534433668,37883027631,21850014366,25074123437,10041737930,34661671075,302194875,3552375205,54564668095,66889249158,65280614793,66891227556,303362605,21847143005,3586826921,62642627255,3062414027,25544433737,7281776973,5685965191,16478433890,54599139996,8970744484,62072464038,7316873910,2525543100]
private def oveB39 : Array Nat := #[23442793150,30422115012,62114263757,59904172087,37885647026,34662062354,7282164099,33588834705,54059397688,26662464134,14808064058,37884191235,21318773407,8965110433,3595334353,63724876500,15881805852,55609204767,74399684673,3048009960,51903263008,5686223401,3059532456,2521592530,374108883,8427172565,1447850711,25544433667,22860077080,23993053277,62110888057,13257466082]
private def oveB40 : Array Nat := #[21838487823,14331204073,16485503467,54066467316,916247034,37527,37528,37529,37530,37531,37533,37536,6280751778,37539,37541,2522655399,29361,29362,33465,35515,35521,33474,35523,35526,33479,33480,17102,17103,21200,17110,21208,729]
private def oveB41 : Array Nat := #[1438575244,3049187986,21839669901,5151070626,304814448,7284136311,5685842339,50798729639,870123906,5155519101,7284265359,304943496,32517323292,62071310732,65296075140,29310261659,901704342,63681923448,54019955123,21293759113,36335184529,54020475293,5151070253,5154212235,63682960011,5151070269,49188637054,16470960789,305068563,62072347278,47041153431,16438991212]
private def oveB42 : Array Nat := #[5151070268,50799249809,3577019012,39034081940,39001323889,42792178319,39570952851,47038534009,77119158655,43865920144,2503277187,65283746194,51898282405,5687941549,7284005106,3593794181,5151070250,16439511427,4676303544,43833162144,13803109035,28835494573,54582636922,66894367104,26662468230,66906679699,7284517460,14876850877,64805845703,15413721800,16439374246,304027786]
private def oveB43 : Array Nat := #[337550001,51904953023,3049700037,304552129,19699919260,3586824873,7316871862,23987919561,304683158,304421052,8965114529,6280759970,1439087284,62642625207,65277991158,70139834758,39538192775,66889507363,14876326556,37918513842,54589307584,27341,27348,37356509240,22860077122,304156850,7283478768,49764688257,8885301762,5167430270,41636,2522659495]
private def oveB44 : Array Nat := #[63716367052,27345,7283609884,41629,39582,39583,47040326350,27347,5151070211,5151070212,55654539415,13257464034,29307629809,51375298850,44931012921,72848300351,16485503467,916247034,35479,35480,35481,35482,35483,35488,35491,35493,35494,35496,33465,33467,33468,35521]
private def oveB45 : Array Nat := #[33474,33475,35526,33482,33483,15055,19152,21202,19157,15062,21207,21208,729,901704342,12175993487,13249735312,319232407,69589340533,74412528012,306385306,9968744985,856103315,328143216,306123144,48642724268,13204134255,70662953375,25056315758,48660679083,76021172656,5733542548,26130059653]
private def oveB46 : Array Nat := #[3049187986,36335184529,7335115392,305994106,306647458,59965627019,8372296086,74435189389,5204793996,319232061,6789454478,319232045,76005052829,75534496393,72845298044,319232042,319232060,76004530444,11630082676,49771500179,48697758357,76004268263,3051815311,305600709,76005312947,6766786934,49716455840,76005439910,23941552536,49717111332,37409571516,75527406282]
private def oveB47 : Array Nat := #[76004399393,36335827648,1988672178,5734187720,73870547370,16971917951,16970881359,43851248262,329038489,38495894190,306506140,76026933679,7344667335,27341,305862953,328655363,18086533804,36335950513,71185535279,3017738635,76005564977,5741277834,66952805018,39581,18091920032,6820510393,5734308539,3595336401,75536036568,76004913582,1991424678,378055337]
private def oveB48 : Array Nat := #[19168539331,76026155164,21847400865,1985784476,39586,41635,5738502836,52458724022,7357379273,11648400084,7353430743,62589964337,43859112025,76004137086,76015409408,76027453956,16971522568,18085755510,4670147231,319232003,319232007,319232014,65811189792,45469718750,6819862806,2456474039,35742470625,35479,35480,37531,35486,35489]
private def oveB49 : Array Nat := #[35492,39589,37543,37544,33470,33476,33477,15054,15055,19152,15058,21203,19157,21206,729,38437067124,309656085,1383397925,308091257,1382224285,308220288,61538634134,19692186251,308873648,61531294060,308482439,22872384150,11061224084,29327819173,14323477135,32040217237,45990863504]
private def oveB50 : Array Nat := #[308353414,2512317069,1382095265,63707603603,74990807584,308742551,1382484391,22872259195,51349485962,38437066794,38437066812,38437066813,42792704657,307825009,1381435772,38437066797,11059792253,61548452494,307566910,63706561156,45989821044,8898943467,307956082,61532203654,914932410,308613523,56175280811,61531167049,42776455577,1380915376,61522510197,22870946226]
private def oveB51 : Array Nat := #[29905959599,29327683949,55653497462,49729813170,11061344972,23444121971,11632961950,309783063,42232629900,42232498834,14336705203,29328718530,10512963647,15351617941,69628914072,60502108575,309518856,2519790187,22392519320,72806611615,70710901413,27349,1381044484,4077322615,24991429127,2522659495,45991631544,14323989185,6816561871,307042356,307687790,1383131657]
private def oveB52 : Array Nat := #[39592,5208840880,25570482877,22872498886,50241411141,1381177684,309258753,13796948631,1984723662,21848947408,306911283,1380653112,307292416,41625,17555049114,27348,38437066768,1383000424,309008830,309129728,43867351707,39580,27346,27350,27352,32046116912,3533637682,6815019065,61538875876,3056916974,35485,39582]
private def oveB53 : Array Nat := #[35488,35489,35490,35491,39588,35494,35501,35508,35525,35527,23245,15057,17107,17111,729,76024715628,49718041001,318839174,7344155282,319363506,56158917036,17506431526,8372296086,12175993487,24519446955,13204265338,49717774748,57250349437,34716574349,73870547370,12166953610,8376869520]
private def oveB54 : Array Nat := #[5733542548,36335184529,72265044364,860676748,42769638038,57250613643,52413008244,73893611955,74992517538,895941146,319101325,319232045,60466071974,6798244482,49742412145,24510263931,319232042,319232060,76049086856,73930691211,72320078478,318445812,57287692947,56213951125,56190626438,319232061,7871986304,8408857224,73381900675,311214762,49718561143,13195876761]
private def oveB55 : Array Nat := #[860797620,310186178,60467231424,8376990408,8375437728,5741015663,859236728,310974852,49711356323,18094801586,310319300,6820512441,64802568903,76024441221,66952805018,32593066658,3021904556,52414167733,42770406075,310712603,310843723,11630080628,34717342385,19168537283,4110882986,310057141,310579427,39581,7357383369,27341,27352,309926013]
private def oveB56 : Array Nat := #[57815921008,56181188987,54057824649,29900466570,25615182491,18091915936,34741988003,13195350226,319484414,311093778,36344462031,10574658257,11648400084,1447852759,13194957003,3056661098,319232007,62589964315,52444203081,36879784158,11651700971,40637880562,21847398727,20773656913,73383459276,64803885537,35479,35480,35481,39580,35486,39583]
private def oveB57 : Array Nat := #[35489,35492,39589,35494,39591,35496,33454,33464,33468,33469,33476,33477,33482,15054,21200,15058,21203,21205,21206,729,21794070892,61522518389,8372298134,44879520171,313594238,67959329152,58832523668,1387336115,313330035,2996904216,1387071902,41652654482]
private def oveB58 : Array Nat := #[55074427308,7293311379,2998344109,2997815694,7292783013,7292916119,2997948839,58832259448,1387202972,4055574570,4055574573,4055574588,4055574589,312549588,41652521361,55074294176,313071983,55073905014,1386813850,41652132264,19146275449,315159053,58834088481,55075992099,313459066,2998206863,7293174182,2503277187,10019469949,2512317069,36335184529,3057050258]
private def oveB59 : Array Nat := #[313989508,1387727266,6798244482,21765105844,3054565785,1388900878,67960893984,41711755915,313719169,313850242,2517694836,372955791,315542160,1389283987,7352277652,1446697621,3057310358,58831218821,2997680509,41652386187,55074158988,2997420443,7292387747,67958800815,7292647858,370211181,10033887619,67959060869,72837955984,41712536218,55134309022,373475999]
private def oveB60 : Array Nat := #[1447217827,311502894,58830432324,58832386439,1387592072,67959191965,7293041065,1387461038,2998073777,7290824739,1385244710,58832124274,372695692,58891625102,315798194,3000152770,2995857441,311896116,69031110718,13796952727,4133276325,41650563095,55072335897,18557509672,1385375798,59904305207,2995988538,61563666815,62637408646,8413446537,17540252045,44920668577]
private def oveB61 : Array Nat := #[35256992164,21835219370,315665048,381987481,2522663591,3066342056,59974003375,5209895600,42257263283,4676299448,914928314,14876846781,311633969,42187565107,55609337912,7290955845,313194865,58831993209,47080073809,49227557478,311367724,311765042,1385506879,312027200,38966470722,2996381766,26142372215,69628916120,60502110623,314108340,314366394,7293430221]
private def oveB62 : Array Nat := #[55075199445,41654086148,2999380488,315417144,2999771707,1389158979,7294739032,10032695925,2516503175,28832217773,49233312436,6820510393,2525543100,19168541379,47085828805,64802568903,10041735882,59889887253,42173147158,2995722305,314505663,2998860233,24470954010,4592181285,14792728615,40637884658,314233183,11648950625,41176850787,55075066215,61565618617,21837171146]
private def oveB63 : Array Nat := #[8415398355,44922620388,17542339052,21837306358,41627,41628,41629,41632,41633,41634,41636,41638,35497,31402,35499,31404,35502,31409,35509,31414,31415,35515,31422,31423,31424,35521,35524,35526,35528,35529,35531,35532]
private def oveB64 : Array Nat := #[21197,19150,23247,21200,19153,23250,27347,21204,21205,23254,27351,23256,729,901704342,12175993487,13249735312,319230359,69589340533,21270958501,41644128791,76015931762,5733542548,45992706475,76021172656,69589600649,11630082676,71225639324,44893278625,3049187986,8372294038,319230013,73930691211]
private def oveB65 : Array Nat := #[72320078478,317514253,44893147539,36335184529,317776502,3017738635,319229994,17559245453,49771500179,48697758357,17022374540,901575304,10533931384,43305466485,319229997,76015538406,75534496393,73870545322,74997625477,69589731708,56211986947,44893669798,70663473576,7893604872,37409571516,75527406282,319230012,5734187720,76016060846,5732897268,76016448075,38499168942]
private def oveB66 : Array Nat := #[36335825600,317895321,1991422630,76015800635,23941544344,902214342,25293,317387198,6819863042,74990654127,25298,316870918,69589209386,5741277834,36343827100,32593064610,36335948465,4673026744,914928314,37418203855,76015145208,66949405191,13257208424,37527,37533,7352797859,19168539331,316215447,76015276260,74465597957,76016312868,37528]
private def oveB67 : Array Nat := #[37417562779,37534,39591,7357379273,11648400084,8427174613,315953256,316084342,32589666820,37530,37537,37540,37559,27350,319229956,319229958,19167893737,5741277440,37495,37503,41631,41632,39589,35496,33465,33470,33477,13006,19152,19153,19155,13015]
private def oveB68 : Array Nat := #[13016,729,7344155282,12175993487,860676748,34716574349,49711354275,56158917036,887683625,72265044364,17540125101,36335184529,76024449413,318706042,57249829297,897255792,76024975726,72287705744,2503277187,856101267,24485368242,3057310358,57287692947,5733542548,57250613643,56213951125,73930691211,6798244482,73381904771,319099277,76025106862,72320078478]
private def oveB69 : Array Nat := #[319229997,319229994,52413008244,24486011527,319230359,72296622717,318966152,318837126,76025235869,37409438378,52414167733,318312669,8433218248,10573116032,319230012,319230013,859244920,54057824649,17542341239,319611521,6820512441,19168539331,4136155844,858851637,8372294038,24485628321,66952802970,76025868958,32593064610,73894245056,25294,1447852759]
private def oveB70 : Array Nat := #[72281557309,72318114309,18091920032,57251107515,318574932,319484414,37533,41635,37548,7357379273,10574658257,374110931,318443764,49227559526,25615182491,34717340337,318181517,372306521,2522655399,25293,36344462031,25304,76024189041,318050423,56176087193,4110881043,39575,37540,41638,21848945360,319229961,37402763392]
private def oveB71 : Array Nat := #[29900462230,26142365857,49708724402,45516,33432,33433,37532,37535,33441,37541,33448,13010,15060,19157,19158,729,16470960789,5196671631,25019867795,48675218068,21794066796,25019224442,17484937742,36335184529,320278928,58313214375,25018960259,25019093404,64761168245,331155854,364833420,25018567027]
private def oveB72 : Array Nat := #[58312823181,53496971660,58314250902,332192400,71783207563,64761039279,67439628681,21794066477,59419455858,320405913,53529596558,21794066474,71723061613,21794066492,372568697,4673028792,321319562,24515889805,34200279555,25018435961,330895745,320539038,5204406900,321184382,320926298,5196542583,14873576125,21794066493,67438711054,76571402872,24515758738,31516574389]
private def oveB73 : Array Nat := #[25018175817,320795219,67441308358,5203095976,1406055070,5205314215,16446829243,319754441,67440019863,24536603144,76079608472,67441177243,25294,1447852759,319885537,320660004,10044486309,5209897648,374110931,75534883224,10559216031,37544,48675984058,24516532930,64762442454,329846919,320016663,355791475,37530,49770179242,25304,1404506307]
private def oveB74 : Array Nat := #[320139609,76585949558,58889525675,13796946583,41628,41635,37540,41638,36283287606,17013731439,40617828596,321041018,37529,37533,41632,39586,37547,6816561871,21794066434,21794066445,21794066446,1446310055,38497210841,37500,37512,37535,33441,33471,21197,19152,21201,15058]
private def oveB75 : Array Nat := #[13012,19157,729,12175993487,323805846,43306508944,7344155282,49711352227,5733542548,322898348,36335184529,322505083,322242926,45992706475,59929330053,6798244482,49771500179,7344280205,323160498,48697758357,319228311,322374004,323029425,17022374540,6799018638,59929201016,319227965,322636172,6799149707,322767265,323549720,319227949]
private def oveB76 : Array Nat := #[69623939467,12150180243,323680883,48665504427,19168543427,25610994372,323926720,74465597957,319227964,13243570563,18094801586,2528817852,66952800922,319227946,321849643,321980721,351709860,10045010634,321456261,6820512441,23246,21848947408,322111831,74443315743,12151597726,69638597290,321718526,323422715,7344409251,37557,44930081480,3595336401]
private def oveB77 : Array Nat := #[374110931,27351,59928936780,37415213431,323291617,36342919796,41627,35485,37542,35522,8427174613,69624072441,32589666814,35481,37543,37544,13262961342,35519,321587350,6819863011,1905979910,70702657635,39025432703,50299719810,18624860291,35484,39583,41632,37541,33481,10957,13007]
private def oveB78 : Array Nat := #[10962,17108,17110,10968,729,33113959051,15397218964,4659800720,3049187986,324340092,47049279865,347003534,75534883473,26089032051,47054772883,47617596053,6784747953,11630082676,45976324528,23982573979,46013403791,47049540008,47087145622,6821827213,379376268,59960396183,324471169,324602250,18084465016,324987412,6761678908,21293759113]
private def oveB79 : Array Nat := #[6761678890,6761678909,47032889925,324209013,4664765099,15397728945,4664634029,4673028792,45975142793,45976060325,914932410,34203022013,324862398,21307763402,47032240555,33113311689,45976957612,6816561871,19164592856,47032492486,324723126,38495896238,325237423,25614267076,23255,54047344981,377412096,37579,374110931,6761678893,345835836,35494]
private def oveB80 : Array Nat := #[35507,3603471035,43331003070,37567,5204404406,18621333704,35479,41624,39584,37540,21316018886,27349,340854885,324077695,49766785387,39589,35495,18090851022,3595336401,6761678848,63723329623,35398,33433,33434,39579,37535,37537,31394,35496,10957,15056,10962]
private def oveB81 : Array Nat := #[17108,15062,729,17536051856,74445021841,62633861774,43305855634,5733542548,326044022,326306184,51340171915,29847128489,325650798,7335115392,32554551686,23963830701,29853551025,24001696405,17022374540,15401538189,69625500303,32591630995,29854075285,71246336662,70667010428,21308180888,289998890,325912946,29854462495,289998908,29853944193,3040148101]
private def oveB82 : Array Nat := #[289998893,29878973054,326951549,29854720644,327201449,51340552876,43864605381,325781871,25610994372,289998909,23964223865,51339266387,30979703488,19168543427,326437257,69624072598,15402183347,3595336401,19164592856,29853419849,17557281282,32594504354,69626145468,70666225849,15400110475,37416661621,70667905723,7357379273,25293,43327085061,37418203855,27754527444]
private def oveB83 : Array Nat := #[43302183148,66952802970,29854970531,69638595242,35501,27762664113,15414631112,25303,35494,35499,37426340537,37575,29853284479,12185428315,29854587457,37532,41632,374110931,289998863,10513481764,51375304801,32589666407,37447,31383,35483,31390,39583,35493,39592,13006,13008,10962]
private def oveB84 : Array Nat := #[15061,17110,729,13249735312,36335184529,319230359,3049187986,328143216,16971141508,335350194,43850203510,334694789,16977693105,328010094,345168525,335219093,16978217389,5733542548,6789454478,17526872719,328405391,16971403683,16977953153,334954892,23941550488,59965627019,13264804492,70703045270,7881943570,319229997,319230012,43859112563]
private def oveB85 : Array Nat := #[74997625477,16971917951,319229994,319230013,16977824131,8960668061,69626950050,13262963390,75532530092,328919677,329431737,327881006,75534496393,327356553,328274311,28289851784,45469720997,13248815539,329298615,4136155844,8425370181,19168541379,54058348937,29362287022,69629166229,16972165812,71225631132,13248553376,76057469350,39496645160,13266238099,40109257380]
private def oveB86 : Array Nat := #[327487655,329036441,5743889051,16972034722,13250380472,18566549569,17003254067,16971272598,328655363,25293,75536038616,327749908,70712335047,43860652752,26618826810,327618766,21845432737,16971653641,39578,37533,37542,49770183338,59966526124,13250503372,47612365067,328524288,16971788914,37527,39585,39587,1988668082,27342]
private def oveB87 : Array Nat := #[3595336401,34672674867,37414695007,74964078750,37532,4670141087,41637,37550,70703944385,6816559823,8427172565,319229968,69628911700,21308563544,2456476087,37511,33432,33438,39584,35495,39592,35525,35529,13010,23251,17108,23254,13015,729,5196671631,16470960789,364833420]
private def oveB88 : Array Nat := #[36335184529,21794064748,330500466,67441056404,58314250902,58312558979,332192400,1405934227,4650760819,1404897701,331155854,4649449844,58313214375,58312687993,67439493551,1404504499,67439884696,4651534990,4651666059,1405549188,24515889805,24515758738,21794064429,330893697,24514984573,21794064444,330629496,21794064426,21794064445,68522017136,1404371333,58312821133]
private def oveB89 : Array Nat := #[332061312,5197183662,1405676167,67441306310,71723059565,11118754475,332442290,58314500812,58311770340,58313462279,331534856,67438971146,58314369700,5196925607,4673026744,21848947408,1403717874,58312425808,1405028828,76079606424,14873574077,26680785613,331667984,10044484261,35503,5209897648,1406298840,13796952727,35496,36885400243,37422271162,23254]
private def oveB90 : Array Nat := #[1447852759,58311903476,41625,67482974927,374110931,13735495732,330760407,331286767,67439102239,58313593355,39586,35500,54017847371,1403324563,68557267429,331403779,39587,3595336401,21794064388,1403965721,43475,39517,37532,37535,10958,15058,10964,19157,729,5196671631,29355862672,3586058902]
private def oveB91 : Array Nat := #[21794064748,16470960789,364833420,333121906,36335184529,332990832,38450825628,35275985549,3003582899,25054740876,30444147348,29349708148,38451087769,30981018259,76615045771,38450956719,65340756622,34202243730,290129981,61536143778,5190517143,290129962,58314918268,290129980,25060766324,29355733637,58315442553,13799834283,35243731631,54052569770,28832219821,58316204748]
private def oveB92 : Array Nat := #[58315049374,71723059565,23956216446,1451803323,67474342598,333384056,65280604553,34169487754,38451218835,54589440714,56704174408,61537049219,23956335272,334146226,21848947408,8427174613,16470313399,29369086655,23246,332728508,23955442008,35525,1447852759,290129965,77149952505,53527632391,35507,4673024696,1439212226,68556716751,3595336401,38451337832]
private def oveB93 : Array Nat := #[1429533313,41623,41628,35514,23252,23955703923,5204144719,38451468901,35480,35481,35482,39581,35492,39591,26680785613,6819862651,35385,35433,35456,39583,33441,39586,33443,17106,17107,10966,10968,729,13249735312,36335184529,3049187986,5733542548]
private def oveB94 : Array Nat := #[319228311,70703045270,17526872719,335350194,335219093,334694789,74988585347,43850203510,348848494,334954892,69624072598,17559245453,334825862,17022374540,36335309451,72320078478,3051946406,43845091746,43825432975,335088013,319227964,319227949,17526483336,75534496393,334563707,34738197022,69629166229,319227965,335733375,13249606259,13262963390,69624990115]
private def oveB95 : Array Nat := #[4136157892,335850160,13248813491,319227946,43861723802,69628916354,69626145468,36335829696,17525442813,23941548440,335469105,71225629084,350280110,40109255332,12186340006,36335692457,75536038616,334299333,19168541379,3595336401,17525705004,334432594,335598198,335981238,10045926090,23245,45469718949,66949405191,7893604872,35486,351963839,69630458576]
private def oveB96 : Array Nat := #[6755780673,59960395849,74963421451,20771821981,13266234003,35499,35501,74445527735,25294,25303,12695699624,75532523719,54058340745,350933554,4670141087,39585,47085824709,7357377225,3051551025,35490,39589,37418203855,319227911,319227914,319227918,18624338000,13248551036,37951555811,35483,35484,39584,33447]
private def oveB97 : Array Nat := #[37544,33454,33458,10962,21203,17108,17109,21206,729,19147317900,52970185357,19146664593,337435282,52969532054,16470960789,76591463044,33622786447,39570952851,39034081940,65280606601,21833515384,33622917522,19147180686,336658820,52969917072,19147049611,26662468230,33622655372,52970048143,367722541,336789893,367722556]
private def oveB98 : Array Nat := #[52969142903,336920971,33622524291,367722557,337552049,37425429177,8971270850,10041737930,337052056,19143917932,26664018602,52971086517,33622393157,26661421497,33623810756,53531028122,8427174613,1447852759,33622262081,47077982637,337814206,19146275449,52970949292,20782426811,33623929556,337172930,37568,64806759111,62114263757,21199,367722538,26661671425]
private def oveB99 : Array Nat := #[41629,49237500596,19168537283,33623679688,337933009,54061202136,336261272,33622130898,33435,33440,41634,33481,337314254,33623167456,39587,2521592530,367722508,367722509,40636043381,33431,33439,35489,33444,39591,8910,17104,15059,8918,729,364833420,10565380756,36335184529]
private def oveB100 : Array Nat := #[5196671631,10019469949,363659640,10565505683,73379402389,66400080530,13204128111,364958349,10539958705,10020375182,363528565,10564075932,10020244107,338231505,339411344,5204656784,12183728755,10539434387,66413707926,1441464365,10539303342,339671460,10539694471,10539825548,339018110,1441464362,339278211,1441464380,1985792668,1441464381,375179929,10541114031]
private def oveB101 : Array Nat := #[2525543100,10021413555,339534238,10540081569,14876850877,6823787193,364704373,10044488357,10540864127,12185270993,338624828,53469446541,340054570,5214085808,10566148795,5205947091,65872362198,338362611,340185657,340435608,33474,10575721115,2522663591,73380043457,33478,34741072588,72851684045,1924333634,15930294473,338493736,339804599,15950064288]
private def oveB102 : Array Nat := #[33448,21198,23252,338100368,33441,72859818670,8427172565,31483035749,18061262955,10016184562,51912562952,339921409,2528291479,41638,1447850711,61568112687,66398767264,33406,37539,29348,33449,35530,19151,17104,8914,8920,729,76058389136,3049187986,74984647316,59965627019,75534883473]
private def oveB103 : Array Nat := #[342163856,18085892755,341508478,6798244482,6821827213,379376268,26089030003,6784483724,21307118230,6784221619,46013403791,48697758357,6783828355,341115255,76058249870,21305688483,6783697330,21305688124,74983735729,18084462968,21305688109,341770630,6784090530,6783304075,355793523,342663851,342794925,59966270129,341901704,56752782016,40109783752,6785381065]
private def oveB104 : Array Nat := #[21305688125,340984182,21307630268,49770183338,6784999946,21307763402,6816561871,5743884955,18086535852,374110931,3595334353,11648398036,21305688106,21308174527,18086953351,69629817504,18086400699,75536036568,33459,54606207683,35527,23255,66939453593,342415838,39578,33442,33446,33456,6820506297,21306605723,33431,35491]
private def oveB105 : Array Nat := #[21305688076,21305688081,21847398483,8969310315,33432,29342,37535,35489,33445,33448,8909,13006,17104,8914,13013,15062,729,43305855634,345168525,13264804492,319228311,43306508944,74445021841,5733542548,1966406261,361038229,17004036525,349632908,17003383172,360384880,360509815,16987521457]
private def oveB106 : Array Nat := #[69624990115,43329049231,348848494,75530570127,319227949,74467562126,361167260,56743752242,16994454155,351455894,43303762336,43304024481,319227964,16991973776,319227946,319227965,344908410,16993282441,350284206,21308180888,61558030587,13262963390,30444925625,17004157350,17005470335,343214221,345039484,36350505648,343083145,69623808397,362343025,344262968]
private def oveB107 : Array Nat := #[35271789210,25610994372,343738574,4670147231,21318777493,19165661863,69626145468,45469718949,13266236051,49774373529,362850995,3595336401,344394049,351709860,1988674226,43864605381,21311564491,16986474755,16991453515,344656353,69626014410,16987130176,16987654647,344773123,75531725495,351963839,25293,27348,343343283,344000744,28289849736,16993147298]
private def oveB108 : Array Nat := #[350149036,43305062950,35486,37417687721,343859431,47611314443,69624582557,35485,37537,38495892142,75531590326,27350,43302185019,343593155,348453078,1905979910,35479,37542,16988277441,23246,23248,374110931,8427174613,23256,319227919,26679630142,35483,39580,39584,35493,39592,35523]
private def oveB109 : Array Nat := #[35529,19151,10962,13015,729,33113959051,15397218964,347003534,75534883473,11042486801,3049187986,21293759113,69620007292,15397343891,24001696405,6821827213,26089030003,346620308,379376268,4659800720,346489220,69619876275,346227073,37411815466,37411684772,43859362447,346751408,15410971286,37411815484,74983735729,69621052030,15396045200]
private def oveB110 : Array Nat := #[37411815469,76057346445,69628916354,347120299,347251373,59437136568,346878465,25614269124,347386557,15396299142,33667332791,346095946,346358147,6816561871,345702701,59960394135,40109257380,41638,49770183338,43860654800,345571530,345964868,54606209731,18090848974,21207,19164592856,27211006268,69620138366,5743889051,33468,34730463655,33438]
private def oveB111 : Array Nat := #[50846673569,34205113001,33456,43331005118,35519,59962464969,41626,33442,37541,374108883,37411815485,63723329693,345440425,37413112447,4670139039,3595334353,37411815428,37411815436,2997286931,37953525832,35413,33390,33432,37544,33480,8909,8914,15060,8917,15062,729,43305855634]
private def oveB112 : Array Nat := #[43306508944,350812712,74445021841,351326861,350421426,69625500303,43304024481,69624988067,348848494,349632908,5733542548,351455894,43303631237,349766031,17022374540,348975476,43303500163,350673446,59960393788,349110654,69623939467,74444620427,74444491406,349241732,349897115,350155180,43303762336,13262963390,59960393773,319226263,350024102,4670147231]
private def oveB113 : Array Nat := #[347930877,19165661863,25610994372,21318777493,59960393770,59960393789,69624453532,351197834,348061961,74444233350,35274670766,349372806,351072898,351838899,13266238099,32594502306,351707812,18094801586,352219864,74443575844,351576729,69626143420,3595336401,74442932732,74445918896,74445529783,69623536008,350278062,74443182600,41633,23245,352088784]
private def oveB114 : Array Nat := #[74441621788,348455223,349491593,69624582557,33438,7361571493,351961791,7357627092,10037787350,69624070187,348322098,348584250,350933554,35479,66952800922,37531,7357383369,347537537,347668633,33437,37546,35508,14873565885,21198,27343,374110931,8427172565,21207,59960393735,59960393737,59960393742,61555791940]
private def oveB115 : Array Nat := #[3027947620,63719526516,22384265362,41609,37532,39584,37544,33475,8914,729,356182667,355269137,10557383317,356835986,356567694,10556340852,356698769,354351508,353694076,10556852884,4659800720,10556981907,10554505640,356305548,356434573,354482587,353958280,10555156907,34204203663,10554112422,33129937558,354089357]
private def oveB116 : Array Nat := #[10554374576,47024371754,10555677223,47024371757,54006315386,47024371772,22389768886,56749507264,10556598921,355793523,357089949,21848947408,12163545310,353302894,8965114529,61044718286,356960921,10557508251,10558020297,47024371773,355389970,10558284483,10556076581,47618751185,355650090,8971926180,357341867,10557891268,33123236563,19164592856,352909531,34712254688]
private def oveB117 : Array Nat := #[69634409130,19159,10555292115,355920513,10558151349,11656536761,10555544070,41626,4677081762,35257645099,62088345773,35480,39584,33667326647,6816559823,75509723265,33634044044,33120897475,354744780,39490,31397,31408,47024371721,47615242276,35487,27302,35497,8909,15058,15060,6869,8918]
private def oveB118 : Array Nat := #[729,359590543,36335184529,74467562126,5741664914,7338392105,76078174859,5204793996,358414722,359451277,7338129841,358676898,7338912404,5741527699,359201304,5205050005,5741920918,5204656784,10573116032,21305686061,7337603449,358152561,7338650242,7337867680,21305686058,21305686077,21305686076,6816561871,12183728755,7339023031,19171816131,2528817852]
private def oveB119 : Array Nat := #[10037787350,3038837026,69636377243,359328381,5205695147,12185148095,5742820055,357890356,21848947408,49711348131,7338248709,359838389,7357383369,5205949139,8427174613,29894965577,10574023327,5742566088,359070229,12184636067,5742303943,7337343303,48695794010,5204265589,18091915936,35520,19150,52981069875,5205314215,6823783097,19135002735,67487582690]
private def oveB120 : Array Nat := #[39490,41628,31396,27341,27345,19154,21305686021,62647748712,33376,33387,10964,6872,729,21310661266,13264804492,5733542548,25072685709,1966406261,17004036525,361038229,360251759,17003250062,7335115392,21310921360,37417048721,360509815,74467562126,43329049231,17003772337,360120686,360644995,361167260]
private def oveB121 : Array Nat := #[290259004,17005470335,362472061,290258989,75531207307,69625627286,21308305825,75529650567,21308178840,4670147231,361298336,361941524,13266238099,290258986,290259005,17003381124,362343025,75530947192,38495896238,4139432644,10580701894,360905097,9479717108,75529388427,69626145468,69624070550,69624582557,7357383369,68535779541,49774371481,32594502306,19169460903]
private def oveB122 : Array Nat := #[362848947,13262963390,3595336401,361820678,17005204006,362601086,362717871,17003897067,17003643157,17002987826,362980026,27341,6261627153,69623800205,21318777493,21311437477,33473,33474,13774815517,359987497,37527,1988674226,4139807444,10037787350,360382594,47611312294,75530567908,69624987904,2456486327,39576,1985786524,21311560395]
private def oveB123 : Array Nat := #[27343,374110931,75530686598,45469718673,35786117319,361679363,17004677641,21310392947,33438,39592,33467,37571,69626010314,21198,27352,35394,33434,33435,31389,37536,29345,15056,8914,19157,13015,729,364833420,10565380756,14800583180,66400080530,73379402389,364958349]
private def oveB124 : Array Nat := #[10565505683,36335184529,363657592,66398910858,5204656784,66413707926,378585739,65871069838,5196671631,66399697423,73379019303,66398648735,66398255390,290912316,290912317,363911563,12183728755,290912301,290912298,72851684045,12185270993,66399826553,73379148416,10565753519,2525541052,5204406900,10563811665,10041737930,5205949139,65872362198,66400328386,66399554057]
private def oveB125 : Array Nat := #[10566025909,363395382,10563942717,73378748935,365087391,65871727264,5202047216,73377708359,39589,365599418,73380043457,66399427077,72851049111,39577,5202049206,5203216863,1985784476,66400459454,19150,37531,37538,39590,37543,27344,21204,65869629909,66399304171,19157,27351,290912256,290912261,290912263]
private def oveB126 : Array Nat := #[290912267,290912273,14331332730,39384,37505,37512,35491,27300,33449,17103,6866,6872,729,19692186251,366008973,22377716370,29893909135,902879888,5734718099,50295003797,365869708,5734578836,902740630,19692185645,19692185660,19692185661,28292467351,46546078360,52451658394,37956143774,34198047392,20776274593]
private def oveB127 : Array Nat := #[365750800,3586976273,5734459934,378059433,35811539628,366123662,22377831057,27341,27345,29905959599,914930362,11648398036,57810938388,29893650965,35799231003,57811448498,1451801275,2521592530,27347,22389766838,35532,35496,35501,35487,1984721614,33598662707,20176889912,27693082694,20241091234,21848945360,35481,35492]
private def oveB128 : Array Nat := #[35525,23247,15062,15063,15064,2777,35483,8358132237,58354754193,76615045771,36885940878,58355014287,369152656,67481819797,1429535361,367851920,364833420,20234826111,368503217,367196531,367589768,29363335725,29369614995,369279638,367065456,58362870413,367978903,367458690,59437136530,370211180,368376229,57280879006]
private def oveB129 : Array Nat := #[367720509,367720490,366934358,369019529,2529477287,367720493,367720508,369541813,67481940628,50837123492,67481432691,13799834283,71248294589,21848947408,368888442,36341608874,35263150412,368234905,367716745,368759362,29370008216,4673028792,67482974927,366803279,36886200989,20783340196,58355915468,13256022441,13796952727,24540902101,51369146686,38490401203]
private def oveB130 : Array Nat := #[20778506755,39578,25294,5185917118,366672206,58354092549,369400485,31400,382249641,58355655361,369664706,19156,369795782,26680785613,19676067999,58354626739,73907357962,53521203584,367327617,381991577,33438,24540519088,69637804722,25297,20217788565,21842938028,41631,58355534498,367720460,367720461,64793528432,35386]
private def oveB131 : Array Nat := #[33388,31356,35491,35519,21202,17107,10966,13015,10968,729,901702294,8432439949,21317341842,61045789326,44939661969,8429687443,21314589333,44937032331,8429810316,4139037332,901701674,901701677,901701692,21852897985,8967996098,10038854311,3059532456,70704751168,3059016263,58893591132,10038338146,21314970310]
private def oveB132 : Array Nat := #[8430068428,25293,25297,11648398036,23997498013,57283494558,40103625377,41177367203,64802566855,15410442952,2460278849,27346,8427172565,369943056,22381650458,10041733834,3062411979,8432814735,21317716624,33457,33465,33434,33440,44874522678,8367300664,8429929113,41709109916,909566002,4130791476,29900595258,47080464448,33442]
private def oveB133 : Array Nat := #[33444,35493,25294,25296,13011,13014,27351,27352,729,36335184529,372695692,372568697,372955791,1446697621,370340209,1446310525,373211796,1446953622,372818573,10044357266,5213174414,371120527,1444862374,380811915,372306521,33119727994,19697955228,10034016643,370209133,381993625,373475999,1447217827]
private def oveB134 : Array Nat := #[46004892051,370602361,21794058301,1444999584,373342876,1446818451,13796952727,21794058300,373076624,21794058285,21794058282,1447084706,370469235,1444211102,1446175355,373723823,26680783565,21848947408,63721628077,4676678353,76603781434,10044486309,373856946,1447598786,373988038,1447729868,71221174478,36341084586,1447336641,21794058604,372163133,4676299448]
private def oveB135 : Array Nat := #[8427174613,65870946544,54059786518,14872138086,371771871,17102,374108883,28231135284,1444725149,2529473191,371376571,371898881,372034054,29352,37552,21204,25303,50836588706,14876971619,37561,27343,27346,21794058242,21794058249,62076801065,58361432131,33411,33475,33482,8918,8920,729]
private def oveB136 : Array Nat := #[5196667535,374917771,2522401425,378718860,2526202509,23464168083,10579266196,375040654,378841746,10579389077,5196666922,5196666925,5196666940,378059433,49236589236,51383548572,34740550307,22925990455,1988024891,44937697864,23462861401,2522782407,378305229,27221725878,21848947408,10578852566,31519324825,18097552027,65342192286,49236064935,18098072242,2525539004]
private def oveB137 : Array Nat := #[6816561871,25298,31519845045,23251,1447852759,374397455,374528535,34741070540,21789595710,54001457221,31407,31421,74939422764,31384,31397,14331336753,13794465844,28826851398,25605625929,33431,33440,10958,10961,10964,10965,729,33119,33123,379902608,34202770065,10580966029,380418707]
private def oveB138 : Array Nat := #[379376268,34202243730,10579923604,48697758357,381336203,379628174,34202495638,34204203663,10027718890,18626172973,18626172988,51894474949,6816561871,355785331,21848947408,3595336401,374110931,25293,25300,380029596,34202897057,378061481,375952055,34198819530,35531,29910268574,375577052,4670141087,23250,23254,8904562754,375820982]
private def oveB139 : Array Nat := #[34198688444,6819863042,2777,34198313463,10576255549,29355,29380,18626172943,66934329373,35382,35409,35410,10965,10968,13264804492,25075964564,379902608,17022900881,5212650126,51383548559,56752257682,21318777493,379234955,17022233238,25075296909,13264136851,40100090230,8961577373,49770185386,19168543427,2518997364,65333023124]
private def oveB140 : Array Nat := #[6816561871,3595336401,67489018569,27341,27352,30444919481,10576888495,17019339457,70706190823,17019230853,376101319,37536,10577023667,374110931,8427174613,13261378235,25302,13790533936,380154560,2777,28816496698,3046692926,25296,18618953818,33437,13265050293,49220595806,29352,19150,19156,2456475649,2456475662]
private def oveB141 : Array Nat := #[2456476087,29270,39580,39583,4659796624,376623755,3060978318,379376268,3063730834,10579923604,24001696405,376746637,4675908241,10577293971,4659796010,4659796013,4659796028,377004713,52457814710,33667332791,3061359307,65879063196,50846677665,3595336401,374110931,25293,25300,49770183338,30979701440,35277421211,17560681117,17557281282]
private def oveB142 : Array Nat := #[35274021382,379753103,3064107670,33636538508,23250,23254,377135787,3061490372,58343610579,38495890094,21316020934,314234923,49772935833,52437899483,376863390,35487,30982449832,46545164732,27754682848,10960,10965,729,4659795970,4659795983,31194,31216,13006,21199,21208,5196665487,377799307,2525282961]
private def oveB143 : Array Nat := #[22926377612,39569375885,8430862995,1988412052,377922190,22926500498,1988534933,18012098602,18012098605,18012098620,34204201641,49236587188,51383546524,34740548259,14338019895,26149179963,25612309064,42792178265,378305229,27221725878,2525663943,27221850832,10578850518,31519322777,18097549979,65342190238,49236062887,6816561871,1447852759,18098070194,51920937660,21198]
private def oveB144 : Array Nat := #[21205,1987891727,44937564695,31519842997,34741068492,21789724734,41117077573,29375,29381,9978564652,29343,29348,65276399665,31453532212,49170272326,18031759433,8913,8914,8915,8916,729,5196665487,378718860,2526202509,23464168083,10579266196,378585739,2526069393,378841746,10579389077,5212379790,51383546524]
private def oveB145 : Array Nat := #[65342190238,14800572458,14800572461,14800572476,378057385,2525541052,6816561871,1447852759,31520223949,18098074290,49236587188,31519322777,34740548259,2526583493,18098451158,21848945360,59434258967,42791260706,25297,31519842997,34741068492,62095544450,18078945559,21198,21205,18097549979,49236062887,5204527286,14331332805,51901681916,33444,49217458415]
private def oveB146 : Array Nat := #[13799051780,28831437319,33431,33439,33440,41409,8914,8915,8916,729,14800572419,14800572432,41069,29170,49770183338,10580701894,10579917460,379234955,379628174,56752257682,4675908241,379493005,10580040339,21318777493,35277945488,379370124,379753103,52994540182,51375028266,27344,27349,6816561871]
private def oveB147 : Array Nat := #[27352,23245,3595334353,38499826332,17108,7831468098,8967457289,33454,15054,374108883,2777,21319956529,33333,37535,66409904627,23104,29387,6860,378059433,380418707,4675386004,65878669973,69637683852,59437136530,43868129933,49773460112,4676303505,18635197070,52994935446,381336203,34204203663,380283516]
private def oveB148 : Array Nat := #[3595336401,25299,25298,25302,10043955837,6816559823,21848945360,17101,17108,37546,37560,2777,50306650631,36950,15054,13013,19692178059,380680845,22392388242,29908581007,917551760,5749389971,50309675669,380541580,5749250708,917412502,66950711824,77151259165,76077517329,381332137,35814812332,50309802650]
private def oveB149 : Array Nat := #[917678753,41717778966,19692177453,19692177468,380807831,22392515224,29908707998,5749516960,47623359013,1984723662,21848947408,19692177469,381709007,1455450834,918579924,19706071578,29909230255,918201018,76614388254,22393035446,1455069883,19149,19153,27334,27340,356171953,35789652167,29884072159,893042924,22367879456,33601538099,20179765304]
private def oveB150 : Array Nat := #[27695958086,27303,27304,1429913785,31385,31387,31396,6867,6870,6871,6872,729,382249641,55143082667,58362866317,2528291473,6824565404,57290431140,7897383572,17024189078,31519451791,13802711701,381844120,380807819,41719868044,5212895886,42793859730,33667187344,20245414547,2529471143,26680783565,21848945360]
private def oveB151 : Array Nat := #[25299,25303,381987481,43868658331,2529598114,19156,9979340844,19153,15054,8410269880,17537075426,21199,21202,10965,13796944535,729,6824,35497,6816561871,21848947408,43868129933,29372615315,25297,71785286292,46015482517,29910272670,50311627439,49237885620,19150,19159,35467,35471]
private def oveB152 : Array Nat := #[23251,76080253444,59437255179,2777,32594746018,30984133288,10957,10964,23245,19150,19157,23214,23233,23182,19151,19155,23183,23189,15058,15063,2777,22580,22598,729]
private def oveTable : Array (Array Nat) := #[oveB0,oveB1,oveB2,oveB3,oveB4,oveB5,oveB6,oveB7,oveB8,oveB9,oveB10,oveB11,oveB12,oveB13,oveB14,oveB15,oveB16,oveB17,oveB18,oveB19,oveB20,oveB21,oveB22,oveB23,oveB24,oveB25,oveB26,oveB27,oveB28,oveB29,oveB30,oveB31,oveB32,oveB33,oveB34,oveB35,oveB36,oveB37,oveB38,oveB39,oveB40,oveB41,oveB42,oveB43,oveB44,oveB45,oveB46,oveB47,oveB48,oveB49,oveB50,oveB51,oveB52,oveB53,oveB54,oveB55,oveB56,oveB57,oveB58,oveB59,oveB60,oveB61,oveB62,oveB63,oveB64,oveB65,oveB66,oveB67,oveB68,oveB69,oveB70,oveB71,oveB72,oveB73,oveB74,oveB75,oveB76,oveB77,oveB78,oveB79,oveB80,oveB81,oveB82,oveB83,oveB84,oveB85,oveB86,oveB87,oveB88,oveB89,oveB90,oveB91,oveB92,oveB93,oveB94,oveB95,oveB96,oveB97,oveB98,oveB99,oveB100,oveB101,oveB102,oveB103,oveB104,oveB105,oveB106,oveB107,oveB108,oveB109,oveB110,oveB111,oveB112,oveB113,oveB114,oveB115,oveB116,oveB117,oveB118,oveB119,oveB120,oveB121,oveB122,oveB123,oveB124,oveB125,oveB126,oveB127,oveB128,oveB129,oveB130,oveB131,oveB132,oveB133,oveB134,oveB135,oveB136,oveB137,oveB138,oveB139,oveB140,oveB141,oveB142,oveB143,oveB144,oveB145,oveB146,oveB147,oveB148,oveB149,oveB150,oveB151,oveB152]
def ove (i : Nat) : Nat := (oveTable[i/32]!)[i%32]!
private def extsB0 : Array Nat := #[1090521383,713366063,1149549140,730122844,1040685698,1023709778,503624291,277301877,1158126208,948214377,1107630706,470260358,562340402,1048885818,671402565,76106396,297515,528788046,470067791,369396304,596195999,402973243,1124383336,461693549,100971069,973378151,235358857,1183095371,737961,1166320218,50940577,178615]
private def extsB1 : Array Nat := #[1157790149,1040349679,948081142,713214433,948095479,529162907,696863392,1099516581,470442664,1024225962,1116416686,420160178,923626168,713769657,1108034237,789260992,965569219,973894342,915088072,185326281,211503823,907758288,555651793,496931539,152998612,572213973,362713814,169560792,4647641,92283174,33884766,327486057]
private def extsB2 : Array Nat := #[553957944,293900863,847551047,520702621,679793242,1040536156,1199925853,839166577,1015355953,478485087,612700768,1090851425,252340898,251963966,663016025,604334698,84234862,76235440,1015759540,26954445,453722815,478888640,345721553,84624058,1040925381,278612692,260545157,34034307,831351469,1075745490,1084134099,1109420759]
private def extsB3 : Array Nat := #[847432135,16959950,662878699,142791153,679655924,126013946,856414891,244148920,101395129,319650491,34304700,336399041,135094978,294484675,327905990,235754184,151872202,42797771,647926480,1058968277,169896664,373717721,553968184,142926424,1199891037,1090839137,1015355953,847583815,294099577,75809342,663011929,604291690]
private def extsB4 : Array Nat := #[84197998,805640795,1040521820,361034334,612692576,336034423,956791428,411365951,679801434,268925577,75678187,26954445,563825360,278612692,1025198805,84066810,378167965,9069217,252338850,873095844,571308715,445336237,906785460,176900793,319650491,34370236,294417091,1166832325,1007372999,512588488,638274250,260930251]
private def extsB5 : Array Nat := #[488659666,765979347,732424919,60840664,122059481,318933481,1082460747,151446082,1191365081,545442283,763677233,830827078,1141185125,1015515773,831210157,545997486,781929171,251826639,562852542,109789897,236669654,495247927,436888217,201505207,772100690,193274466,319126127,159687211,327764639,706433749,691139287,50512334]
private def extsB6 : Array Nat := #[369707682,118121126,160129705,1183548074,856521387,906713780,797680309,244153016,34316988,227232445,638284490,262167245,682750671,303993552,1034414801,622545618,139084505,125841759,197048,327264726,880912855,1040202076,511719786,58765675,830486884,796932453,209760614,738212189,1199585630,822129001,1157642592,981481825]
private def extsB7 : Array Nat := #[536916322,713366063,1183095371,1115986519,923081323,923243123,713527924,1191492141,1015331377,218423863,688185912,293909055,1132761681,830970489,487017083,1023709778,503624291,277301877,1158126208,243577398,788828767,1200069249,92752519,402973243,1149549140,1124383336,461693549,100971069,973378151,1040685698,235358857,562364978]
private def extsB8 : Array Nat := #[1048904250,671402565,444910150,76110492,326187,528898638,260463183,42269264,579424927,1166344794,730122844,939838045,839189105,9001633,965024327,1090820705,948214377,1107630706,570427685,1182796067,301992228,562225591,1090521383,922911161,1199733226,1157790149,170421,839049716,713214433,1115853293,948095479,906578583]
private def extsB9 : Array Nat := #[755655321,529162907,260727453,696863392,956910242,1099516581,470442664,1183529642,1116420782,76274352,420160178,646652597,923626168,713910969,9165498,51108539,1108175549,1091254976,705372866,965569219,948648646,915088072,185326281,35558093,724056783,698184400,580745937,639537874,1067285203,152998612,958231253,362713814]
private def extsB10 : Array Nat := #[430455512,4647641,453149162,319097455,478314994,260377167,1015185864,822413869,1040351727,293931583,906314336,377832042,847583815,881148513,327486057,411552390,142916184,805640795,33884766,335878742,872759897,436718212,76235440,1015759540,26954445,42277456,596200095,1166361178,1040536156,478888640,345721553,84624058]
private def extsB11 : Array Nat := #[278612692,622881490,1067477715,1101032149,1109420759,16949737,545444331,528667124,126013946,608919,520702621,252365474,537479843,109660837,730516135,101540537,17523387,336290497,135094978,847995587,269181638,1150112455,235754184,1050700496,169896664,399131353,453149162,319097455,822413869,411492927,260377167,361161310]
private def extsB12 : Array Nat := #[327486057,142791153,528667124,553832903,117625294,76235440,26954445,84624058,278612692,805640795,873095844,663046745,604326506,345721553,847583815,378167965,596200095,783413971,608919,537479843,109660837,176923321,17523387,806052540,1192852161,705405634,847995587,949582534,638296778,42689227,1050700496,775025362]
private def extsB13 : Array Nat := #[1101032149,221377239,204600024,80485081,1149405670,8557038,125997557,126011898,260213243,1158079045,948095479,101114429,771932647,1040681602,1024225962,244009656,227375805,581429969,973894342,260784843,169560792,713380399,528980595,260405839,268773991,201675314,109369924,822692515,1124412008,1107630706,663583418,320887508]
private def extsB14 : Array Nat := #[537686732,219892439,369279476,529162907,50940577,42625701,1007313575,470442664,1158382270,302752452,1166760645,211503823,564652752,632419027,840981205,615641814,4987609,578992609,889354726,679639535,805485041,721588684,142770621,1057128913,285376978,914522620,512049724,302334528,721603032,998427099,998412765,797282893]
private def extsB15 : Array Nat := #[570790512,75868734,663042649,8839790,740009,1133200046,487289525,898464438,454775503,411351615,914692681,679791194,679975561,1132802641,956641878,688749228,285950641,143344311,1042803406,176902841,17517243,361452220,647717584,654625365,453593753,235065848,1057702596,915096264,136356564,176509501,773542610,479939286]
private def extsB16 : Array Nat := #[203115224,378096285,403335838,243878560,67717793,336159396,604588710,831531693,1016081076,1167315653,1100206791,313215693,1142854355,966693591,600578777,168373,182711,771918292,251822543,1031981532,872593899,369281524,386208314,260379215,268790375,377842282,294077049,1124252151,831210157,252396208,94063309,269173446]
private def extsB17 : Array Nat := #[369836747,169560792,579162671,100993597,1099268691,1006994004,184898116,193268322,529365673,933139151,671972030,824087249,663450298,278948564,537621196,924871383,17386135,76180124,327838367,50940577,1099522725,310987430,1007248039,428427944,546005678,244032184,806066876,1108042429,395025092,1041711813,639058634,649196240]
private def extsB18 : Array Nat := #[498201299,707916501,481424086,4987609,285532731,344252995,1157947973,1183113803,553968184,142926424,1199891037,1090839137,75921982,663124569,377911914,8813166,1015355953,830806598,847583815,1032133221,579148335,1149573716,805640795,1040521820,75684331,8575482,411365951,545749627,637858370,336034423,679801434,1132952180]
private def extsB19 : Array Nat := #[889516627,956791428,386200122,973568646,176484925,268925577,361034334,126319240,612692576,696744586,663380635,76178076,378167965,84566688,9069217,252338850,873095844,604660390,529365673,571308715,596325038,797801141,319650491,822817473,302873284,327889606,512588488,118323913,260930251,537604812,313014989,211835599]
private def extsB20 : Array Nat := #[564673232,488659666,497593043,589839060,841497301,237001430,220768983,60840664,63367897,8561134,268620282,461558263,101114429,503767651,1149586004,101147266,529298089,1024225962,26690226,211503823,260393551,268786279,8723054,1007313575,117924480,302752452,889930439,338817748,1108042429,369836747,707916501,50940577]
private def extsB21 : Array Nat := #[537686732,615641814,327774879,160002720,42650277,470442664,102333113,1159297726,1041857221,649196240,347206353,632419027,219892439,169560792,4987609,168373,182711,201494981,771918292,830640592,1031981532,948077046,251838955,369281524,369263099,386214458,260379215,1124252151,764103348,806066876,1150558919,639058634]
private def extsB22 : Array Nat := #[1124827852,942711511,184898116,193268322,436562543,1157966405,1124559498,244032184,1108042429,671972030,824087249,1049391789,1133206190,1041711813,269173446,498201299,579162671,176611901,251970110,84249198,252396208,94063309,529365673,420192946,438328015,369836747,169560792,335866454,17386135,637858370,663450298,649196240]
private def extsB23 : Array Nat := #[76180124,327838367,50940577,1099522725,428427944,815485652,707916501,481424086,4987609,159556021,771924436,318951911,528660980,201511351,478335438,830656988,1191522861,923089515,613114548,34316988,1191920321,1141596874,1124946636,715156183,964872647,1015386673,75979389,445346477,546579118,713792185,295125699,991980243]
private def extsB24 : Array Nat := #[688175672,1090853473,940022407,277697202,1158365886,109789897,236669654,159732267,67559990,1082610293,1091257024,42681035,60508888,1132823121,335891030,386224698,1157976645,185256604,109400644,50680420,822790819,637864514,436888217,654920349,1082460747,612702816,369781410,571484843,748201,211839695,596206239,8997537]
private def extsB25 : Array Nat := #[1200870079,120277709,741470928,329294545,1000248018,1060238037,340531929,1107468772,545442283,872780377,151157210,117891682,17386135,50940577,529232553,244028088,9134778,975915728,444901958,595890775,596089467,730139228,948261481,327686793,1175415485,1159297726,831210157,1117209262,1041857221,973894342,613145268,889930439]
private def extsB26 : Array Nat := #[126571212,941527767,713380399,101114429,151308866,1032102501,310987430,252396208,369836747,251992638,8723054,445278887,1107630706,470442664,1024025244,327774879,302650016,42650277,110516937,94063309,932926159,338817748,615641814,169560792,4987609,981635524,981649865,310544850,1073910227,1107464676,260213243,92457407]
private def extsB27 : Array Nat := #[92443073,76106396,754345,773423786,1116445358,420313778,344695478,143350455,479476416,135033538,269959878,916030152,260784843,948095479,948247145,1107630706,470260358,101982905,294341315,730563269,939835997,923071083,503655011,671582837,243604022,134716039,25504307,704981557,1183142475,142924376,336153252,914809417]
private def extsB28 : Array Nat := #[369457744,679840346,193821385,572213973,268759655,453665433,1040867994,529103515,1175022239,738814625,428501672,739990224,253446866,590475988,354441942,105650905,166325,1182962132,713214433,713200104,486703613,554257048,940133027,773276330,244032184,504986301,672760510,92883613,50940577,629908151,270107334,622281416]
private def extsB29 : Array Nat := #[370768587,671267292,445334189,252537520,487277237,35343053,546585262,421102258,344679094,462111407,9134778,889930439,293784024,184732135,358955,562385458,25496115,293902911,596066939,277172788,1074100810,730139228,948261481,931633788,638413514,126567116,219892439,344236611,126438054,755333710,679826010,696560230]
private def extsB30 : Array Nat := #[830777926,227107484,772090450,445205159,847548999,529164955,327776927,42558117,201947816,1201574606,740201168,572222165,867300054,4530905,503497161,771932647,8557038,461539795,310546898,1149405670,125997557,126011898,386247226,268800615,369279476,478890688,269189830,915241672,42758859,203942616,126163558,8723054]
private def extsB31 : Array Nat := #[663198339,529298089,663583418,361450172,564652752,646242860,512039484,780821146,201792050,889504339,185039498,730122844,50940577,117754466,822692515,1082493515,981957246,462111407,286028465,1016810190,504840893,328950481,227127964,948261481,1099590309,1117221550,814578358,455105231,151878346,840981205,554257048,696871584]
private def extsB32 : Array Nat := #[1007313575,428436136,731028165,119141065,883571411,111667924,163007190,219892439,4987609,201511351,386048464,545434093,42107387,411372095,1015206343,1082460747,637864514,318951911,528667124,84495008,8997537,748201,579873465,17525435,806365884,909044432,478335438,654920349,864635558,1049324205,906717876,797977269]
private def extsB33 : Array Nat := #[3074765,964862400,1091257024,135090882,42681035,60508888,1158365886,109789897,236669654,336863937,152294090,67559990,923089515,1184092842,294900419,612717152,1090867809,369805986,50680420,671795875,1200870079,939854429,185256604,881511071,488663762,706781909,340531929,755790505,244939448,101425849,362234556,605649584]
private def extsB34 : Array Nat := #[504079037,295271107,260862667,764179124,822899393,881166945,1133277870,353845941,789344960,956664406,595954263,386224698,830923334,755655321,965038663,663054937,596210335,789209761,369717922,822764195,892465874,900854483,60508888,4532953,872866393,50940577,629885623,269189830,622281416,261366475,268620282,554257048]
private def extsB35 : Array Nat := #[940133027,773276330,244032184,504986301,193268322,102333113,9134778,1074053706,931633788,462111407,286028465,1016810190,889930439,537686732,219892439,679826010,730139228,101028413,671457861,948261481,1099614885,931818139,227127964,160002720,1007313575,428436136,1117221550,26866354,1068120787,338817748,1101980373,163007190]
private def extsB36 : Array Nat := #[4987609,411220440,511867388,185158300,294281893,605649584,1175464637,848892611,370109131,1124682398,822764195,614038196,990866108,337187521,890251975,746920494,855939641,587700854,1191360985,780917423,84624058,1040929477,236180168,42277456,453333617,260526725,746768830,361075294,169087659,1049891501,864905907,160121513]
private def extsB37 : Array Nat := #[545997486,396053199,411394623,252019262,159566263,470127183,327606889,679991945,244568760,453726911,747324087,974543558,763724337,478491231,17119844,319218287,722029209,906584727,596273823,9095841,587885220,713691815,1184582350,513843920,783413971,5745369,596271775,1184463530,923757240,202646206,1201095359,763693617]
private def extsB38 : Array Nat := #[1032264293,831791789,1117354670,411800259,1041711813,278360754,60420804,194607817,1125774028,285397473,612717152,17140324,822614647,151364162,169472683,1016722100,488075957,1183167051,9126586,1099723463,136006356,342571,445127291,369707682,1026484949,1116058199,344304195,822702755,1663657,1033542346,77464271,304128720]
private def extsB39 : Array Nat := #[622545618,22522585,981635524,981649865,310544850,1073910227,1149405670,126011898,453665433,1024090780,1669801,1116449454,26690226,344695478,1040867994,1007313575,102333113,294363843,731480773,269959878,822692515,923636408,227375805,1159299774,839598783,336153252,781023919,873304762,60046020,1149977287,771932647,805628507]
private def extsB40 : Array Nat := #[939835997,923071083,1065851521,143350455,135033538,260784843,386230842,260405839,268773991,470260358,8723054,537369224,537686732,219892439,352676396,235229756,914809417,713519732,109369924,285895320,1082751647,738814625,42625701,428501672,1151359694,563901136,253446866,840981205,615641814,332901081,545442283,545427949]
private def extsB41 : Array Nat := #[8557038,293769664,251822543,386046416,151157210,554257048,822692515,1082897066,923507384,1175171773,1091279552,344121820,671466053,1174766194,369584774,117770850,638028426,445373101,613145268,487418549,18707149,462111407,663583418,1149977287,915241672,111667924,713380399,595890775,528962163,293902911,92883613,730122844]
private def extsB42 : Array Nat := #[50940577,386255418,25496115,310712897,286096049,537754316,615932630,17386135,151308866,126442150,1201574606,514978512,270107334,1086554835,1026489045,11662040,931818139,185172636,562657952,1099590309,201947816,965913283,118987465,229571279,941527767,4987609,453665433,227173020,754345,1024629418,597250734,26835634]
private def extsB43 : Array Nat := #[999781046,729989617,160064160,101982905,84646586,51071675,268886631,554531500,462897839,286028465,478923456,135033538,270136006,42758859,1183142475,923071083,176691828,92609072,134716039,671539781,1174768242,352692780,235346492,948261481,731478725,864346709,1200253592,428438184,622295752,253446866,590475988,572213973]
private def extsB44 : Array Nat := #[867300054,584559321,92883613,50940577,629908151,789293760,270107334,622281416,370768587,889533011,319138415,554257048,537551523,1082897066,244028088,1176138429,445012550,847548999,1032127077,252154489,151493245,621095497,730139228,445373101,613145268,487418549,18707149,17386135,529232553,9134778,975915728,268808807]
private def extsB45 : Array Nat := #[462111407,731028165,889930439,126442150,286096049,126571212,545561169,595890775,293784024,713380399,310712897,931818139,293902911,25496115,528962163,151308866,117891682,42474117,1201574606,344679094,229571279,177380025,1085919955,638833354,1102525141,941527767,268921481,185172636,302650016,201947816,965845699,936880857]
private def extsB46 : Array Nat := #[680599,160064160,68842168,177894073,10048186,51991227,722430636,932145839,403391153,218841779,144270007,830634448,1024957098,1108175549,672387774,941193919,822454829,948095479,461738605,445895341,1134009006,731478725,269591238,1090820705,948214377,470444712,93917890,236524232,260823755,595933783,352836219,528857678]
private def extsB47 : Array Nat := #[545710673,914731593,92623408,981815860,285919896,1082473035,772203090,738679416,512187004,76110492,982209202,1099516581,76274352,596214431,1741481,35558093,623594194,137054932,958231253,362713814,734755545,436888217,529117851,161118889,1184463530,1117385390,25934514,488075957,118076070,470442664,1159297726,60256964]
private def extsB48 : Array Nat := #[186284745,1125774028,1016722100,957117121,1099723463,639072970,17459863,50940577,67998392,177699513,873939642,319505083,1049391789,1041887941,973894342,369707682,42625701,379011760,504206013,260784843,503640675,453306993,42441349,151364162,622545618,612686432,1065687659,320887508,169560792,332901081,293784024,545442283]
private def extsB49 : Array Nat := #[8557038,444783068,671470149,1158308504,671769251,1082897066,923507384,1175171773,1091279552,1040681602,445348525,76382896,764246708,797803189,19413709,545593937,1116009047,1149977287,915241672,126442150,286096049,537754316,419881523,134572597,201710130,965014087,227023493,755729065,898325174,456245967,102335161,731028165]
private def extsB50 : Array Nat := #[1085919955,1074100810,830988921,965913283,193389154,1126193870,629908151,11662040,151308866,780823194,931818139,386556573,562657952,50940577,514978512,842121941,404773591,4535001,118076070,169296555,831791789,379157168,1016722100,647582389,596226719,1184463530,68809400,1108955837,202646206,1201095359,1117354670,177861305]
private def extsB51 : Array Nat := #[966349507,1041711813,421089970,60244676,194607817,1125774028,1124524648,67559990,285567547,176611901,1015472689,478505567,151364162,1032264293,75860542,84249198,437023419,1099723463,136006356,1025376981,17308289,1007164040,822702755,1743529,77464271,622545618,4545241,260655773,118049446,571949739,831212205,218860211]
private def extsB52 : Array Nat := #[1015761588,798442165,847858335,1032407715,1024934570,67865272,562776766,840385215,789269184,461687405,8702574,394762888,679975561,553962040,17091172,336042615,134716039,965298855,1133986478,101419705,948652742,587520588,814013036,663018073,319085167,67574326,218569271,436832921,143071832,34019934,319392420,101128765]
private def extsB53 : Array Nat := #[440535759,245064406,219898583,68903640,307690201,529107611,243950240,67744417,766633,102322873,17937083,361474748,185232028,1183568554,546013870,25909938,999129782,378706608,295271107,109789897,152519370,260862667,722305708,311261873,218856115,520977079,1042823886,923130475,50819716,939893341,679848538,118123174]
private def extsB54 : Array Nat := #[445815469,1016693428,67490358,570759792,218784414,294085241,1015507581,1157962309,277318261,419920510,562920126,479675072,146170577,386224698,814029420,923368099,839752383,490867410,1177172691,480271062,732996311,203447000,5745369,608919,352930470,211239595,831232685,77167280,218866355,907508404,344541848,1082739359]
private def extsB55 : Array Nat := #[67871416,228162237,562797246,454509247,1092057792,235211324,1006963284,1074221690,872895106,822397485,92588592,587700854,319265409,470092367,1141181029,252138105,503796352,763828785,478616159,369724066,520559150,805771867,134843044,268810855,537246312,42570405,144145079,35093180,765162195,479949526,335862358,134535733]
private def extsB56 : Array Nat := #[14088921,260682397,118076070,210483883,1049735853,907129524,487307957,3787469,579148335,1149573716,805640795,1040521820,84568736,9071265,1735337,924490424,177722041,18512571,362271420,1184494250,227848893,562852542,1201271487,789344960,8575482,578996705,344304195,1183158859,805489137,554019384,1199936093,1040355823]
private def extsB57 : Array Nat := #[293970495,1149407718,151364162,805474800,336032375,117938816,260545157,1117354670,730694341,377868906,847714887,1032264293,77222576,302873284,512588488,589839060,1007518407,717359831,1116170868,663380635,873095844,8905347,848140995,1032690378,471882454,195058392,340531929,763693617,486869581,1032264293,814160492,25791142]
private def extsB58 : Array Nat := #[528933454,805757531,17308289,101194370,277154356,537201256,342571,369707682,336224932,688624300,839625407,1192909505,629754522,596271775,411800259,1040952005,520464942,260418127,822458925,545634897,627351,772127314,1007008340,160010912,1152314062,599700177,339653332,1026484949,81197785,218270154,310544850,646289964]
private def extsB59 : Array Nat := #[419797555,772237941,545745531,1149405670,335710700,663067225,436574831,243755649,101149314,705008181,478489183,193303138,503655011,1158113920,940010119,293939775,914723401,268773991,377852522,830958201,730294921,151308866,965024327,587536972,1032116837,554146422,822581879,260729501,310987430,379159216,520407598,142924376]
private def extsB60 : Array Nat := #[126163558,948247145,285710970,537369224,336153252,42625701,916030152,964872647,948095479,42119675,369781410,554531500,336282305,706314946,428501672,311116465,194609865,537754316,1118300878,715647703,291033817,1015360049,688204344,1124412008,461711981,1027199701,70898392,646287916,495295031,285579835,101028413,998738558]
private def extsB61 : Array Nat := #[814189183,597375662,705010229,478515807,193303138,436574831,1200065153,940018311,228276925,252006974,151308866,486888013,814008940,554146422,822581879,621207,260668061,604754608,730122844,939838045,1090867809,948261481,721918584,931633788,201947816,973853382,42129908,528863822,310546898,461539795,310561272,511873532]
private def extsB62 : Array Nat := #[612536776,50514382,50500073,335710700,914725449,730303113,763730481,151489149,537369224,950528718,254274258,111667924,715647703,38382297,663198339,444977734,1074100810,461732461,587940524,1149977287,335903318,227123868,596222623,92740144,277289524,772203090,478601823,143231640,235346492,487004749,545710673,268886631]
private def extsB63 : Array Nat := #[629770906,344250947,1032120933,814008940,554146422,680599,126438054,353860277,520407598,142924376,805628507,285710970,336153252,42623653,622295752,369779362,689390252,17537723,135756482,160064160,404177585,26704562,109812425,528865870,260430415,579443359,513503952,798716629,72809177,952240846,725691087,432089816]
private def extsB64 : Array Nat := #[822458925,763814449,486990413,545634897,1032174181,814070380,627351,25793190,528933454,772127314,1007008340,805757531,160010912,277275188,537322088,310909562,117971584,344613528,898261658,689525420,463033007,638214818,151675557,228151997,412701379,92645936,478521951,235252284,268806759,260418127,520464942,826340049]
private def extsB65 : Array Nat := #[776008402,1010889427,549515988,281438937,465451,34019934,1015472689,797368909,1032264293,814160492,25791142,981918260,1124524648,528851534,805675611,319255169,92629552,478505567,596226719,1116365466,723079852,932795055,956981922,1099588261,966349507,822467117,545643089,17406615,772135506,1007016532,84515488,893301458]
private def extsB66 : Array Nat := #[1086239443,339653332,231258841,729989617,50514382,126011898,444783068,671470149,444977734,227123868,487004749,520407598,8723054,285710970,537369224,336153252,681212613,689390252,404177585,336282305,1077015250,615932630,715647703,802734809,537754316,964858304,587385304,8557038,948081142,126011898,797086205,914723401]
private def extsB67 : Array Nat := #[377852522,33737150,964872647,570593739,587370956,33722864,520458798,1015386673,58888657,813877723,813863389,125997557,948095479,151360066,461738605,218280394,218499639,654707285,453671577,1006809574,889588307,1007028820,243956384,965024327,587536972,570759792,260729501,605199024,764582580,59054656,126163558,948247145]
private def extsB68 : Array Nat := #[42625701,781359791,621976264,1186583246,1027199701,674878167,70898392,5559001,218786462,747805367,638753482,42695371,369195,344302147,25653877,596079227,554017336,17146468,822571639,92762759,461742701,8757870,59208328,730296969,520729245,311014054,445364909,764132020,37341901,579449503,805941923,202095294]
private def extsB69 : Array Nat := #[478919360,146393809,293972543,42314320,151366210,109423172,75868734,226863715,67492406,218487351,210344601,285596219,101046845,277453467,142989912,33938014,134847140,498715347,247057110,221891287,70896344,307690201,588094124,814586550,194462409,471286475,163711702,54659800,215577305,260729501,369781410,42625701]
private def extsB70 : Array Nat := #[470444712,77232816,739932866,513440456,186284745,42695371,130339533,1078252242,591712980,616878806,688230968,1032264293,25791142,211499691,143071832,1124438632,319392420,303774404]
private def extsTable : Array (Array Nat) := #[extsB0,extsB1,extsB2,extsB3,extsB4,extsB5,extsB6,extsB7,extsB8,extsB9,extsB10,extsB11,extsB12,extsB13,extsB14,extsB15,extsB16,extsB17,extsB18,extsB19,extsB20,extsB21,extsB22,extsB23,extsB24,extsB25,extsB26,extsB27,extsB28,extsB29,extsB30,extsB31,extsB32,extsB33,extsB34,extsB35,extsB36,extsB37,extsB38,extsB39,extsB40,extsB41,extsB42,extsB43,extsB44,extsB45,extsB46,extsB47,extsB48,extsB49,extsB50,extsB51,extsB52,extsB53,extsB54,extsB55,extsB56,extsB57,extsB58,extsB59,extsB60,extsB61,extsB62,extsB63,extsB64,extsB65,extsB66,extsB67,extsB68,extsB69,extsB70]
def exts (i : Nat) : Nat := (extsTable[i/32]!)[i%32]!
private def startsOverB0 : Array Nat := #[0,237,447,622,790,939,1158,1312,1453,1583,1711,1844,2061,2178,2288,2403,2501,2595,2691,2813,2909,3004,3113,3197,3291,3377,3493,3583,3690,3777,3853,3962]
private def startsOverB1 : Array Nat := #[4045,4103,4202,4265,4352,4412,4462,4516,4573,4629,4686,4722,4752,4812,4849,4872,4887,4888]
private def startsOverTable : Array (Array Nat) := #[startsOverB0,startsOverB1]
def startsOver (i : Nat) : Nat := (startsOverTable[i/32]!)[i%32]!
private def startsExtraB0 : Array Nat := #[0,0,61,118,165,209,322,378,420,465,527,580,649,687,745,807,857,912,974,1033,1083,1112,1153,1210,1250,1310,1370,1410,1472,1525,1566,1618]
private def startsExtraB1 : Array Nat := #[1659,1702,1751,1793,1851,1885,1947,2007,2048,2084,2115,2137,2188,2230,2237,2258,2258,2258]
private def startsExtraTable : Array (Array Nat) := #[startsExtraB0,startsExtraB1]
def startsExtra (i : Nat) : Nat := (startsExtraTable[i/32]!)[i%32]!
private def revRowsB0 : Array Nat := #[2198837046507322820568735172000296395497111703639031655214989481031415655662858396551046983622524691475603520,2162696249821217618215137618282995761805161463866772981130851447475637340800225444037497314043350055714587078,2124316537260600494142276225985762821656081576118724669733229319233394180619356984075646928639684086222827521,2198800641771726253250707320465942554279185016594663310005348741055887738735616140179568159580534921302900994,2162705622156956155524194547248590888843364879373837413591619490913386944305282635826338639645551936198148290,1751495602169449824780452133844769261384469437309448667367654039628175301793608141872959730519764771391422465,2049769017687769198774296095871862879950363614674724004859160418165910413665732485389370083724623815345475975,2162659845085621050897109766748641920587234776822404635921210707500109423872983187666018490001360285541884552,2198810031874538205786337851733305993786506436760379594905215505798982709291159549457813515004465490815640136,1715354805483344622426854580127468627692519200776777090509640401564992565131648333805728082158219725487513991,2088148730248386322847157488169095820099443502422772316256782546407451147321330618454388234966394114945114956,2124261932310280447055910984613154715288115871713679142613971431610607091347220736304312767823281456694694211,2088185117216383693514290327342421074640151814892582745180871313328258436370956336279045191942337167630536835,1676975092922727498353993187830235687543439309789141874980332026933548879362571463694417987818059670813167680,1975239118337709010085950063352810578613197282388068326106013607169353334563758778745274388559557359545897092,2162669217421359588268829423501870164537016355595968494234636225938324839775538840543397839612222205546471744,1751459197433853257462424282310415420166542750265080322158013302462541279881224401334981705059951840900944004,1304154157831576828992066716327021504527178377407542354299124968954085602884371457492032825650845255046549635,1715364177819083159735809129730843131986073819471931100523090420239297245396045951445411734776632419853275460,2013628221001663996420698542154562246258413374902465330775022384609788926674071089124768462874129532607591181,2049705029364047540089040521009871174485745384418284613124256769149514923720683221674452257112448407058281161,2013655235633397048354468337086480609433124061406872803171889749674944929377962466961166477364705736372285961,1602427573349896202986013057716335745837721348345932124924921847642319308253556609437569121868834222960587206,1900691598764877714717969933238910636907479320944067661231944706101869567610134280058997543644497088668545546,2198773627138941638530972727986585269480157912982510675548232240823920604761415754174872714971135760163963590,1715318400747748055108826728593114786474592513732408745299999664399358543219264593267750056698406794997035530,1268013361145471626638484461127247148451661631637387012652501139844760569303868978784122309383328211690631689,1751468587536665209997967732733084514545648867620989517048076244078750713463380194436207742229573977018757834,2088102942139388143930239303145358379784864289527010106431496045039017256246435451384908089207300857216156686,2124280150291551560626515861477365528579478683274669652896233942145309951827300222046484204705313261532529614,1640807285910513327058874450013568685986801239333567340454230222273419817968228610745497577768619405767672589,1975220915969910726411270455638725378776336080712071737486647883310065473380912190369985677465974863948955845]
private def revRowsB1 : Array Nat := #[2088130507959914038740566105794329195370103950296632619328276518401011772540835065260937990202006732983775489,1676920487972407451267627946457627581175473605384096154766647502342654613353330208144149640622463753550037189,1229633648584854502565607770313399793388892114926196183418746373534173824973021677063634301272972339228983490,1640843672878510697725904909825585180485604620029637053619285659928883381981406549648261505397249836046352645,1939034924356446161973037722428118249679070272085899030364715574215734146730267298179943166399746031654094034,1939107698293492466124497182854715701421424260743574694038673203172185170469049759541468194209248434056609797,1527897673999836014297667025197283444500555016058485531353127824194902014167474469048468775057698322500563202,1304117753095980261674038864792667663309264959711924247295008169459939723446459897736075347759962097707134981,1715327773083486592480444005984122407679738565042812419371631092935723283340774336944491482312232462352662721,1268022733481210163947526091575315997873431553142348112675754978836056891526795696767324481673872499769094405,2013564232677942337735442967292570540793795144646025939040118735593736608858045275349172227448492174172279887,2049759645350979098616611641571195714376265618793414984485485764560883615207442614353150673813388057092608911,1566286776663791000632415503999035112145771111813260548066908209578450478618965123858776201146200763976979276,1900664013023677819444399992035441837973965593416677207996933220848973305754374675740125166755141814312542795,2013573605014732437892937965122224454313738789432644108470659270975127914455647551877635754208861346136363655,1602363585026174544300757482854344040373103118088701625324075036695308050256370909896024959599939576777433675,1155086129012023207197627643934489482122045353065692125803573349958717777525713901329385402860912597363630664,1566313791295524052566082923304634345717448066126632804050541251991343398650119758852982758356784110775329419,1864514415109723835546578776413584675838040144565592044882955412418071926083007768850323394307481449316570259,1864577816710505820964675192598775236214396507257864752029691639518871663476055890223589479631617002798358923,1453350154427004718929686895083383502794837054615275781297717644903672443058459614791619909108472874647982728,1267976956409875059320456609592893307233748213941768905648384340350614689865957419028164831492445054351217035,1751432182801068642742602608986363790239313613191870835896616916775176751408108579935287489765174019518145095,1304127143198792214209684694577557380433006604530993626426865198168105937794803084204438510344443646791684747,1826134695818644807751099469635627096105108833648673131742230043640777399983596765429136884189061556701565840,2124216724193760037683344587314480528423792752118522164690614993398036746676223013009172693956336820257088588,1640761497801515148141956264989831245672222026437014215857427198752011980122300301150773270614309792594580368,1193465841572640331270504334748336837184814869776882955037328116269663772327426661143324006692789267850138511,1676938705953678564838145746212133679777492313717985267479331836141553906186498272444310633629483123614995536,1939016721988647878298358114714033049842209070409902441745349850356446285547420709804654531381241050656744852,1939089495925694182512480302928263618496141222334077531271964954313363121683701632254717507124325979037388868,1527879471632037730622987417483198244663693814382488942733762103145508047999486396506680862546292664422113603]
private def revRowsB2 : Array Nat := #[1229579043634534455479242528939879824372547067311915769729691071755484632356623573996325173061691544831008836,1640789063622041042952180688276581438567177412224452234291320087813841791544128431113113522641234524264747136,1193502228540637701937621871670058046372962353700054258866388367629038080724621029267032564575625420636692804,1975166344400662705871638418667566757905110779369202385636264384988801260777591896887449588588281864074896724,1491693480018573166184754684272591115566428008996694054609305446895448421906748734635186199986180033315955859,1080556229661963018509281607680447550400359073676515529617590873210958535215982551868766978251828527555678528,1491766253955619470336111765337879807321228318361604692303136252188241691517557842361766397403378639111725123,1267986328745613596692160967828595273567096298713229431524295654342376824486382598099905027791649381950705731,1826116493450846524076419861921541896268247631972676543122864319781489538800750177053848249170556576811254737,2049678014732314488155081269606939559256880346819186289784255285860723679441529455664156783872655510621975565,1566222788340069341947159929137043406681152881556030048466061398632125313594401117862016796848732323880420305,1118945332325918004844045388734715126046528607295536784156949520849049823101608188860965565503626787904881614,1602418201013106102828241526306875728277023114275691220575527075831482959690085679355340038170814081020511249,1864478012527202072103561778861245210851139925528918274353972540911165638159030533768918669622432367612868053,1864532592980512581664852162256158877439776061470089020414347706887479263598514118871415271131180592189977034,1453322568685804823656116953879914703861323327087094413291189637498161484902527098258556181523768487649510089,1155022140688301548512372065336596506192906742092946767782603699715871063522645423280981744037747417501172170,1566232160676859442104552547604476920133542413436889250929187933995690927721922065262592538646669186860102150,1118972346957651056777799885149107211604805799797840924116302681467752293237943882901181796500994518390440650,1900645839460090243861734198761396943701897714887947717225516207404374924157734289194116057696356659634976021,1417172970771850839758295738258057541725397881476387262221983434200479082557485247748464823363761391525262546,1006008710089131723141301481301537239133512311816011472002417849635502487768674776134518079839768785690325702,1417236372372632825176289778816928972553071764458600442734391844250701708186271051566487650362912913840701897,1304090738463195646954319570830836656126671350101874945275405873674425870754389985537019056462220528973296073,1789975705648278029351782440560796836846970999684607877491578102972791278694617592814587532548672764108174614,1790020913765324220117047051926670495158031346393876241172074392092987805390868376840287167564225331034915601,1378793251480771811962816431480099961992466567319881251855145179256325879961500316543495155415592500460844046,1193420053463642152353586145989609989054107888722799903701296968311001121031984496095219187490154480080843537,1676875279855887041894974468314259271805678614404307852534484762957025887585907207953618610832181507743351757,1229597261615805569049862708056606545664850050628780291676779512007522576833396264735419976431708414437553169,1975148142032864422259621538741114674979827740959705222869556136129979211992243769600699050193918899852494290,1491675277650774882510075076558505915729566807320697465989939725846054455738760662093398214859292399040279830]
private def revRowsB3 : Array Nat := #[1080538027294164734834601999966362350563511141349269179203749089833052711522466660108999613309352641521254657,1491748051587821186724094885411427724395958549300857767741951941000907785206681895857036257887385956136529922,1193447619284168047163897650121054304454535145894869246443996158545889313550237902952950395440416821120090114,1044352035680700170396384569007359489387171801516435196687888434499425370528938154217043919736758805861070101,1527824900062789710083268303402335131725854571888943527714847372592778209399781316469307308338860636620010966,1044424809617746474547828727182352673208586052032021897550250469213790371121273532664960783901519602066391233,1789957503280479745677102832846711637010109798008611288872212379113503417511771004439298897530167784217863511,1790002711397525936505030172000218412232748307984379078405366143234165756605520249553536629169862368976245584,1378775049112973528288136823766014762155605365643884663235779458206931913793512244001707170288704865128473679,1118881344002196346158789810136822150117389996322791426135979870606546029942137954418025073465349764277134160,1602336570394441492366711150606718302693117461585947667454173757835144395789266292220165060489272951018689420,1155076756675233107039958488151348594164380851186486437867412900800144511634979714089347776442885312389899344,1900609432571418872731358221033573705812915335660369347963196428592666144757550212255683140110237590217381267,1417136568189329076315278740705718076738497662439713298598573925726167789210861478804641741093714930326119767,1005981124347931827867731536363079032383870816130300177256661717793439142688488509393656184285408514191417991,1417191148642639585876466744739323205962323550513294784379819787182756921384475530006515273892820618731884936,1118890716338986446316269509448949786020900147107306263129006201541484054257609753484165241134160356579254664,969831526433977843969925622993737778248885539035089025807509839078811421303119681934685478547596325915813204,1453304395122217248073364083497077180225385372446649480811042612282707262903368723380336712880191594025526679,969894928034759829388006740661401838440429498129808562800164783052504583634596386299110015826888699820139079,1826107129998644694333470881053855974534985309588611842319156499867061856923040731849100147612675348892837015,1342634261310405033563499402405269702734328736595403094830617634080592416029586064459708349598183921753609620,931451807142898816174431017698253920953871986597042470055330477595888918934696625419174726890070943276520524,1342679469427451224328661638144824454119436765671037459372259690432550844364064685715966739038703773850592079,1229533835518014046106691430158732137693036351314311961960415916670020611461772057719483792239190443121775439,1044333833312901886721704961293274289550323869189188846274046651121519546835422262457276406103723429029827735,1527806697694991426471251423475883048800584802828196603153663061405444303088905369964577241438349929842042195,1044406607249948190935811847255900590283316282971274972989066160836350359825256101993731442967703756609687680,1080483455724916714294985265246807997613212308799738551959437245272492484576262752924550341925294638281872791,1826088927630846410721454001127403891609702271179114679552448251008239808137692604562349609218312386834166998,1342616058942606749888819794691184502897467534919406506211251913031198449861597991917920364471296286421239253,931433604775100532499751409984168721117024054269796119641488694217983095241180733659407213257035564281545741]
private def revRowsB4 : Array Nat := #[1342661267059652940716644758218372371194166996610290534811075379245216938053188739211236672138193068129317646,1154995126056568496578428112451191168580475198495951776880116420873533100525622134733009629889513100726829838,969795123851456080526908625440486450613605976789180368708729553417064455745575720780082292078918713226118358,1453267988233545876942988105768342079688023650009836418073352056283562811292264454231123691095441373117379858,969849704304766590088183706583796071849681284183711989674076203831945100532627952524946288661447292068852230,1005962950784344252285081045341550046112743109357444698150070634065114419377846202278478141936471536234218966,895292816972532037775129287140949939312167646635080548242192741374356330213273140257491364522791611219129810,1378765685660771698545100765789536211112824219628289295730731607160825771106727807646883162537283038358357205,895338025089578228540378599989297320006794499342245579485174826048099324341968236830325010265234717609870285,1080465253357118430682968385320355914687942539738991627398252936895052473280245322253320924916401278225577173,895274614604733754100449679426864739475319714307834197828350957996450506519757248497723850889756232224155027,1378747483292973414933083885863084128187554450567542371169547295973491864795851861142153095636772332637082772,895319822721779944928361720062845237081524730281498654923990517670659313045950806159095593256341356446536588,1005926543895672881154705067612814945575381386920631442317953441098564962344095399266846762566723935830631572,931424241322898702756817727634009077000181956539084513069771138268626908441696279292003979586794196003792211,931406038955100419144800847707556994074912187478337588508586829891186897145678848620774562577900834840458514]
private def revRowsTable : Array (Array Nat) := #[revRowsB0,revRowsB1,revRowsB2,revRowsB3,revRowsB4]
def revRows (i : Nat) : Nat := (revRowsTable[i/32]!)[i%32]!
def embedDirect (s a b j o : Nat) : Bool :=
  j<2919 && o<144 && permute o s == mask j &&
    fits (permute o (s &&& a)) (one j) (two j) && fits (permute o (s &&& b)) (one j) (two j)

def getUp (a z : Nat) : Nat :=
  let m := testMask (z%2048)
  let t := (z>>>11)%64
  let j := (z>>>17)%4096
  let o := z>>>29
  let allowed := if j=0 then max 1 (baseScore full (R a) m 43) else
    if embedDirect full (R a) m (j-1) o then wt (j-1) else 0
  if t≤allowed then t else 0

def getB (a z : Nat) : Nat :=
  let m := testMask (z%2048)
  let j := ((z>>>11)%4096)-1
  let o := z>>>23
  if embedDirect m (R a) 0 j o then wt j else 0


namespace Local
open PCX150.Sparse (TestTree Valid box leaves)

theorem allTestSmall : ∀ k : Fin 2048, testMask k.val < 2^60 := by decide +kernel
theorem dataSmall (z : Nat) : testMask (z%2048) < 2^60 := allTestSmall ⟨_,Nat.mod_lt _ (by decide)⟩

theorem checkedEmbed {s a b j o : Nat} (range : s<2^60) (ok : embedDirect s a b j o = true) :
    ∃ id : NodeID, id.val=j ∧ Nonempty (Sparse.Embed geo (item id) (triple s a b)) := by
  unfold embedDirect at ok
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨jt,ot⟩,same⟩,f⟩,g⟩ := ok
  exact ⟨⟨j,jt⟩,rfl,embedded ⟨o,ot⟩ range same f g⟩

theorem boardPaid (checks : ∀ i : NodeID, nodeOK i.val=true) (s a b j o : Nat) (range : s<2^60)
    (ok : embedDirect s a b j o=true) (t : TestTree) (valid : Sparse.admissible geo (triple s a b) t) :
    wt j ≤ leaves t := by
  obtain ⟨id,eq,⟨f⟩⟩ := checkedEmbed range ok
  have ready := bankSound checks id _ (Sparse.embedTree f valid)
  simpa only [Sparse.sameLeaves,eq] using ready

theorem rootRaw (t : TestTree) (v : SmallChart.rawValid geo (treeRaw t) (bits full)) : 43≤leaves t := by
  have same : Chart48.node 47 = bits full := by
    change bits rm[47]! = bits full
    have num : rm[47]! = full := by decide +kernel
    rw [num]
  have good : SmallChart.rawValid geo (treeRaw t) (SmallChart.acted (SmallChart.Aut.unit geo) (chart.state chart.root)) := by
    change SmallChart.rawValid geo (treeRaw t) (Chart48.node 47)
    rwa [same]
  have cost := SmallChart.rawLower chart (treeRaw t) chart.root (SmallChart.Aut.unit _) good
  rwa [Chart48.rootWeight,rawLeaves] at cost

theorem upperPaid (checks : ∀ i : NodeID, nodeOK i.val=true) (a z : Nat) (t : TestTree)
    (valid : Sparse.admissible geo (triple full (R a) (testMask (z%2048))) t) : getUp a z ≤ leaves t := by
  let m := testMask (z%2048)
  let k := (z>>>11)%64
  let j := (z>>>17)%4096
  let o := z>>>29
  have fullSize : full<2^60 := by decide +kernel
  have cap (w : Nat) (bound : w≤leaves t) : (if k≤w then k else 0)≤leaves t := by
    split
    · rename_i h
      exact h.trans bound
    · exact Nat.zero_le _
  unfold getUp
  dsimp only
  by_cases jz : j=0
  · rw [if_pos jz]
    have p := scorePaid full (R a) m 43 fullSize t valid (rootRaw t)
    exact cap _ p
  · rw [if_neg jz]
    by_cases ev : embedDirect full (R a) m (j-1) o=true
    · rw [if_pos ev]
      have p := boardPaid checks full (R a) m (j-1) o fullSize ev t valid
      exact cap _ p
    · rw [if_neg ev]
      exact cap 0 (Nat.zero_le _)

theorem middlePaid (checks : ∀ i : NodeID, nodeOK i.val=true) (a z : Nat) (t : TestTree)
    (valid : Sparse.admissible geo (triple (testMask (z%2048)) (R a) 0) t) :
    getB a z ≤ leaves t := by
  let m := testMask (z%2048)
  let j := ((z>>>11)%4096)-1
  let o := z>>>23
  unfold getB
  dsimp only
  by_cases ev : embedDirect m (R a) 0 j o=true
  · rw [if_pos ev]
    exact boardPaid checks _ _ _ _ _ (dataSmall z) ev t valid
  · rw [if_neg ev]
    exact Nat.zero_le _

end Local
end PCX150.Scalar

namespace PCX150.Scalar
open PCX150.Chart48 PCX150.SmallChart PCX150.Bands
def preID (a r : Nat) := (revRows a >>> (6*r))%64
def col (r : Nat) : Nat := (List.range 144).foldl
  (fun z o => z ||| (staticFlags (preID o r) <<< (49*o))) 0
def everyCol : Array Nat := Array.ofFn (fun r : Fin 60 => col r.val)

def meets (m : Nat) : Nat := (List.range 60).foldl
  (fun acc r => if m.testBit r then acc ||| everyCol[r]! else acc) 0
def sameMask (m : Nat) : Nat := (List.range 60).foldl
  (fun acc r => acc &&& (if m.testBit r then everyCol[r]! else big ^^^ everyCol[r]!)) big

structure CountVec where
  w0 : Nat := 0
  w1 : Nat := 0
  w2 : Nat := 0
  w3 : Nat := 0
  w4 : Nat := 0

def inc (v : CountVec) (x : Nat) : CountVec :=
  let c1 := v.w0 &&& x
  let c2 := v.w1 &&& c1
  let c3 := v.w2 &&& c2
  let c4 := v.w3 &&& c3
  ⟨v.w0 ^^^ x, v.w1 ^^^ c1,v.w2 ^^^ c2,v.w3 ^^^ c3,v.w4 ^^^ c4⟩

def thresh (v : CountVec) (k : Nat) : Nat :=
  let advance (i a z : Nat) := if k.testBit i then a &&& z else a ||| z
  if k ≥ 32 then 0 else advance 4 v.w4 (advance 3 v.w3 (advance 2 v.w2 (advance 1 v.w1 (advance 0 v.w0 big))))

def tally (m : Nat) := (List.range 22).foldl
  (fun acc l => inc acc (meets (m &&& tagMask l))) ({} : CountVec)

def weightGE (k : Nat) : Nat :=
  let first := (List.range 49).foldl (fun n i => if k ≤ weightR i then n ||| 2^i else n) 0
  first * (big / (2^49-1))

def packedExtras (a : Nat) : Nat :=
  (List.range (startsExtra (a+1)-startsExtra a)).foldl (fun h i =>
    let z := exts (startsExtra a+i)
    h ||| (sameMask (testMask (z%2048)) <<< (7056*getB a z))) 0

def closeWord : Nat → Nat → Nat
  | 0,t => t
  | n+1,t =>
    let w := closeWord n t
    w ||| (w >>> (7056*2^n))

def extraWord (a k : Nat) := (closeWord 6 (packedExtras a) >>> (7056*k)) % 2^7056

def rowQual (a : Nat) : Array Nat :=
  let r := tally full
  let f := tally (full ^^^ R a)
  let hom := big ^^^ thresh (tally (R a)) 2
  Array.ofFn (fun k : Fin 43 => if k.val≤1 then big else
    (thresh r k.val &&& thresh f (k.val-1)) ||| (hom &&& weightGE k.val) ||| extraWord a k.val)

def covered (a : Nat) : Bool :=
  let qs := rowQual a
  let seen := (List.range (startsOver (a+1)-startsOver a)).foldl (fun acc i =>
    let z := ove (startsOver a+i)
    let m := testMask (z%2048)
    let t := getUp a z
    acc ||| ((big ^^^ meets (full ^^^ m)) &&& qs[41 - weightR a - t]!)) 0
  seen == big
def atCount (v : CountVec) (i : Nat) : Nat :=
  (v.w0.testBit i).toNat+2*(v.w1.testBit i).toNat+4*(v.w2.testBit i).toNat+
    8*(v.w3.testBit i).toNat+16*(v.w4.testBit i).toNat

theorem countZero (i : Nat) : atCount {} i = 0 := by simp [atCount]

theorem countInc (v : CountVec) (x i : Nat) :
    atCount (inc v x) i = (atCount v i + (x.testBit i).toNat)%32 := by
  simp only [atCount,inc,Nat.testBit_and,Nat.testBit_xor]
  cases v.w0.testBit i <;> cases v.w1.testBit i <;> cases v.w2.testBit i <;>
    cases v.w3.testBit i <;> cases v.w4.testBit i <;> cases x.testBit i <;> decide

def compareBits (k : Nat) (a b c d e : Bool) : Bool :=
  let step (n : Nat) (u v : Bool) := if k.testBit n then u && v else u || v
  step 4 e (step 3 d (step 2 c (step 1 b (step 0 a true))))
theorem boolCmp : ∀ (k : Fin 32) (a b c d e : Bool),
    compareBits k.val a b c d e = true ↔ k.val ≤ a.toNat+2*b.toNat+4*c.toNat+8*d.toNat+16*e.toNat := by decide +kernel

theorem finiteCount (v : CountVec) (i : Nat) : atCount v i < 32 := by
  unfold atCount
  cases v.w0.testBit i <;> cases v.w1.testBit i <;> cases v.w2.testBit i <;>
    cases v.w3.testBit i <;> cases v.w4.testBit i <;> decide

theorem cmpGood (v : CountVec) (i k : Nat) (small : i < 7056) :
    (thresh v k).testBit i = true ↔ k ≤ atCount v i := by
  have base : big.testBit i = true := by
    rw [big,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact small
  by_cases outside : k≥32
  · simp [thresh,outside,show ¬ k ≤ atCount v i by have h := finiteCount v i; omega]
  · let f := fun (n a z : Nat) => if k.testBit n then a &&& z else a ||| z
    have step (n a z : Nat) : (f n a z).testBit i =
        (if k.testBit n then a.testBit i && z.testBit i else a.testBit i || z.testBit i) := by
      dsimp [f]
      split <;> simp [Nat.testBit_and,Nat.testBit_or]
    change ((if k≥32 then 0 else f 4 v.w4 (f 3 v.w3 (f 2 v.w2 (f 1 v.w1 (f 0 v.w0 big))))).testBit i = true) ↔ _
    rw [if_neg outside]
    simp only [step,base]
    exact boolCmp ⟨k,by omega⟩ _ _ _ _ _

theorem foldBits (xs : List Nat) (f : Nat → Nat) (i acc : Nat) :
    (xs.foldl (fun a e => a ||| f e) acc).testBit i = true ↔
      acc.testBit i = true ∨ ∃ j ∈ xs, (f j).testBit i = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,ih,Nat.testBit_or,Bool.or_eq_true]
    simp only [List.mem_cons]
    aesop

theorem foldCounts (xs : List Nat) (piece : Nat → Nat) (i : Nat) (v : CountVec)
    (small : atCount v i + xs.length < 32) :
    atCount (xs.foldl (fun x q => inc x (piece q)) v) i =
      atCount v i + (xs.filter (fun q => (piece q).testBit i)).length := by
  induction xs generalizing v with
  | nil => simp
  | cons a xs ih =>
    have low : atCount v i + ((piece a).testBit i).toNat < 32 := by
      cases h : (piece a).testBit i <;> simp_all <;> omega
    have add := countInc v (piece a) i
    rw [Nat.mod_eq_of_lt low] at add
    rw [List.foldl_cons,ih]
    · rw [add]
      cases h : (piece a).testBit i <;> simp [h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · rw [add]
      cases h : (piece a).testBit i <;> simp_all <;> omega


open PCX150.SmallChart (Sample)
abbrev Bank := Fin 49
def lane (b : Bank) (o : Chart48.ID) := 49*o.val+b.val
def active (b : Bank) (o : Chart48.ID) (r : Sample) : Bool :=
  (R b.val).testBit ((Chart48.orient o).s.symm r).val

theorem posLane (b : Bank) (o : Chart48.ID) : lane b o < 7056 := by
  unfold lane; have := b.isLt; have := o.isLt; omega
theorem liveWide (b : Bank) (o : Chart48.ID) : big.testBit (lane b o) = true := by
  rw [big,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
  exact posLane b o

theorem flagData : ∀ (r : Sample) (b : Bank),
    (staticFlags r.val).testBit b.val = (R b.val).testBit r.val := by decide +kernel
theorem flagSmall : ∀ r : Sample, staticFlags r.val < 2^49 := by decide +kernel
theorem indexData : ∀ (o : Chart48.ID) (r : Sample),
    preID o.val r.val = (Chart48.backward Chart48.words[o.val]! 9 r).val := by decide +kernel

theorem stripe (m : Nat) (i : Nat) (b : Bank) (o : Chart48.ID) (tiny : m<2^49) :
    (m <<< (49*i)).testBit (lane b o) = true ↔ i=o.val ∧ m.testBit b.val = true := by
  rw [Nat.testBit_shiftLeft]
  have lim := b.isLt
  unfold lane
  by_cases eq : i=o.val
  · subst i; simp
  · by_cases below : i<o.val
    · have bound : 49 ≤ 49*o.val+b.val-49*i := by omega
      have no := Nat.testBit_lt_two_pow (lt_of_lt_of_le tiny (Nat.pow_le_pow_right (by decide : 0 < 2) bound))
      simp [eq,show 49*i ≤ 49*o.val+b.val by omega,no]
    · simp [eq,show ¬49*i ≤ 49*o.val+b.val by omega]

theorem columnExact (b : Bank) (o : Chart48.ID) (r : Sample) :
    (col r.val).testBit (lane b o) = active b o r := by
  apply Bool.eq_iff_iff.mpr
  unfold col
  rw [foldBits]
  simp only [Nat.zero_testBit,Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨i,mem,h⟩
    let s : Chart48.ID := ⟨i,List.mem_range.mp mem⟩
    have val : preID i r.val = (Chart48.backward Chart48.words[s.val]! 9 r).val := indexData s r
    have sm : staticFlags (preID i r.val)<2^49 := by rw [val]; exact flagSmall _
    obtain ⟨eq,hit⟩ := (stripe _ i b o sm).1 h
    subst i
    have v := indexData o r
    rw [v,flagData] at hit
    simpa [active,Chart48.orient,Chart48.backApply] using hit
  · intro h
    refine ⟨o.val,List.mem_range.mpr o.isLt,?_⟩
    have v := indexData o r
    have sm : staticFlags (preID o.val r.val)<2^49 := by rw [v]; exact flagSmall _
    apply (stripe _ _ b o sm).2
    refine ⟨rfl,?_⟩
    rw [v,flagData]
    simpa [active,Chart48.orient,Chart48.backApply] using h

theorem colLookup (r : Sample) : everyCol[r.val]! = col r.val := by
  rw [getElem!_pos everyCol r.val (by simpa [everyCol] using r.isLt)]
  simp [everyCol]

theorem meeting (m : Nat) (b : Bank) (o : Chart48.ID) :
    (meets m).testBit (lane b o) = true ↔ ∃ r : Sample, m.testBit r.val = true ∧ active b o r = true := by
  have replace (ls : List Nat) (acc : Nat) :
      ls.foldl (fun z i => if m.testBit i then z ||| everyCol[i]! else z) acc =
      ls.foldl (fun z i => z ||| (if m.testBit i then everyCol[i]! else 0)) acc := by
    induction ls generalizing acc with
    | nil => rfl
    | cons a l ih => cases h : m.testBit a <;> simp [h,ih]
  unfold meets
  rw [replace,foldBits]
  constructor
  · rintro (no | ⟨i,mem,hit⟩)
    · simp at no
    · let r : Sample := ⟨i,List.mem_range.mp mem⟩
      cases hv : m.testBit i
      · simp [hv] at hit
      · refine ⟨r,hv,?_⟩
        rw [if_pos hv] at hit
        change (everyCol[r.val]!).testBit (lane b o) = true at hit
        rwa [colLookup,columnExact] at hit
  · rintro ⟨r,hm,h⟩
    right; refine ⟨r.val,List.mem_range.mpr r.isLt,?_⟩
    rw [if_pos hm,colLookup,columnExact]
    exact h

theorem upperMask (m : Nat) (b : Bank) (o : Chart48.ID)
    (h : (big ^^^ meets (full ^^^ m)).testBit (lane b o) = true) :
    ∀ r : Sample, active b o r = true → m.testBit r.val = true := by
  intro r hr
  by_contra bad
  have on : full.testBit r.val = true := by rw [full,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact r.isLt
  have conflict : (meets (full ^^^ m)).testBit (lane b o) = true := by
    apply (meeting _ _ _).2
    refine ⟨r,?_,hr⟩
    cases hb : m.testBit r.val <;> simp_all [Nat.testBit_xor]
  simp [Nat.testBit_xor,liveWide,conflict] at h


def domainMask (b : Bank) (o : ID) := permute o.val (R b.val)
theorem domainBit (b : Bank) (o : ID) (r : Sample) :
    (domainMask b o).testBit r.val = active b o r := actionBit _ _ _

theorem smallTag : ∀ l : Fin 22, tagMask l.val < 2^60 := by decide +kernel
theorem nonemptyWord (m : Nat) (small : m<2^60) :
    m ≠ 0 ↔ ∃ p : Sample, m.testBit p.val = true := by
  constructor
  · intro h
    by_contra no
    apply h
    apply Nat.eq_of_testBit_eq
    intro n
    by_cases ok : n<60
    · have dead : m.testBit n ≠ true := fun yes => no ⟨⟨n,ok⟩,yes⟩
      cases hm : m.testBit n <;> simp_all
    · have smallN := Nat.testBit_lt_two_pow (lt_of_lt_of_le small
          (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt ok)))
      simp [smallN]
  · rintro ⟨p,h⟩ e
    simp [e] at h

theorem tallyCell (m : Nat) (b : Bank) (o : ID) (l : Fin 22) :
    (meets (m &&& tagMask l.val)).testBit (lane b o) =
      ((m &&& domainMask b o) &&& tagMask l.val != 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [meeting]
  simp only [bne_iff_ne]
  rw [nonemptyWord _ (lt_of_le_of_lt Nat.and_le_right (smallTag l))]
  constructor
  · rintro ⟨r,hm,hb⟩
    have hh := Bool.and_eq_true_iff.mp (by simpa only [Nat.testBit_and] using hm)
    exact ⟨r,by simp [Nat.testBit_and,domainBit,hh.1,hh.2,hb]⟩
  · rintro ⟨r,hm⟩
    simp only [Nat.testBit_and,Bool.and_eq_true,domainBit] at hm
    exact ⟨r,by simp [Nat.testBit_and,hm.1.1,hm.2],hm.1.2⟩

theorem counted (m : Nat) (b : Bank) (o : ID) :
    atCount (tally m) (lane b o) = present (m &&& domainMask b o) := by
  let f := fun l : Nat => meets (m &&& tagMask l)
  let g := fun l : Nat => (m &&& domainMask b o) &&& tagMask l != 0
  have rows (ls : List Nat) (ok : ∀ l ∈ ls, l<22) (a : Nat) :
      ls.foldl (fun n k => if g k then n+1 else n) a =
        a + (ls.filter (fun k => (f k).testBit (lane b o))).length := by
    induction ls generalizing a with
    | nil => simp
    | cons k ks ih =>
      have eq : (f k).testBit (lane b o) = g k := tallyCell m b o ⟨k,ok k (by simp)⟩
      have sub := fun k hk => ok k (List.mem_cons_of_mem _ hk)
      cases h : g k <;> simp [List.foldl_cons,eq,h,ih sub,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  unfold tally present
  rw [foldCounts (List.range 22) f _ {} (by simp [countZero])]
  have v := rows (List.range 22) (fun _ h => List.mem_range.mp h) 0
  simpa [countZero,g,f] using v.symm

def priceStripe (k : Nat) := (List.range 49).foldl (fun n i => if k≤weightR i then n ||| 2^i else n) 0
def replicated (k : Nat) : Nat := (List.range 144).foldl (fun n o => n ||| (priceStripe k <<< (49*o))) 0
theorem priceEq : ∀ k : Fin 43, weightGE k.val = replicated k.val := by decide +kernel
theorem priceLow : ∀ k : Fin 43, priceStripe k.val < 2^49 := by decide +kernel
theorem priceEntry : ∀ (k : Fin 43) (b : Bank), (priceStripe k.val).testBit b.val = decide (k.val ≤ weightR b.val) := by decide +kernel
theorem projectedPrice (k : Fin 43) (b : Bank) (o : ID)
    (bit : (weightGE k.val).testBit (lane b o) = true) : k.val ≤ weightR b.val := by
  rw [priceEq,replicated,foldBits] at bit
  rcases bit with nope | ⟨i,mem,hit⟩
  · simp at nope
  · have ok := ((stripe _ i b o (priceLow k)).1 hit).2
    rwa [priceEntry,decide_eq_true_eq] at ok

theorem meetFixed {m : Nat} (b : Bank) (o : ID)
    (yes : (sameMask m).testBit (lane b o) = true) :
    ∀ p : Sample, m.testBit p.val = active b o p := by
  let band := fun i : Nat => if m.testBit i then everyCol[i]! else big ^^^ everyCol[i]!
  have all (ls : List Nat) (start : Nat) (h : (ls.foldl (fun t i => t &&& band i) start).testBit (lane b o) = true) :
      start.testBit (lane b o) = true ∧ ∀ i∈ls, (band i).testBit (lane b o) = true := by
    induction ls generalizing start with
    | nil => simpa using h
    | cons v vs ih =>
      obtain ⟨common,rest⟩ := ih _ h
      rw [Nat.testBit_and,Bool.and_eq_true] at common
      exact ⟨common.1,fun i hi => (List.mem_cons.mp hi).elim (fun e => e ▸ common.2) (rest i)⟩
  intro p
  have h := (all _ _ yes).2 p.val (List.mem_range.mpr p.isLt)
  dsimp [band] at h
  cases e : m.testBit p.val <;> simp [e,colLookup,columnExact,Nat.testBit_xor,liveWide] at h ⊢ <;> simp_all


namespace Local
open PCX150.Sparse (TestTree box Valid leaves)
theorem presentCard (m : Nat) : (Sparse.liveTags Scoring.label (bits m)).card ≤ present m := by
  classical
  let test := fun k : Nat => m &&& tagMask k != 0
  let ls := (List.range 22).filter test
  have fold (xs : List Nat) (n : Nat) :
      xs.foldl (fun k j => if test j then k+1 else k) n = n+(xs.filter test).length := by
    induction xs generalizing n with
    | nil => simp
    | cons a xs ih => cases h : test a <;> simp [h,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have sz : present m=ls.length := by simpa [present,ls,test] using fold (List.range 22) 0
  let labels := Sparse.liveTags Scoring.label (bits m)
  have sub : labels.image Fin.val ⊆ ls.toFinset := by
    intro n hn
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨p,hp,hit⟩ := Sparse.ofLive hl
    have points : (m &&& tagMask l.val).testBit p.val = true := by
      change m.testBit p.val=true at hp
      rw [Nat.testBit_and,tagSame,Scoring.tagBits,hp,hit]
      simp
    have ne : m &&& tagMask l.val ≠ 0 := by intro h; simp [h] at points
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_range.mpr l.isLt,by simpa [test] using ne⟩)
  have bound := Finset.card_le_card sub
  have nd : ls.Nodup := List.nodup_range.filter _
  rw [Finset.card_image_of_injective _ Fin.val_injective,List.toFinset_card_of_nodup nd] at bound
  simpa [sz,labels] using bound

theorem singleTag (m : Nat) (one : present m≤1) : plain geo (bits m) := by
  classical
  let t := Sparse.liveTags Scoring.label (bits m)
  have bound : t.card≤1 := (presentCard m).trans one
  have here (p : Sample) (hp : p∈bits m) : geo.tag p ∈ t := by
    change Scoring.label p ∈ Sparse.liveTags Scoring.label (bits m)
    unfold Sparse.liveTags
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,rfl⟩
  by_cases any : ∃p,p∈bits m
  · obtain ⟨p,hp⟩ := any
    exact ⟨geo.tag p,fun q hq => Finset.card_le_one.mp bound _ (here _ hq) _ (here _ hp)⟩
  · exact ⟨0,fun p hp => False.elim (any ⟨p,hp⟩)⟩

theorem repSmall : ∀ b : Bank, R b.val<2^60 := by decide +kernel
theorem wordRange (b : Bank) (o : ID) : domainMask b o <2^60 := rangePerm o _ (repSmall b)

theorem outsideBits (m a : Nat) (size : m<2^60) :
    (full ^^^ a) &&& m = apart m a := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and,Nat.testBit_xor,apart]
  by_cases l : i<60
  · have wide : full.testBit i = true := by rw [full,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact l
    rw [wide]; cases m.testBit i <;> cases a.testBit i <;> decide
  · have off := Nat.testBit_lt_two_pow (lt_of_lt_of_le size (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt l)))
    simp [off]

theorem countPaid (a b : Bank) (o : ID) (k : Fin 43) (t : TestTree)
    (v : Sparse.admissible geo (triple (domainMask b o) (R a.val) 0) t)
    (first : (thresh (tally full) k.val).testBit (lane b o) = true)
    (second : (thresh (tally (full ^^^ R a.val)) (k.val-1)).testBit (lane b o) = true) :
    k.val ≤ leaves t := by
  let m := domainMask b o
  have x := (cmpGood _ _ _ (posLane b o)).1 first
  have y := (cmpGood _ _ _ (posLane b o)).1 second
  rw [counted,full,Nat.and_comm,Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (wordRange b o)] at x
  rw [counted,outsideBits _ _ (wordRange b o)] at y
  have vs : Valid geo.val (box Scoring.label (Scoring.bitset (R a.val)) (Scoring.bitset 0)) t (Scoring.bitset m) := by
    have sets (s : Nat) : bits s=Scoring.bitset s := rfl
    simpa only [Sparse.admissible,triple,sets,labelSame] using v
  have z := Scoring.numericalLeafCover geo.val m (R a.val) 0 t vs
  have e (s : Nat) : Scoring.apart s 0 = s := by simp [Scoring.apart]
  change k.val≤present m at x
  change k.val-1≤present (apart m (R a.val)) at y
  rw [numSame] at x y
  have same : apart m (R a.val) = Scoring.apart m (R a.val) := rfl
  rw [same] at y
  simp only [Scoring.basic,e] at z
  omega

theorem bankRaw (b : Bank) (o : ID) (t : TestTree) (good : SmallChart.rawValid geo (treeRaw t) (bits (domainMask b o))) :
    weightR b.val≤leaves t := by
  by_cases z : b.val=0
  · simp [weightR,z]
  · let k : Key := ⟨b.val-1,by have := b.isLt; omega⟩
    have name : R b.val=rm[k.val]! := by simp [R,z,k]
    have eq : bits (domainMask b o) = acted (orient o) (Chart48.node k) := by
      rw [domainMask,actionSet,name]
      rfl
    rw [eq] at good
    have pay := SmallChart.rawLower chart (treeRaw t) k (orient o) good
    change weight[k.val]! ≤ SmallChart.leaves (treeRaw t) at pay
    simpa [weightR,z,k,rawLeaves] using pay

theorem monoPaid (a b : Bank) (o : ID) (k : Fin 43) (t : TestTree)
    (v : Sparse.admissible geo (triple (domainMask b o) (R a.val) 0) t)
    (few : (big ^^^ thresh (tally (R a.val)) 2).testBit (lane b o) = true)
    (priced : (weightGE k.val).testBit (lane b o) = true) : k.val ≤ leaves t := by
  apply (projectedPrice k b o priced).trans
  apply bankRaw
  have few' : ¬ 2 ≤ atCount (tally (R a.val)) (lane b o) := by
    intro z
    have bad := (cmpGood _ _ _ (posLane b o)).2 z
    simp [Nat.testBit_xor,liveWide,bad] at few
  rw [counted] at few'
  have mono := singleTag (R a.val &&& domainMask b o) (by omega)
  apply rawIf (bits (domainMask b o)) (box geo.tag (bits (R a.val)) (bits 0)) t v
  intro j
  cases j with
  | inl j => exact ⟨j,fun _ _ h => h⟩
  | inr j =>
    fin_cases j
    · obtain ⟨owner,ok⟩ := mono
      refine ⟨owner,fun r hr h => ok r ((useAnd _ _ _).2 ⟨?_,hr⟩)⟩
      simpa [box] using h
    · refine ⟨0,?_⟩
      intro p _ hp
      have falseBit : (0 : Nat).testBit p.val = true := by simpa [box,bits] using hp
      simp at falseBit

end Local
end PCX150.Scalar

namespace PCX150
open PEqualNP.ProofComplexity
abbrev Row := Fin 60
def fullMask : Nat := 1152921504606846975
def rows : Array Nat := #[672,784,1120,1288,2128,2184,644,770,1092,1281,2114,2177,532,546,1036,1057,2058,2065,84,98,140,161,266,273,1289,2185,1121,2129,1100,2122,673,785,652,778,596,610,786,2130,674,2186,660,2193,1122,1290,1108,1297,1164,1185,676,1124,788,1292,802,1313,2132,2188,2146,2209,2314,2321]
def ones : Array Nat := #[729761264001255936,364805838240031872,58354402365559104,326590701323239464,595657351441551378,230673451842052101,90657122719368468,180640694878079073,881623687009141386,5912485265682627,12099026304418572,1134909993020230704]
def zeros : Array Nat := #[423160240605591039,788115666366815103,1094567102241287871,826330803283607511,557264153165295597,922248052764794874,1062264381887478507,972280809728767902,271297817597705589,1147009019341164348,1140822478302428403,18011511586616271]
def labelMasks : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,13194139533312,52776558133248,211106232532992,844424930131968,3377699720527872,13510798882111488,54043195528445952,216172782113783808,864691128455135232]
def lits : List (Literal V) := [((0,0),false),((0,0),true),((0,1),false),((0,1),true),((0,2),false),((0,2),true),((1,0),false),((1,0),true),((1,1),false),((1,1),true),((1,2),false),((1,2),true),((2,0),false),((2,0),true),((2,1),false),((2,1),true),((2,2),false),((2,2),true),((3,0),false),((3,0),true),((3,1),false),((3,1),true),((3,2),false),((3,2),true)]

def port (v : V) : Nat := 3 * v.1.val + v.2.val

def assignment (r : Row) (v : V) : Bool := (rows[r.val]!).testBit (port v)

def keep (l : Literal V) : Nat := if l.2 then zeros[port l.1]! else ones[port l.1]!

def cut (C : Cl) (s : Nat) (l : Literal V) : Nat := if l ∈ C then s &&& keep l else s

def privateMask (C : Cl) : Nat := lits.foldl (cut C) fullMask

theorem fullBit (r : Row) : fullMask.testBit r.val = true := by
  revert r; decide +kernel

theorem keepBit (l : Literal V) (r : Row) :
    (keep l).testBit r.val = true ↔ assignment r l.1 ≠ l.2 := by
  revert l r; decide +kernel

theorem listed (l : Literal V) : l ∈ lits := by
  revert l; decide +kernel

theorem cutList (C : Cl) (s : Nat) (ls : List (Literal V)) (r : Row) :
    (ls.foldl (cut C) s).testBit r.val = true ↔
      s.testBit r.val = true ∧ (∀ l ∈ ls, l ∈ C → assignment r l.1 ≠ l.2) := by
  induction ls generalizing s with
  | nil => simp
  | cons l t ih =>
    rw [List.foldl_cons, ih]
    by_cases h : l ∈ C
    · simp only [cut, if_pos h, Nat.testBit_and, Bool.and_eq_true, keepBit,
        List.mem_cons]
      aesop
    · simp only [cut, if_neg h, List.mem_cons]
      aesop

theorem privateBit (C : Cl) (r : Row) :
    (privateMask C).testBit r.val = true ↔ ¬ClauseSat (assignment r) C := by
  rw [privateMask,cutList]
  simp only [fullBit, true_and]
  constructor
  · rintro h ⟨l,hl,yes⟩
    exact h l (listed l) hl yes
  · intro h l _ hl yes
    exact h ⟨l,hl,yes⟩

def posAx (i : Fin 4) : Cl := Finset.univ.image (fun j : Fin 3 => ((i,j),true))
def negAx (i j : Fin 4) (h : Fin 3) : Cl := {((i,h),false),((j,h),false)}

theorem posListed (i : Fin 4) : privateMask (posAx i) ∈ labelMasks.toList := by
  revert i; decide +kernel

theorem negListed (i j : Fin 4) (h : Fin 3) (ne : i ≠ j) :
    privateMask (negAx i j h) ∈ labelMasks.toList := by
  revert i j h; decide +kernel

theorem axListed {C : Cl} (hc : C ∈ PHP 4 3) : privateMask C ∈ labelMasks.toList := by
  rcases hc with ⟨i,rfl⟩ | ⟨i,j,h,ne,rfl⟩
  · exact posListed i
  · exact negListed i j h ne


end PCX150

namespace PCX150.Chart48
open PCX150.SmallChart
def alongCode : Array Nat := #[21542142465,38789383680,56036622346,68971138567,73015430152,303041801,94842913043,107776907011,111687505156,4749596165,129337398018,142270930716,146064540701,9179301150,163831546660,167554327832,13556327961,17870299674,176180175643,189702736390,202635619626,206262110251,26594969900,224196888370,227751244559,30971343888,35285970961,236377747730,250065074187,253574589196,43960118285,271624047421,275063258681,48336027450,52651102523,283690209852,293185860110,296591691587,61308080196,65616823605,305212311094,77599294007,319053580308,322446105877,82884304406,340612551757,343934324297,87259762506,91575294539,352561732428,362174817303,365463214163,100232272212,104540558631,374083376680,116406047273,388044954712,391313709344,121804577313,126120315682,399941323811,409601333279,412839387230,134773875039,139085373531,421462761820,150900713821,425811923749,156302791718,160614590307,434435598436,172455716183,448408332902,451679053614,182169921583,186485652272,460306660401,469966677549,473204731500,195139219309,199450717801,481828106090,211266058091,486177260339,216668128308,220979934577,494800942706,232821060423,504464031032,507752429940,242521487989,246830298688,516373116737,258695785282,520718873662,264044311871,268356108409,529342546298,280250973048,289851142469,533724820038,301813417852,543268818248,546674657661,311391046270,315701821264,555297308753,327684283730,559643065678,332915834447,337227632770,568266740099,349239936129,358722200405,572648547414,370801923973,577010228825,380230328154,384542137222,585633913991,396669847650,406031926880,590010943329,418229084809,431166686565,594424392807,440426392936,444738201994,603048077963,457035189360,466229496430,607426612079,478594429069,491531369587,500607646070,611857431159,513090025614,526024216187,539278869119,616303133568,551895466383,564830506884,582078138760,599325052300]
def invName : Array Nat := #[0,1,2,3,4,5,10,7,8,9,6,14,12,13,11,15,16,18,17,19,36,29,30,28,24,25,27,26,23,21,22,31,37,38,35,34,20,32,33,40,39,41,50,43,44,61,67,68,60,59,42,57,58,54,53,55,56,51,52,49,48,45,62,63,70,69,66,46,47,65,64,71,88,83,84,76,75,77,94,95,100,99,93,73,74,92,91,87,72,89,90,86,85,82,78,79,97,96,101,81,80,98,102,116,117,114,113,107,108,109,122,121,124,106,105,120,103,104,119,118,115,111,110,123,112,125,126,135,134,133,131,130,137,129,128,127,136,132,139,138,142,141,140,143]
def follow (o : ID) (g : G) : ID := Fin.ofNat 144 ((alongCode[o.val]! >>> (8*g.val)) % 256)
def inverse (o : ID) : ID := Fin.ofNat 144 invName[o.val]!

theorem followBoard : ∀ (o : ID) (g : G) (r : Sample),
    backward words[(follow o g).val]! 9 r = backward words[o.val]! 9 (rs g r) := by decide +kernel
theorem invertBoard : ∀ (o : ID) (r : Sample),
    backward words[(inverse o).val]! 9 (backward words[o.val]! 9 r) = r := by decide +kernel
theorem zeroBoard : ∀ (r : Sample), backward words[0]! 9 r = r := by decide +kernel

theorem followAct (o : ID) (g : G) (s : Set Sample) :
    acted (gen g) (acted (orient o) s) = acted (orient (follow o g)) s := by
  ext r
  change ((assemble words[o.val]! 9).s.symm (rs g r) ∈ s) ↔
    ((assemble words[(follow o g).val]! 9).s.symm r ∈ s)
  rw [backApply,backApply,followBoard]

theorem zeroAct (s : Set Sample) : acted (orient 0) s = s := by
  ext r
  change ((assemble words[0]! 9).s.symm r ∈ s) ↔ r ∈ s
  rw [backApply,zeroBoard]

theorem invertAct (o : ID) (s : Set Sample) : acted (orient o) (acted (orient (inverse o)) s) = s := by
  ext r
  change ((assemble words[(inverse o).val]! 9).s.symm ((assemble words[o.val]! 9).s.symm r) ∈ s) ↔ r ∈ s
  rw [backApply,backApply,invertBoard]

theorem composeAct (o p : ID) (s : Set Sample) :
    ∃ u : ID, acted (orient o) (acted (orient p) s) = acted (orient u) s := by
  have go (w d : Nat) : ∃ u : ID, acted (assemble w d) (acted (orient p) s) = acted (orient u) s := by
    induction d with
    | zero => exact ⟨p,rfl⟩
    | succ d ih =>
      obtain ⟨u,hu⟩ := ih
      simp only [assemble]
      split
      · exact ⟨u,hu⟩
      · rename_i h
        let g := Fin.ofNat 5 (((w >>> (3*d))%8)-1)
        exact ⟨follow u g,by rw [←actedChain,hu]; exact followAct u g s⟩
  exact go _ _

theorem nextName (k : Key) (q : Var) (b : Bool) :
    plain geo (branch geo (node k) q b) ∨ ∃ (j : Key) (o : ID), branch geo (node k) q b = acted (orient o) (node j) := by
  let d := slot k q b
  have facts := allSteps k q b
  by_cases hom : d%64=63
  · left
    have h := chart.proper k q b
    change (match next k q b with | none => _ | some j => _) at h
    rw [show next k q b = none by simp [next,show slot k q b % 64 = 63 from hom]] at h
    exact h
  · right
    refine ⟨index d,turn d,?_⟩
    ext r
    have e := facts r
    change (if d%64=63 then _ else _) at e
    rw [if_neg hom] at e
    change (_ ∧ geo.val r q = b) ↔ (rm[(index d).val]!.testBit ((assemble words[(turn d).val]! 9).s.symm r).val = true)
    rw [backApply,←e]
    simp [node,bits]

def named (s : Set Sample) := plain geo s ∨ ∃ (k : Key) (o : ID), s = acted (orient o) (node k)

theorem namedBranch {s : Set Sample} (h : named s) (q : Var) (b : Bool) : named (branch geo s q b) := by
  rcases h with ⟨a,mono⟩ | ⟨k,o,rfl⟩
  · exact Or.inl ⟨a,fun r hr => mono r hr.1⟩
  · rw [branchAct]
    rcases nextName k ((orient o).v.symm q) b with mono | ⟨j,p,eq⟩
    · exact Or.inl (actedPlain _ mono)
    · obtain ⟨u,hu⟩ := composeAct o p (node j)
      exact Or.inr ⟨j,u,by rw [eq,hu]⟩

theorem allNamed (qs : List (Var × Bool)) :
    named (qs.foldl (fun s q => branch geo s q.1 q.2) Set.univ) := by
  have walk (xs : List (Var × Bool)) (s : Set Sample) (h : named s) :
      named (xs.foldl (fun t q => branch geo t q.1 q.2) s) := by
    induction xs generalizing s with
    | nil => exact h
    | cons a tail ih => exact ih _ (namedBranch h _ _)
  apply walk
  exact Or.inr ⟨47,0,by rw [zeroAct]; exact chart.start.symm⟩

end PCX150.Chart48

namespace PCX150.PrivateGame
open PEqualNP.ProofComplexity
open PCX150.SmallChart (Sample Var Tag Key Domain Aut acted branch plain)
open PCX150.Chart48 (geo)
open PCX150.Sparse (TestTree Triple Valid box half)

def wire (v : V) : Var := Fin.ofNat 12 (port v)
theorem coord : ∀ p v, geo.val p (wire v) = assignment p v := by decide +kernel
def falsifiers (C : Cl) : Set Sample := {p | ¬ ClauseSat (assignment p) C}
theorem emptyMask : falsifiers ∅ = Set.univ := by
  ext p
  simp [falsifiers,ClauseSat]
theorem insertMask (C : Cl) (l : Literal V) :
    falsifiers (insert l C) = branch geo (falsifiers C) (wire l.1) (!l.2) := by
  ext p
  change (¬ ClauseSat (assignment p) (insert l C)) ↔ (¬ ClauseSat (assignment p) C) ∧ geo.val p (wire l.1) = (!l.2)
  rw [coord]
  have test : assignment p l.1 = (!l.2) ↔ assignment p l.1 ≠ l.2 := by
    cases assignment p l.1 <;> cases l.2 <;> decide
  rw [test]
  unfold ClauseSat
  simp only [Finset.mem_insert]
  aesop

theorem clauseNamed (C : Cl) : Chart48.named (falsifiers C) := by
  induction C using Finset.induction_on with
  | empty => rw [emptyMask]; exact Chart48.allNamed []
  | insert l C fresh ih => rw [insertMask]; exact Chart48.namedBranch ih _ _

theorem labelBook : ∀ n ∈ labelMasks.toList, ∃ k : Tag, ∀ r : Sample,
    n.testBit r.val = true → geo.tag r = k := by decide +kernel

theorem rawOwner {C : Cl} (ax : C ∈ PHP 4 3) : plain geo (falsifiers C) := by
  obtain ⟨k,tk⟩ := labelBook _ (axListed ax)
  exact ⟨k,fun p hp => tk p ((privateBit C p).2 hp)⟩

theorem treeRaw {A : Cl} {i : Nat} (pa : ResTree (PHP 4 3) A i) :
    ∃ t : TestTree, Sparse.leaves t = i+1 ∧
      Valid geo.val (box geo.tag ∅ ∅) t (falsifiers A) := by
  apply Sparse.transferTree (F := PHP 4 3) wire geo.val assignment coord
  · intro C ch
    obtain ⟨k,hk⟩ := rawOwner ch
    exact ⟨Sum.inl k,fun p hp => hk p hp⟩
  · exact pa
  · exact fun _ hp => hp

theorem treeOne {A B : Cl} {j : Nat} (pb : ResTree (insert A (PHP 4 3)) B j) :
    ∃ t : TestTree, Sparse.leaves t=j+1 ∧
      Valid geo.val (box geo.tag (falsifiers A) ∅) t (falsifiers B) := by
  apply Sparse.transferTree (F := insert A (PHP 4 3)) wire geo.val assignment coord
  · intro C ch
    rcases ch with rfl | ax
    · exact ⟨Sum.inr 0,fun p hp => by simpa [box,falsifiers] using hp⟩
    · obtain ⟨k,hk⟩ := rawOwner ax
      exact ⟨Sum.inl k,fun p hp => hk p hp⟩
  · exact pb
  · exact fun _ hp => hp

theorem treeTwo {A B : Cl} {k : Nat} (pc : ResTree (insert B (insert A (PHP 4 3))) ∅ k) :
    ∃ t : TestTree, Sparse.leaves t=k+1 ∧
      Valid geo.val (box geo.tag (falsifiers A) (falsifiers B)) t Set.univ := by
  apply Sparse.transferTree (F := insert B (insert A (PHP 4 3))) wire geo.val assignment coord
  · intro C ch
    rcases ch with rfl | rfl | ax
    · exact ⟨Sum.inr 1,fun p hp => by simpa [box,falsifiers] using hp⟩
    · exact ⟨Sum.inr 0,fun p hp => by simpa [box,falsifiers] using hp⟩
    · obtain ⟨i,hi⟩ := rawOwner ax
      exact ⟨Sum.inl i,fun p hp => hi p hp⟩
  · exact pc
  · intro p _ hp; simpa [ClauseSat] using hp


abbrev Choice := Fin 49
def candidate (a : Choice) : Set Sample := if a.val=0 then ∅ else Chart48.bits (Chart48.rm[a.val-1]!)
def price (a : Choice) := if a.val=0 then 0 else Chart48.weight[a.val-1]!
def code (k : Key) : Choice := ⟨k.val+1,by have := k.isLt; omega⟩
theorem priced (k : Key) : price (code k) = Chart48.chart.wt k := by simp [price,code,Chart48.chart]
theorem coded (k : Key) : candidate (code k) = Chart48.node k := by simp [candidate,code,Chart48.node]
theorem candidateZero : candidate 0 = ∅ := by rfl

def Match (real cur : Set Sample) := cur ⊆ real ∧ (real ⊆ cur ∨ plain geo real)
theorem matchSame (r : Set Sample) : Match r r := ⟨(fun _ h => h),Or.inl (fun _ h => h)⟩
theorem match0 {r : Set Sample} (h : plain geo r) : Match r ∅ := ⟨Set.empty_subset _,Or.inr h⟩

theorem actEmpty (f : Aut geo) : acted f (∅ : Set Sample) = ∅ := rfl
theorem actUniv (f : Aut geo) : acted f (Set.univ : Set Sample) = Set.univ := rfl

theorem twiceInv (o : Chart48.ID) (s : Set Sample) :
    acted (Chart48.orient (Chart48.inverse o)) (acted (Chart48.orient o) s) = s := by
  have inj (f : Aut geo) : Function.Injective (acted f) := by
    intro u v h
    ext r
    have e := Set.ext_iff.mp h (f.s r)
    simpa [SmallChart.acted] using e
  apply inj (Chart48.orient o)
  exact Chart48.invertAct o _

theorem namesPair {a b : Set Sample} (ha : Chart48.named a) (hb : Chart48.named b) :
    ∃ (f : Chart48.ID) (x y : Choice) (o : Chart48.ID),
      Match (acted (Chart48.orient f) a) (candidate x) ∧
      Match (acted (Chart48.orient f) b) (acted (Chart48.orient o) (candidate y)) := by
  have oneB (f : Chart48.ID) : ∃ y o, Match (acted (Chart48.orient f) b) (acted (Chart48.orient o) (candidate y)) := by
    rcases hb with hp | ⟨j,q,rfl⟩
    · exact ⟨0,0,by rw [candidateZero,actEmpty]; exact match0 (SmallChart.actedPlain _ hp)⟩
    · obtain ⟨n,eq⟩ := Chart48.composeAct f q (Chart48.node j)
      exact ⟨code j,n,by rw [coded,eq]; exact matchSame _⟩
  rcases ha with pure | ⟨j,q,rfl⟩
  · obtain ⟨y,o,hm⟩ := oneB 0
    exact ⟨0,0,y,o,by rw [candidateZero]; exact match0 (SmallChart.actedPlain _ pure),hm⟩
  · obtain ⟨y,o,hm⟩ := oneB (Chart48.inverse q)
    exact ⟨Chart48.inverse q,code j,y,o,by rw [twiceInv,coded]; exact matchSame _,hm⟩

theorem canMove (f : Aut geo) (s x y a b : Set Sample) (t : TestTree)
    (h : Valid geo.val (box geo.tag x y) t s)
    (ax : Match (acted f x) a) (byy : Match (acted f y) b) :
    Valid geo.val (box geo.tag a b) (Sparse.renamed f t) (acted f s) := by
  apply Sparse.moveTree f h
  intro i
  cases i with
  | inl i =>
    refine ⟨Sum.inl (f.a i),?_⟩
    intro p _ h
    change geo.tag p = i at h
    exact (f.label p).trans (congrArg f.a h)
  | inr i =>
    fin_cases i
    · rcases ax.2 with sub | ⟨j,pure⟩
      · refine ⟨Sum.inr 0,?_⟩
        intro p hp hx
        have h0 : p ∈ x := by simpa [box] using hx
        have z := sub (show f.s p ∈ acted f x by simpa [SmallChart.acted] using h0)
        simpa [box] using z
      · refine ⟨Sum.inl j,?_⟩
        intro p hp hx
        have h0 : p ∈ x := by simpa [box] using hx
        exact pure _ (by simpa [SmallChart.acted] using h0)
    · rcases byy.2 with sub | ⟨j,pure⟩
      · refine ⟨Sum.inr 1,?_⟩
        intro p hp hx
        have h0 : p ∈ y := by simpa [box] using hx
        have z := sub (show f.s p ∈ acted f y by simpa [SmallChart.acted] using h0)
        simpa [box] using z
      · refine ⟨Sum.inl j,?_⟩
        intro p hp hx
        have h0 : p ∈ y := by simpa [box] using hx
        exact pure _ (by simpa [SmallChart.acted] using h0)

theorem shrink {bit : Sample → Var → Bool} {term : Sparse.Box → Set Sample}
    {s d : Set Sample} {t : TestTree} (h : Valid bit term t s) (inc : d ⊆ s) : Valid bit term t d :=
  Sparse.smaller h inc (fun i => ⟨i,fun _ _ hp => hp⟩)

def converted : TestTree → SmallChart.Tree
  | .leaf => .leaf
  | .cut q l r => .node q (converted l) (converted r)
theorem ccost (t : TestTree) : SmallChart.leaves (converted t) = Sparse.leaves t := by
  induction t with
  | leaf => rfl
  | cut q l r hl hr => simp [converted,SmallChart.leaves,Sparse.leaves,hl,hr]

theorem noExtra {s : Set Sample} {t : TestTree} (h : Valid geo.val (box geo.tag ∅ ∅) t s) :
    SmallChart.rawValid geo (converted t) s := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,hi⟩ := h
    cases i with
    | inl i => exact ⟨i,fun _ hp => hi hp⟩
    | inr i =>
      refine ⟨0,?_⟩
      intro p hp
      have z := hi hp
      fin_cases i <;> simp [box] at z
  | cut q l r hl hr => exact ⟨hl h.1,hr h.2⟩

theorem charge (a : Choice) (t : TestTree) (h : Valid geo.val (box geo.tag ∅ ∅) t (candidate a)) :
    price a ≤ Sparse.leaves t := by
  by_cases z : a.val=0
  · simp [price,z]
  · let k : Key := ⟨a.val-1,by have := a.isLt; omega⟩
    have eq : code k = a := by apply Fin.ext; dsimp [code,k]; omega
    rw [←eq,coded] at h
    rw [←eq,priced,←ccost]
    exact SmallChart.rawLower Chart48.chart (converted t) k (SmallChart.Aut.unit _) (noExtra h)

def scoreClaim := ∀ (a b : Choice) (o : Chart48.ID) (t u : TestTree),
    Valid geo.val (box geo.tag (candidate a) ∅) t (acted (Chart48.orient o) (candidate b)) →
    Valid geo.val (box geo.tag (candidate a) (acted (Chart48.orient o) (candidate b))) u Set.univ →
    41 ≤ price a + Sparse.leaves t + Sparse.leaves u

theorem allThree (test : scoreClaim) {A B : Cl} {i j k : Nat}
    (pa : ResTree (PHP 4 3) A i) (pb : ResTree (insert A (PHP 4 3)) B j)
    (pc : ResTree (insert B (insert A (PHP 4 3))) ∅ k) : 38 ≤ i+j+k := by
  obtain ⟨f,a,b,o,ma,mb⟩ := namesPair (clauseNamed A) (clauseNamed B)
  let ren := Chart48.orient f
  have emp : Match (acted ren ∅) ∅ := by rw [actEmpty]; exact matchSame _
  obtain ⟨x,hx,vx⟩ := treeRaw pa
  obtain ⟨y,hy,vy⟩ := treeOne pb
  obtain ⟨z,hz,vz⟩ := treeTwo pc
  have first := charge a (Sparse.renamed ren x) (shrink (canMove ren _ _ _ _ _ _ vx emp emp) ma.1)
  have snd := shrink (canMove ren _ _ _ _ _ _ vy ma emp) mb.1
  have third := canMove ren _ _ _ _ _ _ vz ma mb
  rw [actUniv] at third
  have total := test a b o _ _ snd third
  simp only [Sparse.sameLeaves,hx,hy,hz] at first total
  omega

end PCX150.PrivateGame

namespace PCX150.Scalar
open PCX150.Chart48 PCX150.SmallChart
abbrev OptionID := Fin 49
def place (b : OptionID) (o : Chart48.ID) : Nat := 49*o.val+b.val
theorem placeRange (b : OptionID) (o : Chart48.ID) : place b o < 7056 := by
  have := b.isLt; have := o.isLt; unfold place; omega

theorem unpackEnd (a b : OptionID) (o : Chart48.ID) (good : covered a.val = true) :
    ∃ z, ((big ^^^ meets (full ^^^ testMask (z%2048))).testBit (place b o) = true) ∧
      ((rowQual a.val)[41-weightR a.val-getUp a.val z]!).testBit (place b o) = true := by
  let n := startsOver (a.val+1)-startsOver a.val
  let itemAt :=  fun i : Nat => ove (startsOver a.val+i)
  let hit := fun i : Nat => (big ^^^ meets (full ^^^ testMask (itemAt i%2048))) &&&
    (rowQual a.val)[41-weightR a.val-getUp a.val (itemAt i)]!
  have eq : (List.range n).foldl (fun acc i => acc ||| hit i) 0 = big := eq_of_beq good
  have yes : ((List.range n).foldl (fun acc i => acc ||| hit i) 0).testBit (place b o) = true := by
    rw [eq,big,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
    exact placeRange _ _
  rcases (foldBits _ _ _ _).1 yes with bad | ⟨i,_,val⟩
  · simp at bad
  · refine ⟨itemAt i,?_⟩
    exact Bool.and_eq_true_iff.mp (by simpa [hit,Nat.testBit_and] using val)

open PCX150.PrivateGame (candidate price)
open PCX150.SmallChart (Sample acted)
open PCX150.Sparse (TestTree Valid box leaves)
def dataB (b : OptionID) (o : Chart48.ID) := acted (Chart48.orient o) (candidate b)
def upperData (z : Nat) := Chart48.bits (testMask (z%2048))

theorem widenSecond (A B H : Set Sample) (sub : B ⊆ H) {t : TestTree}
    (valid : Valid Chart48.geo.val (box Chart48.geo.tag A B) t Set.univ) :
    Valid Chart48.geo.val (box Chart48.geo.tag A H) t Set.univ := by
  apply Sparse.smaller valid (fun _ h => h)
  intro i
  refine ⟨i,?_⟩
  intro p _ h
  cases i with
  | inl k => exact h
  | inr k =>
    fin_cases k
    · simpa [box] using h
    · apply sub
      simpa [box] using h

theorem reachTarget
    (allCases : ∀ a : OptionID, covered a.val = true)
    (compare : ∀ (b : OptionID) (o : Chart48.ID) z,
      (big ^^^ meets (full ^^^ testMask (z%2048))).testBit (place b o) = true → dataB b o ⊆ upperData z)
    (firstTree : ∀ (a b : OptionID) (o : Chart48.ID) k, k<43 →
      ((rowQual a.val)[k]!).testBit (place b o) = true → ∀ t,
      Valid Chart48.geo.val (box Chart48.geo.tag (candidate a) ∅) t (dataB b o) → k ≤ leaves t)
    (lastTree : ∀ (a : OptionID) z t,
      Valid Chart48.geo.val (box Chart48.geo.tag (candidate a) (upperData z)) t Set.univ →
      getUp a.val z ≤ leaves t) : PrivateGame.scoreClaim := by
  intro a b o t u h g
  obtain ⟨z,sub,ok⟩ := unpackEnd a b o (allCases a)
  have hh := compare b o z sub
  have hu := lastTree a z u (widenSecond _ _ _ hh g)
  have ht := firstTree a b o _ (by omega) ok t h
  change 41 ≤ weightR a.val + leaves t + leaves u
  omega


end PCX150.Scalar

namespace PCX150.RootBits
def closeWord : Nat → Nat → Nat
  | 0,t => t
  | n+1,t =>
    let w := closeWord n t
    w ||| (w >>> (7056*2^n))

theorem foldBits (xs : List Nat) (f : Nat → Nat) (i acc : Nat) :
    (xs.foldl (fun a e => a ||| f e) acc).testBit i = true ↔
      acc.testBit i = true ∨ ∃ j ∈ xs, (f j).testBit i = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,ih,Nat.testBit_or,Bool.or_eq_true]
    simp only [List.mem_cons]
    aesop


theorem closure (n t i : Nat) :
    (closeWord n t).testBit i = true ↔ ∃ j<2^n, t.testBit (7056*j+i) = true := by
  induction n generalizing i with
  | zero => simp [closeWord]
  | succ n ih =>
    rw [closeWord,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_shiftRight,ih,ih,Nat.pow_succ]
    constructor
    · rintro (⟨j,lt,hit⟩ | ⟨j,lt,hit⟩)
      · exact ⟨j,by omega,hit⟩
      · exact ⟨j+2^n,by omega,by simpa only [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hit⟩
    · rintro ⟨j,lt,hit⟩
      by_cases small : j<2^n
      · exact Or.inl ⟨j,small,hit⟩
      · right
        have sub : (j-2^n)+2^n=j := by omega
        refine ⟨j-2^n,by omega,?_⟩
        have same : 7056*(j-2^n)+(7056*2^n+i)=7056*j+i := by rw [←Nat.add_assoc,←Nat.mul_add,sub]
        simpa only [same,Nat.add_comm i] using hit

theorem wideStripe (m pos k i : Nat) (small : i<7056) (limit : m<2^7056) :
    (m <<< (7056*pos)).testBit (7056*k+i) = true → k=pos ∧ m.testBit i=true := by
  intro h
  rw [Nat.testBit_shiftLeft] at h
  by_cases eq : k=pos
  · subst k; exact ⟨rfl,by simpa using h⟩
  · by_cases less : k<pos
    · simp [show ¬7056*pos≤7056*k+i by omega] at h
    · have t : 7056 ≤ 7056*k+i-7056*pos := by omega
      have off := Nat.testBit_lt_two_pow (lt_of_lt_of_le limit (Nat.pow_le_pow_right (by decide : 0<2) t))
      simp [show 7056*pos≤7056*k+i by omega,off] at h

theorem extractWord {items : List Nat} (mask cost : Nat → Nat) (k i : Nat)
    (bound : ∀ z ∈ items, mask z < 2^7056) (small : i < 7056)
    (seen : (((closeWord 6 (items.foldl (fun t z => t ||| (mask z <<< (7056*cost z))) 0)) >>> (7056*k)) % 2^7056).testBit i = true) :
    ∃ z ∈ items, k≤cost z ∧ (mask z).testBit i=true := by
  rw [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight] at seen
  simp only [decide_eq_true_eq.mpr small,Bool.true_and] at seen
  obtain ⟨j,_,cell⟩ := (closure 6 _ _).1 seen
  rcases (foldBits _ (fun z => mask z <<< (7056*cost z)) _ _).1 cell with bad | ⟨z,hz,bit⟩
  · simp at bad
  · have e : 7056*j+(7056*k+i) = 7056*(j+k)+i := by omega
    rw [e] at bit
    have result := wideStripe (mask z) (cost z) (j+k) i small (bound z hz) bit
    exact ⟨z,hz,by omega,result.2⟩

end PCX150.RootBits

namespace PCX150
open PEqualNP.ProofComplexity
abbrev TreeLower := ∀ {P Q : Cl} {i j k : Nat},
  ResTree (PHP 4 3) P i → ResTree (insert P (PHP 4 3)) Q j →
  ResTree (insert Q (insert P (PHP 4 3))) ∅ k → 38 ≤ i+j+k
end PCX150
namespace PCX150.Scalar.Local
open PCX150.Chart48 PCX150.SmallChart
open PCX150.Sparse (TestTree Valid box leaves)

theorem chosenSet (a : Bank) : bits (R a.val) = PrivateGame.candidate a := by
  by_cases z : a.val=0
  · ext r; simp [bits,R,PrivateGame.candidate,z]
  · simp [R,PrivateGame.candidate,z]
theorem activeSet (b : Bank) (o : ID) : bits (domainMask b o) = dataB b o := by
  rw [domainMask,actionSet,chosenSet]
  rfl
theorem fullSet : bits full = Set.univ := by
  ext r
  exact iff_of_true (by change full.testBit r.val=true; rw [full,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact r.isLt) trivial

theorem sameLow (m : Nat) : sameMask m < 2^7056 := by
  let f := fun i : Nat => if m.testBit i then everyCol[i]! else big ^^^ everyCol[i]!
  have sub (xs : List Nat) (n : Nat) : xs.foldl (fun t i => t &&& f i) n ≤ n := by
    induction xs generalizing n with
    | nil => exact le_rfl
    | cons a l ih => exact (ih _).trans Nat.and_le_left
  exact lt_of_le_of_lt (sub _ big) (by unfold big; have := Nat.two_pow_pos 7056; omega)

theorem learntMiddle (p : ∀ i : NodeID, nodeOK i.val=true) (a b : Bank) (o : ID) (k : Nat) (t : TestTree)
    (good : Sparse.admissible geo (triple (domainMask b o) (R a.val) 0) t)
    (data : (extraWord a.val k).testBit (lane b o)=true) : k≤leaves t := by
  let n := startsExtra (a.val+1)-startsExtra a.val
  let z := fun i => exts (startsExtra a.val+i)
  let maskOf := fun i => sameMask (testMask (z i%2048))
  let cost := fun i => getB a.val (z i)
  have foldEq (d w : Nat) : closeWord d w = RootBits.closeWord d w := by
    induction d with
    | zero => rfl
    | succ d ih => simp [closeWord,RootBits.closeWord,ih]
  have data' : (((RootBits.closeWord 6 ((List.range n).foldl
        (fun acc i => acc ||| (maskOf i <<< (7056*cost i))) 0)) >>> (7056*k))%2^7056).testBit (lane b o)=true := by
    simpa only [extraWord,packedExtras,foldEq] using data
  obtain ⟨i,mem,paid,eq⟩ := RootBits.extractWord maskOf cost k (lane b o)
    (fun i _ => sameLow _) (posLane b o) data'
  have cells := meetFixed b o eq
  have same : bits (testMask (z i % 2048)) = bits (domainMask b o) := by
    ext r
    change (_=true) ↔ (_=true)
    rw [cells,domainBit]
  have useful : Sparse.admissible geo (triple (testMask (z i %2048)) (R a.val) 0) t := by
    change Valid _ _ _ (bits (testMask (z i%2048)))
    rw [same]
    exact good
  exact paid.trans (middlePaid p _ _ t useful)

theorem decodedRow (p : ∀ i : NodeID, nodeOK i.val=true) (a b : Bank) (o : ID) (k : Fin 43)
    (hit : ((rowQual a.val)[k.val]!).testBit (lane b o)=true) (t : TestTree)
    (good : Sparse.admissible geo (triple (domainMask b o) (R a.val) 0) t) : k.val≤leaves t := by
  by_cases few : k.val≤1
  · exact few.trans (positive t)
  · have array : (rowQual a.val)[k.val]! =
        (thresh (tally full) k.val &&& thresh (tally (full ^^^ R a.val)) (k.val-1)) |||
        ((big ^^^ thresh (tally (R a.val)) 2) &&& weightGE k.val) ||| extraWord a.val k.val := by
      rw [getElem!_pos _ _ (by simpa [rowQual] using k.isLt)]
      simp [rowQual,few]
    rw [array] at hit
    simp only [Nat.testBit_or,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true] at hit
    rcases hit with (⟨x,y⟩ | ⟨x,y⟩) | u
    · exact countPaid a b o k t good x y
    · exact monoPaid a b o k t good x y
    · exact learntMiddle p a b o k.val t good u

theorem resolve38 (p : ∀ i : NodeID, nodeOK i.val=true) (all : ∀a : Bank, covered a.val=true) : TreeLower := by
  intro A B ia ib ic x y z
  apply PrivateGame.allThree ?_ x y z
  apply reachTarget all
  · intro b o z bitsOK r hr
    have real : active b o r = true := by
      rw [←activeSet] at hr
      exact (domainBit b o r).symm.trans hr
    exact upperMask _ b o bitsOK r real
  · intro a b o k range hit t good
    apply decodedRow p a b o ⟨k,range⟩ hit t
    change Valid _ (box geo.tag (bits (R a.val)) (bits 0)) _ (bits (domainMask b o))
    have empty : bits 0 = ∅ := by ext r; simp [bits]
    rwa [chosenSet,empty,activeSet]
  · intro a z t good
    apply upperPaid p a.val z t
    change Valid _ (box geo.tag (bits (R a.val)) _) _ (bits full)
    rw [chosenSet,fullSet]
    exact good

end PCX150.Scalar.Local
