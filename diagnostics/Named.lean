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

namespace PCX150.Chart48
open PCX150.SmallChart
set_option maxRecDepth 10000
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
