import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17379.A17379
abbrev Col := Finset (Fin 285)
def canJoin (bank : List Col) (w : Col) : Prop :=
  ∃ a∈bank,∃ b∈bank, ¬a⊆b ∧ ¬b⊆a ∧ w=a∪b

noncomputable def paid {N : ℕ} (P : Fin N → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter P).card

theorem counted {N b : ℕ} (P : Fin N → Prop) :
    (∀ (m : ℕ) (f : Fin m → ℕ), Function.Injective f →
        (∀ j,∃ h : f j<N, ¬P ⟨f j,h⟩) → b+m≤N) ↔ b≤paid P := by
  classical
  let A := Finset.univ.filter (fun i : Fin N => ¬P i)
  have sum : paid P + A.card=N := by
    simpa [paid,A] using Finset.card_filter_add_card_filter_not (s:=Finset.univ) P
  constructor
  · intro hyp
    let eq : A ≃ Fin A.card := Fintype.equivFinOfCardEq (by simp)
    let f (j : Fin A.card) : ℕ := (eq.symm j).1.val
    have inj : Function.Injective f := by
      intro i j ij
      apply eq.symm.injective
      apply Subtype.ext
      exact Fin.ext ij
    have test (j : Fin A.card) : ∃ h : f j<N, ¬P ⟨f j,h⟩ := by
      refine ⟨(eq.symm j).1.isLt,?_⟩
      exact (Finset.mem_filter.mp (eq.symm j).property).2
    have lower := hyp A.card f inj test
    omega
  · intro bound m f inj hit
    let g (j : Fin m) : A := ⟨⟨f j,(hit j).choose⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hit j).choose_spec⟩⟩
    have gi : Function.Injective g := by
      intro i j ij
      exact inj (congrArg (fun a : A => a.1.val) ij)
    have sm : m≤A.card := by simpa using Fintype.card_le_of_injective g gi
    omega

def admissible (raw L : List Col) := ∀ i : Fin L.length,
  let B := raw++L.take i.val
  ∃ a∈B,∃ b∈B,¬a⊆b ∧ ¬b⊆a ∧ L.get i ∉ B ∧ (L.get i=a∩b ∨ L.get i=a∪b)
def cap (raw L : List Col) (target : Col) :=
  ∃ a∈raw++L,∃ b∈raw++L,¬a⊆b ∧ ¬b⊆a ∧ a∩b=target

def reps : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]
def raw : List Col := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (reps.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ))
def target : Col := (List.filter (fun (x9 : Fin 285) => decide (↑x9 < (51 : ℕ))) (List.finRange 285)).toFinset
def pay (L : List Col) (i : Fin L.length) := canJoin (raw++L.take i.val) (L.getD i.val ∅)
theorem semantic_iff : (have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))) (x4 : ℕ) (x5 : Fin x4 → ℕ),   (∀ (x6 : Fin x3.length),       have x7 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x6) x3;       ∃ x8 ∈ x7, ∃ x9 ∈ x7, ¬x8 ⊆ x9 ∧ ¬x9 ⊆ x8 ∧ x3.get x6 ∉ x7 ∧ (x3.get x6 = x8 ∩ x9 ∨ x3.get x6 = x8 ∪ x9)) →     (∃ x7 ∈ x2 ++ x3, ∃ x8 ∈ x2 ++ x3, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x7 ∩ x8 = (List.filter (fun (x9 : Fin (285 : ℕ)) => Decidable.decide (↑x9 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset) → Function.Injective x5 → (∀ (x9 : Fin x4), x5 x9 < x3.length ∧ ¬∃ x10 ∈ x2 ++ List.take (x5 x9) x3, ∃ x11 ∈ x2 ++ List.take (x5 x9) x3, ¬x10 ⊆ x11 ∧ ¬x11 ⊆ x10 ∧ x3.getD (x5 x9) ∅ = x10 ∪ x11) → (50 : ℕ) + x4 ≤ x3.length) ↔ ∀ L, admissible raw L → cap raw L target → 50≤paid (pay L) := by
  constructor
  · intro h L ha hc
    apply (counted (pay L)).mp
    intro m f inj hf
    apply h L m f ha hc inj
    intro j
    obtain ⟨bound,no⟩ := hf j
    exact ⟨bound,no⟩
  · intro h
    dsimp only
    intro L m f valid capH inj tests
    apply (counted (pay L)).mpr (h L valid capH) m f inj
    intro j
    exact ⟨(tests j).1,(tests j).2⟩

end PEqualNP.Outside.L_meta_17379.A17379

namespace PEqualNP.Outside.L_meta_17379.A17379.Control
abbrev W := BitVec 285
def col (w : W) : Col := Finset.univ.filter fun i => w.getLsbD i.val
theorem membership (w : W) (i : Fin 285) : i∈col w ↔ w.getLsbD i.val=true := by simp [col]
theorem col_inj : Function.Injective col := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have eq := Finset.ext_iff.mp h (⟨i,hi⟩ : Fin 285)
  simp only [membership] at eq
  cases u : a.getLsbD i <;> cases v : b.getLsbD i <;> simp_all
theorem band (a b : W) : col (a&&&b)=col a∩col b := by
  ext i
  simp [membership,BitVec.getLsbD_and]
theorem bor (a b : W) : col (a|||b)=col a∪col b := by
  ext i
  simp [membership,BitVec.getLsbD_or]
theorem contained (a b : W) : col a⊆col b ↔ a&&&b=a := by
  rw [←Finset.inter_eq_left,←band]
  exact col_inj.eq_iff
def rawW : List W := [
(((2256232236711936 : W) <<< 0) + ((18210141916168560 : W) <<< 56) + ((54616454796060697 : W) <<< 112) + ((7055098066250817 : W) <<< 168) + ((4808203678925410 : W) <<< 224) + ((9 : W) <<< 280)),
(((4512464439873537 : W) <<< 0) + ((36561004140823520 : W) <<< 56) + ((37184111647215650 : W) <<< 112) + ((9607146193844354 : W) <<< 168) + ((9616407357850820 : W) <<< 224) + ((18 : W) <<< 280)),
(((11276728693432322 : W) <<< 0) + ((923676755363776 : W) <<< 56) + ((2319424275783765 : W) <<< 112) + ((19214292387680517 : W) <<< 168) + ((19514289692412296 : W) <<< 224) + ((4 : W) <<< 280)),
(((24804982356197380 : W) <<< 0) + ((1706633202241152 : W) <<< 56) + ((4630053532287146 : W) <<< 112) + ((42931634714018315 : W) <<< 168) + ((39028545025086224 : W) <<< 224) + ((8 : W) <<< 280)),
(((51861764526080008 : W) <<< 0) + ((3554003892837376 : W) <<< 56) + ((9260107064443220 : W) <<< 112) + ((13806225145922582 : W) <<< 168) + ((5718055395271713 : W) <<< 224) + ((17 : W) <<< 280)),
(((31665935014232080 : W) <<< 0) + ((7108007783577857 : W) <<< 56) + ((18511418035995304 : W) <<< 112) + ((27612450291845164 : W) <<< 168) + ((11717585763060290 : W) <<< 224) + ((2 : W) <<< 280)),
(((63331870028464160 : W) <<< 0) + ((14216015569252866 : W) <<< 56) + ((37014039978968400 : W) <<< 112) + ((55224350827884632 : W) <<< 168) + ((23153696553604228 : W) <<< 224) + ((4 : W) <<< 280)),
(((54606146019000384 : W) <<< 0) + ((28432031138505733 : W) <<< 56) + ((1979282013031072 : W) <<< 112) + ((38390557862027441 : W) <<< 168) + ((46307393107208457 : W) <<< 224) + ((8 : W) <<< 280)),
(((37154698000072832 : W) <<< 0) + ((56864062277011467 : W) <<< 56) + ((3958564026062144 : W) <<< 112) + ((4724071441940834 : W) <<< 168) + ((20275717199778323 : W) <<< 224) + ((17 : W) <<< 280)),
(((277026439424 : W) <<< 0) + ((41670530516094999 : W) <<< 56) + ((7917128052124289 : W) <<< 112) + ((9448142883881668 : W) <<< 168) + ((40832909376267302 : W) <<< 224) + ((2 : W) <<< 280)),
(((554052878848 : W) <<< 0) + ((11283466994262062 : W) <<< 56) + ((15834256104248579 : W) <<< 112) + ((18896285767763336 : W) <<< 168) + ((9608224714606668 : W) <<< 224) + ((5 : W) <<< 280)),
(((1108105757696 : W) <<< 0) + ((22566933988524124 : W) <<< 56) + ((31668512208497158 : W) <<< 112) + ((37792571535526672 : W) <<< 168) + ((19216449429213336 : W) <<< 224) + ((10 : W) <<< 280)),
(((2216211515392 : W) <<< 0) + ((45133867977048248 : W) <<< 56) + ((63337024416994316 : W) <<< 112) + ((3527549033125408 : W) <<< 168) + ((38432898858426673 : W) <<< 224) + ((20 : W) <<< 280)),
(((45036271185170432 : W) <<< 0) + ((11259892656791560 : W) <<< 56) + ((9433848434132292 : W) <<< 112) + ((19219741369827632 : W) <<< 168) + ((19211371621189641 : W) <<< 224) + ((4 : W) <<< 280)),
(((18014948332412929 : W) <<< 0) + ((22519785313583121 : W) <<< 56) + ((18858901848984200 : W) <<< 112) + ((38438933050950240 : W) <<< 168) + ((38422708882641426 : W) <<< 224) + ((8 : W) <<< 280)),
(((36029896664825858 : W) <<< 0) + ((45180308115521570 : W) <<< 56) + ((37717803697968384 : W) <<< 112) + ((317222125315264 : W) <<< 168) + ((4506383110382629 : W) <<< 224) + ((17 : W) <<< 280)),
(((2199291723780 : W) <<< 0) + ((18303022191018309 : W) <<< 56) + ((3386809451031041 : W) <<< 112) + ((634444250630528 : W) <<< 168) + ((9294241197475914 : W) <<< 224) + ((2 : W) <<< 280)),
(((4398583447560 : W) <<< 0) + ((36606044382036618 : W) <<< 56) + ((6773618902062082 : W) <<< 112) + ((1268888501261056 : W) <<< 168) + ((18588482394951828 : W) <<< 224) + ((4 : W) <<< 280)),
(((2260596980580368 : W) <<< 0) + ((1154494726145044 : W) <<< 56) + ((13547237804124165 : W) <<< 112) + ((2537777002513921 : W) <<< 168) + ((37176964789903656 : W) <<< 224) + ((8 : W) <<< 280)),
(((4521193961160736 : W) <<< 0) + ((2308989452290088 : W) <<< 56) + ((27094475608248330 : W) <<< 112) + ((5076103760841730 : W) <<< 168) + ((2296335537685072 : W) <<< 224) + ((17 : W) <<< 280)),
(((9042387922321472 : W) <<< 0) + ((4758699213066576 : W) <<< 56) + ((54188950142754836 : W) <<< 112) + ((10152207521683460 : W) <<< 168) + ((4874146052080800 : W) <<< 224) + ((2 : W) <<< 280)),
(((18084775844642944 : W) <<< 0) + ((9376660937778080 : W) <<< 56) + ((36320306247712808 : W) <<< 112) + ((20303865287553033 : W) <<< 168) + ((9748292104161600 : W) <<< 224) + ((4 : W) <<< 280)),
(((38421351502971136 : W) <<< 0) + ((18753321877653056 : W) <<< 56) + ((591814550388816 : W) <<< 112) + ((40607730575106067 : W) <<< 168) + ((19215109235806336 : W) <<< 224) + ((8 : W) <<< 280)),
(((4785108968014336 : W) <<< 0) + ((37506643755306113 : W) <<< 56) + ((1183629100777632 : W) <<< 112) + ((9157867112284198 : W) <<< 168) + ((38430218471612673 : W) <<< 224) + ((16 : W) <<< 280)),
(((11822017749713920 : W) <<< 0) + ((2814973164197890 : W) <<< 56) + ((2358462108533073 : W) <<< 112) + ((22819333851938892 : W) <<< 168) + ((4802842905297410 : W) <<< 224) + ((1 : W) <<< 280)),
(((23644035499427840 : W) <<< 0) + ((5629946328395780 : W) <<< 56) + ((4716924217066146 : W) <<< 112) + ((45638667703877784 : W) <<< 168) + ((9605685810594820 : W) <<< 224) + ((2 : W) <<< 280))
]
def gatesW : List W := [
(((41667162439946369 : W) <<< 0) + ((57391870815489003 : W) <<< 56) + ((39998908668925282 : W) <<< 112) + ((14330650562722274 : W) <<< 168) + ((29883327390865111 : W) <<< 224) + ((19 : W) <<< 280)),
(((68970235449446561 : W) <<< 0) + ((70903099295005675 : W) <<< 56) + ((40421190929438066 : W) <<< 112) + ((69519817018505722 : W) <<< 168) + ((34457295795967703 : W) <<< 224) + ((23 : W) <<< 280)),
(((69110973072085169 : W) <<< 0) + ((70903099311782891 : W) <<< 56) + ((58510356233803770 : W) <<< 112) + ((69519817035414014 : W) <<< 168) + ((34880629248024279 : W) <<< 224) + ((23 : W) <<< 280)),
(((8797166895120 : W) <<< 0)),
(((33922167250944016 : W) <<< 0) + ((25318141109811569 : W) <<< 56) + ((55113473248701113 : W) <<< 112) + ((34649956138495085 : W) <<< 168) + ((16243210523920994 : W) <<< 224) + ((11 : W) <<< 280)),
(((70439113526116424 : W) <<< 0) + ((30859825886854149 : W) <<< 56) + ((11239369749597172 : W) <<< 112) + ((52192383753479351 : W) <<< 168) + ((50899548518034729 : W) <<< 224) + ((25 : W) <<< 280)),
(((70584283571781720 : W) <<< 0) + ((35451549655891317 : W) <<< 56) + ((65283975135865853 : W) <<< 112) + ((70788705536666879 : W) <<< 168) + ((53469111642976107 : W) <<< 224) + ((27 : W) <<< 280)),
(((4398583447560 : W) <<< 0)),
(((11277836799190018 : W) <<< 0) + ((23481813576861660 : W) <<< 56) + ((33987936417131095 : W) <<< 112) + ((55810578092317461 : W) <<< 168) + ((19515673914612120 : W) <<< 224) + ((14 : W) <<< 280)),
(((33952919233576980 : W) <<< 0) + ((8814503530086273 : W) <<< 56) + ((23071101749248682 : W) <<< 112) + ((70544085005863471 : W) <<< 168) + ((48318404819049298 : W) <<< 224) + ((10 : W) <<< 280)),
(((33971756964340758 : W) <<< 0) + ((26877285922406365 : W) <<< 56) + ((34339790339959551 : W) <<< 112) + ((71740371912612671 : W) <<< 168) + ((67551210927545306 : W) <<< 224) + ((14 : W) <<< 280)),
(((1099645861890 : W) <<< 0)),
(((65588102265176096 : W) <<< 0) + ((32285402815099762 : W) <<< 56) + ((55038746728770905 : W) <<< 112) + ((62261852311927897 : W) <<< 168) + ((23458266241226470 : W) <<< 224) + ((13 : W) <<< 280)),
(((65589210370933792 : W) <<< 0) + ((32299149932065662 : W) <<< 56) + ((68551779065179999 : W) <<< 112) + ((62899726921383769 : W) <<< 168) + ((24584442099717886 : W) <<< 224) + ((15 : W) <<< 280)),
(((65589764423812640 : W) <<< 0) + ((34550950282621822 : W) <<< 56) + ((70873964937150303 : W) <<< 112) + ((62899726925643737 : W) <<< 168) + ((33627375566315262 : W) <<< 224) + ((15 : W) <<< 280)),
(((281509340643840 : W) <<< 0)),
(((65882874712432706 : W) <<< 0) + ((29074232912963525 : W) <<< 56) + ((4289905900301045 : W) <<< 112) + ((57534481505513909 : W) <<< 168) + ((64691367127361929 : W) <<< 224) + ((12 : W) <<< 280)),
(((63332147054903584 : W) <<< 0) + ((51381709507392023 : W) <<< 56) + ((44931090719584209 : W) <<< 112) + ((64654896693883612 : W) <<< 168) + ((59483006000477350 : W) <<< 224) + ((6 : W) <<< 280)),
(((66164626984149346 : W) <<< 0) + ((69748604585637847 : W) <<< 56) + ((44963118429679605 : W) <<< 112) + ((66981490277086205 : W) <<< 168) + ((69761258500242863 : W) <<< 224) + ((14 : W) <<< 280)),
(((17594333790240 : W) <<< 0)),
(((52987665507188872 : W) <<< 0) + ((58166197628296203 : W) <<< 56) + ((13218671089980756 : W) <<< 112) + ((14017350977439094 : W) <<< 168) + ((25993188479497779 : W) <<< 224) + ((17 : W) <<< 280)),
(((52988773612946568 : W) <<< 0) + ((62678596637940831 : W) <<< 56) + ((35736738017623894 : W) <<< 112) + ((51734997856931702 : W) <<< 168) + ((25998960950179515 : W) <<< 224) + ((27 : W) <<< 280)),
(((52989050639385992 : W) <<< 0) + ((62680933100149855 : W) <<< 56) + ((35737287790215127 : W) <<< 112) + ((51753728750374902 : W) <<< 168) + ((62309301933766335 : W) <<< 224) + ((27 : W) <<< 280)),
(((70377335160960 : W) <<< 0)),
(((24813847168700421 : W) <<< 0) + ((38267602979131360 : W) <<< 56) + ((41794373969858730 : W) <<< 112) + ((52538780907862667 : W) <<< 168) + ((48038020889614292 : W) <<< 224) + ((26 : W) <<< 280)),
(((24814124195139845 : W) <<< 0) + ((42783298576687095 : W) <<< 56) + ((44046259701775019 : W) <<< 112) + ((52837852634020559 : W) <<< 168) + ((52841789338859510 : W) <<< 224) + ((26 : W) <<< 280)),
(((274911465472 : W) <<< 0)),
(((54606700071879232 : W) <<< 0) + ((30705824976856111 : W) <<< 56) + ((17813383494262691 : W) <<< 112) + ((57251649594025401 : W) <<< 168) + ((46908417963026765 : W) <<< 224) + ((13 : W) <<< 280)),
(((55732601052988096 : W) <<< 0) + ((67298740188736559 : W) <<< 56) + ((17831259157585891 : W) <<< 112) + ((61905352156505595 : W) <<< 168) + ((67183447951244127 : W) <<< 224) + ((29 : W) <<< 280)),
(((4295491648 : W) <<< 0)),
(((59118610458873921 : W) <<< 0) + ((64711525938685925 : W) <<< 56) + ((38028695512636066 : W) <<< 112) + ((47962510958557363 : W) <<< 168) + ((46916532482452941 : W) <<< 224) + ((26 : W) <<< 280)),
(((59120826670389313 : W) <<< 0) + ((64739020172617725 : W) <<< 56) + ((65054760185454254 : W) <<< 112) + ((49238260177469107 : W) <<< 168) + ((49168884199435773 : W) <<< 224) + ((30 : W) <<< 280)),
(((59121934776147009 : W) <<< 0) + ((69242620873730045 : W) <<< 56) + ((69699131929394862 : W) <<< 112) + ((49238260185989043 : W) <<< 168) + ((67254751132630525 : W) <<< 224) + ((30 : W) <<< 280)),
(((563018681287680 : W) <<< 0)),
(((70157638280839208 : W) <<< 0) + ((17629007062269442 : W) <<< 56) + ((46133407405475156 : W) <<< 112) + ((69030575973807198 : W) <<< 168) + ((24297740627653797 : W) <<< 224) + ((21 : W) <<< 280)),
(((70159854492354600 : W) <<< 0) + ((53754571842715322 : W) <<< 56) + ((64148493260805468 : W) <<< 112) + ((71423149783070334 : W) <<< 168) + ((62727888221615541 : W) <<< 224) + ((21 : W) <<< 280)),
(((70195038898014252 : W) <<< 0) + ((53754571846909626 : W) <<< 56) + ((68670784586896894 : W) <<< 112) + ((71423149787297407 : W) <<< 168) + ((62763352840452021 : W) <<< 224) + ((29 : W) <<< 280)),
(((2199291723780 : W) <<< 0)),
(((51870629338583049 : W) <<< 0) + ((39939051812429792 : W) <<< 56) + ((46442017004048758 : W) <<< 112) + ((14405484756040854 : W) <<< 168) + ((15334454154536165 : W) <<< 224) + ((19 : W) <<< 280)),
(((51888358963589131 : W) <<< 0) + ((40510816112746464 : W) <<< 56) + ((48694920758686071 : W) <<< 112) + ((33618660450106775 : W) <<< 168) + ((33634880860302829 : W) <<< 224) + ((23 : W) <<< 280)),
(((51888913016467979 : W) <<< 0) + ((49537808724344814 : W) <<< 56) + ((53198692188943735 : W) <<< 112) + ((33618660986977695 : W) <<< 168) + ((33634885155286509 : W) <<< 224) + ((23 : W) <<< 280)),
(((549822930945 : W) <<< 0)),
(((2493237954816 : W) <<< 0) + ((50765705869496511 : W) <<< 56) + ((71253533977050765 : W) <<< 112) + ((12834915773945572 : W) <<< 168) + ((43237008799540535 : W) <<< 224) + ((22 : W) <<< 280)),
(((3047290833664 : W) <<< 0) + ((53022178641162431 : W) <<< 56) + ((71325036630343567 : W) <<< 112) + ((31449726023866348 : W) <<< 168) + ((52842484667903359 : W) <<< 224) + ((23 : W) <<< 280)),
(((31668982305065744 : W) <<< 0) + ((53304272160274879 : W) <<< 56) + ((71465779487539119 : W) <<< 112) + ((31449863462821868 : W) <<< 168) + ((52842484802121599 : W) <<< 224) + ((23 : W) <<< 280)),
(((140754670321920 : W) <<< 0)),
(((39410930236784768 : W) <<< 0) + ((57059805415197051 : W) <<< 56) + ((58011793957240153 : W) <<< 112) + ((7275020123958627 : W) <<< 168) + ((25083886380405363 : W) <<< 224) + ((25 : W) <<< 280)),
(((48435859116531842 : W) <<< 0) + ((57420446307307515 : W) <<< 56) + ((58051926332980573 : W) <<< 112) + ((26418926317010279 : W) <<< 168) + ((26280174360943611 : W) <<< 224) + ((29 : W) <<< 280)),
(((48438075328047234 : W) <<< 0) + ((66427647709532155 : W) <<< 56) + ((67340669820861789 : W) <<< 112) + ((26418926334050151 : W) <<< 168) + ((62451908227333115 : W) <<< 224) + ((29 : W) <<< 280)),
(((1126037362575360 : W) <<< 0)),
(((1196414697736320 : W) <<< 0)),
(((1759433379024000 : W) <<< 0)),
(((13195750342680 : W) <<< 0)),
(((294705090986520 : W) <<< 0)),
(((1761632670747780 : W) <<< 0)),
(((1374557327362 : W) <<< 0)),
(((312299424776760 : W) <<< 0)),
(((453054095098680 : W) <<< 0)),
(((453058390590328 : W) <<< 0)),
(((2214691061338108 : W) <<< 0)),
(((2215240884269053 : W) <<< 0)),
(((2216615441596415 : W) <<< 0)),
(((11258999068426239 : W) <<< 0) + ((4758699213066576 : W) <<< 56) + ((54188950142754836 : W) <<< 112) + ((10152207521683460 : W) <<< 168) + ((4874146052080800 : W) <<< 224) + ((2 : W) <<< 280)),
(((27021597764222975 : W) <<< 0) + ((1706633202241152 : W) <<< 56) + ((4630053532287146 : W) <<< 112) + ((42931634714018315 : W) <<< 168) + ((39028545025086224 : W) <<< 224) + ((8 : W) <<< 280))
]
def tmask : W := (((2251799813685247 : W) <<< 0))
def lit (i : ℕ) (j : Fin 285) : Bool :=
  (reps.getD ((j.val+1)/13) 0).testBit ((i/13)*13+(i+13-(j.val+1)%13)%13)
def atRaw (i : ℕ) : Col := ((List.finRange 285).filter (lit i)).toFinset
theorem member_atRaw (i : ℕ) (j : Fin 285) : j∈atRaw i ↔ lit i j=true := by simp [atRaw]
theorem index_raw {w : Col} (h : w∈raw) : ∃ i : Fin 26, w=atRaw i.val := by
  change w∈(List.range 26).map atRaw at h
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp h
  exact ⟨⟨i,List.mem_range.mp hi⟩,eq.symm⟩

theorem rawW_len : rawW.length=26 := rfl
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem physical_bits : ∀ i : Fin 26,∀ j : Fin 285,lit i.val j=(rawW.getD i.val 0).getLsbD j.val := by decide +kernel
theorem raw_eq : raw=rawW.map col := by
  change (List.range 26).map atRaw=rawW.map col
  apply List.ext_getElem
  · simp [rawW_len]
  · intro i h1 h2
    have hi : i<26 := by simpa using h1
    simp only [List.getElem_map,List.getElem_range]
    ext j
    rw [member_atRaw,membership,physical_bits ⟨i,hi⟩ j,List.getD_eq_getElem _ _ (by rwa [rawW_len])]
set_option maxRecDepth 10000 in
theorem target_bit : ∀ j : Fin 285, decide (j.val<51)=tmask.getLsbD j.val := by decide +kernel
theorem target_eq : target=col tmask := by
  ext j
  simp only [target,List.mem_toFinset,List.mem_filter,List.mem_finRange,true_and, membership]
  rw [target_bit]

def ok (B : List W) (v : W) := v∉B ∧ ∃ a∈B,∃ b∈B,
  ((a&&&b)≠a ∧ (a&&&b)≠b ∧ (v=(a&&&b) ∨ v=(a|||b)))
instance (B : List W) (v : W) : Decidable (ok B v) := by unfold ok;infer_instance
def unionable (B : List W) (v : W) := ∃ a∈B,∃ b∈B, (a&&&b)≠a ∧ (a&&&b)≠b ∧ v=(a|||b)
instance (B : List W) (v : W) : Decidable (unionable B v) := by unfold unionable; infer_instance

theorem transfer (B : List W) (v : W) (h : ok B v) :
    ∃ a∈B.map col,∃ b∈B.map col,¬a⊆b ∧ ¬b⊆a ∧ col v∉B.map col ∧ (col v=a∩b ∨ col v=a∪b) := by
  obtain ⟨new,a,ha,b,hb,l,r,op⟩ := h
  refine ⟨col a,List.mem_map_of_mem ha,col b,List.mem_map_of_mem hb,fun sub=>l ((contained a b).mp sub),
      fun sub=>r (by simpa [BitVec.and_comm] using (contained b a).mp sub),?_,?_⟩
  · intro dup
    obtain ⟨u,hu,eq⟩ := List.mem_map.mp dup
    exact new (col_inj eq ▸ hu)
  · rcases op with h|h
    · left; rw [h,band]
    · right;rw [h,bor]

theorem reflect (B : List W) (v : W) (h : canJoin (B.map col) (col v)) : unionable B v := by
  obtain ⟨x,hx,y,hy,xy,yx,eq⟩ := h
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
  refine ⟨a,ha,b,hb,fun e=>xy ((contained a b).mpr e),fun e=>yx ((contained b a).mpr ?_),?_⟩
  · simpa [BitVec.and_comm] using e
  · exact col_inj (eq.trans (bor a b).symm)

def chosen (j : Fin 13) : ℕ := #[3,7,11,15,19,23,26,29,33,37,41,45,49][j.val]!
def preds : Array (ℕ × ℕ) := #[(8,1),(26,6),(5,27),(18,28),(0,5),(7,4),(30,31),(17,32),(11,2),(5,3),(34,35),(15,36),(0,6),(11,38),(10,39),(23,40),(7,2),(6,9),(42,43),(19,44),(8,4),(46,11),(9,47),(21,48),(1,3),(50,9),(13,51),(7,10),(8,53),(20,54),(7,1),(56,12),(57,11),(24,58),(6,4),(12,60),(61,3),(16,62),(1,4),(64,2),(65,10),(14,66),(9,12),(68,10),(69,5),(22,70),(0,8),(72,2),(73,12),(25,74),(75,49),(59,76),(29,33),(41,78),(77,63),(37,52),(45,79),(82,71),(83,55),(84,80),(85,67),(86,81),(87,20),(87,3)]
def previous (i : ℕ) := rawW++gatesW.take i
def here (i : ℕ) := gatesW.getD i 0
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem supplied : ∀ i : Fin 64,
   let z := preds[i.val]!
   let C := previous i.val
   let a := C.getD z.1 0
   let b := C.getD z.2 0
   here i.val∉C ∧ a∈C ∧ b∈C ∧ (a&&&b)≠a ∧ (a&&&b)≠b ∧
      (here i.val=(a&&&b) ∨ here i.val=(a|||b)) := by decide +kernel
theorem legal (i : Fin 64) : ok (rawW++gatesW.take i.val) (gatesW.getD i.val 0) := by
  obtain ⟨novel,ha,hb,ab,ba,op⟩ := supplied i
  exact ⟨novel,_,ha,_,hb,ab,ba,op⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem strict_mask : ∀ j : Fin 13, chosen j<64 ∧
  (previous (chosen j)).all (fun a => decide ((a&&&here (chosen j))≠a))=true := by decide +kernel
theorem excluded (j : Fin 13) : chosen j<64 ∧ ¬unionable (rawW++gatesW.take (chosen j)) (gatesW.getD (chosen j) 0) := by
  obtain ⟨lt,all⟩ := strict_mask j
  refine ⟨lt,?_⟩
  rintro ⟨a,ha,b,_,_,_,eq⟩
  have bad := of_decide_eq_true (List.all_eq_true.mp all a ha)
  apply bad
  change a &&& gatesW.getD (chosen j) 0=a
  rw [eq]
  exact BitVec.eq_of_getLsbD_eq (fun i hi => by simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]; cases a.getLsbD i <;> simp)
def outputA : W := (rawW++gatesW).getD 88 0
def outputB : W := (rawW++gatesW).getD 89 0
set_option maxRecDepth 10000 in
theorem tops : outputA∈rawW++gatesW ∧ outputB∈rawW++gatesW ∧
    outputA&&&outputB=tmask ∧ outputA&&&outputB≠outputA ∧ outputA&&&outputB≠outputB := by decide +kernel

private theorem map_take_cols (l : List W) (i : Nat) :
    (l.map col).take i = (l.take i).map col := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (List.cons (col a)) (ih i)

theorem control :
    ∃ (L : List Col) (f : Fin 13 → ℕ), L.length=64 ∧ admissible raw L ∧ cap raw L target ∧
        Function.Injective f ∧ ∀ j, f j<L.length ∧ ¬canJoin (raw++L.take (f j)) (L.getD (f j) ∅) := by
  let L := gatesW.map col
  have len : L.length=64 := by rfl
  have bank_map (i : ℕ) : raw++L.take i=(rawW++gatesW.take i).map col := by
    rw [raw_eq,List.map_append]
    exact congrArg (List.append (rawW.map col)) (map_take_cols gatesW i)
  have val (i : ℕ) (hi : i<64) : L.getD i ∅=col (gatesW.getD i 0) := by
    rw [List.getD_eq_getElem _ _ (by simpa [len] using hi),List.getD_eq_getElem _ _ (by exact hi : i<gatesW.length)]
    simp [L] <;> rfl
  refine ⟨L,chosen,len,?_,?_,by decide +kernel,?_⟩
  · intro i
    have hi : i.val<64 := by simpa only [len] using i.isLt
    have pr := transfer _ _ (legal ⟨i.val,hi⟩)
    rw [←bank_map,←val _ hi,List.getD_eq_getElem _ _ i.isLt] at pr
    exact pr
  · have mk : raw++L=(rawW++gatesW).map col := by simp [raw_eq,L]
    rw [cap,mk,target_eq]
    obtain ⟨ha,hb,eq,l,r⟩ := tops
    exact ⟨col outputA,List.mem_map_of_mem ha,col outputB,List.mem_map_of_mem hb,
      fun h=>l ((contained _ _).mp h),fun h=>r (by simpa [BitVec.and_comm] using (contained _ _).mp h),
      (band _ _).symm.trans (congrArg col eq)⟩
  · intro j
    obtain ⟨hi,no⟩ := excluded j
    refine ⟨by rwa [len],?_⟩
    rw [bank_map,val _ hi]
    exact fun h => no (reflect _ _ h)
end PEqualNP.Outside.L_meta_17379.A17379.Control

namespace PEqualNP.Outside.L_meta_17379.A17379
def lit (i : ℕ) (j : Fin 285) : Bool :=
  (reps.getD ((j.val+1)/13) 0).testBit ((i/13)*13+(i+13-(j.val+1)%13)%13)
def atRaw (i : ℕ) : Col := ((List.finRange 285).filter (lit i)).toFinset
theorem member_atRaw (i : ℕ) (j : Fin 285) : j∈atRaw i ↔ lit i j=true := by simp [atRaw]
theorem index_raw {w : Col} (h : w∈raw) : ∃ i : Fin 26, w=atRaw i.val := by
  change w∈(List.range 26).map atRaw at h
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp h
  exact ⟨⟨i,List.mem_range.mp hi⟩,eq.symm⟩

theorem small_private : ∀ i : Fin 26, (lit i.val 0 && lit i.val 1)=false := by decide +kernel
theorem no_raw_target : ∀ z∈raw, ¬target⊆z := by
  intro z hz sub
  obtain ⟨i,rfl⟩ := index_raw hz
  have u := (member_atRaw i.val 0).mp (sub (by simp [target] : (0 : Fin 285)∈target))
  have v := (member_atRaw i.val 1).mp (sub (by simp [target] : (1 : Fin 285)∈target))
  have bad := small_private i
  simp [u,v] at bad

theorem cut_first : have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))) (x4 : ℕ) (x5 : Fin x4 → ℕ),   (∀ (x6 : Fin x3.length),       have x7 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x6) x3;       ∃ x8 ∈ x7, ∃ x9 ∈ x7, ¬x8 ⊆ x9 ∧ ¬x9 ⊆ x8 ∧ x3.get x6 ∉ x7 ∧ (x3.get x6 = x8 ∩ x9 ∨ x3.get x6 = x8 ∪ x9)) →     (∃ x7 ∈ x2, ∃ x8 ∈ x2 ++ x3, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x7 ∩ x8 = (List.filter (fun (x9 : Fin (285 : ℕ)) => Decidable.decide (↑x9 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset) → Function.Injective x5 → (∀ (x9 : Fin x4), x5 x9 < x3.length ∧ ¬∃ x10 ∈ x2 ++ List.take (x5 x9) x3, ∃ x11 ∈ x2 ++ List.take (x5 x9) x3, ¬x10 ⊆ x11 ∧ ¬x11 ⊆ x10 ∧ x3.getD (x5 x9) ∅ = x10 ∪ x11) → (50 : ℕ) + x4 ≤ x3.length := by
  dsimp only
  intro L m f valid pair inj choose
  obtain ⟨a,ha,b,_,_,_,eq⟩ := pair
  change a ∩ b = target at eq
  exact (no_raw_target a ha (eq ▸ Finset.inter_subset_left)).elim

theorem both_gates (L : List Col) (h : cap raw L target) :
    ∃ a∈L,∃ b∈L,¬a⊆b ∧ ¬b⊆a ∧ a∩b=target := by
  obtain ⟨a,ha,b,hb,ab,ba,eq⟩ := h
  refine ⟨a,(List.mem_append.mp ha).resolve_left ?_,b,(List.mem_append.mp hb).resolve_left ?_,ab,ba,eq⟩
  · intro hraw
    exact no_raw_target a hraw (by rw [←eq];exact Finset.inter_subset_left)
  · intro hraw
    exact no_raw_target b hraw (by rw [←eq];exact Finset.inter_subset_right)
end PEqualNP.Outside.L_meta_17379.A17379
