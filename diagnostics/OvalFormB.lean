import PEqualNP.Defs
namespace Plane9341.OvalForm
open Finset
abbrev V := Fin 21
abbrev H := Fin 168
abbrev Box := Finset V × Finset V
def hs : Array (Nat × Nat) := #[(1369,872450),(2738,1744900),(4157,385088),(5476,1392649),(8314,770176),(9507,608268),(10952,688147),(12359,115736),(16628,1540352),(19014,1216536),(20681,360978),(21904,1376294),(24718,231472),(31233,32862),(33256,983553),(33969,860420),(36355,536604),(38028,335921),(41362,721956),(43808,655437),(49436,462944),(50245,332056),(53537,328268),(62466,65724),(66512,1967106),(67209,796690),(67938,1720840),(72710,1073208),(76056,671842),(76865,540954),(82724,1443912),(87616,1310874),(98872,925888),(100490,664112),(102917,271448),(107074,656536),(124932,131448),(133024,1837061),(133195,578064),(134418,1593380),(135876,1344529),(139907,560148),(141361,573764),(145420,49265),(147981,301136),(152112,1343684),(153730,1081908),(164625,791620),(165448,790673),(175232,524597),(196905,805440),(197744,1851776),(200980,1328224),(205834,542896),(214148,1313072),(229569,788240),(249864,262896),(262315,633344),(264729,569410),(266048,1576971),(266390,1156128),(268836,1089609),(270545,623874),(271752,591907),(279814,1120296),(282722,1147528),(286757,100680),(290840,98530),(295235,595464),(295962,602272),(304224,590217),(307460,66665),(329250,1583240),(330896,1581346),(336641,527434),(350464,1049194),(362529,533320),(393810,1610880),(395488,1606401),(401960,559297),(411668,1085792),(428296,528993),(459138,1576480),(499728,525792),(524630,1266688),(525327,96272),(529458,1138820),(532096,1056791),(532780,215105),(536849,83014),(537672,82067),(541090,1247748),(543504,1183814),(550017,67862),(559628,143441),(561283,75284),(565444,197905),(573514,201360),(581680,197060),(590470,1190928),(591924,1204544),(595977,25170),(608448,1180434),(614920,133330),(658500,1069329),(661792,1065541),(673282,1054868),(700928,1237),(706561,4948),(725058,1066640),(729093,19792),(787620,1124609),(790976,1115651),(803081,72258),(803920,1118594),(819221,79168),(823336,74433),(856592,1057986),(918276,1055809),(999456,1051584),(1049260,436225),(1050654,192544),(1053329,304134),(1054755,57868),(1058916,180489),(1064192,16431),(1065560,430210),(1066753,268302),(1073698,166028),(1075344,164134),(1082180,398345),(1087008,270477),(1100034,135724),(1115173,289032),(1118529,280074),(1119256,286882),(1122566,150568),(1130888,395810),(1147028,402720),(1163360,394120),(1179733,316672),(1180940,284705),(1183848,311937),(1191954,50340),(1196193,297732),(1216896,263717),(1229840,266660),(1311239,48136),(1317000,41507),(1323584,33931),(1329217,37642),(1346564,12585),(1401856,2474),(1413122,9896),(1450116,36129),(1458186,39584),(1575240,152067),(1575953,28934),(1581952,134151),(1606162,144516),(1607840,140037),(1638442,158336),(1646672,148866),(1704195,24068),(1713184,18821),(1836552,14467),(1900673,12034),(1998912,6017)]
def rows : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def bit (r c : V) := (rows.getD r.val 0).testBit c.val
def mk (m : Nat) : Finset V := univ.filter fun v=>m.testBit v.val
def hbox (h : H) : Box := (mk (hs[h.val]!).1,mk (hs[h.val]!).2)
def rawPrice (b : Box) (p : V) : ℤ := b.2.card - 4*((b.2.filter (fun c=>bit p c=true)).card : ℤ)
def rowMark (b : Box) (p : V) : ℤ := if p∈b.1 then 1 else 0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side0 : ∀ p : V, rawPrice (hbox 0) p = 8*rowMark (hbox 0) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side1 : ∀ p : V, rawPrice (hbox 1) p = 8*rowMark (hbox 1) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side2 : ∀ p : V, rawPrice (hbox 2) p = 8*rowMark (hbox 2) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side3 : ∀ p : V, rawPrice (hbox 3) p = 8*rowMark (hbox 3) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side4 : ∀ p : V, rawPrice (hbox 4) p = 8*rowMark (hbox 4) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side5 : ∀ p : V, rawPrice (hbox 5) p = 8*rowMark (hbox 5) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side6 : ∀ p : V, rawPrice (hbox 6) p = 8*rowMark (hbox 6) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side7 : ∀ p : V, rawPrice (hbox 7) p = 8*rowMark (hbox 7) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side8 : ∀ p : V, rawPrice (hbox 8) p = 8*rowMark (hbox 8) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side9 : ∀ p : V, rawPrice (hbox 9) p = 8*rowMark (hbox 9) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side10 : ∀ p : V, rawPrice (hbox 10) p = 8*rowMark (hbox 10) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side11 : ∀ p : V, rawPrice (hbox 11) p = 8*rowMark (hbox 11) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side12 : ∀ p : V, rawPrice (hbox 12) p = 8*rowMark (hbox 12) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side13 : ∀ p : V, rawPrice (hbox 13) p = 8*rowMark (hbox 13) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side14 : ∀ p : V, rawPrice (hbox 14) p = 8*rowMark (hbox 14) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side15 : ∀ p : V, rawPrice (hbox 15) p = 8*rowMark (hbox 15) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side16 : ∀ p : V, rawPrice (hbox 16) p = 8*rowMark (hbox 16) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side17 : ∀ p : V, rawPrice (hbox 17) p = 8*rowMark (hbox 17) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side18 : ∀ p : V, rawPrice (hbox 18) p = 8*rowMark (hbox 18) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side19 : ∀ p : V, rawPrice (hbox 19) p = 8*rowMark (hbox 19) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side20 : ∀ p : V, rawPrice (hbox 20) p = 8*rowMark (hbox 20) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side21 : ∀ p : V, rawPrice (hbox 21) p = 8*rowMark (hbox 21) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side22 : ∀ p : V, rawPrice (hbox 22) p = 8*rowMark (hbox 22) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side23 : ∀ p : V, rawPrice (hbox 23) p = 8*rowMark (hbox 23) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side24 : ∀ p : V, rawPrice (hbox 24) p = 8*rowMark (hbox 24) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side25 : ∀ p : V, rawPrice (hbox 25) p = 8*rowMark (hbox 25) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side26 : ∀ p : V, rawPrice (hbox 26) p = 8*rowMark (hbox 26) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side27 : ∀ p : V, rawPrice (hbox 27) p = 8*rowMark (hbox 27) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side28 : ∀ p : V, rawPrice (hbox 28) p = 8*rowMark (hbox 28) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side29 : ∀ p : V, rawPrice (hbox 29) p = 8*rowMark (hbox 29) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side30 : ∀ p : V, rawPrice (hbox 30) p = 8*rowMark (hbox 30) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side31 : ∀ p : V, rawPrice (hbox 31) p = 8*rowMark (hbox 31) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side32 : ∀ p : V, rawPrice (hbox 32) p = 8*rowMark (hbox 32) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side33 : ∀ p : V, rawPrice (hbox 33) p = 8*rowMark (hbox 33) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side34 : ∀ p : V, rawPrice (hbox 34) p = 8*rowMark (hbox 34) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side35 : ∀ p : V, rawPrice (hbox 35) p = 8*rowMark (hbox 35) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side36 : ∀ p : V, rawPrice (hbox 36) p = 8*rowMark (hbox 36) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side37 : ∀ p : V, rawPrice (hbox 37) p = 8*rowMark (hbox 37) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side38 : ∀ p : V, rawPrice (hbox 38) p = 8*rowMark (hbox 38) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side39 : ∀ p : V, rawPrice (hbox 39) p = 8*rowMark (hbox 39) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side40 : ∀ p : V, rawPrice (hbox 40) p = 8*rowMark (hbox 40) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side41 : ∀ p : V, rawPrice (hbox 41) p = 8*rowMark (hbox 41) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side42 : ∀ p : V, rawPrice (hbox 42) p = 8*rowMark (hbox 42) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side43 : ∀ p : V, rawPrice (hbox 43) p = 8*rowMark (hbox 43) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side44 : ∀ p : V, rawPrice (hbox 44) p = 8*rowMark (hbox 44) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side45 : ∀ p : V, rawPrice (hbox 45) p = 8*rowMark (hbox 45) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side46 : ∀ p : V, rawPrice (hbox 46) p = 8*rowMark (hbox 46) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side47 : ∀ p : V, rawPrice (hbox 47) p = 8*rowMark (hbox 47) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side48 : ∀ p : V, rawPrice (hbox 48) p = 8*rowMark (hbox 48) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side49 : ∀ p : V, rawPrice (hbox 49) p = 8*rowMark (hbox 49) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side50 : ∀ p : V, rawPrice (hbox 50) p = 8*rowMark (hbox 50) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side51 : ∀ p : V, rawPrice (hbox 51) p = 8*rowMark (hbox 51) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side52 : ∀ p : V, rawPrice (hbox 52) p = 8*rowMark (hbox 52) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side53 : ∀ p : V, rawPrice (hbox 53) p = 8*rowMark (hbox 53) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side54 : ∀ p : V, rawPrice (hbox 54) p = 8*rowMark (hbox 54) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side55 : ∀ p : V, rawPrice (hbox 55) p = 8*rowMark (hbox 55) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side56 : ∀ p : V, rawPrice (hbox 56) p = 8*rowMark (hbox 56) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side57 : ∀ p : V, rawPrice (hbox 57) p = 8*rowMark (hbox 57) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side58 : ∀ p : V, rawPrice (hbox 58) p = 8*rowMark (hbox 58) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side59 : ∀ p : V, rawPrice (hbox 59) p = 8*rowMark (hbox 59) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side60 : ∀ p : V, rawPrice (hbox 60) p = 8*rowMark (hbox 60) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side61 : ∀ p : V, rawPrice (hbox 61) p = 8*rowMark (hbox 61) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side62 : ∀ p : V, rawPrice (hbox 62) p = 8*rowMark (hbox 62) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side63 : ∀ p : V, rawPrice (hbox 63) p = 8*rowMark (hbox 63) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side64 : ∀ p : V, rawPrice (hbox 64) p = 8*rowMark (hbox 64) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side65 : ∀ p : V, rawPrice (hbox 65) p = 8*rowMark (hbox 65) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side66 : ∀ p : V, rawPrice (hbox 66) p = 8*rowMark (hbox 66) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side67 : ∀ p : V, rawPrice (hbox 67) p = 8*rowMark (hbox 67) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side68 : ∀ p : V, rawPrice (hbox 68) p = 8*rowMark (hbox 68) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side69 : ∀ p : V, rawPrice (hbox 69) p = 8*rowMark (hbox 69) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side70 : ∀ p : V, rawPrice (hbox 70) p = 8*rowMark (hbox 70) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side71 : ∀ p : V, rawPrice (hbox 71) p = 8*rowMark (hbox 71) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side72 : ∀ p : V, rawPrice (hbox 72) p = 8*rowMark (hbox 72) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side73 : ∀ p : V, rawPrice (hbox 73) p = 8*rowMark (hbox 73) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side74 : ∀ p : V, rawPrice (hbox 74) p = 8*rowMark (hbox 74) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side75 : ∀ p : V, rawPrice (hbox 75) p = 8*rowMark (hbox 75) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side76 : ∀ p : V, rawPrice (hbox 76) p = 8*rowMark (hbox 76) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side77 : ∀ p : V, rawPrice (hbox 77) p = 8*rowMark (hbox 77) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side78 : ∀ p : V, rawPrice (hbox 78) p = 8*rowMark (hbox 78) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side79 : ∀ p : V, rawPrice (hbox 79) p = 8*rowMark (hbox 79) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side80 : ∀ p : V, rawPrice (hbox 80) p = 8*rowMark (hbox 80) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side81 : ∀ p : V, rawPrice (hbox 81) p = 8*rowMark (hbox 81) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side82 : ∀ p : V, rawPrice (hbox 82) p = 8*rowMark (hbox 82) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side83 : ∀ p : V, rawPrice (hbox 83) p = 8*rowMark (hbox 83) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side84 : ∀ p : V, rawPrice (hbox 84) p = 8*rowMark (hbox 84) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side85 : ∀ p : V, rawPrice (hbox 85) p = 8*rowMark (hbox 85) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side86 : ∀ p : V, rawPrice (hbox 86) p = 8*rowMark (hbox 86) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side87 : ∀ p : V, rawPrice (hbox 87) p = 8*rowMark (hbox 87) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side88 : ∀ p : V, rawPrice (hbox 88) p = 8*rowMark (hbox 88) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side89 : ∀ p : V, rawPrice (hbox 89) p = 8*rowMark (hbox 89) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side90 : ∀ p : V, rawPrice (hbox 90) p = 8*rowMark (hbox 90) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side91 : ∀ p : V, rawPrice (hbox 91) p = 8*rowMark (hbox 91) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side92 : ∀ p : V, rawPrice (hbox 92) p = 8*rowMark (hbox 92) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side93 : ∀ p : V, rawPrice (hbox 93) p = 8*rowMark (hbox 93) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side94 : ∀ p : V, rawPrice (hbox 94) p = 8*rowMark (hbox 94) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side95 : ∀ p : V, rawPrice (hbox 95) p = 8*rowMark (hbox 95) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side96 : ∀ p : V, rawPrice (hbox 96) p = 8*rowMark (hbox 96) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side97 : ∀ p : V, rawPrice (hbox 97) p = 8*rowMark (hbox 97) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side98 : ∀ p : V, rawPrice (hbox 98) p = 8*rowMark (hbox 98) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side99 : ∀ p : V, rawPrice (hbox 99) p = 8*rowMark (hbox 99) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side100 : ∀ p : V, rawPrice (hbox 100) p = 8*rowMark (hbox 100) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side101 : ∀ p : V, rawPrice (hbox 101) p = 8*rowMark (hbox 101) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side102 : ∀ p : V, rawPrice (hbox 102) p = 8*rowMark (hbox 102) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side103 : ∀ p : V, rawPrice (hbox 103) p = 8*rowMark (hbox 103) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side104 : ∀ p : V, rawPrice (hbox 104) p = 8*rowMark (hbox 104) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side105 : ∀ p : V, rawPrice (hbox 105) p = 8*rowMark (hbox 105) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side106 : ∀ p : V, rawPrice (hbox 106) p = 8*rowMark (hbox 106) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side107 : ∀ p : V, rawPrice (hbox 107) p = 8*rowMark (hbox 107) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side108 : ∀ p : V, rawPrice (hbox 108) p = 8*rowMark (hbox 108) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side109 : ∀ p : V, rawPrice (hbox 109) p = 8*rowMark (hbox 109) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side110 : ∀ p : V, rawPrice (hbox 110) p = 8*rowMark (hbox 110) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side111 : ∀ p : V, rawPrice (hbox 111) p = 8*rowMark (hbox 111) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side112 : ∀ p : V, rawPrice (hbox 112) p = 8*rowMark (hbox 112) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side113 : ∀ p : V, rawPrice (hbox 113) p = 8*rowMark (hbox 113) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side114 : ∀ p : V, rawPrice (hbox 114) p = 8*rowMark (hbox 114) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side115 : ∀ p : V, rawPrice (hbox 115) p = 8*rowMark (hbox 115) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side116 : ∀ p : V, rawPrice (hbox 116) p = 8*rowMark (hbox 116) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side117 : ∀ p : V, rawPrice (hbox 117) p = 8*rowMark (hbox 117) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side118 : ∀ p : V, rawPrice (hbox 118) p = 8*rowMark (hbox 118) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side119 : ∀ p : V, rawPrice (hbox 119) p = 8*rowMark (hbox 119) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side120 : ∀ p : V, rawPrice (hbox 120) p = 8*rowMark (hbox 120) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side121 : ∀ p : V, rawPrice (hbox 121) p = 8*rowMark (hbox 121) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side122 : ∀ p : V, rawPrice (hbox 122) p = 8*rowMark (hbox 122) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side123 : ∀ p : V, rawPrice (hbox 123) p = 8*rowMark (hbox 123) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side124 : ∀ p : V, rawPrice (hbox 124) p = 8*rowMark (hbox 124) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side125 : ∀ p : V, rawPrice (hbox 125) p = 8*rowMark (hbox 125) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side126 : ∀ p : V, rawPrice (hbox 126) p = 8*rowMark (hbox 126) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side127 : ∀ p : V, rawPrice (hbox 127) p = 8*rowMark (hbox 127) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side128 : ∀ p : V, rawPrice (hbox 128) p = 8*rowMark (hbox 128) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side129 : ∀ p : V, rawPrice (hbox 129) p = 8*rowMark (hbox 129) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side130 : ∀ p : V, rawPrice (hbox 130) p = 8*rowMark (hbox 130) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side131 : ∀ p : V, rawPrice (hbox 131) p = 8*rowMark (hbox 131) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side132 : ∀ p : V, rawPrice (hbox 132) p = 8*rowMark (hbox 132) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side133 : ∀ p : V, rawPrice (hbox 133) p = 8*rowMark (hbox 133) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side134 : ∀ p : V, rawPrice (hbox 134) p = 8*rowMark (hbox 134) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side135 : ∀ p : V, rawPrice (hbox 135) p = 8*rowMark (hbox 135) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side136 : ∀ p : V, rawPrice (hbox 136) p = 8*rowMark (hbox 136) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side137 : ∀ p : V, rawPrice (hbox 137) p = 8*rowMark (hbox 137) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side138 : ∀ p : V, rawPrice (hbox 138) p = 8*rowMark (hbox 138) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side139 : ∀ p : V, rawPrice (hbox 139) p = 8*rowMark (hbox 139) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side140 : ∀ p : V, rawPrice (hbox 140) p = 8*rowMark (hbox 140) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side141 : ∀ p : V, rawPrice (hbox 141) p = 8*rowMark (hbox 141) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side142 : ∀ p : V, rawPrice (hbox 142) p = 8*rowMark (hbox 142) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side143 : ∀ p : V, rawPrice (hbox 143) p = 8*rowMark (hbox 143) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side144 : ∀ p : V, rawPrice (hbox 144) p = 8*rowMark (hbox 144) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side145 : ∀ p : V, rawPrice (hbox 145) p = 8*rowMark (hbox 145) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side146 : ∀ p : V, rawPrice (hbox 146) p = 8*rowMark (hbox 146) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side147 : ∀ p : V, rawPrice (hbox 147) p = 8*rowMark (hbox 147) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side148 : ∀ p : V, rawPrice (hbox 148) p = 8*rowMark (hbox 148) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side149 : ∀ p : V, rawPrice (hbox 149) p = 8*rowMark (hbox 149) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side150 : ∀ p : V, rawPrice (hbox 150) p = 8*rowMark (hbox 150) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side151 : ∀ p : V, rawPrice (hbox 151) p = 8*rowMark (hbox 151) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side152 : ∀ p : V, rawPrice (hbox 152) p = 8*rowMark (hbox 152) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side153 : ∀ p : V, rawPrice (hbox 153) p = 8*rowMark (hbox 153) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side154 : ∀ p : V, rawPrice (hbox 154) p = 8*rowMark (hbox 154) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side155 : ∀ p : V, rawPrice (hbox 155) p = 8*rowMark (hbox 155) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side156 : ∀ p : V, rawPrice (hbox 156) p = 8*rowMark (hbox 156) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side157 : ∀ p : V, rawPrice (hbox 157) p = 8*rowMark (hbox 157) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side158 : ∀ p : V, rawPrice (hbox 158) p = 8*rowMark (hbox 158) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side159 : ∀ p : V, rawPrice (hbox 159) p = 8*rowMark (hbox 159) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side160 : ∀ p : V, rawPrice (hbox 160) p = 8*rowMark (hbox 160) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side161 : ∀ p : V, rawPrice (hbox 161) p = 8*rowMark (hbox 161) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side162 : ∀ p : V, rawPrice (hbox 162) p = 8*rowMark (hbox 162) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side163 : ∀ p : V, rawPrice (hbox 163) p = 8*rowMark (hbox 163) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side164 : ∀ p : V, rawPrice (hbox 164) p = 8*rowMark (hbox 164) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side165 : ∀ p : V, rawPrice (hbox 165) p = 8*rowMark (hbox 165) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side166 : ∀ p : V, rawPrice (hbox 166) p = 8*rowMark (hbox 166) p-2 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem side167 : ∀ p : V, rawPrice (hbox 167) p = 8*rowMark (hbox 167) p-2 := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 12000 in
theorem ovalPrice (h : H) (p : V) : rawPrice (hbox h) p = 8*rowMark (hbox h) p-2 := by
  fin_cases h
  · exact side0 p
  · exact side1 p
  · exact side2 p
  · exact side3 p
  · exact side4 p
  · exact side5 p
  · exact side6 p
  · exact side7 p
  · exact side8 p
  · exact side9 p
  · exact side10 p
  · exact side11 p
  · exact side12 p
  · exact side13 p
  · exact side14 p
  · exact side15 p
  · exact side16 p
  · exact side17 p
  · exact side18 p
  · exact side19 p
  · exact side20 p
  · exact side21 p
  · exact side22 p
  · exact side23 p
  · exact side24 p
  · exact side25 p
  · exact side26 p
  · exact side27 p
  · exact side28 p
  · exact side29 p
  · exact side30 p
  · exact side31 p
  · exact side32 p
  · exact side33 p
  · exact side34 p
  · exact side35 p
  · exact side36 p
  · exact side37 p
  · exact side38 p
  · exact side39 p
  · exact side40 p
  · exact side41 p
  · exact side42 p
  · exact side43 p
  · exact side44 p
  · exact side45 p
  · exact side46 p
  · exact side47 p
  · exact side48 p
  · exact side49 p
  · exact side50 p
  · exact side51 p
  · exact side52 p
  · exact side53 p
  · exact side54 p
  · exact side55 p
  · exact side56 p
  · exact side57 p
  · exact side58 p
  · exact side59 p
  · exact side60 p
  · exact side61 p
  · exact side62 p
  · exact side63 p
  · exact side64 p
  · exact side65 p
  · exact side66 p
  · exact side67 p
  · exact side68 p
  · exact side69 p
  · exact side70 p
  · exact side71 p
  · exact side72 p
  · exact side73 p
  · exact side74 p
  · exact side75 p
  · exact side76 p
  · exact side77 p
  · exact side78 p
  · exact side79 p
  · exact side80 p
  · exact side81 p
  · exact side82 p
  · exact side83 p
  · exact side84 p
  · exact side85 p
  · exact side86 p
  · exact side87 p
  · exact side88 p
  · exact side89 p
  · exact side90 p
  · exact side91 p
  · exact side92 p
  · exact side93 p
  · exact side94 p
  · exact side95 p
  · exact side96 p
  · exact side97 p
  · exact side98 p
  · exact side99 p
  · exact side100 p
  · exact side101 p
  · exact side102 p
  · exact side103 p
  · exact side104 p
  · exact side105 p
  · exact side106 p
  · exact side107 p
  · exact side108 p
  · exact side109 p
  · exact side110 p
  · exact side111 p
  · exact side112 p
  · exact side113 p
  · exact side114 p
  · exact side115 p
  · exact side116 p
  · exact side117 p
  · exact side118 p
  · exact side119 p
  · exact side120 p
  · exact side121 p
  · exact side122 p
  · exact side123 p
  · exact side124 p
  · exact side125 p
  · exact side126 p
  · exact side127 p
  · exact side128 p
  · exact side129 p
  · exact side130 p
  · exact side131 p
  · exact side132 p
  · exact side133 p
  · exact side134 p
  · exact side135 p
  · exact side136 p
  · exact side137 p
  · exact side138 p
  · exact side139 p
  · exact side140 p
  · exact side141 p
  · exact side142 p
  · exact side143 p
  · exact side144 p
  · exact side145 p
  · exact side146 p
  · exact side147 p
  · exact side148 p
  · exact side149 p
  · exact side150 p
  · exact side151 p
  · exact side152 p
  · exact side153 p
  · exact side154 p
  · exact side155 p
  · exact side156 p
  · exact side157 p
  · exact side158 p
  · exact side159 p
  · exact side160 p
  · exact side161 p
  · exact side162 p
  · exact side163 p
  · exact side164 p
  · exact side165 p
  · exact side166 p
  · exact side167 p

def rowSum (b : Box) (x : V→ℚ) := ∑ p, x p*(rowMark b p : ℚ)
def columnSum (b : Box) (x : V→ℚ) := ∑ p, x p*(rawPrice b p : ℚ)
def form (b : Box) (x : V→ℚ) := rowSum b x * columnSum b x

theorem centeredPrice (h : H) (x : V→ℚ) (center : ∑ p,x p=0) :
    columnSum (hbox h) x=8*rowSum (hbox h) x := by
  unfold columnSum rowSum
  have atP (p : V) : x p * (rawPrice (hbox h) p : ℚ) =
      8*(x p*(rowMark (hbox h) p : ℚ))-2*x p := by
    rw [ovalPrice]
    push_cast
    ring
  simp only [atP,Finset.sum_sub_distrib,← Finset.mul_sum,center,mul_zero,sub_zero]

theorem physicalCentered {k m : ℕ} (ov : Fin k→H) (ordinary : Fin m→Box) (x : V→ℚ)
    (center : ∑ p,x p=0) (outside : ∀j,rowSum (ordinary j) x=0) :
    (∑ i, form (hbox (ov i)) x) + (∑ j,form (ordinary j) x) =
      8* ∑ i, (rowSum (hbox (ov i)) x)^2 := by
  simp only [form,centeredPrice _ _ center,outside,zero_mul,sum_const_zero,add_zero,mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem nonnegative {k m : ℕ} (ov : Fin k→H) (ordinary : Fin m→Box) (x : V→ℚ)
    (center : ∑ p,x p=0) (outside : ∀j,rowSum (ordinary j) x=0) :
    0≤(∑ i, form (hbox (ov i)) x) + (∑ j,form (ordinary j) x) := by
  rw [physicalCentered ov ordinary x center outside]
  exact mul_nonneg (by decide) (Finset.sum_nonneg fun _ _=>sq_nonneg _)
end Plane9341.OvalForm
