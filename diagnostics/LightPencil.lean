import PEqualNP.Defs

namespace Research9350

abbrev V := Fin 21
abbrev O := Fin 168
abbrev F := Fin 48
def catalog : Array (Nat × Nat) := #[(1369,872450),(2738,1744900),(4157,385088),(5476,1392649),(8314,770176),(9507,608268),(10952,688147),(12359,115736),(16628,1540352),(19014,1216536),(20681,360978),(21904,1376294),(24718,231472),(31233,32862),(33256,983553),(33969,860420),(36355,536604),(38028,335921),(41362,721956),(43808,655437),(49436,462944),(50245,332056),(53537,328268),(62466,65724),(66512,1967106),(67209,796690),(67938,1720840),(72710,1073208),(76056,671842),(76865,540954),(82724,1443912),(87616,1310874),(98872,925888),(100490,664112),(102917,271448),(107074,656536),(124932,131448),(133024,1837061),(133195,578064),(134418,1593380),(135876,1344529),(139907,560148),(141361,573764),(145420,49265),(147981,301136),(152112,1343684),(153730,1081908),(164625,791620),(165448,790673),(175232,524597),(196905,805440),(197744,1851776),(200980,1328224),(205834,542896),(214148,1313072),(229569,788240),(249864,262896),(262315,633344),(264729,569410),(266048,1576971),(266390,1156128),(268836,1089609),(270545,623874),(271752,591907),(279814,1120296),(282722,1147528),(286757,100680),(290840,98530),(295235,595464),(295962,602272),(304224,590217),(307460,66665),(329250,1583240),(330896,1581346),(336641,527434),(350464,1049194),(362529,533320),(393810,1610880),(395488,1606401),(401960,559297),(411668,1085792),(428296,528993),(459138,1576480),(499728,525792),(524630,1266688),(525327,96272),(529458,1138820),(532096,1056791),(532780,215105),(536849,83014),(537672,82067),(541090,1247748),(543504,1183814),(550017,67862),(559628,143441),(561283,75284),(565444,197905),(573514,201360),(581680,197060),(590470,1190928),(591924,1204544),(595977,25170),(608448,1180434),(614920,133330),(658500,1069329),(661792,1065541),(673282,1054868),(700928,1237),(706561,4948),(725058,1066640),(729093,19792),(787620,1124609),(790976,1115651),(803081,72258),(803920,1118594),(819221,79168),(823336,74433),(856592,1057986),(918276,1055809),(999456,1051584),(1049260,436225),(1050654,192544),(1053329,304134),(1054755,57868),(1058916,180489),(1064192,16431),(1065560,430210),(1066753,268302),(1073698,166028),(1075344,164134),(1082180,398345),(1087008,270477),(1100034,135724),(1115173,289032),(1118529,280074),(1119256,286882),(1122566,150568),(1130888,395810),(1147028,402720),(1163360,394120),(1179733,316672),(1180940,284705),(1183848,311937),(1191954,50340),(1196193,297732),(1216896,263717),(1229840,266660),(1311239,48136),(1317000,41507),(1323584,33931),(1329217,37642),(1346564,12585),(1401856,2474),(1413122,9896),(1450116,36129),(1458186,39584),(1575240,152067),(1575953,28934),(1581952,134151),(1606162,144516),(1607840,140037),(1638442,158336),(1646672,148866),(1704195,24068),(1713184,18821),(1836552,14467),(1900673,12034),(1998912,6017)]
def originCatalog : Array (Nat × Nat) := #[(1369,872450),(4157,385088),(9507,608268),(12359,115736),(20681,360978),(31233,32862),(33969,860420),(36355,536604),(50245,332056),(53537,328268),(67209,796690),(76865,540954),(102917,271448),(133195,578064),(139907,560148),(141361,573764),(147981,301136),(164625,791620),(196905,805440),(229569,788240),(262315,633344),(264729,569410),(270545,623874),(286757,100680),(295235,595464),(336641,527434),(362529,533320),(525327,96272),(536849,83014),(550017,67862),(561283,75284),(595977,25170),(706561,4948),(729093,19792),(803081,72258),(819221,79168),(1053329,304134),(1054755,57868),(1066753,268302),(1115173,289032),(1118529,280074),(1179733,316672),(1196193,297732),(1311239,48136),(1329217,37642),(1575953,28934),(1704195,24068),(1900673,12034)]
def localLabels : Array (Array F) := #[#[0,0,1,0,0,2,0,3,0,0,4,0,0,5,0,6,7,0,0,0,0,8,9,0,0,10,0,0,0,11,0,0,0,0,12,0,0,0,13,0,0,14,15,0,16,0,0,17,0,0,18,0,0,0,0,19,0,20,21,0,0,0,22,0,0,0,23,0,24,0,0,0,0,0,25,0,26,0,0,0,0,0,0,0,0,27,0,0,0,28,0,0,0,29,0,30,0,0,0,0,0,31,0,0,0,0,0,0,32,0,33,0,0,34,0,35,0,0,0,0,0,0,36,37,0,0,0,38,0,0,0,0,0,39,40,0,0,0,0,0,41,0,0,0,42,0,0,43,0,0,44,0,0,0,0,0,0,45,0,0,0,0,0,46,0,0,47,0],#[0,0,0,0,1,36,0,37,0,2,0,0,3,0,0,0,38,0,4,0,0,0,0,5,0,0,6,7,0,0,0,0,0,8,0,9,0,0,39,10,0,40,0,0,0,0,11,0,0,0,0,0,0,12,0,0,0,41,0,0,13,0,0,0,14,15,0,0,42,16,0,0,17,0,0,0,0,18,0,0,0,0,19,0,20,43,21,0,0,0,0,22,0,0,0,44,0,23,0,24,0,0,0,0,0,0,25,0,0,26,0,0,0,0,0,0,0,0,0,0,0,27,0,45,0,0,0,0,28,0,0,0,29,0,0,0,30,0,0,0,0,0,0,31,0,0,0,46,0,0,0,0,0,32,0,33,0,0,0,34,0,35,0,47,0,0,0,0],#[0,0,27,0,0,0,0,45,1,36,0,0,37,0,0,0,0,2,0,0,3,28,0,0,0,0,0,38,0,0,4,0,0,0,29,0,5,0,0,0,6,0,0,7,30,0,0,0,0,0,0,0,8,0,9,0,0,0,0,0,39,10,0,0,40,0,31,0,0,0,0,11,0,0,0,0,0,0,0,0,12,0,0,0,41,46,0,0,13,0,0,0,0,0,14,0,15,0,0,42,16,0,0,0,17,0,0,0,0,0,32,18,0,0,0,33,0,0,19,0,20,43,0,0,21,0,0,0,0,0,22,0,0,34,0,0,44,0,23,0,35,24,0,0,0,0,0,47,0,0,0,25,0,0,26,0,0,0,0,0,0,0,0,0,0,0,0,0],#[20,0,43,0,27,0,0,0,0,0,21,0,45,0,1,0,0,36,0,0,37,0,0,0,0,22,0,0,2,0,0,0,3,28,0,0,0,0,34,0,0,0,0,38,44,0,0,0,4,0,23,0,0,29,0,0,5,35,24,0,0,0,0,6,0,0,0,7,0,30,0,0,0,0,0,0,0,0,0,8,0,9,0,0,0,47,0,0,39,0,10,0,0,0,40,0,0,31,0,0,0,25,0,11,0,0,0,0,0,0,0,0,0,26,0,0,12,0,0,0,41,46,0,0,0,0,13,0,0,0,0,0,0,0,0,14,0,15,0,0,0,42,16,0,0,0,0,0,17,0,0,0,0,0,0,32,18,0,0,0,0,33,0,0,0,19,0,0],#[41,20,46,0,43,0,0,0,27,0,0,0,0,0,0,13,0,0,21,0,45,0,0,0,1,0,0,0,36,0,0,0,37,0,0,0,0,0,0,22,0,0,14,0,0,2,0,15,0,0,0,3,28,0,0,0,0,0,42,0,34,0,16,0,0,0,0,38,0,44,0,0,0,4,0,0,0,23,0,0,29,0,0,5,35,0,24,0,0,17,0,0,6,0,0,0,0,0,7,0,30,0,0,0,0,0,0,0,0,0,0,0,0,0,8,32,0,9,0,0,0,47,18,0,0,0,39,0,0,10,0,0,0,0,0,40,0,0,31,0,33,0,0,25,0,0,11,0,0,0,0,0,0,0,0,0,0,19,0,26,0,0,12,0,0,0,0,0],#[0,41,47,20,46,18,0,0,43,0,0,0,0,0,27,39,0,0,0,0,0,0,10,0,0,0,13,0,0,0,21,0,45,0,0,0,0,1,0,0,0,0,40,0,0,36,0,0,0,0,31,37,0,0,0,0,0,33,0,0,0,22,0,0,0,14,25,0,0,0,2,0,15,0,0,0,11,0,3,28,0,0,0,0,0,0,42,0,34,0,0,16,0,0,0,0,0,0,38,0,44,0,0,0,0,4,0,0,0,0,0,23,0,0,0,0,29,0,0,5,35,0,0,19,24,0,0,0,17,0,0,6,0,26,0,0,0,0,0,7,0,0,30,0,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,32,0,0,9,0,0,0],#[35,0,0,41,47,0,20,19,46,18,24,0,0,0,43,0,0,0,0,0,0,17,0,0,27,0,39,0,0,6,0,0,0,0,0,10,0,0,26,0,13,0,0,0,0,0,0,0,21,0,0,45,0,0,0,7,0,0,0,1,0,0,30,0,0,40,0,0,12,0,36,0,0,0,0,0,0,31,37,0,0,0,0,0,33,0,0,0,0,0,22,0,0,0,0,0,14,25,0,0,0,0,2,0,15,0,0,0,0,11,0,0,3,0,28,0,0,0,0,0,0,0,0,0,42,0,34,0,0,0,16,0,0,0,8,0,0,0,0,38,32,0,44,0,0,0,0,0,0,4,9,0,0,0,0,0,23,0,0,0,0,0,29,0,0,0,0,5],#[0,35,0,0,0,0,41,0,47,0,42,20,19,0,46,34,0,18,24,0,0,0,0,0,43,16,0,0,0,0,0,0,0,17,0,0,0,27,0,0,39,8,0,0,0,0,6,0,0,0,0,0,0,0,10,38,0,32,0,0,26,0,44,13,0,0,0,0,0,0,0,0,0,21,0,0,0,0,45,0,0,0,7,0,0,0,0,1,0,0,0,30,0,4,0,9,40,0,0,12,0,0,36,0,0,0,0,0,0,0,0,31,37,0,0,0,0,0,0,0,33,0,23,0,0,0,0,0,0,22,0,0,0,0,0,0,0,14,25,0,0,0,0,0,29,2,0,0,15,0,0,0,0,0,11,0,0,0,3,0,28,0,0,0,0,0,5,0],#[33,0,0,35,0,23,0,0,0,0,0,41,0,0,47,0,0,0,42,20,19,0,22,0,46,0,34,0,18,0,24,0,0,0,0,0,0,43,0,16,0,0,0,0,0,0,0,14,0,0,25,0,17,0,0,0,0,0,0,27,0,0,0,39,8,0,0,0,29,0,0,6,0,0,2,0,0,0,0,0,0,10,38,0,32,0,0,0,26,15,0,44,13,0,0,0,0,0,0,0,0,0,0,0,0,21,0,0,0,0,0,0,45,11,0,0,0,0,7,0,0,0,0,0,0,1,0,3,0,0,30,0,4,0,28,0,9,40,0,0,0,12,0,0,0,36,0,0,0,0,0,0,0,0,0,0,31,0,37,0,0,0,0,5,0,0,0,0],#[0,33,0,0,0,0,35,0,0,23,0,0,0,1,0,0,3,0,0,41,0,0,0,0,47,30,0,0,0,0,42,20,19,0,4,22,0,46,0,0,34,28,0,0,9,18,0,40,24,0,0,0,0,0,0,0,0,0,12,43,0,16,0,0,0,0,0,0,0,0,0,0,14,0,36,0,0,25,0,17,0,0,0,0,0,0,0,27,0,0,0,0,39,0,8,0,0,0,0,29,0,0,0,6,0,0,2,0,0,0,0,0,0,0,0,0,0,10,38,0,32,0,31,0,0,0,26,37,15,0,44,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,21,0,0,0,0,0,0,0,0,45,11,0,0,0,0,0,7,0,0],#[32,0,0,33,0,31,0,0,0,0,0,35,0,0,0,26,37,23,0,0,0,15,0,1,0,44,0,3,0,13,0,41,0,0,0,0,0,47,0,30,0,0,0,0,0,0,0,0,42,20,0,19,0,4,22,0,0,0,0,46,0,0,0,34,28,0,0,0,0,9,18,0,40,24,0,0,0,0,0,0,0,0,0,0,0,5,12,43,0,0,16,0,0,21,0,0,0,0,0,0,0,0,0,0,14,0,36,0,0,0,0,25,0,0,17,0,0,0,0,0,0,0,0,0,0,27,0,45,0,0,0,39,0,11,0,8,0,0,0,0,0,29,0,0,0,0,6,0,0,0,0,2,0,0,0,0,0,7,0,0,0,0,0,0,10,38,0,0],#[0,32,0,0,0,0,33,0,0,31,0,0,0,27,0,0,45,0,0,35,0,0,0,0,0,0,26,37,23,39,0,0,0,15,0,0,1,0,11,44,0,0,8,3,0,0,13,0,0,41,0,0,0,0,0,0,0,0,29,47,0,30,0,0,0,0,0,0,0,0,0,0,0,42,0,20,6,0,19,0,4,22,0,0,0,0,0,46,0,0,0,0,34,0,28,0,0,0,0,0,9,2,18,0,40,24,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,7,12,43,0,0,0,16,0,0,21,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,14,0,10,36,0,0,0,0,25,38,0,0,17,0,0,0,0,0,0,0],#[0,0,5,32,0,0,0,7,0,0,12,33,0,43,0,0,0,31,0,0,0,0,16,27,0,0,0,45,0,0,0,35,0,0,21,0,0,0,0,0,26,0,0,37,0,23,39,0,0,0,0,0,15,0,0,0,1,0,0,0,11,44,0,0,0,8,0,3,0,0,0,13,0,0,0,41,0,0,0,0,0,0,0,0,0,0,29,47,0,14,30,0,0,0,0,10,0,0,0,0,0,36,0,0,0,42,0,20,0,6,0,0,19,0,0,0,4,22,0,0,0,0,25,38,0,46,0,0,0,0,0,34,0,0,17,28,0,0,0,0,0,0,9,2,0,18,0,0,40,24,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,5,25,32,38,0,0,0,0,7,46,0,0,0,0,12,33,0,0,0,43,0,0,0,0,31,34,0,0,0,0,0,16,27,0,0,0,0,17,28,45,0,0,0,0,0,35,0,0,0,21,0,0,0,0,0,0,0,0,9,26,0,0,2,37,0,0,23,39,0,0,18,0,0,0,0,15,0,0,0,1,0,0,0,0,11,40,44,0,0,24,0,0,8,0,3,0,0,0,0,13,0,0,0,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,29,47,0,0,14,30,0,0,0,0,0,0,10,0,0,0,0,0,0,36,0,0,0,0,0,42,0,0,20,0,6,0,0,0,19,0,0,0,4,0,22,0,0,0],#[0,0,0,0,0,0,0,0,5,25,29,32,38,47,0,0,0,0,0,0,7,14,30,46,0,0,0,0,0,0,12,33,0,0,0,0,43,0,0,0,0,0,0,0,10,31,34,0,0,0,0,0,0,0,16,0,27,0,0,0,0,0,0,0,17,28,36,45,0,0,0,0,0,0,0,35,0,0,0,0,21,0,0,0,0,0,0,0,0,0,0,9,26,42,0,0,0,2,37,0,0,0,23,39,0,0,18,0,20,0,0,0,0,6,15,0,0,0,0,1,0,0,0,0,0,0,11,19,40,44,0,0,24,0,0,0,0,8,0,3,0,0,0,0,4,0,13,0,0,0,22,0,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,11,19,25,29,32,38,40,44,47,0,0,0,0,0,0,0,0,7,14,24,30,46,0,0,0,0,0,0,0,0,0,0,8,12,33,0,0,0,0,0,3,43,0,0,0,0,0,0,0,0,0,0,0,4,10,31,34,0,0,0,0,13,0,0,0,0,16,0,27,0,0,0,0,0,0,0,0,0,0,17,22,28,36,45,0,0,0,0,0,0,0,0,35,41,0,0,0,0,0,0,0,21,0,0,0,0,0,0,0,0,0,0,0,0,0,9,26,42,0,0,0,0,0,2,37,0,0,0,0,0,23,39,0,0,0,0,18,0,20,0,0,0,0,0,6,15,0,0,0,0,0,0,1],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,9,11,19,25,26,29,32,38,40,42,44,47,0,0,0,0,0,0,0,0,0,0,0,0,0,2,7,14,24,30,37,46,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,12,23,33,39,0,0,0,0,0,3,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,10,18,31,34,0,0,0,0,0,13,20,0,0,0,0,0,0,16,0,27,0,0,0,0,0,0,0,0,0,0,0,0,0,6,15,17,22,28,36,45,0,0,0,0,0,0,0,0,0,0,0,0,35,41,0,0,0,0,0,0,0,0,21,0,0,0,1,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,6,9,11,15,17,19,22,25,26,28,29,32,36,38,40,42,44,45,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,7,14,24,30,37,46,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,12,23,33,35,39,41,0,0,0,0,0,0,0,3,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,10,18,21,31,34,0,0,0,0,0,0,0,13,20,0,0,0,0,0,0,0,1,16,0,0,27],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,5,6,9,10,11,15,17,18,19,21,22,25,26,28,29,31,32,34,36,38,40,42,44,45,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,7,13,14,20,24,30,37,46,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,8,12,16,23,33,35,39,41,0,0,0,0,0,0,0,0,0,3,27,43],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,4,5,6,8,9,10,11,12,15,16,17,18,19,21,22,23,25,26,28,29,31,32,33,34,35,36,38,39,40,41,42,44,45,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,7,13,14,20,24,27,30,37,43,46],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47]]
def Zcol : Array Nat := #[2015212,1933273,1769395,1441639,786127,1572254,1047357,2094714,2092277,2087403,2077655,2058159,2019167,1941183,1785215,1473279,849407,1698814,1300477,503803,1007606]
def rowBits (h : O) := (catalog[h.val]!).1
def colBits (h : O) := (catalog[h.val]!).2
def localLabel (r : V) (h : O) : F := (localLabels[r.val]!)[h.val]!
def rr (r : V) (m : Nat) := ((m >>> r.val) ||| (m <<< (21-r.val))) % (2^21)
def ra (i : F) := (originCatalog[i.val]!).1
def cb (i : F) := (originCatalog[i.val]!).2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reindex : ∀ (r : V) (h : O), (rowBits h).testBit r.val = true →
    (ra (localLabel r h), cb (localLabel r h)) =
    (rr r (rowBits h), rr r (colBits h)) := by decide +kernel

def pencil (a b c u v w : Nat) : Prop :=
    a &&& b = 1 ∧ a &&& c = 1 ∧ b &&& c = 1 ∧
    ∃ j : V, u &&& v = 2^j.val ∧ u &&& w = 2^j.val ∧ v &&& w = 2^j.val ∧
      a ||| b ||| c = Zcol[j.val]!

instance (a b c u v w : Nat) : Decidable (pencil a b c u v w) := by
  unfold pencil
  infer_instance

def signature (i j k : F) : Prop :=
  cb i ||| cb j ||| cb k = 917342 → pencil (ra i) (ra j) (ra k) (cb i) (cb j) (cb k)
instance (i j k : F) : Decidable (signature i j k) := by
  unfold signature
  infer_instance

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row0 : ∀ j k : F, signature 0 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row1 : ∀ j k : F, signature 1 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row2 : ∀ j k : F, signature 2 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row3 : ∀ j k : F, signature 3 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row4 : ∀ j k : F, signature 4 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row5 : ∀ j k : F, signature 5 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row6 : ∀ j k : F, signature 6 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row7 : ∀ j k : F, signature 7 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row8 : ∀ j k : F, signature 8 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row9 : ∀ j k : F, signature 9 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row10 : ∀ j k : F, signature 10 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row11 : ∀ j k : F, signature 11 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row12 : ∀ j k : F, signature 12 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row13 : ∀ j k : F, signature 13 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row14 : ∀ j k : F, signature 14 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row15 : ∀ j k : F, signature 15 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row16 : ∀ j k : F, signature 16 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row17 : ∀ j k : F, signature 17 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row18 : ∀ j k : F, signature 18 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row19 : ∀ j k : F, signature 19 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row20 : ∀ j k : F, signature 20 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row21 : ∀ j k : F, signature 21 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row22 : ∀ j k : F, signature 22 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row23 : ∀ j k : F, signature 23 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row24 : ∀ j k : F, signature 24 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row25 : ∀ j k : F, signature 25 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row26 : ∀ j k : F, signature 26 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row27 : ∀ j k : F, signature 27 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row28 : ∀ j k : F, signature 28 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row29 : ∀ j k : F, signature 29 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row30 : ∀ j k : F, signature 30 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row31 : ∀ j k : F, signature 31 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row32 : ∀ j k : F, signature 32 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row33 : ∀ j k : F, signature 33 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row34 : ∀ j k : F, signature 34 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row35 : ∀ j k : F, signature 35 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row36 : ∀ j k : F, signature 36 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row37 : ∀ j k : F, signature 37 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row38 : ∀ j k : F, signature 38 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row39 : ∀ j k : F, signature 39 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row40 : ∀ j k : F, signature 40 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row41 : ∀ j k : F, signature 41 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row42 : ∀ j k : F, signature 42 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row43 : ∀ j k : F, signature 43 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row44 : ∀ j k : F, signature 44 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row45 : ∀ j k : F, signature 45 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row46 : ∀ j k : F, signature 46 j k := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row47 : ∀ j k : F, signature 47 j k := by decide +kernel

theorem signature_all (i j k : F) : signature i j k := by
  fin_cases i
  · exact row0 j k
  · exact row1 j k
  · exact row2 j k
  · exact row3 j k
  · exact row4 j k
  · exact row5 j k
  · exact row6 j k
  · exact row7 j k
  · exact row8 j k
  · exact row9 j k
  · exact row10 j k
  · exact row11 j k
  · exact row12 j k
  · exact row13 j k
  · exact row14 j k
  · exact row15 j k
  · exact row16 j k
  · exact row17 j k
  · exact row18 j k
  · exact row19 j k
  · exact row20 j k
  · exact row21 j k
  · exact row22 j k
  · exact row23 j k
  · exact row24 j k
  · exact row25 j k
  · exact row26 j k
  · exact row27 j k
  · exact row28 j k
  · exact row29 j k
  · exact row30 j k
  · exact row31 j k
  · exact row32 j k
  · exact row33 j k
  · exact row34 j k
  · exact row35 j k
  · exact row36 j k
  · exact row37 j k
  · exact row38 j k
  · exact row39 j k
  · exact row40 j k
  · exact row41 j k
  · exact row42 j k
  · exact row43 j k
  · exact row44 j k
  · exact row45 j k
  · exact row46 j k
  · exact row47 j k

-- The 16 column bits are measured relative to r in Singer cyclic coordinates.
-- Three catalog rectangles covering all of the row also cover its entire
-- corresponding column. Their pairwise intersections are all that same cell.
theorem row_triple_forces_column (r : V) (x y z : O)
    (hx : (rowBits x).testBit r.val = true)
    (hy : (rowBits y).testBit r.val = true)
    (hz : (rowBits z).testBit r.val = true)
    (allCols : rr r (colBits x) ||| rr r (colBits y) ||| rr r (colBits z) = 917342) :
    pencil (rr r (rowBits x)) (rr r (rowBits y)) (rr r (rowBits z))
      (rr r (colBits x)) (rr r (colBits y)) (rr r (colBits z)) := by
  have ex := reindex r x hx
  have ey := reindex r y hy
  have ez := reindex r z hz
  have H := signature_all (localLabel r x) (localLabel r y) (localLabel r z)
  unfold signature at H
  have ax := congrArg Prod.fst ex
  have ay := congrArg Prod.fst ey
  have az := congrArg Prod.fst ez
  have bx := congrArg Prod.snd ex
  have by_ := congrArg Prod.snd ey
  have bz := congrArg Prod.snd ez
  simp only [Prod.fst, Prod.snd] at ax ay az bx by_ bz
  rw [ax,ay,az,bx,by_,bz] at H
  exact H allCols

end Research9350
