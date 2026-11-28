
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9829.NoFill
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 10000
set_option maxHeartbeats 0
abbrev V := Fin 26
def donor : Circuit := ⟨[⟨.or,[13,14]⟩,⟨.or,[16,22]⟩,⟨.or,[26,27]⟩,⟨.or,[17,21]⟩,⟨.or,[22,24]⟩,⟨.or,[29,30]⟩,⟨.or,[15,19]⟩,⟨.or,[20,32]⟩,⟨.or,[13,15]⟩,⟨.or,[21,25]⟩,⟨.or,[34,35]⟩,⟨.or,[14,20]⟩,⟨.or,[24,19]⟩,⟨.or,[37,38]⟩,⟨.or,[13,19]⟩,⟨.or,[23,24]⟩,⟨.or,[40,41]⟩,⟨.or,[18,22]⟩,⟨.or,[23,25]⟩,⟨.or,[43,44]⟩,⟨.or,[16,20]⟩,⟨.or,[21,23]⟩,⟨.or,[46,47]⟩,⟨.or,[22,33]⟩,⟨.or,[14,18]⟩,⟨.or,[50,35]⟩,⟨.or,[13,17]⟩,⟨.or,[18,20]⟩,⟨.or,[52,53]⟩,⟨.or,[16,17]⟩,⟨.or,[19,25]⟩,⟨.or,[55,56]⟩,⟨.or,[15,16]⟩,⟨.or,[18,24]⟩,⟨.or,[58,59]⟩,⟨.or,[14,15]⟩,⟨.or,[17,23]⟩,⟨.or,[61,62]⟩,⟨.and,[0,28]⟩,⟨.and,[1,36]⟩,⟨.and,[2,39]⟩,⟨.and,[3,42]⟩,⟨.and,[4,45]⟩,⟨.and,[5,31]⟩,⟨.and,[6,48]⟩,⟨.and,[7,49]⟩,⟨.and,[8,51]⟩,⟨.and,[9,54]⟩,⟨.and,[10,57]⟩,⟨.and,[11,60]⟩,⟨.and,[12,63]⟩,⟨.or,[65,66]⟩,⟨.or,[67,68]⟩,⟨.or,[70,72]⟩,⟨.or,[73,74]⟩,⟨.or,[75,76]⟩,⟨.or,[77,78]⟩,⟨.or,[79,80]⟩,⟨.or,[82,83]⟩,⟨.or,[81,84]⟩,⟨.or,[64,69]⟩,⟨.or,[71,86]⟩,⟨.or,[85,87]⟩],88⟩
def flags : List (V × V) := [(0,13),(0,17),(0,23),(0,25),(1,13),(1,14),(1,18),(1,24),(2,14),(2,15),(2,19),(2,25),(3,13),(3,15),(3,16),(3,20),(4,14),(4,16),(4,17),(4,21),(5,15),(5,17),(5,18),(5,22),(6,16),(6,18),(6,19),(6,23),(7,17),(7,19),(7,20),(7,24),(8,18),(8,20),(8,21),(8,25),(9,13),(9,19),(9,21),(9,22),(10,14),(10,20),(10,22),(10,23),(11,15),(11,21),(11,23),(11,24),(12,16),(12,22),(12,24),(12,25)]
def ev (p q : V) (a b : Bool) (w : Nat) (i : V) : Bool :=
  if i=p then a else if i=q then b else w.testBit i.val
def source (p q : V) (a b : Bool) (w : Nat) :=
  donor.eval (List.ofFn (ev p q a b w))
def target (p q : V) (w : Nat) :=
  flags.any (fun ij => ev p q false false w ij.1 && ev p q false false w ij.2)
def rows : Array (V × V × Nat) := #[(13,14,65552),(0,12,33554436),(0,8,8389632),(0,11,8389632),(0,7,131088),(0,6,262176),(0,5,262208),(13,18,32800),(13,24,69632),(0,4,131200),(0,10,8390656),(0,2,33558528),(14,25,262176),(0,9,33558528),(0,3,33558528),(18,25,131073),(24,25,8388609),(14,17,2097168),(14,23,4195328),(17,18,33554433),(23,24,33554433),(17,24,33554433),(18,23,33554433),(13,15,33554436),(13,19,262208),(13,20,17408),(13,16,16400),(13,22,17408),(13,21,16400),(15,25,8388609),(19,25,131073),(15,17,8388609),(19,23,131073),(17,19,8388609),(15,23,131073),(20,25,131073),(21,25,8388609),(22,25,16781312),(16,25,16781312),(22,23,17408),(16,17,16400),(17,21,33554433),(20,23,33554433),(17,22,16386),(16,23,16386),(17,20,33554433),(21,23,33554433),(0,1,8389632),(13,25,32772),(1,10,16400),(1,4,17408),(1,11,8389632),(1,6,262176),(1,7,16781312),(1,5,262208),(13,17,65552),(13,23,2099200),(1,8,16781312),(1,12,16777344),(1,2,4198400),(2,10,8390656),(2,4,131200),(11,12,33554436),(7,12,33554436),(6,8,4195328),(5,8,65552),(5,6,262146),(7,11,8389632),(4,10,16386),(6,9,4195328),(7,9,2097168),(3,11,1049600),(3,5,32772),(3,10,1048832),(3,4,69632),(9,10,4198400),(4,9,2099200),(3,6,4195328),(3,7,131088),(9,11,2097168),(5,9,32776),(9,12,4195328),(3,8,1049600),(3,12,65552),(8,9,4198400),(2,3,32800),(2,9,33558528),(2,6,33558528),(2,11,33558528),(2,7,33558528),(2,5,33558528),(8,10,1048584),(4,8,131200),(10,12,4194816),(4,12,65544),(4,6,131200),(4,11,131200),(7,10,8390656),(5,10,8390656),(5,11,8389632),(6,7,131088),(8,11,8389632),(6,12,33554436),(7,8,131088),(5,12,33554436),(17,25,32772),(23,25,32772),(17,23,33554433),(1,9,17408),(1,3,16400),(2,12,33554433),(2,8,65552),(10,11,16400),(6,10,16400),(4,7,17408),(4,5,17408),(5,7,262208),(6,11,524800),(8,12,16777344),(3,9,32800),(14,15,262176),(14,19,262146),(15,18,33554436),(19,24,262146),(18,19,16777218),(15,24,33554433),(14,16,262146),(14,21,131088),(14,22,262146),(14,20,16777218),(22,24,16386),(18,20,16386),(18,21,8388609),(16,24,16386),(18,22,16386),(20,24,16386),(16,18,16386),(21,24,33558528),(14,18,16777218),(14,24,262146),(18,24,33558528),(19,22,2097664),(15,20,65544),(15,16,33554436),(19,21,4194816),(21,22,33558528),(16,20,32776),(15,19,2097664),(15,22,2097664),(19,20,33554433),(15,21,4194816),(16,19,33558528),(16,22,524800),(20,21,32776),(16,21,32776),(20,22,8389632)]
def r (i : Fin 156) := rows[i.val]!
def fails (i : Fin 156) := ∀ a b : Bool,
  source (r i).1 (r i).2.1 a b (r i).2.2 ≠ target (r i).1 (r i).2.1 (r i).2.2
instance (i : Fin 156) : Decidable (fails i) := by unfold fails; infer_instance

theorem prevents (i : Fin 156) (bad : fails i) :
  ¬∃ h k : Nat → Bool, ∀ w, source (r i).1 (r i).2.1 (h w) (k w) w =
    target (r i).1 (r i).2.1 w := by
  rintro ⟨h,k,all⟩
  exact bad (h (r i).2.2) (k (r i).2.2) (all (r i).2.2)
private theorem chart0 : fails (0:Fin 156) := by decide +kernel
private theorem chart1 : fails (1:Fin 156) := by decide +kernel
private theorem chart2 : fails (2:Fin 156) := by decide +kernel
private theorem chart3 : fails (3:Fin 156) := by decide +kernel
private theorem chart4 : fails (4:Fin 156) := by decide +kernel
private theorem chart5 : fails (5:Fin 156) := by decide +kernel
private theorem chart6 : fails (6:Fin 156) := by decide +kernel
private theorem chart7 : fails (7:Fin 156) := by decide +kernel
private theorem chart8 : fails (8:Fin 156) := by decide +kernel
private theorem chart9 : fails (9:Fin 156) := by decide +kernel
private theorem chart10 : fails (10:Fin 156) := by decide +kernel
private theorem chart11 : fails (11:Fin 156) := by decide +kernel
private theorem chart12 : fails (12:Fin 156) := by decide +kernel
private theorem chart13 : fails (13:Fin 156) := by decide +kernel
private theorem chart14 : fails (14:Fin 156) := by decide +kernel
private theorem chart15 : fails (15:Fin 156) := by decide +kernel
private theorem chart16 : fails (16:Fin 156) := by decide +kernel
private theorem chart17 : fails (17:Fin 156) := by decide +kernel
private theorem chart18 : fails (18:Fin 156) := by decide +kernel
private theorem chart19 : fails (19:Fin 156) := by decide +kernel
private theorem chart20 : fails (20:Fin 156) := by decide +kernel
private theorem chart21 : fails (21:Fin 156) := by decide +kernel
private theorem chart22 : fails (22:Fin 156) := by decide +kernel
private theorem chart23 : fails (23:Fin 156) := by decide +kernel
private theorem chart24 : fails (24:Fin 156) := by decide +kernel
private theorem chart25 : fails (25:Fin 156) := by decide +kernel
private theorem chart26 : fails (26:Fin 156) := by decide +kernel
private theorem chart27 : fails (27:Fin 156) := by decide +kernel
private theorem chart28 : fails (28:Fin 156) := by decide +kernel
private theorem chart29 : fails (29:Fin 156) := by decide +kernel
private theorem chart30 : fails (30:Fin 156) := by decide +kernel
private theorem chart31 : fails (31:Fin 156) := by decide +kernel
private theorem chart32 : fails (32:Fin 156) := by decide +kernel
private theorem chart33 : fails (33:Fin 156) := by decide +kernel
private theorem chart34 : fails (34:Fin 156) := by decide +kernel
private theorem chart35 : fails (35:Fin 156) := by decide +kernel
private theorem chart36 : fails (36:Fin 156) := by decide +kernel
private theorem chart37 : fails (37:Fin 156) := by decide +kernel
private theorem chart38 : fails (38:Fin 156) := by decide +kernel
private theorem chart39 : fails (39:Fin 156) := by decide +kernel
private theorem chart40 : fails (40:Fin 156) := by decide +kernel
private theorem chart41 : fails (41:Fin 156) := by decide +kernel
private theorem chart42 : fails (42:Fin 156) := by decide +kernel
private theorem chart43 : fails (43:Fin 156) := by decide +kernel
private theorem chart44 : fails (44:Fin 156) := by decide +kernel
private theorem chart45 : fails (45:Fin 156) := by decide +kernel
private theorem chart46 : fails (46:Fin 156) := by decide +kernel
private theorem chart47 : fails (47:Fin 156) := by decide +kernel
private theorem chart48 : fails (48:Fin 156) := by decide +kernel
private theorem chart49 : fails (49:Fin 156) := by decide +kernel
private theorem chart50 : fails (50:Fin 156) := by decide +kernel
private theorem chart51 : fails (51:Fin 156) := by decide +kernel
private theorem chart52 : fails (52:Fin 156) := by decide +kernel
private theorem chart53 : fails (53:Fin 156) := by decide +kernel
private theorem chart54 : fails (54:Fin 156) := by decide +kernel
private theorem chart55 : fails (55:Fin 156) := by decide +kernel
private theorem chart56 : fails (56:Fin 156) := by decide +kernel
private theorem chart57 : fails (57:Fin 156) := by decide +kernel
private theorem chart58 : fails (58:Fin 156) := by decide +kernel
private theorem chart59 : fails (59:Fin 156) := by decide +kernel
private theorem chart60 : fails (60:Fin 156) := by decide +kernel
private theorem chart61 : fails (61:Fin 156) := by decide +kernel
private theorem chart62 : fails (62:Fin 156) := by decide +kernel
private theorem chart63 : fails (63:Fin 156) := by decide +kernel
private theorem chart64 : fails (64:Fin 156) := by decide +kernel
private theorem chart65 : fails (65:Fin 156) := by decide +kernel
private theorem chart66 : fails (66:Fin 156) := by decide +kernel
private theorem chart67 : fails (67:Fin 156) := by decide +kernel
private theorem chart68 : fails (68:Fin 156) := by decide +kernel
private theorem chart69 : fails (69:Fin 156) := by decide +kernel
private theorem chart70 : fails (70:Fin 156) := by decide +kernel
private theorem chart71 : fails (71:Fin 156) := by decide +kernel
private theorem chart72 : fails (72:Fin 156) := by decide +kernel
private theorem chart73 : fails (73:Fin 156) := by decide +kernel
private theorem chart74 : fails (74:Fin 156) := by decide +kernel
private theorem chart75 : fails (75:Fin 156) := by decide +kernel
private theorem chart76 : fails (76:Fin 156) := by decide +kernel
private theorem chart77 : fails (77:Fin 156) := by decide +kernel
private theorem chart78 : fails (78:Fin 156) := by decide +kernel
private theorem chart79 : fails (79:Fin 156) := by decide +kernel
private theorem chart80 : fails (80:Fin 156) := by decide +kernel
private theorem chart81 : fails (81:Fin 156) := by decide +kernel
private theorem chart82 : fails (82:Fin 156) := by decide +kernel
private theorem chart83 : fails (83:Fin 156) := by decide +kernel
private theorem chart84 : fails (84:Fin 156) := by decide +kernel
private theorem chart85 : fails (85:Fin 156) := by decide +kernel
private theorem chart86 : fails (86:Fin 156) := by decide +kernel
private theorem chart87 : fails (87:Fin 156) := by decide +kernel
private theorem chart88 : fails (88:Fin 156) := by decide +kernel
private theorem chart89 : fails (89:Fin 156) := by decide +kernel
private theorem chart90 : fails (90:Fin 156) := by decide +kernel
private theorem chart91 : fails (91:Fin 156) := by decide +kernel
private theorem chart92 : fails (92:Fin 156) := by decide +kernel
private theorem chart93 : fails (93:Fin 156) := by decide +kernel
private theorem chart94 : fails (94:Fin 156) := by decide +kernel
private theorem chart95 : fails (95:Fin 156) := by decide +kernel
private theorem chart96 : fails (96:Fin 156) := by decide +kernel
private theorem chart97 : fails (97:Fin 156) := by decide +kernel
private theorem chart98 : fails (98:Fin 156) := by decide +kernel
private theorem chart99 : fails (99:Fin 156) := by decide +kernel
private theorem chart100 : fails (100:Fin 156) := by decide +kernel
private theorem chart101 : fails (101:Fin 156) := by decide +kernel
private theorem chart102 : fails (102:Fin 156) := by decide +kernel
private theorem chart103 : fails (103:Fin 156) := by decide +kernel
private theorem chart104 : fails (104:Fin 156) := by decide +kernel
private theorem chart105 : fails (105:Fin 156) := by decide +kernel
private theorem chart106 : fails (106:Fin 156) := by decide +kernel
private theorem chart107 : fails (107:Fin 156) := by decide +kernel
private theorem chart108 : fails (108:Fin 156) := by decide +kernel
private theorem chart109 : fails (109:Fin 156) := by decide +kernel
private theorem chart110 : fails (110:Fin 156) := by decide +kernel
private theorem chart111 : fails (111:Fin 156) := by decide +kernel
private theorem chart112 : fails (112:Fin 156) := by decide +kernel
private theorem chart113 : fails (113:Fin 156) := by decide +kernel
private theorem chart114 : fails (114:Fin 156) := by decide +kernel
private theorem chart115 : fails (115:Fin 156) := by decide +kernel
private theorem chart116 : fails (116:Fin 156) := by decide +kernel
private theorem chart117 : fails (117:Fin 156) := by decide +kernel
private theorem chart118 : fails (118:Fin 156) := by decide +kernel
private theorem chart119 : fails (119:Fin 156) := by decide +kernel
private theorem chart120 : fails (120:Fin 156) := by decide +kernel
private theorem chart121 : fails (121:Fin 156) := by decide +kernel
private theorem chart122 : fails (122:Fin 156) := by decide +kernel
private theorem chart123 : fails (123:Fin 156) := by decide +kernel
private theorem chart124 : fails (124:Fin 156) := by decide +kernel
private theorem chart125 : fails (125:Fin 156) := by decide +kernel
private theorem chart126 : fails (126:Fin 156) := by decide +kernel
private theorem chart127 : fails (127:Fin 156) := by decide +kernel
private theorem chart128 : fails (128:Fin 156) := by decide +kernel
private theorem chart129 : fails (129:Fin 156) := by decide +kernel
private theorem chart130 : fails (130:Fin 156) := by decide +kernel
private theorem chart131 : fails (131:Fin 156) := by decide +kernel
private theorem chart132 : fails (132:Fin 156) := by decide +kernel
private theorem chart133 : fails (133:Fin 156) := by decide +kernel
private theorem chart134 : fails (134:Fin 156) := by decide +kernel
private theorem chart135 : fails (135:Fin 156) := by decide +kernel
private theorem chart136 : fails (136:Fin 156) := by decide +kernel
private theorem chart137 : fails (137:Fin 156) := by decide +kernel
private theorem chart138 : fails (138:Fin 156) := by decide +kernel
private theorem chart139 : fails (139:Fin 156) := by decide +kernel
private theorem chart140 : fails (140:Fin 156) := by decide +kernel
private theorem chart141 : fails (141:Fin 156) := by decide +kernel
private theorem chart142 : fails (142:Fin 156) := by decide +kernel
private theorem chart143 : fails (143:Fin 156) := by decide +kernel
private theorem chart144 : fails (144:Fin 156) := by decide +kernel
private theorem chart145 : fails (145:Fin 156) := by decide +kernel
private theorem chart146 : fails (146:Fin 156) := by decide +kernel
private theorem chart147 : fails (147:Fin 156) := by decide +kernel
private theorem chart148 : fails (148:Fin 156) := by decide +kernel
private theorem chart149 : fails (149:Fin 156) := by decide +kernel
private theorem chart150 : fails (150:Fin 156) := by decide +kernel
private theorem chart151 : fails (151:Fin 156) := by decide +kernel
private theorem chart152 : fails (152:Fin 156) := by decide +kernel
private theorem chart153 : fails (153:Fin 156) := by decide +kernel
private theorem chart154 : fails (154:Fin 156) := by decide +kernel
private theorem chart155 : fails (155:Fin 156) := by decide +kernel

theorem allpairs (i : Fin 156) :
  ¬∃ h k : Nat → Bool, ∀ w, source (r i).1 (r i).2.1 (h w) (k w) w =
    target (r i).1 (r i).2.1 w := by
  apply prevents
  fin_cases i
  · exact chart0
  · exact chart1
  · exact chart2
  · exact chart3
  · exact chart4
  · exact chart5
  · exact chart6
  · exact chart7
  · exact chart8
  · exact chart9
  · exact chart10
  · exact chart11
  · exact chart12
  · exact chart13
  · exact chart14
  · exact chart15
  · exact chart16
  · exact chart17
  · exact chart18
  · exact chart19
  · exact chart20
  · exact chart21
  · exact chart22
  · exact chart23
  · exact chart24
  · exact chart25
  · exact chart26
  · exact chart27
  · exact chart28
  · exact chart29
  · exact chart30
  · exact chart31
  · exact chart32
  · exact chart33
  · exact chart34
  · exact chart35
  · exact chart36
  · exact chart37
  · exact chart38
  · exact chart39
  · exact chart40
  · exact chart41
  · exact chart42
  · exact chart43
  · exact chart44
  · exact chart45
  · exact chart46
  · exact chart47
  · exact chart48
  · exact chart49
  · exact chart50
  · exact chart51
  · exact chart52
  · exact chart53
  · exact chart54
  · exact chart55
  · exact chart56
  · exact chart57
  · exact chart58
  · exact chart59
  · exact chart60
  · exact chart61
  · exact chart62
  · exact chart63
  · exact chart64
  · exact chart65
  · exact chart66
  · exact chart67
  · exact chart68
  · exact chart69
  · exact chart70
  · exact chart71
  · exact chart72
  · exact chart73
  · exact chart74
  · exact chart75
  · exact chart76
  · exact chart77
  · exact chart78
  · exact chart79
  · exact chart80
  · exact chart81
  · exact chart82
  · exact chart83
  · exact chart84
  · exact chart85
  · exact chart86
  · exact chart87
  · exact chart88
  · exact chart89
  · exact chart90
  · exact chart91
  · exact chart92
  · exact chart93
  · exact chart94
  · exact chart95
  · exact chart96
  · exact chart97
  · exact chart98
  · exact chart99
  · exact chart100
  · exact chart101
  · exact chart102
  · exact chart103
  · exact chart104
  · exact chart105
  · exact chart106
  · exact chart107
  · exact chart108
  · exact chart109
  · exact chart110
  · exact chart111
  · exact chart112
  · exact chart113
  · exact chart114
  · exact chart115
  · exact chart116
  · exact chart117
  · exact chart118
  · exact chart119
  · exact chart120
  · exact chart121
  · exact chart122
  · exact chart123
  · exact chart124
  · exact chart125
  · exact chart126
  · exact chart127
  · exact chart128
  · exact chart129
  · exact chart130
  · exact chart131
  · exact chart132
  · exact chart133
  · exact chart134
  · exact chart135
  · exact chart136
  · exact chart137
  · exact chart138
  · exact chart139
  · exact chart140
  · exact chart141
  · exact chart142
  · exact chart143
  · exact chart144
  · exact chart145
  · exact chart146
  · exact chart147
  · exact chart148
  · exact chart149
  · exact chart150
  · exact chart151
  · exact chart152
  · exact chart153
  · exact chart154
  · exact chart155
end PEqualNP.Outside.L_meta_9829.NoFill
