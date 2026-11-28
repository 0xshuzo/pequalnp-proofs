import PEqualNP.Defs
namespace Research9815.Decoder
abbrev Pair := Nat × Nat
def put (n : Nat) (L : List Nat) := if n∈L then L else n::L
def putPair (p : Pair) (L : List Nat) := put p.1 (put p.2 L)
def blocked (k : Nat) (opts : List (List Pair)) (used : List Nat) : Bool :=
  if used.length>k then true else match opts with
  | [] => false
  | L::Ls => L.all (fun p => blocked k Ls (putPair p used))
def opts00 : List Pair := [(5, 5),(65, 65),(68, 68),(71, 71),(77, 77),(79, 79),(85, 85),(101, 101),(87, 18),(87, 26),(87, 50),(87, 58),(93, 24),(93, 26),(93, 56),(93, 58),(95, 26),(95, 58),(103, 34),(103, 42),(103, 50),(103, 58),(103, 93),(109, 40),(109, 42),(109, 56),(109, 58),(109, 87),(111, 42),(111, 58),(117, 48),(117, 50),(117, 56),(117, 58),(119, 50),(119, 58),(125, 56),(125, 58),(127, 58)]
def opts01 : List Pair := [(17, 17),(33, 33),(48, 48),(51, 51),(53, 53),(57, 57),(59, 59),(113, 113),(115, 115),(55, 6),(55, 14),(61, 12),(61, 14),(63, 14),(70, 55),(76, 61),(78, 55),(78, 61),(78, 63),(117, 68),(117, 70),(117, 76),(117, 78),(119, 70),(119, 78),(121, 55),(121, 72),(121, 74),(121, 76),(121, 78),(123, 74),(123, 78),(125, 76),(125, 78),(127, 78)]
def opts02 : List Pair := [(24, 24),(72, 72),(80, 80),(89, 89),(90, 90),(92, 92),(120, 120),(91, 3),(91, 7),(91, 35),(91, 39),(93, 5),(93, 7),(93, 37),(93, 39),(94, 6),(94, 7),(94, 38),(94, 39),(95, 7),(95, 39),(121, 33),(121, 35),(121, 37),(121, 39),(121, 94),(122, 34),(122, 35),(122, 38),(122, 39),(122, 93),(123, 35),(123, 39),(124, 36),(124, 37),(124, 38),(124, 39),(124, 91),(125, 37),(125, 39),(126, 38),(126, 39),(127, 39)]
def opts03 : List Pair := [(12, 12),(36, 36),(40, 40),(45, 45),(46, 46),(60, 60),(108, 108),(110, 110),(47, 3),(47, 19),(61, 17),(61, 19),(62, 18),(62, 19),(63, 19),(67, 47),(81, 61),(82, 62),(83, 47),(83, 61),(83, 62),(83, 63),(109, 62),(109, 65),(109, 67),(109, 81),(109, 83),(111, 67),(111, 83),(124, 47),(124, 80),(124, 81),(124, 82),(124, 83),(125, 81),(125, 83),(126, 82),(126, 83),(127, 83)]
def opts04 : List Pair := [(6, 6),(18, 18),(20, 20),(23, 23),(30, 30),(54, 54),(86, 86),(31, 9),(41, 31),(55, 33),(55, 41),(62, 40),(62, 41),(63, 41),(73, 31),(87, 62),(87, 65),(87, 73),(94, 55),(94, 72),(94, 73),(95, 73),(97, 55),(97, 87),(104, 62),(104, 94),(105, 31),(105, 55),(105, 62),(105, 63),(105, 87),(105, 94),(105, 95),(118, 31),(118, 96),(118, 97),(118, 104),(118, 105),(119, 97),(119, 105),(126, 104),(126, 105),(127, 105)]
def opts10 : List Pair := [(5, 5),(65, 65),(68, 68),(71, 71),(77, 77),(79, 79),(85, 85),(101, 101),(109, 109),(87, 18),(87, 26),(87, 50),(87, 58),(93, 24),(93, 26),(93, 56),(93, 58),(95, 26),(95, 58),(103, 34),(103, 42),(103, 50),(103, 58),(103, 93),(111, 42),(111, 58),(117, 48),(117, 50),(117, 56),(117, 58),(119, 50),(119, 58),(125, 56),(125, 58),(127, 58)]
def opts11 : List Pair := [(34, 34),(66, 66),(96, 96),(99, 99),(102, 102),(106, 106),(114, 114),(103, 5),(103, 13),(103, 21),(103, 29),(107, 9),(107, 13),(107, 25),(107, 29),(110, 12),(110, 13),(110, 28),(110, 29),(111, 13),(111, 29),(115, 17),(115, 21),(115, 25),(115, 29),(115, 110),(118, 20),(118, 21),(118, 28),(118, 29),(118, 107),(119, 21),(119, 29),(122, 24),(122, 25),(122, 28),(122, 29),(122, 103),(123, 25),(123, 29),(126, 28),(126, 29),(127, 29)]
def opts12 : List Pair := [(17, 17),(33, 33),(48, 48),(51, 51),(53, 53),(57, 57),(59, 59),(113, 113),(55, 6),(55, 14),(61, 12),(61, 14),(63, 14),(70, 55),(76, 61),(78, 55),(78, 61),(78, 63),(115, 61),(115, 66),(115, 70),(115, 74),(115, 78),(117, 68),(117, 70),(117, 76),(117, 78),(119, 70),(119, 78),(121, 55),(121, 72),(121, 74),(121, 76),(121, 78),(123, 74),(123, 78),(125, 76),(125, 78),(127, 78)]
def opts13 : List Pair := [(24, 24),(72, 72),(80, 80),(89, 89),(90, 90),(92, 92),(120, 120),(91, 3),(91, 7),(91, 35),(91, 39),(93, 5),(93, 7),(93, 37),(93, 39),(94, 6),(94, 7),(94, 38),(94, 39),(95, 7),(95, 39),(121, 33),(121, 35),(121, 37),(121, 39),(121, 94),(122, 34),(122, 35),(122, 38),(122, 39),(122, 93),(123, 35),(123, 39),(124, 36),(124, 37),(124, 38),(124, 39),(124, 91),(125, 37),(125, 39),(126, 38),(126, 39),(127, 39)]
def opts14 : List Pair := [(6, 6),(18, 18),(20, 20),(23, 23),(30, 30),(54, 54),(62, 62),(86, 86),(31, 9),(41, 31),(55, 33),(55, 41),(63, 41),(73, 31),(87, 65),(87, 73),(94, 55),(94, 72),(94, 73),(95, 73),(97, 55),(97, 87),(104, 94),(105, 31),(105, 55),(105, 63),(105, 87),(105, 94),(105, 95),(118, 31),(118, 96),(118, 97),(118, 104),(118, 105),(119, 97),(119, 105),(126, 104),(126, 105),(127, 105)]
set_option maxRecDepth 20000 in
private theorem g0_0 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (5, 5) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_1 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (65, 65) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_2 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (68, 68) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_3 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (71, 71) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_4 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (77, 77) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_5 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (79, 79) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_6 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (85, 85) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_7 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (101, 101) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_8 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (87, 18) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_9 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (87, 26) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_10 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (87, 50) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_11 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (87, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_12 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (93, 24) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_13 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (93, 26) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_14 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (93, 56) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_15 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (93, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_16 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (95, 26) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_17 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (95, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_18 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (103, 34) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_19 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (103, 42) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_20 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (103, 50) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_21 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (103, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_22 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (103, 93) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_23 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (109, 40) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_24 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (109, 42) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_25 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (109, 56) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_26 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (109, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_27 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (109, 87) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_28 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (111, 42) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_29 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (111, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_30 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (117, 48) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_31 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (117, 50) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_32 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (117, 56) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_33 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (117, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_34 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (119, 50) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_35 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (119, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_36 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (125, 56) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_37 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (125, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g0_38 : blocked 4 [opts01,opts02,opts03,opts04] (putPair (127, 58) [])=true := by decide +kernel
theorem five0 : blocked 4 [opts00,opts01,opts02,opts03,opts04] []=true := by
  change (opts00.all (fun q => blocked 4 [opts01,opts02,opts03,opts04] (putPair q [])))=true
  simp only [opts00,List.all_cons,List.all_nil,Bool.and_eq_true_iff]
  exact ⟨g0_0,g0_1,g0_2,g0_3,g0_4,g0_5,g0_6,g0_7,g0_8,g0_9,g0_10,g0_11,g0_12,g0_13,g0_14,g0_15,g0_16,g0_17,g0_18,g0_19,g0_20,g0_21,g0_22,g0_23,g0_24,g0_25,g0_26,g0_27,g0_28,g0_29,g0_30,g0_31,g0_32,g0_33,g0_34,g0_35,g0_36,g0_37,g0_38,rfl⟩
set_option maxRecDepth 20000 in
private theorem g1_0 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (5, 5) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_1 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (65, 65) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_2 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (68, 68) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_3 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (71, 71) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_4 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (77, 77) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_5 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (79, 79) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_6 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (85, 85) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_7 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (101, 101) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_8 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (109, 109) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_9 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (87, 18) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_10 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (87, 26) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_11 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (87, 50) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_12 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (87, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_13 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (93, 24) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_14 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (93, 26) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_15 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (93, 56) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_16 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (93, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_17 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (95, 26) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_18 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (95, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_19 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (103, 34) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_20 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (103, 42) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_21 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (103, 50) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_22 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (103, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_23 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (103, 93) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_24 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (111, 42) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_25 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (111, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_26 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (117, 48) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_27 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (117, 50) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_28 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (117, 56) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_29 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (117, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_30 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (119, 50) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_31 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (119, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_32 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (125, 56) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_33 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (125, 58) [])=true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem g1_34 : blocked 4 [opts11,opts12,opts13,opts14] (putPair (127, 58) [])=true := by decide +kernel
theorem five1 : blocked 4 [opts10,opts11,opts12,opts13,opts14] []=true := by
  change (opts10.all (fun q => blocked 4 [opts11,opts12,opts13,opts14] (putPair q [])))=true
  simp only [opts10,List.all_cons,List.all_nil,Bool.and_eq_true_iff]
  exact ⟨g1_0,g1_1,g1_2,g1_3,g1_4,g1_5,g1_6,g1_7,g1_8,g1_9,g1_10,g1_11,g1_12,g1_13,g1_14,g1_15,g1_16,g1_17,g1_18,g1_19,g1_20,g1_21,g1_22,g1_23,g1_24,g1_25,g1_26,g1_27,g1_28,g1_29,g1_30,g1_31,g1_32,g1_33,g1_34,rfl⟩
end Research9815.Decoder
