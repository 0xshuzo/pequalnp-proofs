import Mathlib
namespace Theta4970
def cover (P : BitVec 14) : Prop :=
  (P &&& (2059 : BitVec 14) ≠ 0) ∧
  (P &&& (4109 : BitVec 14) ≠ 0) ∧
  (P &&& (8206 : BitVec 14) ≠ 0) ∧
  (P &&& (2064 : BitVec 14) ≠ 0) ∧
  (P &&& (4128 : BitVec 14) ≠ 0) ∧
  (P &&& (8256 : BitVec 14) ≠ 0) ∧
  (P &&& (1424 : BitVec 14) ≠ 0) ∧
  (P &&& (1696 : BitVec 14) ≠ 0) ∧
  (P &&& (1856 : BitVec 14) ≠ 0)
def minimal (P : BitVec 14) : Prop :=
  ((P &&& (1 : BitVec 14) ≠ 0) → (P &&& (2059 : BitVec 14) = (1 : BitVec 14)) ∨ (P &&& (4109 : BitVec 14) = (1 : BitVec 14))) ∧
  ((P &&& (2 : BitVec 14) ≠ 0) → (P &&& (2059 : BitVec 14) = (2 : BitVec 14)) ∨ (P &&& (8206 : BitVec 14) = (2 : BitVec 14))) ∧
  ((P &&& (4 : BitVec 14) ≠ 0) → (P &&& (4109 : BitVec 14) = (4 : BitVec 14)) ∨ (P &&& (8206 : BitVec 14) = (4 : BitVec 14))) ∧
  ((P &&& (8 : BitVec 14) ≠ 0) → (P &&& (2059 : BitVec 14) = (8 : BitVec 14)) ∨ (P &&& (4109 : BitVec 14) = (8 : BitVec 14)) ∨ (P &&& (8206 : BitVec 14) = (8 : BitVec 14))) ∧
  ((P &&& (16 : BitVec 14) ≠ 0) → (P &&& (2064 : BitVec 14) = (16 : BitVec 14)) ∨ (P &&& (1424 : BitVec 14) = (16 : BitVec 14))) ∧
  ((P &&& (32 : BitVec 14) ≠ 0) → (P &&& (4128 : BitVec 14) = (32 : BitVec 14)) ∨ (P &&& (1696 : BitVec 14) = (32 : BitVec 14))) ∧
  ((P &&& (64 : BitVec 14) ≠ 0) → (P &&& (8256 : BitVec 14) = (64 : BitVec 14)) ∨ (P &&& (1856 : BitVec 14) = (64 : BitVec 14))) ∧
  ((P &&& (128 : BitVec 14) ≠ 0) → (P &&& (1424 : BitVec 14) = (128 : BitVec 14)) ∨ (P &&& (1696 : BitVec 14) = (128 : BitVec 14))) ∧
  ((P &&& (256 : BitVec 14) ≠ 0) → (P &&& (1424 : BitVec 14) = (256 : BitVec 14)) ∨ (P &&& (1856 : BitVec 14) = (256 : BitVec 14))) ∧
  ((P &&& (512 : BitVec 14) ≠ 0) → (P &&& (1696 : BitVec 14) = (512 : BitVec 14)) ∨ (P &&& (1856 : BitVec 14) = (512 : BitVec 14))) ∧
  ((P &&& (1024 : BitVec 14) ≠ 0) → (P &&& (1424 : BitVec 14) = (1024 : BitVec 14)) ∨ (P &&& (1696 : BitVec 14) = (1024 : BitVec 14)) ∨ (P &&& (1856 : BitVec 14) = (1024 : BitVec 14))) ∧
  ((P &&& (2048 : BitVec 14) ≠ 0) → (P &&& (2059 : BitVec 14) = (2048 : BitVec 14)) ∨ (P &&& (2064 : BitVec 14) = (2048 : BitVec 14))) ∧
  ((P &&& (4096 : BitVec 14) ≠ 0) → (P &&& (4109 : BitVec 14) = (4096 : BitVec 14)) ∨ (P &&& (4128 : BitVec 14) = (4096 : BitVec 14))) ∧
  ((P &&& (8192 : BitVec 14) ≠ 0) → (P &&& (8206 : BitVec 14) = (8192 : BitVec 14)) ∨ (P &&& (8256 : BitVec 14) = (8192 : BitVec 14)))
def allowed (P : BitVec 14) (U : BitVec 22) : Prop :=
  ((U &&& (256 : BitVec 22) ≠ 0) → (P &&& (1 : BitVec 14) ≠ 0)) ∧
  ((U &&& (512 : BitVec 22) ≠ 0) → (P &&& (2 : BitVec 14) ≠ 0)) ∧
  ((U &&& (1024 : BitVec 22) ≠ 0) → (P &&& (4 : BitVec 14) ≠ 0)) ∧
  ((U &&& (2048 : BitVec 22) ≠ 0) → (P &&& (8 : BitVec 14) ≠ 0)) ∧
  ((U &&& (4096 : BitVec 22) ≠ 0) → (P &&& (16 : BitVec 14) ≠ 0)) ∧
  ((U &&& (8192 : BitVec 22) ≠ 0) → (P &&& (32 : BitVec 14) ≠ 0)) ∧
  ((U &&& (16384 : BitVec 22) ≠ 0) → (P &&& (64 : BitVec 14) ≠ 0)) ∧
  ((U &&& (32768 : BitVec 22) ≠ 0) → (P &&& (128 : BitVec 14) ≠ 0)) ∧
  ((U &&& (65536 : BitVec 22) ≠ 0) → (P &&& (256 : BitVec 14) ≠ 0)) ∧
  ((U &&& (131072 : BitVec 22) ≠ 0) → (P &&& (512 : BitVec 14) ≠ 0)) ∧
  ((U &&& (262144 : BitVec 22) ≠ 0) → (P &&& (1024 : BitVec 14) ≠ 0)) ∧
  ((U &&& (524288 : BitVec 22) ≠ 0) → (P &&& (2048 : BitVec 14) ≠ 0)) ∧
  ((U &&& (1048576 : BitVec 22) ≠ 0) → (P &&& (4096 : BitVec 14) ≠ 0)) ∧
  ((U &&& (2097152 : BitVec 22) ≠ 0) → (P &&& (8192 : BitVec 14) ≠ 0))
def separates (U : BitVec 22) : Prop :=
  (U &&& (2848 : BitVec 22) ≠ 0) ∧
  (U &&& (3392 : BitVec 22) ≠ 0) ∧
  (U &&& (3712 : BitVec 22) ≠ 0) ∧
  (U &&& (4112 : BitVec 22) ≠ 0) ∧
  (U &&& (4128 : BitVec 22) ≠ 0) ∧
  (U &&& (4384 : BitVec 22) ≠ 0) ∧
  (U &&& (4640 : BitVec 22) ≠ 0) ∧
  (U &&& (6944 : BitVec 22) ≠ 0) ∧
  (U &&& (8208 : BitVec 22) ≠ 0) ∧
  (U &&& (8256 : BitVec 22) ≠ 0) ∧
  (U &&& (8512 : BitVec 22) ≠ 0) ∧
  (U &&& (9280 : BitVec 22) ≠ 0) ∧
  (U &&& (11584 : BitVec 22) ≠ 0) ∧
  (U &&& (12304 : BitVec 22) ≠ 0) ∧
  (U &&& (16400 : BitVec 22) ≠ 0) ∧
  (U &&& (16512 : BitVec 22) ≠ 0) ∧
  (U &&& (17024 : BitVec 22) ≠ 0) ∧
  (U &&& (17536 : BitVec 22) ≠ 0) ∧
  (U &&& (20096 : BitVec 22) ≠ 0) ∧
  (U &&& (20496 : BitVec 22) ≠ 0) ∧
  (U &&& (24592 : BitVec 22) ≠ 0) ∧
  (U &&& (28688 : BitVec 22) ≠ 0) ∧
  (U &&& (360450 : BitVec 22) ≠ 0) ∧
  (U &&& (363298 : BitVec 22) ≠ 0) ∧
  (U &&& (425988 : BitVec 22) ≠ 0) ∧
  (U &&& (429380 : BitVec 22) ≠ 0) ∧
  (U &&& (458760 : BitVec 22) ≠ 0) ∧
  (U &&& (462472 : BitVec 22) ≠ 0) ∧
  (U &&& (524289 : BitVec 22) ≠ 0) ∧
  (U &&& (524290 : BitVec 22) ≠ 0) ∧
  (U &&& (533569 : BitVec 22) ≠ 0) ∧
  (U &&& (541825 : BitVec 22) ≠ 0) ∧
  (U &&& (548882 : BitVec 22) ≠ 0) ∧
  (U &&& (557058 : BitVec 22) ≠ 0) ∧
  (U &&& (573458 : BitVec 22) ≠ 0) ∧
  (U &&& (589826 : BitVec 22) ≠ 0) ∧
  (U &&& (598034 : BitVec 22) ≠ 0) ∧
  (U &&& (884738 : BitVec 22) ≠ 0) ∧
  (U &&& (1048577 : BitVec 22) ≠ 0) ∧
  (U &&& (1048580 : BitVec 22) ≠ 0) ∧
  (U &&& (1053217 : BitVec 22) ≠ 0) ∧
  (U &&& (1065601 : BitVec 22) ≠ 0) ∧
  (U &&& (1069076 : BitVec 22) ≠ 0) ∧
  (U &&& (1081348 : BitVec 22) ≠ 0) ∧
  (U &&& (1097748 : BitVec 22) ≠ 0) ∧
  (U &&& (1179652 : BitVec 22) ≠ 0) ∧
  (U &&& (1183764 : BitVec 22) ≠ 0) ∧
  (U &&& (1474564 : BitVec 22) ≠ 0) ∧
  (U &&& (1572865 : BitVec 22) ≠ 0) ∧
  (U &&& (1589377 : BitVec 22) ≠ 0) ∧
  (U &&& (2097153 : BitVec 22) ≠ 0) ∧
  (U &&& (2097160 : BitVec 22) ≠ 0) ∧
  (U &&& (2101537 : BitVec 22) ≠ 0) ∧
  (U &&& (2105665 : BitVec 22) ≠ 0) ∧
  (U &&& (2109464 : BitVec 22) ≠ 0) ∧
  (U &&& (2162696 : BitVec 22) ≠ 0) ∧
  (U &&& (2170904 : BitVec 22) ≠ 0) ∧
  (U &&& (2228232 : BitVec 22) ≠ 0) ∧
  (U &&& (2232344 : BitVec 22) ≠ 0) ∧
  (U &&& (2555912 : BitVec 22) ≠ 0) ∧
  (U &&& (2621441 : BitVec 22) ≠ 0) ∧
  (U &&& (2629697 : BitVec 22) ≠ 0) ∧
  (U &&& (3145729 : BitVec 22) ≠ 0) ∧
  (U &&& (3149857 : BitVec 22) ≠ 0) ∧
  (U &&& (3670017 : BitVec 22) ≠ 0)
def picked (P : BitVec 14) := (if (P &&& (1 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (2 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (4 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (8 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (16 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (32 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (64 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (128 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (256 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (512 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (1024 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (2048 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (4096 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)+(if (P &&& (8192 : BitVec 14) ≠ 0) then (1 : BitVec 6) else 0)
def sources (U : BitVec 22) := (if (U &&& (1 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (2 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (4 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (8 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (16 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (32 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (64 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (128 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (256 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (512 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (1024 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (2048 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (4096 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (8192 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (16384 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (32768 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (65536 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (131072 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (262144 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (524288 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (1048576 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)+(if (U &&& (2097152 : BitVec 22) ≠ 0) then (1 : BitVec 6) else 0)
def exceptions (P : BitVec 14) (U : BitVec 22) : Prop :=
  (P=120 ∧ U=255) ∨
  (P=120 ∧ U=30735) ∨
  (P=15360 ∧ U=255) ∨
  (P=15360 ∧ U=3932400)
set_option maxHeartbeats 0 in
theorem sourceCertificate (P : BitVec 14) (U : BitVec 22) :
    cover P → minimal P → allowed P U → separates U → picked P + sources U ≤ 12 → exceptions P U := by
  unfold cover minimal allowed separates picked sources exceptions
  bv_decide
def graph (x : BitVec 8) : Bool := decide (x &&& (33 : BitVec 8) = (33 : BitVec 8)) || decide (x &&& (65 : BitVec 8) = (65 : BitVec 8)) || decide (x &&& (129 : BitVec 8) = (129 : BitVec 8)) || decide (x &&& (34 : BitVec 8) = (34 : BitVec 8)) || decide (x &&& (68 : BitVec 8) = (68 : BitVec 8)) || decide (x &&& (136 : BitVec 8) = (136 : BitVec 8)) || decide (x &&& (18 : BitVec 8) = (18 : BitVec 8)) || decide (x &&& (20 : BitVec 8) = (20 : BitVec 8)) || decide (x &&& (24 : BitVec 8) = (24 : BitVec 8))
def W : Array (BitVec 8 × BitVec 8) := #[(0,0),(32,33),(16,18),(16,18),(16,20),(16,20),(16,18),(16,18),(16,24),(16,24),(16,18),(16,18),(16,20),(16,20),(16,18),(17,18),(2,18),(2,18),(0,20),(0,20),(0,18),(0,18),(0,24),(0,24),(0,18),(0,18),(0,20),(0,20),(0,18),(0,18),(0,34),(1,33),(1,33),(0,34),(0,18),(0,18),(1,20),(0,20),(0,18),(0,18),(1,24),(0,24),(0,18),(0,18),(1,20),(0,20),(0,18),(1,18),(1,18),(0,18),(0,20),(0,20),(0,18),(0,18),(0,24),(0,24),(0,18),(0,18),(0,20),(0,20),(0,18),(1,18),(0,33),(1,65),(1,65),(0,33),(1,18),(0,18),(0,20),(0,20),(0,18),(0,18),(1,24),(0,24),(1,18),(0,18),(0,20),(0,20),(0,18),(1,18),(1,18),(0,18),(0,20),(0,20),(0,18),(0,18),(0,24),(0,24),(0,18),(0,18),(0,20),(1,20),(0,18),(0,18),(0,34),(1,33),(1,33),(0,34),(0,18),(0,18),(0,20),(0,20),(0,18),(0,18),(1,24),(0,24),(0,18),(0,18),(0,20),(0,20),(0,18),(1,18),(1,18),(0,18),(0,20),(0,20),(0,18),(0,18),(0,24),(0,24),(0,18),(1,18),(0,20),(1,20),(0,18),(1,18),(0,33),(1,129),(1,129),(0,33),(1,18),(0,18),(1,20),(0,20),(1,18),(0,18),(0,24),(0,24),(0,18),(0,18),(0,20),(0,20),(0,18),(1,18),(1,18),(0,18),(0,20),(0,20),(0,18),(0,18),(0,24),(1,24),(0,18),(0,18),(0,20),(0,20),(0,18),(0,18),(0,34),(1,33),(1,33),(0,34),(0,18),(0,18),(1,20),(0,20),(0,18),(0,18),(0,24),(0,24),(0,18),(0,18),(0,20),(0,20),(0,18),(1,18),(1,18),(0,18),(0,20),(0,20),(0,18),(1,18),(0,24),(1,24),(0,18),(0,18),(0,20),(0,20),(0,18),(1,18),(0,33),(1,65),(1,65),(0,33),(1,18),(0,18),(0,20),(0,20),(0,18),(0,18),(0,24),(0,24),(0,18),(0,18),(0,20),(0,20),(0,18),(1,18),(1,18),(0,18),(0,20),(1,20),(0,18),(0,18),(0,24),(1,24),(0,18),(0,18),(0,20),(1,20),(0,18),(0,18),(0,34),(1,33),(1,33),(0,34),(0,18),(0,18),(0,20),(0,20),(0,18),(0,18),(0,24),(0,24),(0,18),(0,18),(0,20),(0,20),(2,18),(2,18),(17,18),(16,18),(16,20),(16,20),(16,18),(16,18),(16,24),(16,24),(16,18),(16,18),(16,20),(16,20),(16,18),(16,18),(32,33),(0,0)]
set_option maxHeartbeats 0 in
theorem noSplit : ∀ m : Fin 256, 0<m.val → m.val<255 →
    let b := BitVec.ofNat 8 m.val
    let (x,y) := W[m.val]?.getD (0,0)
    graph x ≠ (graph (x ||| b) && graph (x ||| ~~~b)) ∧
      graph y ≠ (graph (y &&& b) || graph (y &&& ~~~b)) := by decide +kernel
end Theta4970
