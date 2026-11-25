import Mathlib

namespace PathOr2846

structure W where
  value : BitVec 16
  points : Bool
  lines : Bool
  flat : Bool

def a : W := ⟨43690,true,false,true⟩
def b : W := ⟨52428,false,true,true⟩
def c : W := ⟨61680,true,false,true⟩
def d : W := ⟨65280,false,true,true⟩

def gate (isor : Bool) (x y : W) : W :=
  ⟨if isor then x.value ||| y.value else x.value &&& y.value,
   isor && x.points && y.points, isor && x.lines && y.lines,
   x.flat && y.flat && (isor || (x.points && y.lines) || (x.lines && y.points))⟩

def pick (z : BitVec 3) (e f g : W) : W :=
  if z=0 then a else if z=1 then b else if z=2 then c else if z=3 then d else
  if z=4 then e else if z=5 then f else g

def build (o p q : Bool) (i j k l m n s t : BitVec 3) : W :=
  let e := gate o (pick i a a a) (pick j a a a)
  let f := gate p (pick k e a a) (pick l e a a)
  let g := gate q (pick m e f a) (pick n e f a)
  gate true (pick s e f g) (pick t e f g)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem orRootFlat (o p q : Bool) (i j k l m n s t : BitVec 3) :
    (build o p q i j k l m n s t).value = 63688 →
    (build o p q i j k l m n s t).flat = true := by
  dsimp [build,gate,pick,a,b,c,d]
  bv_decide

end PathOr2846
