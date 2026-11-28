import PEqualNP.Defs
namespace Local17147
abbrev Row := Nat × List (Int × Nat)
def hit (set n:Nat) : Bool := set.testBit n
def atoms (dim code:Nat) := (List.range ((1 <<< dim)-1)).filterMap fun i=>if hit code i then some (i+1) else none
def mask (s:List Nat) := s.foldl (fun out i=>out ||| (1 <<< i)) 0
def reach (d:Nat) (p:List Nat) := p.foldl (fun R a=>R ||| mask ((List.range (1 <<< d)).filterMap fun i=>
  if hit R i && (i &&& a)==0 then some (i ||| a) else none)) 1
def scoreRow (R:Nat) (row:Row) : Option Int :=
  ((row.2.find? fun x=>(x.2 &&& R) != 0).map fun val=> (row.1:Int)*val.1)
def score (R:Nat) (rows:List Row) : Option Int := (rows.mapM (scoreRow R)).map List.sum
def weight (d x:Nat) := ((List.range d).filter (hit x)).length
def linked (d:Nat) (p:List Nat) := ((List.range d).filter fun i=>(List.range d).any fun j=>
  i != j && p.all fun a=> !hit a j || hit a i).length
def defines (d R H:Nat) : Bool := (List.range (1 <<< d)).all fun a=>(List.range (1 <<< d)).all fun b=>
  !(decide (weight d a≤2 ∧ weight d b≤2) && ((a &&& b)==0) && ((b &&& H)==b)) ||
    (List.range (1 <<< d)).any fun s=>hit R s && ((s &&& a)==a) && ((s &&& b)==0)
def cost (d:Nat) (atPoint:Bool) (k h:Nat) : Int :=
  1620*(k:Int)+(if atPoint then 729*(h:Int)-17199*(d:Int) else -729*(h:Int)+15957*(d:Int))
def budget (d:Nat) (atPoint:Bool) (charge:Int) (k h:Nat) : Int :=
  864*(k:Int)+(if atPoint then 162*(h:Int) else -162*(h:Int))+charge
def verify (d:Nat) (atPoint:Bool) (charge:Int) (rows:List Row) (code:Nat) : Bool := Id.run do
  let p:=atoms d code
  if p.isEmpty || decide (p.length > d) then return true
  let R:=reach d p
  let some sc := score R rows | return true
  let ok (h:Nat) := decide (sc≤cost d atPoint p.length h ∧ sc≤budget d atPoint charge p.length h)
  if atPoint then return ok (linked d p)
  return (List.range (1 <<< d)).all fun H=> !defines d R H || ok (weight d H)
def point : List Row := [(9,[(71,170)]),(9,[(71,204)]),(9,[(-1296,8),(-1311,128)]),(9,[(71,68),(68,136)]),(9,[(71,12),(68,192)]),(9,[(71,34),(68,136)]),(9,[(71,10),(68,160)]),(9,[(-1296,64),(-1311,128)]),(9,[(71,240)]),(9,[(-1296,32),(-1311,128)]),(9,[(71,80),(68,160)]),(9,[(71,48),(68,192)]),(9,[(0,85),(-3,170)]),(9,[(-648,4),(-663,72),(-678,128)]),(9,[(0,15),(-3,240)]),(9,[(0,51),(-3,204)]),(9,[(-648,2),(-663,40),(-678,128)]),(9,[(-648,16),(-663,96),(-678,128)])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem pointThree : ∀i:Fin 128,verify 3 true (-49329) point i.val = true := by decide +kernel
def line : List Row := [(9,[(528,2),(525,32),(513,8),(510,128)]),(9,[(528,2),(525,8),(513,32),(510,128)]),(9,[(528,4),(525,64),(513,8),(510,128)]),(9,[(528,4),(525,8),(513,64),(510,128)]),(18,[(0,255)]),(9,[(528,16),(525,64),(513,32),(510,128)]),(9,[(528,16),(525,32),(513,64),(510,128)]),(9,[(1056,8),(1041,128)]),(9,[(1056,8),(1053,128)]),(18,[(-648,170)]),(9,[(1056,32),(1041,128)]),(9,[(1056,32),(1053,128)]),(18,[(-648,204)]),(9,[(1056,64),(1041,128)]),(9,[(1056,64),(1053,128)]),(18,[(-648,240)])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem lineThree : ∀i:Fin 128,verify 3 false (48438) line i.val = true := by decide +kernel
end Local17147
