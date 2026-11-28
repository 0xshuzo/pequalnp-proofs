import PEqualNP.Defs
namespace Palette17147
open scoped BigOperators
abbrev Record := Int × Int × Int
def table0 : List Record := [(3,2,-47331),(3,0,-46737),(3,1,-47034),(2,2,-47331),(2,3,-47790),(1,3,-48114)]
def table1 : List Record := [(4,2,-62910),(4,3,-63207),(4,1,-62712),(3,3,-63333),(4,4,-63828),(3,4,-63756),(3,2,-63081),(4,0,-62739),(3,1,-63243)]
def table2 : List Record := [(4,2,-62910),(4,1,-62613),(3,3,-63207),(4,3,-63207),(4,0,-62316),(3,4,-63504),(3,1,-63207),(2,3,-63693),(4,4,-63828),(3,2,-62910),(2,4,-63504),(1,4,-64260)]
def table3 : List Record := [(3,0,50544),(3,-1,50544),(3,-2,50544),(3,-3,50544),(2,0,49896),(2,-1,49896),(1,0,49086)]
def table4 : List Record := [(4,0,67392),(4,-1,67392),(4,-2,67392),(3,0,66744),(3,-1,66744),(4,-3,67392),(2,0,66096),(2,-1,65934),(3,-2,66744),(4,-4,67392),(1,0,65448)]
def casesTable (i:Fin 5) : List Record := [table0,table1,table2,table3,table4][i.val]?.getD []
def charges (i:Fin 5) : Int := ([-49329,-65997,-65772,48438,64584]:List Int)[i.val]?.getD 0
def kind (i:Fin 26) : Fin 5 := if i.val=0 then 0 else if i.val≤2 then 1 else if i.val≤12 then 2 else if i.val=13 then 3 else 4
def allowed (i:Fin 5) (x:Record) : Bool := decide (x.2.2 ≤ 864*x.1+162*x.2.1+charges i)
theorem paid_local : ∀i:Fin 5,(casesTable i).all (allowed i)=true := by decide +kernel
theorem paid_global (r:Fin 26→Record) (localCost:∀i,r i∈casesTable (kind i))
    (balance:∑i,(r i).2.1=0) (cells:39933≤∑i,(r i).2.2) : 65≤∑i,(r i).1 := by
  have le (i:Fin 26) : (r i).2.2≤864*(r i).1+162*(r i).2.1+charges (kind i) :=
    of_decide_eq_true (List.all_eq_true.mp (paid_local (kind i)) _ (localCost i))
  have h:=Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin 26))) (fun i _=>le i)
  have off : ∑i:Fin 26,charges (kind i)= -15597 := by decide +kernel
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,balance,mul_zero,add_zero,off] at h
  omega
theorem all_subgraphs {P L:Type} [Fintype P] [Fintype L]
    (pK pH pD pS:P→Int) (lK lH lD lS:L→Int) (edges:Int)
    (hp:∀v,pS v≤1620*pK v+729*pH v-17199*pD v)
    (hl:∀v,lS v≤1620*lK v-729*lH v+15957*lD v)
    (balance:∑v,pH v=∑v,lH v) (dp:∑v,pD v=edges) (dl:∑v,lD v=edges)
    (score:783*edges≤(∑v,pS v)+(∑v,lS v)) :
    5*edges≤4*((∑v,pK v)+(∑v,lK v)) := by
  have a:=Finset.sum_le_sum (s:=(Finset.univ:Finset P)) (fun i _=>hp i)
  have b:=Finset.sum_le_sum (s:=(Finset.univ:Finset L)) (fun i _=>hl i)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,dp,dl,balance] at a b
  linarith
end Palette17147
