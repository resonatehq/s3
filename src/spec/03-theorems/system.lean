import «02-abstract».«system»
import «02-abstract».«properties»

namespace Abstraction

def Legal (tr : Trace) : Prop :=
  ∀ t : Nat, (AbstractModel.Properties.catalogue.all fun l =>
    match l.property with
    | .state f => f (tr t).now (tr t).state
    | .trans f => f (tr t).now (tr t).state (tr (t+1)).state) = true

theorem valid_implies_legal (mat : Bool) (tr : Trace)
    (hv : Valid mat tr) (h0 : (tr 0).state = AbstractModel.ServerState.init) :
    Legal tr := sorry

def oid (suffix : String) : ServerModel.Ident := { origin := "o", suffix }

def extTags   : ServerModel.Tags := [("resonate:external", "true")]
def tgtTags   : ServerModel.Tags := [("resonate:target", "w1")]
def timerTags : ServerModel.Tags := [("resonate:timer", "true")]

end Abstraction
