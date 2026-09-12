import «02-abstract».«system»
import «02-abstract».«properties»

namespace Abstract

def Legal (tr : Trace) : Prop :=
  ∀ t : Nat, (Abstract.Properties.catalogue.all fun l =>
    match l.property with
    | .state f => f (tr t).now (tr t).state
    | .trans f => f (tr t).now (tr t).state (tr (t+1)).state) = true

theorem valid_implies_legal (mat : Bool) (tr : Trace)
    (hv : Valid mat tr) (h0 : (tr 0).state = Abstract.State.init) :
    Legal tr := sorry

def oid (suffix : String) : Protocol.Ident := { origin := "o", suffix }

def extType      : Protocol.OType := .external
def tgtType      : Protocol.OType := .runnable "w1"
def deadlineType : Protocol.OType := .deadline

end Abstract
