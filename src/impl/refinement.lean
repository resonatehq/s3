import impl.system
import «02-abstract».«system»

namespace Abstract

open ServerModel (Request Response)

structure Observation where
  req : Request
  res : Response
  now : Nat

def Frame.observe (f : Frame) : Option Observation :=
  match f.event, f.reply with
  | .external req, .external res =>
      some ⟨req, res, f.now⟩
  | _, _ =>
      none

def observed (tr : Trace) (n : Nat) : List Observation :=
  ((List.range n).map tr).filterMap Frame.observe

def nth (tr : Trace) (k : Nat) (o : Observation) : Prop :=
  ∃ n, (observed tr n)[k]? = some o

end Abstract

namespace Concrete

def Frame.observe (f : Frame) : Option Abstract.Observation :=
  match f.event, f.reply with
  | .external req, .external res =>
      some ⟨req, res, f.now⟩
  | _, _ =>
      none

def observed (tr : Trace) (n : Nat) : List Abstract.Observation :=
  ((List.range n).map tr).filterMap Frame.observe

def nth (tr : Trace) (k : Nat) (o : Abstract.Observation) : Prop :=
  ∃ n, (observed tr n)[k]? = some o

end Concrete

namespace Refinement

theorem refines (H : Concrete.Hasher) (tr : Concrete.Trace)
    (valid : Concrete.Valid H tr) (init : (tr 0).state = Concrete.State.init) :
    ∃ tr' : Abstract.Trace,
      Abstract.Valid false tr' ∧
      (tr' 0).state = AbstractModel.ServerState.init ∧
      ∀ k o, Concrete.nth tr k o ↔ Abstract.nth tr' k o :=
  sorry

end Refinement
