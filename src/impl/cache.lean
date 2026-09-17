import impl.system

namespace Concrete

structure Cached (H : Hasher) where
  state : State := {}
  cache : List (String × Origin × H.Hash) := []

def Cached.init (H : Hasher) : Cached H := {}

def Cached.read {H : Hasher} (cs : Cached H) (name : String) : Origin × Cond H :=
  match cs.cache.find? (·.1 == name) with
  | some (_, org, etag) =>
      (org, .hash etag)
  | none =>
      (cs.state.origin name, Cond.of H (cs.state.blob? (.origin name)))

def Cached.forget {H : Hasher} (cs : Cached H) (name : String) : List (String × Origin × H.Hash) :=
  cs.cache.filter (·.1 != name)

def attempt (H : Hasher) (name : String) (f : Origin → α × Commands) (cs : Cached H) :
    α × Cached H × Bool :=
  let (org, cond) := cs.read name
  let (a, c) := f org
  let (s', ok) := applyAll cs.state (c.effects name cond)
  let etag := H.hash (.origin c.org)
  (a, { state := s', cache := if ok then (name, c.org, etag) :: cs.forget name else cs.forget name }, ok)

def runCached (H : Hasher) (name : String) (f : Origin → α × Commands) (cs : Cached H) :
    α × Cached H × Bool :=
  let (a, cs', ok) := attempt H name f cs
  if ok then (a, cs', ok) else attempt H name f cs'

def stepCached (H : Hasher) (ev : Event) (now : Nat) (cs : Cached H) : Reply × Cached H :=
  match ev with
  | .external req =>
      match req.origin? with
      | some name =>
          let (r, cs', ok) := runCached H name (fun org => handle now org ev) cs
          (if ok then r else .stutter, cs')
      | none =>
          (.stutter, cs)
  | .internal t =>
      if (cs.state.blob? (.timer t)).isSome ∧ t.deadline ≤ now then
        let (r, cs', ok) := runCached H t.id.origin (fun org => handle now org ev) cs
        (if ok then r else .stutter, cs')
      else
        (.stutter, cs)
  | .stutter =>
      (.stutter, cs)

namespace Cached

structure Frame (H : Hasher) where
  state : Cached H
  event : Event
  reply : Reply
  now   : Nat

abbrev Trace (H : Hasher) := Nat → Frame H

def Valid (H : Hasher) (tr : Trace H) : Prop :=
  ∀ t : Nat,
    stepCached H (tr t).event (tr t).now (tr t).state = ((tr t).reply, (tr (t + 1)).state) ∧
    (tr t).now ≤ (tr (t + 1)).now

end Cached

end Concrete
