import impl.system

namespace Concrete

open Protocol (Object)

structure Cached (H : Hasher) where
  state : State := {}
  cache : List (String × List (List Object) × H.Hash) := []

def Cached.init (H : Hasher) : Cached H := {}

def Cached.read {H : Hasher} (cs : Cached H) (name : String) : List (List Object) × Cond H :=
  match cs.cache.find? (·.1 == name) with
  | some (_, parts, etag) =>
      (parts, .hash etag)
  | none =>
      (cs.state.parts name, Cond.of H (cs.state.blob? (.origin name)))

def Cached.forget {H : Hasher} (cs : Cached H) (name : String) : List (String × List (List Object) × H.Hash) :=
  cs.cache.filter (·.1 != name)

def attempt (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands) (cs : Cached H) :
    α × Cached H × Bool :=
  let (parts, cond) := cs.read name
  let (a, c) := f (view parts)
  let (s', ok) := applyAll cs.state (c.effects (write H cfg name parts cond c.org))
  (a, { state := s',
        cache := match ok, s'.blob? (.origin name) with
                 | true, some (.origin parts') => (name, parts', H.hash (.origin parts')) :: cs.forget name
                 | _, _ => cs.forget name }, ok)

def runCached (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands) (cs : Cached H) :
    α × Cached H × Bool :=
  let (a, cs', ok) := attempt H cfg name f cs
  if ok then (a, cs', ok) else attempt H cfg name f cs'

def stepCached (H : Hasher) (cfg : Config) (ev : Event) (now : Nat) (cs : Cached H) : Reply × Cached H :=
  match ev with
  | .external req =>
      match req.origin? with
      | some name =>
          let (r, cs', ok) := runCached H cfg name (fun org => handle ev now org) cs
          (if ok then r else .stutter, cs')
      | none =>
          (.stutter, cs)
  | .internal t =>
      if (cs.state.blob? (.timer t)).isSome ∧ t.deadline ≤ now then
        let (r, cs', ok) := runCached H cfg t.id.origin (fun org => handle ev now org) cs
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

def Valid (H : Hasher) (cfg : Config) (tr : Trace H) : Prop :=
  ∀ t : Nat,
    stepCached H cfg (tr t).event (tr t).now (tr t).state = ((tr t).reply, (tr (t + 1)).state) ∧
    (tr t).now ≤ (tr (t + 1)).now

end Cached

end Concrete
