import «02-abstract».«external»

namespace AbstractModel
namespace Internal

open ServerModel (Ident nextCron occurrences expand Schedule
                  PromiseTimeoutReq PromiseRegisterCallbackReq PromiseRegisterListenerReq
                  TaskLeaseTimeoutReq TaskRetryTimeoutReq ScheduleTimeoutReq)

def processPromiseTimeout (req : PromiseTimeoutReq) (now : Nat) : H Unit := do
  let _ ← touchObject req.id now

def resumeOne (awaited awaiter : Ident) (now : Nat) : H Unit := do
  match ← touchTaskObject awaiter now with
  | none => pure ()
  | some o =>
  match o.task with
  | none => pure ()
  | some t =>
      match t.state with
      | .suspended =>
          setTask o.id { t with state := .pending, resumes := [awaited],
                                retryTimeoutAt := some now }
      | .pending | .acquired | .halted =>
          if !(t.resumes.contains awaited) then
            setTask o.id { t with resumes := t.resumes ++ [awaited] }
      | .fulfilled =>
          pure ()

def processCallback (req : PromiseRegisterCallbackReq) (now : Nat) : H Unit := do
  match ← touchObject req.awaited now with
  | none => pure ()
  | some o =>
      if o.promise.state == .pending then
        pure ()
      else if o.promise.callbacks.contains req.awaiter then
        setPromise o.id { o.promise with
                          callbacks := o.promise.callbacks.filter (· != req.awaiter) }
        resumeOne o.id req.awaiter now

def processListener (req : PromiseRegisterListenerReq) (now : Nat) : H Unit := do
  match ← touchObject req.awaited now with
  | none => pure ()
  | some o =>
      if o.promise.state == .pending then
        pure ()
      else if o.promise.listeners.contains req.address then
        setPromise o.id { o.promise with
                          listeners := o.promise.listeners.filter (· != req.address) }
        setMessage req.address (.unblock (o.promise.toRecord o.id))

def processLeaseTimeout (req : TaskLeaseTimeoutReq) (now : Nat) : H Unit := do
  match ← viewTaskObject req.id now with
  | none => pure ()
  | some o =>
  match o.task with
  | none => pure ()
  | some t =>
      match t.leaseTimeoutAt with
      | none => pure ()
      | some deadline =>
          if t.state == .acquired ∧ deadline ≤ now then
            if o.promise.state == .pending then
              setTask o.id { t with state := .pending, pid := none, ttl := none,
                                    leaseTimeoutAt := none, retryTimeoutAt := some now }

def processRetryTimeout (req : TaskRetryTimeoutReq) (now : Nat) : H Unit := do
  match ← viewTaskObject req.id now with
  | none => pure ()
  | some o =>
  match o.task with
  | none => pure ()
  | some t =>
      match t.retryTimeoutAt with
      | none => pure ()
      | some due =>
          if t.state == .pending ∧ due ≤ now then
            if o.promise.state == .pending then
              match o.promise.type with
              | .runnable target =>
                  setTask o.id { t with
                                 retryTimeoutAt := some (now + (← ask).config.retryTimeout) }
                  setMessage target (.execute o.id t.version)
              | _ => pure ()

def fireOccurrence (s : Schedule) (t : Nat) : H Unit :=
  createIfAbsent
    { id := expand s.promiseId s.id t, timeoutAt := t + s.promiseTimeout,
      param := s.promiseParam, type := s.promiseType } t

def fireAll (s : Schedule) : List Nat → H Unit
  | [] => pure ()
  | t :: ts => do
      fireOccurrence s t
      fireAll s ts

def processSchedule (req : ScheduleTimeoutReq) (now : Nat) : H Unit := do
  match ← getSchedule req.schedule with
  | none => pure ()
  | some s =>
      let ts := (occurrences s.cron s.nextRunAt now).filter (· ≤ now)
      fireAll s ts
      match ts.getLast? with
      | some last =>
          setSchedule { s with lastRunAt := some last,
                               nextRunAt := nextCron s.cron last }
      | none => pure ()

end Internal
end AbstractModel
