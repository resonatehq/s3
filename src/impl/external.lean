import impl.state

namespace Concrete

open Protocol (Ident Message PromiseState TaskState Object PromiseObject TaskObject)
open Protocol (PromiseGetReq PromiseGetRes
                  PromiseCreateReq PromiseCreateRes
                  PromiseSettleReq PromiseSettleRes
                  PromiseRegisterCallbackReq PromiseRegisterCallbackRes
                  PromiseRegisterListenerReq PromiseRegisterListenerRes
                  PromiseSearchReq PromiseSearchRes
                  TaskGetReq TaskGetRes
                  TaskCreateReq TaskCreateRes
                  TaskAcquireReq TaskAcquireRes
                  TaskFenceReq TaskFenceRes
                  TaskHeartbeatReq TaskHeartbeatRes
                  TaskSuspendReq TaskSuspendRes
                  TaskFulfillReq TaskFulfillRes
                  TaskReleaseReq TaskReleaseRes
                  TaskHaltReq TaskHaltRes
                  TaskContinueReq TaskContinueRes
                  TaskSearchReq TaskSearchRes
                  ScheduleGetReq ScheduleGetRes
                  ScheduleCreateReq ScheduleCreateRes
                  ScheduleDeleteReq ScheduleDeleteRes
                  ScheduleSearchReq ScheduleSearchRes)

def promiseGet (req : PromiseGetReq) (now : Nat) (org : Origin) : PromiseGetRes × Commands :=
  match org.get req.id now with
  | none =>
      ({ status := 404 }, {})
  | some o =>
      ({ status := 200, promise := some (o.promise.toRecord o.id) }, {})

def promiseCreate (req : PromiseCreateReq) (now : Nat) (org : Origin) : PromiseCreateRes × Commands :=
  match org.get req.id now with
  | some o =>
      ({ status := 200, promise := some (o.promise.toRecord o.id) }, {})
  | none =>
      if req.timeoutAt > now then
        let p : PromiseObject :=
          { state := .pending, param := req.param, type := req.type,
            timeoutAt := req.timeoutAt, createdAt := now }
        if p.type.isRunnable then
          let due :=
            match req.delay with
            | some d =>
                max d now
            | none =>
                now
          let t : TaskObject := { state := .pending, version := 0, retryTimeoutAt := some due }
          let o : Object := ⟨req.id, p, some t⟩
          ({ status := 200, promise := some (p.toRecord req.id) }, { arm := o.timers, add := [o] })
        else
          let o : Object := ⟨req.id, p, none⟩
          ({ status := 200, promise := some (p.toRecord req.id) }, { arm := o.timers, add := [o] })
      else
        let p : PromiseObject :=
          { state := if req.type == .deadline then .resolved else .rejectedTimedout,
            param := req.param, type := req.type,
            timeoutAt := req.timeoutAt, createdAt := req.timeoutAt,
            settledAt := some req.timeoutAt }
        let t : Option TaskObject :=
          if p.type.isRunnable then some { state := .fulfilled, version := 0 } else none
        ({ status := 200, promise := some (p.toRecord req.id) },
         { add := [⟨req.id, p, t⟩] })

def promiseSettle (req : PromiseSettleReq) (now : Nat) (org : Origin) : PromiseSettleRes × Commands :=
  if !req.state.settable then
    ({ status := 400 }, {})
  else
    match org.get req.id now with
    | none =>
        ({ status := 404 }, {})
    | some o =>
        if o.promise.state == .pending then
          let p := { o.promise with state := req.state, value := req.value, settledAt := some now }
          ({ status := 200, promise := some (p.toRecord o.id) },
           { add := [{ o with promise := p,
                                 task := o.task.map fun t =>
                                   if t.state == .fulfilled then t else t.fulfill }],
             del := o.timers })
        else
          ({ status := 200, promise := some (o.promise.toRecord o.id) }, {})

def promiseRegisterCallback (req : PromiseRegisterCallbackReq) (now : Nat) (org : Origin) : PromiseRegisterCallbackRes × Commands :=
  if req.awaited == req.awaiter ∨ !req.awaited.sameOrigin req.awaiter then
    ({ status := 400 }, {})
  else
    match org.get req.awaited now, org.get req.awaiter now with
    | none, _ =>
        ({ status := 404 }, {})
    | some _, none =>
        ({ status := 422 }, {})
    | some awaited, some awaiter =>
        if !awaiter.promise.type.isRunnable ∨ !awaited.promise.type.awaitable then
          ({ status := 422 }, {})
        else if awaited.promise.state == .pending ∧ awaiter.promise.state == .pending then
          ({ status := 200, promise := some (awaited.promise.toRecord awaited.id) },
           { add := [{ awaited with promise := awaited.promise.addCallback req.awaiter }] })
        else
          ({ status := 200, promise := some (awaited.promise.toRecord awaited.id) }, {})

def promiseRegisterListener (req : PromiseRegisterListenerReq) (now : Nat) (org : Origin) : PromiseRegisterListenerRes × Commands :=
  match org.get req.awaited now with
  | none =>
      ({ status := 404 }, {})
  | some awaited =>
      if !awaited.promise.type.awaitable then
        ({ status := 422 }, {})
      else if awaited.promise.state == .pending then
        ({ status := 200, promise := some (awaited.promise.toRecord awaited.id) },
         { add := [{ awaited with promise := awaited.promise.addListener req.address }] })
      else
        ({ status := 200, promise := some (awaited.promise.toRecord awaited.id) }, {})

def promiseSearch (_req : PromiseSearchReq) (_now : Nat) (_org : Origin) : PromiseSearchRes × Commands :=
  ({ status := 501 }, {})

def taskGet (req : TaskGetReq) (now : Nat) (org : Origin) : TaskGetRes × Commands :=
  match (org.get req.id now).bind fun o => o.task.map (o.id, ·) with
  | none =>
      ({ status := 404 }, {})
  | some (id, t) =>
      ({ status := 200, task := some (t.toRecord id) }, {})

def taskCreate (req : TaskCreateReq) (now : Nat) (org : Origin) : TaskCreateRes × Commands :=
  let a := req.action
  if !a.type.isRunnable then
    ({ status := 400 }, {})
  else
    match org.get a.id now with
    | none =>
        if a.timeoutAt > now then
          let p : PromiseObject :=
            { state := .pending, param := a.param, type := a.type,
              timeoutAt := a.timeoutAt, createdAt := now }
          let t : TaskObject :=
            { state := .acquired, version := 1, ttl := some req.ttl, pid := some req.pid,
              leaseTimeoutAt := some (now + req.ttl) }
          let o : Object := ⟨a.id, p, some t⟩
          ({ status := 200, task := some (t.toRecord a.id), promise := some (p.toRecord a.id) },
           { arm := o.timers, add := [o] })
        else
          let p : PromiseObject :=
            { state := .rejectedTimedout, param := a.param, type := a.type,
              timeoutAt := a.timeoutAt, createdAt := a.timeoutAt, settledAt := some a.timeoutAt }
          let t : TaskObject := { state := .fulfilled, version := 0 }
          ({ status := 200, task := some (t.toRecord a.id), promise := some (p.toRecord a.id) },
           { add := [⟨a.id, p, some t⟩] })
    | some o =>
        if !o.promise.type.isRunnable then
          ({ status := 422 }, {})
        else
          match o.task with
          | none =>
              ({ status := 409 }, {})
          | some t =>
              if t.state == .fulfilled then
                ({ status := 200, task := some (t.toRecord o.id),
                   promise := some (o.promise.toRecord o.id) }, {})
              else if t.state == .pending then
                let t' := { t with state := .acquired, version := t.version + 1,
                                   ttl := some req.ttl, pid := some req.pid,
                                   leaseTimeoutAt := some (now + req.ttl),
                                   retryTimeoutAt := none, resumes := [] }
                ({ status := 200, task := some (t'.toRecord o.id),
                   promise := some (o.promise.toRecord o.id) },
                 { arm := t'.timers o.id, add := [{ o with task := some t' }], del := t.timers o.id })
              else
                ({ status := 409 }, {})

def taskAcquire (req : TaskAcquireReq) (now : Nat) (org : Origin) : TaskAcquireRes × Commands :=
  match (org.get req.id now).bind fun o => o.task.map (o, ·) with
  | none =>
      ({ status := 404 }, {})
  | some (o, t) =>
      if t.state != .pending ∨ o.promise.state != .pending ∨ t.version != req.version then
        ({ status := 409 }, {})
      else
        let t' := { t with state := .acquired, version := t.version + 1,
                           ttl := some req.ttl, pid := some req.pid,
                           leaseTimeoutAt := some (now + req.ttl),
                           retryTimeoutAt := none, resumes := [] }
        ({ status := 200, task := some (t'.toRecord o.id), promise := some (o.promise.toRecord o.id) },
         { arm := t'.timers o.id, add := [{ o with task := some t' }], del := t.timers o.id })

def taskFence (req : TaskFenceReq) (now : Nat) (org : Origin) : TaskFenceRes × Commands :=
  if req.action.targetId == req.id ∨ !req.action.targetId.sameOrigin req.id then
    ({ status := 400 }, {})
  else
    match (org.get req.id now).bind fun o => o.task.map (o, ·) with
    | none =>
        ({ status := 404 }, {})
    | some (o, t) =>
        if t.state != .acquired ∨ o.promise.state != .pending ∨ t.version != req.version then
          ({ status := 409 }, {})
        else
          match req.action with
          | .create r =>
              let (res, c) := promiseCreate r now org
              ({ status := 200, action := some (.create res) }, c)
          | .settle r =>
              let (res, c) := promiseSettle r now org
              ({ status := 200, action := some (.settle res) }, c)

def taskHeartbeat (req : TaskHeartbeatReq) (now : Nat) (org : Origin) : TaskHeartbeatRes × Commands :=
  ({ status := 200 },
   req.tasks.foldl (init := {}) fun c ref =>
     match (org.get ref.id now).bind fun o => o.task.map (o, ·) with
     | none =>
         c
     | some (o, t) =>
         if t.state == .acquired ∧ t.version == ref.version
             ∧ t.pid == some req.pid ∧ o.promise.state == .pending then
           let lease := now + t.ttl.getD 0
           let t' := { t with leaseTimeoutAt := some lease }
           { c with
             arm := c.arm ++ (if t.leaseTimeoutAt == some lease then [] else t'.timers o.id),
             add := c.add ++ [{ o with task := some t' }],
             del := c.del ++ (if t.leaseTimeoutAt == some lease then [] else t.timers o.id) }
         else
           c)

def taskSuspend (req : TaskSuspendReq) (now : Nat) (org : Origin) : TaskSuspendRes × Commands :=
  let awaitedIds := req.actions.map (·.awaited)
  if req.actions.isEmpty ∨ awaitedIds.contains req.id
      ∨ awaitedIds.any (fun a => !a.sameOrigin req.id)
      ∨ awaitedIds.eraseDups.length != awaitedIds.length then
    ({ status := 400 }, {})
  else
    match (org.get req.id now).bind fun o => o.task.map (o, ·) with
    | none =>
        ({ status := 404 }, {})
    | some (o, t) =>
        if t.state != .acquired ∨ o.promise.state != .pending ∨ t.version != req.version then
          ({ status := 409 }, {})
        else
          let awaited := awaitedIds.map (org.get · now)
          if awaited.any (fun oa => !(oa.map (·.promise.type.awaitable)).getD false) then
            ({ status := 422 }, {})
          else if awaited.any (fun oa => (oa.map (·.promise.state != .pending)).getD false) then
            ({ status := 300 }, { add := [{ o with task := some { t with resumes := [] } }] })
          else
            let registered := awaited.foldl (init := []) fun adds oa =>
              match oa with
              | some oa =>
                  adds ++ [{ oa with promise := oa.promise.addCallback req.id }]
              | none =>
                  adds
            ({ status := 200 },
             { add := registered ++
                 [{ o with task := some { t with state := .suspended, pid := none, ttl := none,
                                                 leaseTimeoutAt := none, retryTimeoutAt := none,
                                                 resumes := [] } }],
               del := t.timers o.id })

def taskFulfill (req : TaskFulfillReq) (now : Nat) (org : Origin) : TaskFulfillRes × Commands :=
  if !req.action.state.settable then
    ({ status := 400 }, {})
  else
    match (org.get req.id now).bind fun o => o.task.map (o, ·) with
    | none =>
        ({ status := 404 }, {})
    | some (o, t) =>
        if t.state != .acquired ∨ o.promise.state != .pending ∨ t.version != req.version then
          ({ status := 409 }, {})
        else
          let p := { o.promise with state := req.action.state, value := req.action.value,
                                    settledAt := some now }
          ({ status := 200, promise := some (p.toRecord o.id) },
           { add := [{ o with promise := p,
                                 task := some (if t.state == .fulfilled then t else t.fulfill) }],
             del := o.timers })

def taskRelease (req : TaskReleaseReq) (now : Nat) (org : Origin) : TaskReleaseRes × Commands :=
  match (org.get req.id now).bind fun o => o.task.map (o, ·) with
  | none =>
      ({ status := 404 }, {})
  | some (o, t) =>
      if t.state != .acquired ∨ o.promise.state != .pending ∨ t.version != req.version then
        ({ status := 409 }, {})
      else
        let t' := { t with state := .pending, pid := none, ttl := none, leaseTimeoutAt := none,
                           retryTimeoutAt := some now }
        ({ status := 200 }, { arm := t'.timers o.id, add := [{ o with task := some t' }], del := t.timers o.id })

def taskHalt (req : TaskHaltReq) (now : Nat) (org : Origin) : TaskHaltRes × Commands :=
  match (org.get req.id now).bind fun o => o.task.map (o, ·) with
  | none =>
      ({ status := 404 }, {})
  | some (o, t) =>
      if t.state == .fulfilled then
        ({ status := 409 }, {})
      else if t.state == .halted then
        ({ status := 200 }, {})
      else
        ({ status := 200 },
         { add := [{ o with task := some { t with state := .halted, pid := none, ttl := none,
                                                     leaseTimeoutAt := none,
                                                     retryTimeoutAt := none } }],
           del := t.timers o.id })

def taskContinue (req : TaskContinueReq) (now : Nat) (org : Origin) : TaskContinueRes × Commands :=
  match (org.get req.id now).bind fun o => o.task.map (o, ·) with
  | none =>
      ({ status := 404 }, {})
  | some (o, t) =>
      if t.state != .halted ∨ o.promise.state != .pending then
        ({ status := 409 }, {})
      else
        let t' := { t with state := .pending, retryTimeoutAt := some now }
        ({ status := 200 }, { arm := t'.timers o.id, add := [{ o with task := some t' }] })

def taskSearch (_req : TaskSearchReq) (_now : Nat) (_org : Origin) : TaskSearchRes × Commands :=
  ({ status := 501 }, {})

def scheduleGet (_req : ScheduleGetReq) (_now : Nat) (_org : Origin) : ScheduleGetRes × Commands :=
  ({ status := 501 }, {})

def scheduleCreate (_req : ScheduleCreateReq) (_now : Nat) (_org : Origin) : ScheduleCreateRes × Commands :=
  ({ status := 501 }, {})

def scheduleDelete (_req : ScheduleDeleteReq) (_now : Nat) (_org : Origin) : ScheduleDeleteRes × Commands :=
  ({ status := 501 }, {})

def scheduleSearch (_req : ScheduleSearchReq) (_now : Nat) (_org : Origin) : ScheduleSearchRes × Commands :=
  ({ status := 501 }, {})

end Concrete
