import refinement.lookup

namespace Refinement

open Protocol (Ident Message OutboxEntry Object PromiseObject TaskObject PromiseState TaskState)
open Concrete (Origin Commands)

structure Sim (o : String) (org : Origin) (S : Abstract.State) {α : Type}
    (r : α × List Abstract.Effect) (res : α) (c : Commands) : Prop where
  res   : r.1 = res
  fx    : Fx o r.2
  loc   : Local o c.org (Abstract.applyAll S r.2)
  send  : sendsOf r.2 = c.send
  orig  : (∀ ob ∈ org.current.objects, ob.id.origin = o) → ∀ ob ∈ c.org.current.objects, ob.id.origin = o

theorem find_set_at {org : Origin} {x : Object} {id : Ident} (hx : x.id = id) :
    Origin.find (org.set x) id = some x := by
  rw [← hx]; exact find_set_same org x

theorem Sim.skip {o : String} {org : Origin} {S : Abstract.State} {α : Type} (hL : Local o org S)
    (a : α) : Sim o org S (a, []) a { org } :=
  ⟨rfl, trivial, hL, rfl, fun h => h⟩

theorem Local_setPromise {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    {id : Ident} (hid : id.origin = o) {p : PromiseObject} {x : Object} (hx : x.id = id)
    (h : Abstract.Object.withPromise id p (Origin.find org id) = x) :
    Local o (org.set x) (Abstract.applyAll S [.setPromise id p]) := by
  intro id' hid'
  simp only [Abstract.applyAll]
  by_cases e : id' = id
  · subst e
    rw [find_setPromise_same, hL _ hid', h, find_set_at hx]
  · rw [find_setPromise_other _ _ _ _ e, find_set_other _ _ _ (hx ▸ e), hL _ hid']

theorem Local_setPromise_setTask {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    {id : Ident} (hid : id.origin = o) {p : PromiseObject} {t : TaskObject} {x : Object} (hx : x.id = id)
    (h : { Abstract.Object.withPromise id p (Origin.find org id) with task := some t } = x) :
    Local o (org.set x) (Abstract.applyAll S [.setPromise id p, .setTask id t]) := by
  intro id' hid'
  simp only [Abstract.applyAll]
  by_cases e : id' = id
  · subst e
    rw [find_setTask, if_pos rfl, find_setPromise_same, hL _ hid', find_set_at hx, Option.map_some]
    rw [← h]
  · rw [find_setTask, if_neg e, find_setPromise_other _ _ _ _ e, find_set_other _ _ _ (hx ▸ e),
        hL _ hid']

theorem Local_setTask {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    {id : Ident} (hid : id.origin = o) {t : TaskObject} {x : Object} (hx : x.id = id)
    (h : (Origin.find org id).map (fun ob => { ob with task := some t }) = some x) :
    Local o (org.set x) (Abstract.applyAll S [.setTask id t]) := by
  intro id' hid'
  simp only [Abstract.applyAll]
  by_cases e : id' = id
  · subst e
    rw [find_setTask, if_pos rfl, hL _ hid', h, find_set_at hx]
  · rw [find_setTask, if_neg e, find_set_other _ _ _ (hx ▸ e), hL _ hid']

theorem orig_set {o : String} {org : Origin} {x : Object} (hx : x.id.origin = o) :
    (∀ ob ∈ org.current.objects, ob.id.origin = o) → ∀ ob ∈ (org.set x).current.objects, ob.id.origin = o :=
  fun h => set_derived h hx

theorem find_orig {org : Origin} {id : Ident} {ob : Object}
    (h : Origin.find org id = some ob) : ob.id = id := (find_mem h).2

theorem get_some {org : Origin} {id : Ident} {now : Nat} {x : Object}
    (h : org.get id now = some x) : ∃ ob, Origin.find org id = some ob ∧ x = ob.project now := by
  rw [get_eq] at h
  cases hf : Origin.find org id with
  | none => rw [hf] at h; cases h
  | some ob => rw [hf] at h; exact ⟨ob, rfl, (Option.some.inj h).symm⟩

open Protocol (PromiseGetReq PromiseCreateReq PromiseSettleReq PromiseRegisterCallbackReq
               PromiseRegisterListenerReq PromiseSearchReq)

theorem promiseGet_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : PromiseGetReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.promiseGet req now (env S))
      (Concrete.promiseGet req now org).1 (Concrete.promiseGet req now org).2 := by
  unfold Abstract.promiseGet Concrete.promiseGet
  simp only [bind_apply, readObject_false, get_eq, hL req.id hid]
  cases Origin.find org req.id with
  | none => exact Sim.skip hL _
  | some ob => exact Sim.skip hL _

theorem promiseCreate_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : PromiseCreateReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.promiseCreate req now (env S))
      (Concrete.promiseCreate req now org).1 (Concrete.promiseCreate req now org).2 := by
  unfold Abstract.promiseCreate Concrete.promiseCreate
  simp only [bind_apply, readObject_false, get_eq, hL req.id hid]
  cases hf : Origin.find org req.id with
  | some ob => exact Sim.skip hL _
  | none =>
      cases hdel : req.delay <;>
      simp only [Option.map_none, Abstract.createPromise, bind_apply, pure_apply, hdel] <;>
      by_cases h1 : req.timeoutAt > now <;>
      by_cases h2 : req.type.isRunnable = true <;>
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] <;>
      first
        | exact ⟨rfl, ⟨hid, hid, trivial⟩,
            Local_setPromise_setTask hL hid rfl (by simp [hf, Abstract.Object.withPromise]),
            rfl, orig_set hid⟩
        | exact ⟨rfl, ⟨hid, trivial⟩,
            Local_setPromise hL hid rfl (by simp [hf, Abstract.Object.withPromise]),
            rfl, orig_set hid⟩

theorem settable_ne_pending {st : PromiseState} (h : st.settable = true) : (st != .pending) = true := by
  cases st <;> simp_all [Protocol.PromiseState.settable]

theorem project_pending_eq {ob : Object} {now : Nat}
    (h : ((ob.project now).promise.state == PromiseState.pending) = true) : ob.project now = ob :=
  project_pending_id ob now (by simpa using h)

theorem promiseSettle_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : PromiseSettleReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.promiseSettle req now (env S))
      (Concrete.promiseSettle req now org).1 (Concrete.promiseSettle req now org).2 := by
  unfold Abstract.promiseSettle Concrete.promiseSettle
  by_cases hs : req.state.settable = true
  · have hs' : (!req.state.settable) = false := by simp [hs]
    simp only [hs', Bool.false_eq_true, ↓reduceIte, bind_apply, readObject_false, get_eq, hL req.id hid]
    cases hf : Origin.find org req.id with
    | none => exact Sim.skip hL _
    | some ob =>
        simp only [Option.map_some]
        by_cases hp : ((ob.project now).promise.state == PromiseState.pending) = true
        · have heq := project_pending_eq hp
          rw [heq] at hp ⊢
          simp only [hp, ↓reduceIte, Abstract.setSettled, bind_apply, setPromise_apply,
            settable_ne_pending hs, pure_apply]
          have hob := find_orig hf
          have hido : ob.id.origin = o := hob ▸ hid
          cases ht : ob.task with
          | none =>
              refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_set hido⟩
              exact Local_setPromise hL hido rfl (by rw [hob, hf]; simp [Abstract.Object.withPromise, ht, hob])
          | some t =>
              by_cases hft : (t.state != TaskState.fulfilled) = true
              · have hft' : t.state ≠ TaskState.fulfilled := by simpa using hft
                simp only [hft, ↓reduceIte, setTask_apply]
                refine ⟨rfl, ⟨hido, hido, trivial⟩, ?_, rfl, orig_set hido⟩
                exact Local_setPromise_setTask hL hido rfl
                  (by rw [hob, hf]; simp [Abstract.Object.withPromise, hob, hft'])
              · have hft' : t.state = TaskState.fulfilled := by simpa using hft
                simp only [hft, Bool.false_eq_true, ↓reduceIte, pure_apply]
                refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_set hido⟩
                exact Local_setPromise hL hido rfl
                  (by rw [hob, hf]; simp [Abstract.Object.withPromise, ht, hob, hft'])
        · have hp' : ((ob.project now).promise.state == PromiseState.pending) = false := by simpa using hp
          simp only [hp', Bool.false_eq_true, ↓reduceIte, pure_apply]
          exact Sim.skip hL _
  · have hs' : (!req.state.settable) = true := by simpa using hs
    simp only [hs', ↓reduceIte, pure_apply]
    exact Sim.skip hL _

theorem sameOrigin_eq {a b : Ident} (h : a.sameOrigin b = true) : b.origin = a.origin := by
  simp [Protocol.Ident.sameOrigin] at h; exact h.symm

theorem promiseRegisterCallback_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : PromiseRegisterCallbackReq) (hid : req.awaited.origin = o) :
    Sim o org S (Abstract.promiseRegisterCallback req now (env S))
      (Concrete.promiseRegisterCallback req now org).1 (Concrete.promiseRegisterCallback req now org).2 := by
  unfold Abstract.promiseRegisterCallback Concrete.promiseRegisterCallback
  by_cases h1 : (req.awaited == req.awaiter) = true
  · simp only [h1, true_or, ↓reduceIte, pure_apply]
    exact Sim.skip hL _
  · by_cases h2 : req.awaited.sameOrigin req.awaiter = true
    · have h2' : (!req.awaited.sameOrigin req.awaiter) = false := by simp [h2]
      have hid2 : req.awaiter.origin = o := (sameOrigin_eq h2).trans hid
      simp only [h1, h2', Bool.false_eq_true, or_self, ↓reduceIte, bind_apply, pure_apply,
        readObject_false, get_eq, hL req.awaited hid]
      cases hf : Origin.find org req.awaited with
      | none => exact Sim.skip hL _
      | some awaited =>
          simp only [Option.map_some, bind_apply, readObject_false, hL req.awaiter hid2]
          cases hg : Origin.find org req.awaiter with
          | none => exact Sim.skip hL _
          | some awaiter =>
              simp only [Option.map_some]
              by_cases h3 : (!(awaiter.project now).promise.type.isRunnable) = true
              · simp only [h3, true_or, ↓reduceIte, pure_apply]
                exact Sim.skip hL _
              · have h3' : (!(awaiter.project now).promise.type.isRunnable) = false := by simpa using h3
                by_cases h4 : (!(awaited.project now).promise.type.awaitable) = true
                · simp only [h3', h4, Bool.false_eq_true, false_or, ↓reduceIte, bind_apply, pure_apply]
                  exact Sim.skip hL _
                · have h4' : (!(awaited.project now).promise.type.awaitable) = false := by simpa using h4
                  simp only [h3', h4', Bool.false_eq_true, or_self, ↓reduceIte, bind_apply, pure_apply]
                  by_cases h5 : ((awaited.project now).promise.state == PromiseState.pending) = true
                  · have heq := project_pending_eq h5
                    rw [heq] at h5 ⊢
                    have hob := find_orig hf
                    have hido : awaited.id.origin = o := hob ▸ hid
                    by_cases h6 : ((awaiter.project now).promise.state == PromiseState.pending) = true
                    · simp only [h5, h6, and_self, ↓reduceIte, bind_apply, setPromise_apply, pure_apply]
                      refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_set hido⟩
                      exact Local_setPromise hL hido rfl
                        (by rw [hob, hf]; simp [Abstract.Object.withPromise, hob])
                    · simp only [h5, h6, and_false, Bool.false_eq_true, ↓reduceIte, bind_apply, pure_apply]
                      exact Sim.skip hL _
                  · have h5' : ((awaited.project now).promise.state == PromiseState.pending) = false := by
                      simpa using h5
                    simp only [h5', Bool.false_eq_true, false_and, ↓reduceIte, pure_apply]
                    exact Sim.skip hL _
    · have h2' : (!req.awaited.sameOrigin req.awaiter) = true := by simpa using h2
      simp only [h1, h2', or_true, Bool.false_eq_true, ↓reduceIte]
      exact Sim.skip hL _

theorem promiseRegisterListener_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : PromiseRegisterListenerReq) (hid : req.awaited.origin = o) :
    Sim o org S (Abstract.promiseRegisterListener req now (env S))
      (Concrete.promiseRegisterListener req now org).1 (Concrete.promiseRegisterListener req now org).2 := by
  unfold Abstract.promiseRegisterListener Concrete.promiseRegisterListener
  simp only [bind_apply, readObject_false, get_eq, hL req.awaited hid]
  cases hf : Origin.find org req.awaited with
  | none => exact Sim.skip hL _
  | some awaited =>
      simp only [Option.map_some]
      by_cases h4 : (!(awaited.project now).promise.type.awaitable) = true
      · simp only [h4, ↓reduceIte, pure_apply]
        exact Sim.skip hL _
      · have h4' : (!(awaited.project now).promise.type.awaitable) = false := by simpa using h4
        simp only [h4', Bool.false_eq_true, ↓reduceIte, bind_apply, pure_apply]
        by_cases h5 : ((awaited.project now).promise.state == PromiseState.pending) = true
        · have heq := project_pending_eq h5
          rw [heq] at h5 ⊢
          have hob := find_orig hf
          have hido : awaited.id.origin = o := hob ▸ hid
          simp only [h5, ↓reduceIte]
          refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_set hido⟩
          exact Local_setPromise hL hido rfl (by rw [hob, hf]; simp [Abstract.Object.withPromise, hob])
        · have h5' : ((awaited.project now).promise.state == PromiseState.pending) = false := by simpa using h5
          simp only [h5', Bool.false_eq_true, ↓reduceIte, pure_apply]
          exact Sim.skip hL _

theorem project_task (ob : Object) (now : Nat) :
    (ob.project now).task = ob.task.map (·.view (ob.promise.project now)) := rfl

theorem project_promise (ob : Object) (now : Nat) :
    (ob.project now).promise = ob.promise.project now := rfl

theorem view_not_fulfilled {t : TaskObject} {p : PromiseObject} (h : (t.view p).state ≠ .fulfilled) :
    p.state = .pending := by
  unfold TaskObject.view at h
  by_cases hp : p.state = .pending
  · exact hp
  · exfalso
    have hp' : (p.state != PromiseState.pending) = true := by simpa using hp
    by_cases ht : t.state = .fulfilled
    · simp [hp', ht] at h
    · have ht' : (t.state != TaskState.fulfilled) = true := by simpa using ht
      simp [hp', ht', TaskObject.fulfill] at h

theorem project_pending_of_task {ob : Object} {now : Nat} {tv : TaskObject}
    (htv : (ob.project now).task = some tv) (h : tv.state ≠ .fulfilled) : ob.project now = ob := by
  rw [project_task] at htv
  cases ht : ob.task with
  | none => rw [ht] at htv; cases htv
  | some t =>
      rw [ht, Option.map_some, Option.some.injEq] at htv
      subst htv
      exact project_pending_id ob now (view_not_fulfilled h)

theorem project_pending_ne {ob : Object} {now : Nat}
    (h : ((ob.project now).promise.state != PromiseState.pending) = false) : ob.project now = ob :=
  project_pending_id ob now (by simpa using h)

open Protocol (TaskGetReq TaskCreateReq TaskAcquireReq TaskFenceReq TaskHeartbeatReq TaskSuspendReq
               TaskFulfillReq TaskReleaseReq TaskHaltReq TaskContinueReq TaskSearchReq)

theorem taskGet_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : TaskGetReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.taskGet req now (env S))
      (Concrete.taskGet req now org).1 (Concrete.taskGet req now org).2 := by
  unfold Abstract.taskGet Concrete.taskGet
  simp only [bind_apply, readTaskObject_false, get_eq, hL req.id hid]
  cases hf : Origin.find org req.id with
  | none => exact Sim.skip hL _
  | some ob =>
      cases ht : ob.task with
      | none =>
          simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
            Option.map_some, project_task, Option.map_none]
          exact Sim.skip hL _
      | some t =>
          simp only [ht, Option.isSome_some, ↓reduceIte, Option.bind_some, Option.map_some, project_task]
          exact Sim.skip hL _

theorem taskAcquire_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : TaskAcquireReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.taskAcquire req now (env S))
      (Concrete.taskAcquire req now org).1 (Concrete.taskAcquire req now org).2 := by
  unfold Abstract.taskAcquire Concrete.taskAcquire
  simp only [bind_apply, readTaskObject_false, get_eq, hL req.id hid]
  cases hf : Origin.find org req.id with
  | none => exact Sim.skip hL _
  | some ob =>
      cases ht : ob.task with
      | none =>
          simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
            Option.map_some, project_task, Option.map_none]
          exact Sim.skip hL _
      | some t =>
          obtain ⟨tv, htv⟩ : ∃ tv, (ob.project now).task = some tv :=
            ⟨t.view (ob.promise.project now), by rw [project_task, ht]; rfl⟩
          simp only [ht, Option.isSome_some, ↓reduceIte, Option.bind_some, Option.map_some, htv]
          by_cases c1 : (tv.state != TaskState.pending) = true
          · simp only [c1, true_or, ↓reduceIte, pure_apply]
            exact Sim.skip hL _
          · have c1' : (tv.state != TaskState.pending) = false := by simpa using c1
            by_cases c2 : ((ob.project now).promise.state != PromiseState.pending) = true
            · simp only [c1', c2, Bool.false_eq_true, false_or, true_or, ↓reduceIte]
              exact Sim.skip hL _
            · have c2' : ((ob.project now).promise.state != PromiseState.pending) = false := by simpa using c2
              by_cases c3 : (tv.version != req.version) = true
              · simp only [c1', c2', c3, Bool.false_eq_true, or_true, ↓reduceIte]
                exact Sim.skip hL _
              · have c3' : (tv.version != req.version) = false := by simpa using c3
                simp only [c1', c2', c3', Bool.false_eq_true, or_self, ↓reduceIte, bind_apply,
                  setTask_apply, pure_apply]
                have heq := project_pending_ne c2'
                rw [heq] at htv ⊢
                have hob := find_orig hf
                have hido : ob.id.origin = o := hob ▸ hid
                refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_set hido⟩
                exact Local_setTask hL hido rfl (by rw [hob, hf]; simp [hob])

theorem taskRelease_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : TaskReleaseReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.taskRelease req now (env S))
      (Concrete.taskRelease req now org).1 (Concrete.taskRelease req now org).2 := by
  unfold Abstract.taskRelease Concrete.taskRelease
  simp only [bind_apply, readTaskObject_false, get_eq, hL req.id hid]
  cases hf : Origin.find org req.id with
  | none => exact Sim.skip hL _
  | some ob =>
      cases ht : ob.task with
      | none =>
          simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
            Option.map_some, project_task, Option.map_none]
          exact Sim.skip hL _
      | some t =>
          obtain ⟨tv, htv⟩ : ∃ tv, (ob.project now).task = some tv :=
            ⟨t.view (ob.promise.project now), by rw [project_task, ht]; rfl⟩
          simp only [ht, Option.isSome_some, ↓reduceIte, Option.bind_some, Option.map_some, htv]
          by_cases c1 : (tv.state != TaskState.acquired) = true
          · simp only [c1, true_or, ↓reduceIte, pure_apply]
            exact Sim.skip hL _
          · have c1' : (tv.state != TaskState.acquired) = false := by simpa using c1
            by_cases c2 : ((ob.project now).promise.state != PromiseState.pending) = true
            · simp only [c1', c2, Bool.false_eq_true, false_or, true_or, ↓reduceIte]
              exact Sim.skip hL _
            · have c2' : ((ob.project now).promise.state != PromiseState.pending) = false := by simpa using c2
              by_cases c3 : (tv.version != req.version) = true
              · simp only [c1', c2', c3, Bool.false_eq_true, or_true, ↓reduceIte]
                exact Sim.skip hL _
              · have c3' : (tv.version != req.version) = false := by simpa using c3
                simp only [c1', c2', c3', Bool.false_eq_true, or_self, ↓reduceIte, bind_apply,
                  setTask_apply, pure_apply]
                have heq := project_pending_ne c2'
                rw [heq] at htv ⊢
                have hob := find_orig hf
                have hido : ob.id.origin = o := hob ▸ hid
                refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_set hido⟩
                exact Local_setTask hL hido rfl (by rw [hob, hf]; simp [hob])

theorem taskContinue_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : TaskContinueReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.taskContinue req now (env S))
      (Concrete.taskContinue req now org).1 (Concrete.taskContinue req now org).2 := by
  unfold Abstract.taskContinue Concrete.taskContinue
  simp only [bind_apply, readTaskObject_false, get_eq, hL req.id hid]
  cases hf : Origin.find org req.id with
  | none => exact Sim.skip hL _
  | some ob =>
      cases ht : ob.task with
      | none =>
          simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
            Option.map_some, project_task, Option.map_none]
          exact Sim.skip hL _
      | some t =>
          obtain ⟨tv, htv⟩ : ∃ tv, (ob.project now).task = some tv :=
            ⟨t.view (ob.promise.project now), by rw [project_task, ht]; rfl⟩
          simp only [ht, Option.isSome_some, ↓reduceIte, Option.bind_some, Option.map_some, htv]
          by_cases c1 : (tv.state != TaskState.halted) = true
          · simp only [c1, true_or, ↓reduceIte, pure_apply]
            exact Sim.skip hL _
          · have c1' : (tv.state != TaskState.halted) = false := by simpa using c1
            by_cases c2 : ((ob.project now).promise.state != PromiseState.pending) = true
            · simp only [c1', c2, Bool.false_eq_true, false_or, ↓reduceIte]
              exact Sim.skip hL _
            · have c2' : ((ob.project now).promise.state != PromiseState.pending) = false := by simpa using c2
              simp only [c1', c2', Bool.false_eq_true, or_self, ↓reduceIte, bind_apply,
                setTask_apply, pure_apply]
              have heq := project_pending_ne c2'
              rw [heq] at htv ⊢
              have hob := find_orig hf
              have hido : ob.id.origin = o := hob ▸ hid
              refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_set hido⟩
              exact Local_setTask hL hido rfl (by rw [hob, hf]; simp [hob])

theorem taskHalt_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : TaskHaltReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.taskHalt req now (env S))
      (Concrete.taskHalt req now org).1 (Concrete.taskHalt req now org).2 := by
  unfold Abstract.taskHalt Concrete.taskHalt
  simp only [bind_apply, readTaskObject_false, get_eq, hL req.id hid]
  cases hf : Origin.find org req.id with
  | none => exact Sim.skip hL _
  | some ob =>
      cases ht : ob.task with
      | none =>
          simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
            Option.map_some, project_task, Option.map_none]
          exact Sim.skip hL _
      | some t =>
          obtain ⟨tv, htv⟩ : ∃ tv, (ob.project now).task = some tv :=
            ⟨t.view (ob.promise.project now), by rw [project_task, ht]; rfl⟩
          simp only [ht, Option.isSome_some, ↓reduceIte, Option.bind_some, Option.map_some, htv]
          by_cases c1 : (tv.state == TaskState.fulfilled) = true
          · simp only [c1, ↓reduceIte, pure_apply]
            exact Sim.skip hL _
          · have c1' : (tv.state == TaskState.fulfilled) = false := by simpa using c1
            by_cases c2 : (tv.state == TaskState.halted) = true
            · simp only [c1', c2, Bool.false_eq_true, ↓reduceIte]
              exact Sim.skip hL _
            · have c2' : (tv.state == TaskState.halted) = false := by simpa using c2
              simp only [c1', c2', Bool.false_eq_true, ↓reduceIte, bind_apply, setTask_apply, pure_apply]
              have heq := project_pending_of_task htv (by simpa using c1')
              rw [heq] at htv ⊢
              have hob := find_orig hf
              have hido : ob.id.origin = o := hob ▸ hid
              refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_set hido⟩
              exact Local_setTask hL hido rfl (by rw [hob, hf]; simp [hob])

theorem taskFulfill_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : TaskFulfillReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.taskFulfill req now (env S))
      (Concrete.taskFulfill req now org).1 (Concrete.taskFulfill req now org).2 := by
  unfold Abstract.taskFulfill Concrete.taskFulfill
  by_cases hs : req.action.state.settable = true
  · have hs' : (!req.action.state.settable) = false := by simp [hs]
    simp only [hs', Bool.false_eq_true, ↓reduceIte, bind_apply, readTaskObject_false, get_eq, hL req.id hid]
    cases hf : Origin.find org req.id with
    | none => exact Sim.skip hL _
    | some ob =>
        cases ht : ob.task with
        | none =>
            simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
              Option.map_some, project_task, Option.map_none]
            exact Sim.skip hL _
        | some t =>
            obtain ⟨tv, htv⟩ : ∃ tv, (ob.project now).task = some tv :=
              ⟨t.view (ob.promise.project now), by rw [project_task, ht]; rfl⟩
            simp only [ht, Option.isSome_some, ↓reduceIte, Option.bind_some, Option.map_some, htv,
              pure_apply]
            by_cases c1 : (tv.state != TaskState.acquired) = true
            · simp only [c1, true_or, ↓reduceIte, pure_apply]
              exact Sim.skip hL _
            · have c1' : (tv.state != TaskState.acquired) = false := by simpa using c1
              by_cases c2 : ((ob.project now).promise.state != PromiseState.pending) = true
              · simp only [c1', c2, Bool.false_eq_true, false_or, true_or, ↓reduceIte]
                exact Sim.skip hL _
              · have c2' : ((ob.project now).promise.state != PromiseState.pending) = false := by
                  simpa using c2
                by_cases c3 : (tv.version != req.version) = true
                · simp only [c1', c2', c3, Bool.false_eq_true, or_true, ↓reduceIte]
                  exact Sim.skip hL _
                · have c3' : (tv.version != req.version) = false := by simpa using c3
                  have heq := project_pending_ne c2'
                  rw [heq] at htv c2' ⊢
                  have hacq : tv.state = TaskState.acquired := by simpa using c1'
                  have hnf : (tv.state != TaskState.fulfilled) = true := by simp [hacq]
                  have hnf' : (tv.state == TaskState.fulfilled) = false := by simp [hacq]
                  simp only [c1', c2', c3', Bool.false_eq_true, or_self, ↓reduceIte, bind_apply,
                    Abstract.setSettled, setPromise_apply, settable_ne_pending hs, htv, hnf, hnf',
                    setTask_apply, pure_apply]
                  have hob := find_orig hf
                  have hido : ob.id.origin = o := hob ▸ hid
                  refine ⟨rfl, ⟨hido, hido, trivial⟩, ?_, rfl, orig_set hido⟩
                  exact Local_setPromise_setTask hL hido rfl
                    (by rw [hob, hf]; simp [Abstract.Object.withPromise, hob])
  · have hs' : (!req.action.state.settable) = true := by simpa using hs
    simp only [hs', ↓reduceIte, pure_apply]
    exact Sim.skip hL _

theorem taskCreate_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : TaskCreateReq) (hid : req.action.id.origin = o) :
    Sim o org S (Abstract.taskCreate req now (env S))
      (Concrete.taskCreate req now org).1 (Concrete.taskCreate req now org).2 := by
  unfold Abstract.taskCreate Concrete.taskCreate
  by_cases hr : req.action.type.isRunnable = true
  · have hr' : (!req.action.type.isRunnable) = false := by simp [hr]
    simp only [hr', Bool.false_eq_true, ↓reduceIte, bind_apply, readObject_false, get_eq,
      hL req.action.id hid]
    cases hf : Origin.find org req.action.id with
    | none =>
        simp only [Option.map_none, pure_apply]
        by_cases h1 : req.action.timeoutAt > now <;>
        simp only [h1, ↓reduceIte] <;>
        exact ⟨rfl, ⟨hid, hid, trivial⟩,
          Local_setPromise_setTask hL hid rfl (by simp [hf, Abstract.Object.withPromise]),
          rfl, orig_set hid⟩
    | some ob =>
        simp only [Option.map_some, pure_apply]
        by_cases h2 : (!(ob.project now).promise.type.isRunnable) = true
        · simp only [h2, ↓reduceIte, pure_apply]
          exact Sim.skip hL _
        · have h2' : (!(ob.project now).promise.type.isRunnable) = false := by simpa using h2
          simp only [h2', Bool.false_eq_true, ↓reduceIte, bind_apply, pure_apply]
          cases ht : ob.task with
          | none =>
              simp only [project_task, ht, Option.map_none]
              exact Sim.skip hL _
          | some t =>
              obtain ⟨tv, htv⟩ : ∃ tv, (ob.project now).task = some tv :=
                ⟨t.view (ob.promise.project now), by rw [project_task, ht]; rfl⟩
              simp only [htv]
              by_cases c1 : (tv.state == TaskState.fulfilled) = true
              · simp only [c1, ↓reduceIte, pure_apply]
                exact Sim.skip hL _
              · have c1' : (tv.state == TaskState.fulfilled) = false := by simpa using c1
                by_cases c2 : (tv.state == TaskState.pending) = true
                · simp only [c1', c2, Bool.false_eq_true, ↓reduceIte, bind_apply, setTask_apply, pure_apply]
                  have heq := project_pending_of_task htv (by simpa using c1')
                  rw [heq] at htv ⊢
                  have hob := find_orig hf
                  have hido : ob.id.origin = o := hob ▸ hid
                  refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_set hido⟩
                  exact Local_setTask hL hido rfl (by rw [hob, hf]; simp [hob])
                · have c2' : (tv.state == TaskState.pending) = false := by simpa using c2
                  simp only [c1', c2', Bool.false_eq_true, ↓reduceIte, pure_apply]
                  exact Sim.skip hL _
  · have hr' : (!req.action.type.isRunnable) = true := by simpa using hr
    simp only [hr', ↓reduceIte, pure_apply]
    exact Sim.skip hL _

theorem Sim.map {o : String} {org : Origin} {S : Abstract.State} {α β : Type}
    {r : α × List Abstract.Effect} {res : α} {c : Commands} (f : α → β) (h : Sim o org S r res c) :
    Sim o org S (f r.1, r.2 ++ []) (f res) c :=
  ⟨by rw [h.res], by rw [List.append_nil]; exact h.fx, by rw [List.append_nil]; exact h.loc,
   by rw [List.append_nil]; exact h.send, h.orig⟩

theorem taskFence_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : TaskFenceReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.taskFence req now (env S))
      (Concrete.taskFence req now org).1 (Concrete.taskFence req now org).2 := by
  unfold Abstract.taskFence Concrete.taskFence
  by_cases h1 : (req.action.targetId == req.id) = true
  · simp only [h1, true_or, ↓reduceIte, pure_apply]
    exact Sim.skip hL _
  · by_cases h2 : req.action.targetId.sameOrigin req.id = true
    · have h2' : (!req.action.targetId.sameOrigin req.id) = false := by simp [h2]
      have hidt : req.action.targetId.origin = o := by
        have := sameOrigin_eq h2; rw [← hid, this]
      simp only [h1, h2', Bool.false_eq_true, or_self, ↓reduceIte, bind_apply, pure_apply,
        readTaskObject_false, get_eq, hL req.id hid]
      cases hf : Origin.find org req.id with
      | none => exact Sim.skip hL _
      | some ob =>
          cases ht : ob.task with
          | none =>
              simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
                Option.map_some, project_task, Option.map_none]
              exact Sim.skip hL _
          | some t =>
              obtain ⟨tv, htv⟩ : ∃ tv, (ob.project now).task = some tv :=
                ⟨t.view (ob.promise.project now), by rw [project_task, ht]; rfl⟩
              simp only [ht, Option.isSome_some, ↓reduceIte, Option.bind_some, Option.map_some, htv]
              by_cases c1 : (tv.state != TaskState.acquired) = true
              · simp only [c1, true_or, ↓reduceIte, pure_apply]
                exact Sim.skip hL _
              · have c1' : (tv.state != TaskState.acquired) = false := by simpa using c1
                by_cases c2 : ((ob.project now).promise.state != PromiseState.pending) = true
                · simp only [c1', c2, Bool.false_eq_true, false_or, true_or, ↓reduceIte]
                  exact Sim.skip hL _
                · have c2' : ((ob.project now).promise.state != PromiseState.pending) = false := by
                    simpa using c2
                  by_cases c3 : (tv.version != req.version) = true
                  · simp only [c1', c2', c3, Bool.false_eq_true, or_true, ↓reduceIte]
                    exact Sim.skip hL _
                  · have c3' : (tv.version != req.version) = false := by simpa using c3
                    simp only [c1', c2', c3', Bool.false_eq_true, or_self, ↓reduceIte, bind_apply, pure_apply]
                    cases ha : req.action with
                    | create r =>
                        have hr : r.id.origin = o := by
                          simpa [Protocol.TaskFenceAction.targetId, ha] using hidt
                        simp only
                        rcases hC : Concrete.promiseCreate r now org with ⟨res, c⟩
                        have h := promiseCreate_sim hL now r hr
                        rw [hC] at h
                        exact Sim.map (fun res => ({ status := 200, action := some (.create res) } :
                          Protocol.TaskFenceRes)) h
                    | settle r =>
                        have hr : r.id.origin = o := by
                          simpa [Protocol.TaskFenceAction.targetId, ha] using hidt
                        simp only
                        rcases hC : Concrete.promiseSettle r now org with ⟨res, c⟩
                        have h := promiseSettle_sim hL now r hr
                        rw [hC] at h
                        exact Sim.map (fun res => ({ status := 200, action := some (.settle res) } :
                          Protocol.TaskFenceRes)) h
    · have h2' : (!req.action.targetId.sameOrigin req.id) = true := by simpa using h2
      simp only [h1, h2', or_true, Bool.false_eq_true, ↓reduceIte]
      exact Sim.skip hL _

theorem Local_setTask_from {o : String} {d : Origin} {T : Abstract.State} (hL : Local o d T)
    {id : Ident} (hid : id.origin = o) {t : TaskObject} {x y : Object} (hx : x.id = id)
    (hy : Origin.find d id = some y) (hxy : x = { y with task := some t }) :
    Local o (d.set x) (Abstract.applyAll T [.setTask id t]) := by
  intro id' hid'
  simp only [Abstract.applyAll]
  by_cases e : id' = id
  · subst e
    rw [find_setTask, if_pos rfl, hL _ hid', hy, Option.map_some, find_set_at hx, hxy]
  · rw [find_setTask, if_neg e, find_set_other _ _ _ (hx ▸ e), hL _ hid']

theorem Local_setPromise_from {o : String} {d : Origin} {T : Abstract.State} (hL : Local o d T)
    {id : Ident} (hid : id.origin = o) {p : PromiseObject} {x y : Object} (hx : x.id = id)
    (hy : Origin.find d id = some y) (hxy : x = { y with promise := p }) :
    Local o (d.set x) (Abstract.applyAll T [.setPromise id p]) := by
  intro id' hid'
  simp only [Abstract.applyAll]
  by_cases e : id' = id
  · subst e
    rw [find_setPromise_same, hL _ hid', hy, find_set_at hx, hxy]
    rfl
  · rw [find_setPromise_other _ _ _ _ e, find_set_other _ _ _ (hx ▸ e), hL _ hid']

open Protocol (TaskRef)

def hbStep (now : Nat) (org : Origin) (pid : String) (c : Commands) (ref : TaskRef) : Commands :=
  match (org.get ref.id now).bind fun o => o.task.map (o, ·) with
  | none =>
      c
  | some (o, t) =>
      if t.state == .acquired ∧ t.version == ref.version
          ∧ t.pid == some pid ∧ o.promise.state == .pending then
        let lease := now + t.ttl.getD 0
        let t' := { t with leaseTimeoutAt := some lease }
        { c with
          arm := c.arm ++ (if t.leaseTimeoutAt == some lease then [] else t'.timers o.id),
          org := c.org.set { o with task := some t' },
          del := c.del ++ (if t.leaseTimeoutAt == some lease then [] else t.timers o.id) }
      else
        c

theorem taskHeartbeat_eq (now : Nat) (org : Origin) (req : TaskHeartbeatReq) :
    Concrete.taskHeartbeat req now org =
      ({ status := 200 }, req.tasks.foldl (hbStep now org req.pid) { org }) := rfl

structure Acc (o : String) (org : Origin) (d : Origin) (T : Abstract.State) : Prop where
  loc   : Local o d T
  prom  : ∀ id, (Origin.find d id).map (·.promise) = (Origin.find org id).map (·.promise)
  orig  : (∀ ob ∈ org.current.objects, ob.id.origin = o) → ∀ ob ∈ d.current.objects, ob.id.origin = o

theorem heartbeatAll_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (pid : String) (now : Nat) :
    ∀ (refs : List TaskRef) (c : Commands) (T : Abstract.State),
      (∀ ref ∈ refs, ref.id.origin = o) → Acc o org c.org T → c.send = [] →
      Fx o (Abstract.heartbeatAll pid now refs (env S)).2 ∧
      Acc o org (refs.foldl (hbStep now org pid) c).org
        (Abstract.applyAll T (Abstract.heartbeatAll pid now refs (env S)).2) ∧
      sendsOf (Abstract.heartbeatAll pid now refs (env S)).2 = (refs.foldl (hbStep now org pid) c).send
  | [], c, T, _, hacc, hsend => ⟨trivial, hacc, by simp [Abstract.heartbeatAll, pure_apply, sendsOf, hsend]⟩
  | ref :: refs, c, T, hrefs, hacc, hsend => by
      have hid : ref.id.origin = o := hrefs ref (List.mem_cons_self ..)
      have hrest : ∀ r ∈ refs, r.id.origin = o := fun r hr => hrefs r (List.mem_cons_of_mem _ hr)
      simp only [Abstract.heartbeatAll, bind_apply, List.foldl_cons]
      suffices h : Fx o (Abstract.heartbeatOne pid ref now (env S)).2 ∧
          Acc o org (hbStep now org pid c ref).org
            (Abstract.applyAll T (Abstract.heartbeatOne pid ref now (env S)).2) ∧
          (hbStep now org pid c ref).send = [] ∧
          sendsOf (Abstract.heartbeatOne pid ref now (env S)).2 = [] by
        obtain ⟨h1, h2, h3, h4⟩ := h
        obtain ⟨i1, i2, i3⟩ := heartbeatAll_sim hL pid now refs _ _ hrest h2 h3
        refine ⟨(Fx_append _ _ _).2 ⟨h1, i1⟩, ?_, ?_⟩
        · rw [applyAll_append]; exact i2
        · rw [sendsOf_append, h4, i3]; rfl
      unfold Abstract.heartbeatOne hbStep
      simp only [bind_apply, readTaskObject_false, get_eq, hL ref.id hid]
      cases hf : Origin.find org ref.id with
      | none => exact ⟨trivial, hacc, hsend, rfl⟩
      | some ob =>
          cases ht : ob.task with
          | none =>
              simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
                Option.map_some, project_task, Option.map_none]
              exact ⟨trivial, hacc, hsend, rfl⟩
          | some t =>
              obtain ⟨tv, htv⟩ : ∃ tv, (ob.project now).task = some tv :=
                ⟨t.view (ob.promise.project now), by rw [project_task, ht]; rfl⟩
              simp only [ht, Option.isSome_some, ↓reduceIte, Option.bind_some, Option.map_some, htv]
              by_cases hc : (tv.state == TaskState.acquired) = true ∧ (tv.version == ref.version) = true
                  ∧ (tv.pid == some pid) = true ∧ ((ob.project now).promise.state == PromiseState.pending) = true
              · have heq := project_pending_eq hc.2.2.2
                rw [heq] at htv hc ⊢
                simp only [hc, and_self, ↓reduceIte, setTask_apply]
                have hob := find_orig hf
                have hido : ob.id.origin = o := hob ▸ hid
                refine ⟨⟨hido, trivial⟩, ?_, hsend, rfl⟩
                have hp := hacc.prom ref.id
                rw [hf, Option.map_some] at hp
                cases hy : Origin.find c.org ref.id with
                | none => rw [hy] at hp; cases hp
                | some y =>
                    rw [hy, Option.map_some, Option.some.injEq] at hp
                    have hyid : y.id = ob.id := (find_orig hy).trans hob.symm
                    have hy' : Origin.find c.org ob.id = some y := by rw [hob]; exact hy
                    simp only [List.nil_append]
                    refine ⟨Local_setTask_from hacc.loc hido rfl hy' ?_, ?_,
                      fun h => set_derived (hacc.orig h) hido⟩
                    · cases y with
                      | mk yi yp yt =>
                          cases ob with
                          | mk oi op ot =>
                              simp only at hyid hp
                              subst hyid; subst hp; rfl
                    · intro id
                      by_cases e : id = ref.id
                      · subst e
                        have hx : ({ ob with task := some { tv with leaseTimeoutAt := some (now + tv.ttl.getD 0) } }
                          : Object).id = ref.id := hob
                        rw [find_set_at hx, hf]; rfl
                      · rw [find_set_other _ _ _ (hob ▸ e)]; exact hacc.prom id
              · simp only [hc, ↓reduceIte, pure_apply]
                exact ⟨trivial, hacc, hsend, rfl⟩

theorem taskHeartbeat_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : TaskHeartbeatReq) (hid : ∀ ref ∈ req.tasks, ref.id.origin = o) :
    Sim o org S (Abstract.taskHeartbeat req now (env S))
      (Concrete.taskHeartbeat req now org).1 (Concrete.taskHeartbeat req now org).2 := by
  rw [taskHeartbeat_eq]
  unfold Abstract.taskHeartbeat
  simp only [bind_apply, pure_apply, List.append_nil]
  have hacc : Acc o org org S := ⟨hL, fun _ => rfl, fun h => h⟩
  obtain ⟨h1, h2, h3⟩ := heartbeatAll_sim hL req.pid now req.tasks { org } S hid hacc rfl
  exact ⟨rfl, h1, h2.loc, h3, h2.orig⟩

def regStep (awaiter : Ident) (d : Origin) (oa : Option Object) : Origin :=
  match oa with
  | some oa =>
      d.set { oa with promise := oa.promise.addCallback awaiter }
  | none =>
      d

theorem taskSuspend_eq (now : Nat) (org : Origin) (req : TaskSuspendReq) :
    Concrete.taskSuspend req now org =
      (let awaitedIds := req.actions.map (·.awaited)
       if req.actions.isEmpty ∨ awaitedIds.contains req.id
           ∨ awaitedIds.any (fun a => !a.sameOrigin req.id)
           ∨ awaitedIds.eraseDups.length != awaitedIds.length then
         ({ status := 400 }, { org })
       else
         match (org.get req.id now).bind fun o => o.task.map (o, ·) with
         | none =>
             ({ status := 404 }, { org })
         | some (o, t) =>
             if t.state != .acquired ∨ o.promise.state != .pending ∨ t.version != req.version then
               ({ status := 409 }, { org })
             else
               let awaited := awaitedIds.map (org.get · now)
               if awaited.any (fun oa => !(oa.map (·.promise.type.awaitable)).getD false) then
                 ({ status := 422 }, { org })
               else if awaited.any (fun oa => (oa.map (·.promise.state != .pending)).getD false) then
                 ({ status := 300 }, { org := org.set { o with task := some { t with resumes := [] } } })
               else
                 ({ status := 200 },
                  { org := (awaited.foldl (regStep req.id) org).set
                      { o with task := some { t with state := .suspended, pid := none, ttl := none,
                                                     leaseTimeoutAt := none, retryTimeoutAt := none,
                                                     resumes := [] } },
                    del := t.timers o.id })) := rfl

theorem contains_map_awaited (actions : List PromiseRegisterCallbackReq) (id : Ident) :
    (actions.map (·.awaited)).contains id = actions.any (·.awaited == id) := by
  induction actions with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.map_cons, List.contains_cons, List.any_cons, ih, Bool.beq_comm]

theorem any_map_sameOrigin (actions : List PromiseRegisterCallbackReq) (id : Ident) :
    (actions.map (·.awaited)).any (fun a => !a.sameOrigin id) =
      actions.any (fun a => !a.awaited.sameOrigin id) := by
  rw [List.any_map]; rfl

theorem checkAwaited_eq {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S) (now : Nat) :
    ∀ actions : List PromiseRegisterCallbackReq, (∀ a ∈ actions, a.awaited.origin = o) →
      Abstract.checkAwaited now actions (env S) =
        (if ((actions.map (·.awaited)).map (org.get · now)).any
              (fun oa => !(oa.map (·.promise.type.awaitable)).getD false) then none
         else some (((actions.map (·.awaited)).map (org.get · now)).any
              (fun oa => (oa.map (·.promise.state != .pending)).getD false)), [])
  | [], _ => rfl
  | a :: rest, h => by
      have ha : a.awaited.origin = o := h a (List.mem_cons_self ..)
      have hrest : ∀ b ∈ rest, b.awaited.origin = o := fun b hb => h b (List.mem_cons_of_mem _ hb)
      simp only [Abstract.checkAwaited, bind_apply, readObject_false, hL a.awaited ha, List.map_cons,
        List.any_cons]
      cases hf : Origin.find org a.awaited with
      | none =>
          have hg : org.get a.awaited now = none := by rw [get_eq, hf]; rfl
          simp only [hg, Option.map_none, Option.getD_none, Bool.not_false, Bool.true_or, ↓reduceIte,
            pure_apply, List.nil_append]
      | some ob =>
          have hg : org.get a.awaited now = some (ob.project now) := by rw [get_eq, hf]; rfl
          simp only [hg, Option.map_some, Option.getD_some]
          by_cases hw : (!(ob.project now).promise.type.awaitable) = true
          · simp only [hw, Bool.true_or, ↓reduceIte, pure_apply, List.nil_append]
          · have hw' : (!(ob.project now).promise.type.awaitable) = false := by simpa using hw
            simp only [hw', Bool.false_eq_true, ↓reduceIte, Bool.false_or, bind_apply,
              checkAwaited_eq hL now rest hrest]
            by_cases h1 : ((rest.map (·.awaited)).map (org.get · now)).any
                (fun oa => !(oa.map (·.promise.type.awaitable)).getD false) = true
            · simp only [h1, ↓reduceIte, pure_apply, List.nil_append]
            · have h1' : ((rest.map (·.awaited)).map (org.get · now)).any
                  (fun oa => !(oa.map (·.promise.type.awaitable)).getD false) = false := by simpa using h1
              simp only [h1', Bool.false_eq_true, ↓reduceIte, pure_apply, List.nil_append, Bool.or_comm]

structure RAcc (o : String) (org : Origin) (d : Origin) (T : Abstract.State) : Prop where
  loc  : Local o d T
  task : ∀ id, (Origin.find d id).map (·.task) = (Origin.find org id).map (·.task)

theorem registerAwaited_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (awaiter : Ident) (now : Nat) :
    ∀ (actions : List PromiseRegisterCallbackReq) (d : Origin) (T : Abstract.State),
      (∀ a ∈ actions, a.awaited.origin = o) →
      (∀ a ∈ actions, ∀ ob, Origin.find org a.awaited = some ob → ob.project now = ob) →
      RAcc o org d T →
      Fx o (Abstract.registerAwaited awaiter now actions (env S)).2 ∧
      RAcc o org (((actions.map (·.awaited)).map (org.get · now)).foldl (regStep awaiter) d)
        (Abstract.applyAll T (Abstract.registerAwaited awaiter now actions (env S)).2) ∧
      sendsOf (Abstract.registerAwaited awaiter now actions (env S)).2 = [] ∧
      (∀ id, id ∉ actions.map (·.awaited) →
        Origin.find (((actions.map (·.awaited)).map (org.get · now)).foldl (regStep awaiter) d) id =
          Origin.find d id) ∧
      ((∀ ob ∈ d.current.objects, ob.id.origin = o) →
        ∀ ob ∈ (((actions.map (·.awaited)).map (org.get · now)).foldl (regStep awaiter) d).current.objects,
          ob.id.origin = o)
  | [], d, T, _, _, hacc => ⟨trivial, hacc, rfl, fun _ _ => rfl, fun h => h⟩
  | a :: rest, d, T, h, hproj, hacc => by
      have ha : a.awaited.origin = o := h a (List.mem_cons_self ..)
      have hrest : ∀ b ∈ rest, b.awaited.origin = o := fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hprest : ∀ b ∈ rest, ∀ ob, Origin.find org b.awaited = some ob → ob.project now = ob :=
        fun b hb => hproj b (List.mem_cons_of_mem _ hb)
      simp only [Abstract.registerAwaited, bind_apply, readObject_false, hL a.awaited ha, List.map_cons,
        List.foldl_cons]
      cases hf : Origin.find org a.awaited with
      | none =>
          have hg : org.get a.awaited now = none := by rw [get_eq, hf]; rfl
          simp only [hg, Option.map_none, List.nil_append, regStep]
          obtain ⟨i1, i2, i3, i4, i5⟩ := registerAwaited_sim hL awaiter now rest d T hrest hprest hacc
          exact ⟨i1, i2, i3, fun id hid => i4 id (fun m => hid (List.mem_cons_of_mem _ m)), i5⟩
      | some ob =>
          have heq : ob.project now = ob := hproj a (List.mem_cons_self ..) ob hf
          have hg : org.get a.awaited now = some ob := by rw [get_eq, hf, Option.map_some, heq]
          simp only [hg, Option.map_some, heq, bind_apply, setPromise_apply, List.nil_append,
            List.cons_append, regStep]
          have hob := find_orig hf
          have hido : ob.id.origin = o := hob ▸ ha
          have hx : ({ ob with promise := ob.promise.addCallback awaiter } : Object).id = ob.id := rfl
          have htk := hacc.task a.awaited
          rw [hf, Option.map_some] at htk
          cases hy : Origin.find d a.awaited with
          | none => rw [hy] at htk; cases htk
          | some y =>
              rw [hy, Option.map_some, Option.some.injEq] at htk
              have hyid : y.id = ob.id := (find_orig hy).trans hob.symm
              have hy' : Origin.find d ob.id = some y := by rw [hob]; exact hy
              have hacc' : RAcc o org (d.set { ob with promise := ob.promise.addCallback awaiter })
                  (Abstract.applyAll T [.setPromise ob.id (ob.promise.addCallback awaiter)]) := by
                refine ⟨Local_setPromise_from hacc.loc hido hx hy' ?_, ?_⟩
                · cases y with
                  | mk yi yp yt =>
                      cases ob with
                      | mk oi op ot =>
                          simp only at hyid htk
                          subst hyid; subst htk; rfl
                · intro id
                  by_cases e : id = ob.id
                  · subst e
                    rw [find_set_at hx, hob, hf]; rfl
                  · rw [find_set_other _ _ _ (hx ▸ e)]; exact hacc.task id
              obtain ⟨i1, i2, i3, i4, i5⟩ :=
                registerAwaited_sim hL awaiter now rest _ _ hrest hprest hacc'
              simp only [Abstract.applyAll] at i2
              refine ⟨⟨hido, i1⟩, by simp only [Abstract.applyAll]; exact i2, i3, ?_,
                fun h => i5 (set_derived h hido)⟩
              intro id hid
              rw [i4 id (fun m => hid (List.mem_cons_of_mem _ m)),
                find_set_other _ _ _ (by rw [hx, hob]; exact fun e => hid (e ▸ List.mem_cons_self ..))]

theorem taskSuspend_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : TaskSuspendReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.taskSuspend req now (env S))
      (Concrete.taskSuspend req now org).1 (Concrete.taskSuspend req now org).2 := by
  rw [taskSuspend_eq]
  unfold Abstract.taskSuspend
  by_cases h1 : req.actions.isEmpty = true
  · simp only [h1, true_or, ↓reduceIte, pure_apply]
    exact Sim.skip hL _
  · have h1' : req.actions.isEmpty = false := by simpa using h1
    by_cases h2 : req.actions.any (·.awaited == req.id) = true
    · simp only [h1', h2, contains_map_awaited, Bool.false_eq_true, false_or, true_or, ↓reduceIte]
      exact Sim.skip hL _
    · have h2' : req.actions.any (·.awaited == req.id) = false := by simpa using h2
      by_cases h3 : req.actions.any (fun a => !a.awaited.sameOrigin req.id) = true
      · simp only [h1', h2', h3, contains_map_awaited, any_map_sameOrigin, Bool.false_eq_true, false_or,
          true_or, ↓reduceIte]
        exact Sim.skip hL _
      · have h3' : req.actions.any (fun a => !a.awaited.sameOrigin req.id) = false := by simpa using h3
        by_cases h4 : ((req.actions.map (·.awaited)).eraseDups.length != (req.actions.map (·.awaited)).length) = true
        · simp only [h1', h2', h3', h4, contains_map_awaited, any_map_sameOrigin, Bool.false_eq_true,
            or_true, ↓reduceIte]
          exact Sim.skip hL _
        · have h4' : ((req.actions.map (·.awaited)).eraseDups.length != (req.actions.map (·.awaited)).length) = false := by
            simpa using h4
          simp only [h1', h2', h3', h4', contains_map_awaited, any_map_sameOrigin, Bool.false_eq_true,
            or_self, ↓reduceIte, bind_apply, pure_apply, readTaskObject_false, hL req.id hid]
          rw [get_eq org req.id now]
          have horig : ∀ a ∈ req.actions, a.awaited.origin = o := by
            intro a ha
            have hs : a.awaited.sameOrigin req.id = true := by
              simpa using List.any_eq_false.1 h3' a ha
            rw [← hid]; exact (sameOrigin_eq hs).symm
          cases hf : Origin.find org req.id with
          | none => exact Sim.skip hL _
          | some ob =>
              cases ht : ob.task with
              | none =>
                  simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
                    Option.map_some, project_task, Option.map_none]
                  exact Sim.skip hL _
              | some t =>
                  obtain ⟨tv, htv⟩ : ∃ tv, (ob.project now).task = some tv :=
                    ⟨t.view (ob.promise.project now), by rw [project_task, ht]; rfl⟩
                  simp only [ht, Option.isSome_some, ↓reduceIte, Option.bind_some, Option.map_some, htv]
                  by_cases c1 : (tv.state != TaskState.acquired) = true
                  · simp only [c1, true_or, ↓reduceIte, pure_apply]
                    exact Sim.skip hL _
                  · have c1' : (tv.state != TaskState.acquired) = false := by simpa using c1
                    by_cases c2 : ((ob.project now).promise.state != PromiseState.pending) = true
                    · simp only [c1', c2, Bool.false_eq_true, false_or, true_or, ↓reduceIte]
                      exact Sim.skip hL _
                    · have c2' : ((ob.project now).promise.state != PromiseState.pending) = false := by
                        simpa using c2
                      by_cases c3 : (tv.version != req.version) = true
                      · simp only [c1', c2', c3, Bool.false_eq_true, or_true, ↓reduceIte]
                        exact Sim.skip hL _
                      · have c3' : (tv.version != req.version) = false := by simpa using c3
                        have heq := project_pending_ne c2'
                        rw [heq] at htv c2' ⊢
                        simp only [c1', c2', c3', Bool.false_eq_true, or_self, ↓reduceIte, bind_apply,
                          pure_apply, checkAwaited_eq hL now req.actions horig]
                        have hob := find_orig hf
                        have hido : ob.id.origin = o := hob ▸ hid
                        by_cases a1 : ((req.actions.map (·.awaited)).map (org.get · now)).any
                            (fun oa => !(oa.map (·.promise.type.awaitable)).getD false) = true
                        · simp only [a1, ↓reduceIte, pure_apply, List.nil_append]
                          exact Sim.skip hL _
                        · have a1' : ((req.actions.map (·.awaited)).map (org.get · now)).any
                              (fun oa => !(oa.map (·.promise.type.awaitable)).getD false) = false := by
                            simpa using a1
                          by_cases a2 : ((req.actions.map (·.awaited)).map (org.get · now)).any
                              (fun oa => (oa.map (·.promise.state != .pending)).getD false) = true
                          · simp only [a1', a2, Bool.false_eq_true, ↓reduceIte, bind_apply, setTask_apply,
                              pure_apply, List.append_nil, List.nil_append]
                            refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_set hido⟩
                            exact Local_setTask hL hido rfl (by rw [hob, hf]; simp [hob])
                          · have a2' : ((req.actions.map (·.awaited)).map (org.get · now)).any
                                (fun oa => (oa.map (·.promise.state != .pending)).getD false) = false := by
                              simpa using a2
                            simp only [a1', a2', Bool.false_eq_true, ↓reduceIte, bind_apply, setTask_apply,
                              pure_apply, List.append_nil, List.nil_append]
                            have hproj : ∀ a ∈ req.actions, ∀ ob, Origin.find org a.awaited = some ob →
                                ob.project now = ob := by
                              intro a ha ob' hf'
                              have hm : org.get a.awaited now ∈ (req.actions.map (·.awaited)).map (org.get · now) :=
                                List.mem_map.2 ⟨a.awaited, List.mem_map.2 ⟨a, ha, rfl⟩, rfl⟩
                              have hs := List.any_eq_false.1 a2' _ hm
                              rw [get_eq, hf', Option.map_some, Option.map_some, Option.getD_some] at hs
                              exact project_pending_ne (by simpa using hs)
                            obtain ⟨i1, i2, i3, i4, i5⟩ :=
                              registerAwaited_sim hL req.id now req.actions org S horig hproj ⟨hL, fun _ => rfl⟩
                            have hnm : req.id ∉ req.actions.map (·.awaited) := by
                              intro hm
                              obtain ⟨a, ha, hae⟩ := List.mem_map.1 hm
                              have := List.any_eq_false.1 h2' a ha
                              simp [hae] at this
                            have hy : Origin.find (((req.actions.map (·.awaited)).map (org.get · now)).foldl
                                (regStep req.id) org) ob.id = some ob := by
                              rw [hob, i4 req.id hnm, hf]
                            refine ⟨rfl, (Fx_append _ _ _).2 ⟨i1, hido, trivial⟩, ?_, ?_,
                              fun h => set_derived (i5 h) hido⟩
                            · rw [applyAll_append]
                              exact Local_setTask_from i2.loc hido rfl hy rfl
                            · rw [sendsOf_append, i3]; rfl

end Refinement
