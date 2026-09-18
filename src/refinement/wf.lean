import refinement.sweep

namespace Refinement

open Protocol (Ident Message Object PromiseObject TaskObject PromiseState TaskState Request)
open Concrete (Origin Commands)
open scoped List

def Good (o : Object) : Prop :=
  o.promise.listeners.Nodup ∧ o.promise.callbacks.Nodup ∧
    ∀ w ∈ o.promise.callbacks, w ≠ o.id ∧ w.origin = o.id.origin

theorem WF_good {org : Origin} (h : WF org) {id : Ident} {now : Nat} {o : Object}
    (hf : org.get id now = some o) : Good o := by
  obtain ⟨ob, hfind, rfl⟩ := get_some hf
  obtain ⟨h1, h2, h3⟩ := h ob (find_mem hfind).1
  refine ⟨?_, ?_, fun w hw => ?_⟩
  · show (ob.promise.project now).listeners.Nodup
    rw [project_listeners]; exact h1
  · show (ob.promise.project now).callbacks.Nodup
    rw [project_callbacks]; exact h2
  · have hw' : w ∈ (ob.promise.project now).callbacks := hw
    rw [project_callbacks] at hw'
    exact h3 w hw'

theorem WF_set_of {o : Object} (hg : Good o) {x : Object} (hid : x.id = o.id)
    (hcb : x.promise.callbacks <+ o.promise.callbacks) (hls : x.promise.listeners <+ o.promise.listeners)
    {d : Origin} (hd : WF d) : WF (d.set x) :=
  WF_set_fresh hd ⟨hg.1.sublist hls, hg.2.1.sublist hcb, fun w hw => by
    rw [hid]; exact hg.2.2 w (hcb.subset hw)⟩

theorem addCallback_listeners (p : PromiseObject) (w : Ident) : (p.addCallback w).listeners = p.listeners := by
  unfold PromiseObject.addCallback; split <;> rfl

theorem addListener_callbacks (p : PromiseObject) (a : String) : (p.addListener a).callbacks = p.callbacks := by
  unfold PromiseObject.addListener; split <;> rfl

theorem WF_set_add {o : Object} (hg : Good o) {w : Ident} (hne : w ≠ o.id) (ho : w.origin = o.id.origin)
    {d : Origin} (hd : WF d) : WF (d.set { o with promise := o.promise.addCallback w }) := by
  refine WF_set_fresh hd ⟨?_, ?_, fun a ha => ?_⟩
  · show (o.promise.addCallback w).listeners.Nodup
    rw [addCallback_listeners]; exact hg.1
  · show (o.promise.addCallback w).callbacks.Nodup
    unfold PromiseObject.addCallback
    split
    · exact hg.2.1
    · rename_i hc
      exact nodup_append_single hg.2.1 (fun hm => by simp at hc; exact hc hm)
  · have ha' : a ∈ (o.promise.addCallback w).callbacks := ha
    unfold PromiseObject.addCallback at ha'
    split at ha'
    · exact hg.2.2 a ha'
    · simp only [List.mem_append, List.mem_singleton] at ha'
      rcases ha' with ha' | rfl
      · exact hg.2.2 a ha'
      · exact ⟨hne, ho⟩

theorem WF_set_addListener {o : Object} (hg : Good o) (a : String) {d : Origin} (hd : WF d) :
    WF (d.set { o with promise := o.promise.addListener a }) := by
  refine WF_set_fresh hd ⟨?_, ?_, ?_⟩
  · show (o.promise.addListener a).listeners.Nodup
    unfold PromiseObject.addListener
    split
    · exact hg.1
    · rename_i hc
      exact nodup_append_single hg.1 (fun hm => by simp at hc; exact hc hm)
  · show (o.promise.addListener a).callbacks.Nodup
    rw [addListener_callbacks]; exact hg.2.1
  · show ∀ w ∈ (o.promise.addListener a).callbacks, _
    rw [addListener_callbacks]; exact hg.2.2

theorem WF_set_new {d : Origin} (hd : WF d) (id : Ident) (p : PromiseObject) (t : Option TaskObject)
    (hp : p.callbacks = []) (hl : p.listeners = []) : WF (d.set ⟨id, p, t⟩) :=
  WF_set_fresh hd ⟨by show p.listeners.Nodup; rw [hl]; exact List.nodup_nil,
    by show p.callbacks.Nodup; rw [hp]; exact List.nodup_nil, fun w hw => by simp [hp] at hw⟩

open Protocol (PromiseGetReq PromiseCreateReq PromiseSettleReq PromiseRegisterCallbackReq
               PromiseRegisterListenerReq PromiseSearchReq TaskGetReq TaskCreateReq TaskAcquireReq
               TaskFenceReq TaskHeartbeatReq TaskSuspendReq TaskFulfillReq TaskReleaseReq TaskHaltReq
               TaskContinueReq TaskSearchReq TaskRef)

theorem promiseGet_wf {org : Origin} (h : WF org) (now : Nat) (req : PromiseGetReq) :
    WF (Concrete.promiseGet req now org).2.org := by
  unfold Concrete.promiseGet
  split <;> exact h

theorem promiseCreate_wf {org : Origin} (h : WF org) (now : Nat) (req : PromiseCreateReq) :
    WF (Concrete.promiseCreate req now org).2.org := by
  unfold Concrete.promiseCreate
  split
  · exact h
  · dsimp only
    split
    · split
      · exact WF_set_new h _ _ _ rfl rfl
      · exact WF_set_new h _ _ _ rfl rfl
    · exact WF_set_new h _ _ _ rfl rfl

theorem promiseSettle_wf {org : Origin} (h : WF org) (now : Nat) (req : PromiseSettleReq) :
    WF (Concrete.promiseSettle req now org).2.org := by
  unfold Concrete.promiseSettle
  split
  · exact h
  · cases hf : org.get req.id now with
    | none => exact h
    | some o =>
        dsimp only
        split
        · refine WF_set_of (WF_good h hf) ?_ ?_ ?_ h <;> first | rfl | exact List.Sublist.refl _
        · exact h

theorem promiseRegisterCallback_wf {org : Origin} (h : WF org) (now : Nat)
    (req : PromiseRegisterCallbackReq) :
    WF (Concrete.promiseRegisterCallback req now org).2.org := by
  unfold Concrete.promiseRegisterCallback
  by_cases hc : (req.awaited == req.awaiter) = true ∨ (!req.awaited.sameOrigin req.awaiter) = true
  · rw [if_pos hc]
    exact h
  · rw [if_neg hc]
    cases hf : org.get req.awaited now with
    | none => exact h
    | some awaited =>
        cases hg : org.get req.awaiter now with
        | none => exact h
        | some awaiter =>
            dsimp only
            split
            · exact h
            · split
              · have hne : req.awaiter ≠ awaited.id := by
                  rw [get_id hf]
                  intro e
                  exact hc (Or.inl (by simp [e]))
                have ho : req.awaiter.origin = awaited.id.origin := by
                  rw [get_id hf]
                  by_cases hs : req.awaited.sameOrigin req.awaiter = true
                  · exact sameOrigin_eq hs
                  · exact absurd (Or.inr (by simpa using hs)) hc
                exact WF_set_add (WF_good h hf) hne ho h
              · exact h

theorem promiseRegisterListener_wf {org : Origin} (h : WF org) (now : Nat)
    (req : PromiseRegisterListenerReq) :
    WF (Concrete.promiseRegisterListener req now org).2.org := by
  unfold Concrete.promiseRegisterListener
  cases hf : org.get req.awaited now with
  | none => exact h
  | some awaited =>
      dsimp only
      split
      · exact h
      · split
        · exact WF_set_addListener (WF_good h hf) req.address h
        · exact h

theorem taskGet_wf {org : Origin} (h : WF org) (now : Nat) (req : TaskGetReq) :
    WF (Concrete.taskGet req now org).2.org := by
  unfold Concrete.taskGet
  split <;> exact h

theorem taskCreate_wf {org : Origin} (h : WF org) (now : Nat) (req : TaskCreateReq) :
    WF (Concrete.taskCreate req now org).2.org := by
  unfold Concrete.taskCreate
  dsimp only
  split
  · exact h
  · cases hf : org.get req.action.id now with
    | none =>
        dsimp only
        split
        · exact WF_set_new h _ _ _ rfl rfl
        · exact WF_set_new h _ _ _ rfl rfl
    | some o =>
        dsimp only
        split
        · exact h
        · split
          · exact h
          · split
            · exact h
            · split
              · refine WF_set_of (WF_good h hf) ?_ ?_ ?_ h <;> first | rfl | exact List.Sublist.refl _
              · exact h

theorem taskAcquire_wf {org : Origin} (h : WF org) (now : Nat) (req : TaskAcquireReq) :
    WF (Concrete.taskAcquire req now org).2.org := by
  unfold Concrete.taskAcquire
  cases hf : org.get req.id now with
  | none => exact h
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact h
      | some t =>
          simp only [Option.map_some]
          split
          · exact h
          · refine WF_set_of (WF_good h hf) ?_ ?_ ?_ h <;> first | rfl | exact List.Sublist.refl _

theorem taskFence_wf {org : Origin} (h : WF org) (now : Nat) (req : TaskFenceReq) :
    WF (Concrete.taskFence req now org).2.org := by
  unfold Concrete.taskFence
  split
  · exact h
  · cases org.get req.id now with
    | none => exact h
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact h
        | some t =>
            simp only [Option.map_some]
            split
            · exact h
            · cases req.action with
              | create r =>
                  rcases hC : Concrete.promiseCreate r now org with ⟨res, c⟩
                  have := promiseCreate_wf h now r
                  rw [hC] at this
                  simp only [hC]
                  exact this
              | settle r =>
                  rcases hC : Concrete.promiseSettle r now org with ⟨res, c⟩
                  have := promiseSettle_wf h now r
                  rw [hC] at this
                  simp only [hC]
                  exact this

theorem hbStep_wf {org : Origin} (h : WF org) (now : Nat) (pid : String) :
    ∀ (refs : List TaskRef) (c : Commands), WF c.org → WF (refs.foldl (hbStep now org pid) c).org
  | [], _, hc => hc
  | ref :: refs, c, hc => by
      simp only [List.foldl_cons]
      refine hbStep_wf h now pid refs _ ?_
      unfold hbStep
      cases hf : org.get ref.id now with
      | none => exact hc
      | some o =>
          simp only [Option.bind_some]
          cases o.task with
          | none => exact hc
          | some t =>
              simp only [Option.map_some]
              split
              · refine WF_set_of (WF_good h hf) ?_ ?_ ?_ hc <;> first | rfl | exact List.Sublist.refl _
              · exact hc

theorem taskHeartbeat_wf {org : Origin} (h : WF org) (now : Nat) (req : TaskHeartbeatReq) :
    WF (Concrete.taskHeartbeat req now org).2.org := by
  rw [taskHeartbeat_eq]
  exact hbStep_wf h now req.pid req.tasks _ h

theorem regStep_wf {org : Origin} (h : WF org) (now : Nat) (awaiter : Ident) :
    ∀ (ids : List Ident) (d : Origin), WF d →
      (∀ id ∈ ids, id ≠ awaiter ∧ awaiter.origin = id.origin) →
      WF ((ids.map (org.get · now)).foldl (regStep awaiter) d)
  | [], _, hd, _ => hd
  | id :: ids, d, hd, hids => by
      simp only [List.map_cons, List.foldl_cons]
      refine regStep_wf h now awaiter ids _ ?_ (fun i hi => hids i (List.mem_cons_of_mem _ hi))
      unfold regStep
      cases hf : org.get id now with
      | none => exact hd
      | some oa =>
          have hi := hids id (List.mem_cons_self ..)
          refine WF_set_add (WF_good h hf) ?_ ?_ hd
          · rw [get_id hf]; exact hi.1.symm
          · rw [get_id hf]; exact hi.2

theorem taskSuspend_wf {org : Origin} (h : WF org) (now : Nat) (req : TaskSuspendReq) :
    WF (Concrete.taskSuspend req now org).2.org := by
  rw [taskSuspend_eq]
  dsimp only
  split
  · exact h
  · rename_i hc
    cases hf : org.get req.id now with
    | none => exact h
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact h
        | some t =>
            simp only [Option.map_some]
            split
            · exact h
            · split
              · exact h
              · split
                · refine WF_set_of (WF_good h hf) ?_ ?_ ?_ h <;> first | rfl | exact List.Sublist.refl _
                · refine WF_set_of (WF_good h hf) ?_ ?_ ?_ ?_
                  · rfl
                  · exact List.Sublist.refl _
                  · exact List.Sublist.refl _
                  refine regStep_wf h now req.id _ org h ?_
                  intro id hid
                  simp only [not_or] at hc
                  obtain ⟨_, h2, h3, _⟩ := hc
                  constructor
                  · intro e
                    subst e
                    exact h2 (List.contains_iff_mem.2 hid)
                  · have h3' := List.any_eq_false.1 (eq_false_of_ne_true h3) id hid
                    exact sameOrigin_eq (by simpa using h3')

theorem taskFulfill_wf {org : Origin} (h : WF org) (now : Nat) (req : TaskFulfillReq) :
    WF (Concrete.taskFulfill req now org).2.org := by
  unfold Concrete.taskFulfill
  split
  · exact h
  · cases hf : org.get req.id now with
    | none => exact h
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact h
        | some t =>
            simp only [Option.map_some]
            split
            · exact h
            · refine WF_set_of (WF_good h hf) ?_ ?_ ?_ h <;> first | rfl | exact List.Sublist.refl _

theorem taskRelease_wf {org : Origin} (h : WF org) (now : Nat) (req : TaskReleaseReq) :
    WF (Concrete.taskRelease req now org).2.org := by
  unfold Concrete.taskRelease
  cases hf : org.get req.id now with
  | none => exact h
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact h
      | some t =>
          simp only [Option.map_some]
          split
          · exact h
          · refine WF_set_of (WF_good h hf) ?_ ?_ ?_ h <;> first | rfl | exact List.Sublist.refl _

theorem taskHalt_wf {org : Origin} (h : WF org) (now : Nat) (req : TaskHaltReq) :
    WF (Concrete.taskHalt req now org).2.org := by
  unfold Concrete.taskHalt
  cases hf : org.get req.id now with
  | none => exact h
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact h
      | some t =>
          simp only [Option.map_some]
          split
          · exact h
          · split
            · exact h
            · refine WF_set_of (WF_good h hf) ?_ ?_ ?_ h <;> first | rfl | exact List.Sublist.refl _

theorem taskContinue_wf {org : Origin} (h : WF org) (now : Nat) (req : TaskContinueReq) :
    WF (Concrete.taskContinue req now org).2.org := by
  unfold Concrete.taskContinue
  cases hf : org.get req.id now with
  | none => exact h
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact h
      | some t =>
          simp only [Option.map_some]
          split
          · exact h
          · refine WF_set_of (WF_good h hf) ?_ ?_ ?_ h <;> first | rfl | exact List.Sublist.refl _

theorem handleExternal_wf {org : Origin} (h : WF org) (now : Nat) (req : Request) :
    WF (Concrete.handleExternal req now org).2.org := by
  cases req with
  | promiseGet r =>
      rcases hC : Concrete.promiseGet r now org with ⟨res, c⟩
      have := promiseGet_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | promiseCreate r =>
      rcases hC : Concrete.promiseCreate r now org with ⟨res, c⟩
      have := promiseCreate_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | promiseSettle r =>
      rcases hC : Concrete.promiseSettle r now org with ⟨res, c⟩
      have := promiseSettle_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | promiseRegisterCallback r =>
      rcases hC : Concrete.promiseRegisterCallback r now org with ⟨res, c⟩
      have := promiseRegisterCallback_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | promiseRegisterListener r =>
      rcases hC : Concrete.promiseRegisterListener r now org with ⟨res, c⟩
      have := promiseRegisterListener_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | promiseSearch r => exact h
  | scheduleGet r => exact h
  | scheduleCreate r => exact h
  | scheduleDelete r => exact h
  | scheduleSearch r => exact h
  | taskGet r =>
      rcases hC : Concrete.taskGet r now org with ⟨res, c⟩
      have := taskGet_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskCreate r =>
      rcases hC : Concrete.taskCreate r now org with ⟨res, c⟩
      have := taskCreate_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskAcquire r =>
      rcases hC : Concrete.taskAcquire r now org with ⟨res, c⟩
      have := taskAcquire_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskFence r =>
      rcases hC : Concrete.taskFence r now org with ⟨res, c⟩
      have := taskFence_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskHeartbeat r =>
      rcases hC : Concrete.taskHeartbeat r now org with ⟨res, c⟩
      have := taskHeartbeat_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskSuspend r =>
      rcases hC : Concrete.taskSuspend r now org with ⟨res, c⟩
      have := taskSuspend_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskFulfill r =>
      rcases hC : Concrete.taskFulfill r now org with ⟨res, c⟩
      have := taskFulfill_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskRelease r =>
      rcases hC : Concrete.taskRelease r now org with ⟨res, c⟩
      have := taskRelease_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskHalt r =>
      rcases hC : Concrete.taskHalt r now org with ⟨res, c⟩
      have := taskHalt_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskContinue r =>
      rcases hC : Concrete.taskContinue r now org with ⟨res, c⟩
      have := taskContinue_wf h now r
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskSearch r => exact h

end Refinement
