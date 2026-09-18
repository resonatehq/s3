import refinement.cache

namespace Refinement

open Protocol (Ident Object PromiseObject TaskObject Request)
open Protocol (PromiseGetReq PromiseCreateReq PromiseSettleReq PromiseRegisterCallbackReq
                  PromiseRegisterListenerReq TaskGetReq TaskCreateReq TaskAcquireReq TaskFenceReq
                  TaskHeartbeatReq TaskSuspendReq TaskFulfillReq TaskReleaseReq TaskHaltReq TaskContinueReq
                  TaskRef)
open Concrete (Origin Commands Timer Path Blob)

def Armed (s : Concrete.State) : Prop :=
  ∀ t : Timer, (s.blob? (.timer t)).isSome = true → t.kind = .promiseTimeout →
    ∃ o ∈ (s.origin t.id.origin).objects, o.id = t.id ∧ o.promise.type ≠ .internal

theorem Armed.init : Armed Concrete.State.init := by
  intro t ht _
  simp [Concrete.State.init, Concrete.State.blob?] at ht

def KeepDoc (org d : Origin) : Prop :=
  ∀ o ∈ org.objects, ∃ o' ∈ d.objects, o'.id = o.id ∧ o'.promise.type = o.promise.type

theorem KeepDoc.refl (org : Origin) : KeepDoc org org := fun o ho => ⟨o, ho, rfl, rfl⟩

theorem KeepDoc.trans {a b c : Origin} (h1 : KeepDoc a b) (h2 : KeepDoc b c) : KeepDoc a c := by
  intro o ho
  obtain ⟨o', ho', hi, ht⟩ := h1 o ho
  obtain ⟨o'', ho'', hi', ht'⟩ := h2 o' ho'
  exact ⟨o'', ho'', hi'.trans hi, ht'.trans ht⟩

theorem mem_set_self (org : Origin) (x : Object) : x ∈ (org.set x).objects := by
  unfold Concrete.Origin.set
  split
  · rename_i h
    obtain ⟨o, ho, he⟩ := List.any_eq_true.1 h
    exact List.mem_map.2 ⟨o, ho, by simp [he]⟩
  · simp

theorem mem_set_of_ne {org : Origin} {x o : Object} (ho : o ∈ org.objects) (hne : o.id ≠ x.id) :
    o ∈ (org.set x).objects := by
  unfold Concrete.Origin.set
  split
  · exact List.mem_map.2 ⟨o, ho, by simp [hne]⟩
  · simp [ho]

theorem KeepDoc.set {org d : Origin} (hd : KeepDoc org d) {x : Object}
    (hty : ∀ o ∈ org.objects, o.id = x.id → o.promise.type = x.promise.type) : KeepDoc org (d.set x) := by
  intro o ho
  by_cases e : o.id = x.id
  · exact ⟨x, mem_set_self d x, e.symm, (hty o ho e).symm⟩
  · obtain ⟨o', ho', hi, ht⟩ := hd o ho
    exact ⟨o', mem_set_of_ne ho' (fun h => e (hi.symm.trans h)), hi, ht⟩

structure Keep (org : Origin) (c : Commands) : Prop where
  arm : ∀ t ∈ c.arm, t.kind = .promiseTimeout → ∃ o ∈ c.org.objects, o.id = t.id ∧ o.promise.type ≠ .internal
  doc : KeepDoc org c.org

theorem Keep.id (org : Origin) : Keep org { org } :=
  ⟨fun _ ht => absurd ht List.not_mem_nil, KeepDoc.refl org⟩

theorem Keep.merge {org : Origin} {c d : Commands} (hc : Keep org c) (hd : Keep c.org d) :
    Keep org (c.merge d) := by
  refine ⟨fun t ht hk => ?_, hc.doc.trans hd.doc⟩
  show ∃ o ∈ d.org.objects, o.id = t.id ∧ o.promise.type ≠ .internal
  have ht' : t ∈ c.arm ++ d.arm := ht
  rcases List.mem_append.1 ht' with ht | ht
  · obtain ⟨o, ho, hi, hty⟩ := hc.arm t ht hk
    obtain ⟨o', ho', hi', hty'⟩ := hd.doc o ho
    exact ⟨o', ho', hi'.trans hi, fun h => hty (hty'.symm.trans h)⟩
  · exact hd.arm t ht hk

theorem task_timers_kind {tk : TaskObject} {id : Ident} {t : Timer} (ht : t ∈ tk.timers id) :
    t.kind ≠ .promiseTimeout := by
  unfold Protocol.TaskObject.timers at ht
  split at ht
  · rw [List.mem_singleton] at ht; subst ht; simp
  · rw [List.mem_singleton] at ht; subst ht; simp
  · simp at ht

theorem timers_kind {o : Object} {t : Timer} (ht : t ∈ o.timers) (hk : t.kind = .promiseTimeout) :
    t.id = o.id ∧ o.promise.type ≠ .internal := by
  unfold Protocol.Object.timers at ht
  rw [List.mem_append] at ht
  rcases ht with ht | ht
  · split at ht
    · rename_i hc
      rw [List.mem_singleton] at ht
      subst ht
      exact ⟨rfl, by simpa using hc.2⟩
    · simp at ht
  · cases htk : o.task with
    | none => rw [htk] at ht; simp at ht
    | some tk =>
        rw [htk] at ht
        simp only [Option.map_some, Option.getD_some] at ht
        exact absurd hk (task_timers_kind ht)

theorem project_type (p : PromiseObject) (n : Nat) : (p.project n).type = p.type := by
  unfold PromiseObject.project
  split <;> (try split) <;> rfl

theorem addCallback_type (p : PromiseObject) (w : Ident) : (p.addCallback w).type = p.type := by
  unfold PromiseObject.addCallback; split <;> rfl

theorem addListener_type (p : PromiseObject) (a : String) : (p.addListener a).type = p.type := by
  unfold PromiseObject.addListener; split <;> rfl

theorem type_of_get {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) {id : Ident} {now : Nat} {o : Object}
    (hf : org.get id now = some o) {x : Object} (hx : x.id = o.id) (hxt : x.promise.type = o.promise.type) :
    ∀ o' ∈ org.objects, o'.id = x.id → o'.promise.type = x.promise.type := by
  obtain ⟨ob, hfind, rfl⟩ := get_some hf
  obtain ⟨hob, -⟩ := find_mem hfind
  intro o' ho' he
  have : o' = ob := eq_of_id_nodup hnd ho' hob (he.trans hx)
  subst this
  rw [hxt]
  exact (project_type o'.promise now).symm

theorem type_of_none {org : Origin} {id : Ident} {now : Nat} (hf : org.get id now = none) {x : Object}
    (hx : x.id = id) : ∀ o' ∈ org.objects, o'.id = x.id → o'.promise.type = x.promise.type := by
  intro o' ho' he
  exfalso
  rw [get_eq] at hf
  have hfind : Origin.find org id = none := by
    cases h : Origin.find org id with
    | none => rfl
    | some _ => rw [h] at hf; cases hf
  unfold Origin.find at hfind
  exact (List.find?_eq_none.1 hfind o' ho') (by simp [he, hx])

theorem Keep.set {org d : Origin} (hd : KeepDoc org d) {x : Object}
    (hty : ∀ o ∈ org.objects, o.id = x.id → o.promise.type = x.promise.type)
    {A D : List Timer} {S : List (String × Protocol.Message)}
    (harm : ∀ t ∈ A, t.kind = .promiseTimeout → t.id = x.id ∧ x.promise.type ≠ .internal) :
    Keep org { arm := A, org := d.set x, del := D, send := S } :=
  ⟨fun t ht hk => ⟨x, mem_set_self d x, (harm t ht hk).1.symm, (harm t ht hk).2⟩, hd.set hty⟩

theorem noarm {x : Object} : ∀ t ∈ ([] : List Timer), t.kind = .promiseTimeout → t.id = x.id ∧ x.promise.type ≠ .internal :=
  fun _ ht => absurd ht List.not_mem_nil

theorem taskarm {x : Object} {tk : TaskObject} {id : Ident} :
    ∀ t ∈ tk.timers id, t.kind = .promiseTimeout → t.id = x.id ∧ x.promise.type ≠ .internal :=
  fun _ ht hk => absurd hk (task_timers_kind ht)

theorem objarm {x : Object} : ∀ t ∈ x.timers, t.kind = .promiseTimeout → t.id = x.id ∧ x.promise.type ≠ .internal :=
  fun _ ht hk => timers_kind ht hk

theorem promiseGet_keep {org : Origin} (now : Nat) (req : PromiseGetReq) : Keep org (Concrete.promiseGet req now org).2 := by
  unfold Concrete.promiseGet
  split <;> exact Keep.id org

theorem promiseCreate_keep {org : Origin} (now : Nat) (req : PromiseCreateReq) : Keep org (Concrete.promiseCreate req now org).2 := by
  unfold Concrete.promiseCreate
  split
  · exact Keep.id org
  · rename_i hf
    dsimp only
    split
    · split
      · exact Keep.set (KeepDoc.refl org) (type_of_none hf (by rfl)) objarm
      · exact Keep.set (KeepDoc.refl org) (type_of_none hf (by rfl)) objarm
    · exact Keep.set (KeepDoc.refl org) (type_of_none hf (by rfl)) noarm

theorem promiseSettle_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : PromiseSettleReq) : Keep org (Concrete.promiseSettle req now org).2 := by
  unfold Concrete.promiseSettle
  split
  · exact Keep.id org
  · split
    · exact Keep.id org
    · rename_i hf
      split
      · exact Keep.set (KeepDoc.refl org) (type_of_get hnd hf (by rfl) (by rfl)) noarm
      · exact Keep.id org

theorem promiseRegisterCallback_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : PromiseRegisterCallbackReq) :
    Keep org (Concrete.promiseRegisterCallback req now org).2 := by
  unfold Concrete.promiseRegisterCallback
  split
  · exact Keep.id org
  · split
    · exact Keep.id org
    · exact Keep.id org
    · rename_i hA _
      split
      · exact Keep.id org
      · split
        · exact Keep.set (KeepDoc.refl org) (type_of_get hnd hA (by rfl) (by exact addCallback_type _ _)) noarm
        · exact Keep.id org

theorem promiseRegisterListener_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : PromiseRegisterListenerReq) :
    Keep org (Concrete.promiseRegisterListener req now org).2 := by
  unfold Concrete.promiseRegisterListener
  split
  · exact Keep.id org
  · rename_i hf
    split
    · exact Keep.id org
    · split
      · exact Keep.set (KeepDoc.refl org) (type_of_get hnd hf (by rfl) (by exact addListener_type _ _)) noarm
      · exact Keep.id org

theorem taskGet_keep {org : Origin} (now : Nat) (req : TaskGetReq) : Keep org (Concrete.taskGet req now org).2 := by
  unfold Concrete.taskGet
  split <;> exact Keep.id org

theorem taskCreate_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : TaskCreateReq) : Keep org (Concrete.taskCreate req now org).2 := by
  unfold Concrete.taskCreate
  dsimp only
  split
  · exact Keep.id org
  · split
    · rename_i hf
      split
      · exact Keep.set (KeepDoc.refl org) (type_of_none hf (by rfl)) objarm
      · exact Keep.set (KeepDoc.refl org) (type_of_none hf (by rfl)) noarm
    · rename_i hf
      split
      · exact Keep.id org
      · split
        · exact Keep.id org
        · split
          · exact Keep.id org
          · split
            · exact Keep.set (KeepDoc.refl org) (type_of_get hnd hf (by rfl) (by rfl)) taskarm
            · exact Keep.id org

theorem taskAcquire_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : TaskAcquireReq) : Keep org (Concrete.taskAcquire req now org).2 := by
  unfold Concrete.taskAcquire
  cases hf : org.get req.id now with
  | none => exact Keep.id org
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Keep.id org
      | some t =>
          simp only [Option.map_some]
          split
          · exact Keep.id org
          · exact Keep.set (KeepDoc.refl org) (type_of_get hnd hf (by rfl) (by rfl)) taskarm

theorem taskFence_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : TaskFenceReq) : Keep org (Concrete.taskFence req now org).2 := by
  unfold Concrete.taskFence
  split
  · exact Keep.id org
  · cases hf : org.get req.id now with
    | none => exact Keep.id org
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact Keep.id org
        | some t =>
            simp only [Option.map_some]
            split
            · exact Keep.id org
            · split
              · exact promiseCreate_keep now _
              · exact promiseSettle_keep hnd now _

theorem hbStep_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (pid : String) : ∀ (refs : List TaskRef) (c : Commands),
    (∀ t ∈ c.arm, t.kind ≠ .promiseTimeout) → KeepDoc org c.org →
    (∀ t ∈ (refs.foldl (hbStep now org pid) c).arm, t.kind ≠ .promiseTimeout) ∧
      KeepDoc org (refs.foldl (hbStep now org pid) c).org
  | [], _, ha, hd => ⟨ha, hd⟩
  | ref :: refs, c, ha, hd => by
      rw [List.foldl_cons]
      refine hbStep_keep hnd now pid refs _ ?_ ?_
      · unfold hbStep
        cases hf : org.get ref.id now with
        | none => exact ha
        | some o =>
            simp only [Option.bind_some]
            cases o.task with
            | none => exact ha
            | some t =>
                simp only [Option.map_some]
                split
                · intro tm htm
                  simp only [List.mem_append] at htm
                  rcases htm with htm | htm
                  · exact ha tm htm
                  · split at htm
                    · simp at htm
                    · exact task_timers_kind htm
                · exact ha
      · unfold hbStep
        cases hf : org.get ref.id now with
        | none => exact hd
        | some o =>
            simp only [Option.bind_some]
            cases o.task with
            | none => exact hd
            | some t =>
                simp only [Option.map_some]
                split
                · exact hd.set (type_of_get hnd hf (by rfl) (by rfl))
                · exact hd

theorem taskHeartbeat_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : TaskHeartbeatReq) : Keep org (Concrete.taskHeartbeat req now org).2 := by
  rw [taskHeartbeat_eq]
  obtain ⟨ha, hd⟩ := hbStep_keep hnd now req.pid req.tasks { org } (fun t ht => absurd ht List.not_mem_nil)
    (KeepDoc.refl org)
  exact ⟨fun t ht hk => absurd hk (ha t ht), hd⟩

theorem regStep_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (awaiter : Ident) : ∀ (ids : List Ident) (d : Origin), KeepDoc org d →
    KeepDoc org ((ids.map (org.get · now)).foldl (regStep awaiter) d)
  | [], _, hd => hd
  | id :: ids, d, hd => by
      simp only [List.map_cons, List.foldl_cons]
      refine regStep_keep hnd now awaiter ids _ ?_
      unfold regStep
      cases hf : org.get id now with
      | none => exact hd
      | some oa => exact hd.set (type_of_get hnd hf (by rfl) (by exact addCallback_type _ _))

theorem taskSuspend_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : TaskSuspendReq) : Keep org (Concrete.taskSuspend req now org).2 := by
  rw [taskSuspend_eq]
  dsimp only
  split
  · exact Keep.id org
  · cases hf : org.get req.id now with
    | none => exact Keep.id org
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact Keep.id org
        | some t =>
            simp only [Option.map_some]
            split
            · exact Keep.id org
            · split
              · exact Keep.id org
              · split
                · exact Keep.set (KeepDoc.refl org) (type_of_get hnd hf (by rfl) (by rfl)) noarm
                · exact Keep.set (regStep_keep hnd now req.id _ org (KeepDoc.refl org))
                    (type_of_get hnd hf (by rfl) (by rfl)) noarm

theorem taskFulfill_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : TaskFulfillReq) : Keep org (Concrete.taskFulfill req now org).2 := by
  unfold Concrete.taskFulfill
  split
  · exact Keep.id org
  · cases hf : org.get req.id now with
    | none => exact Keep.id org
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact Keep.id org
        | some t =>
            simp only [Option.map_some]
            split
            · exact Keep.id org
            · exact Keep.set (KeepDoc.refl org) (type_of_get hnd hf (by rfl) (by rfl)) noarm

theorem taskRelease_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : TaskReleaseReq) : Keep org (Concrete.taskRelease req now org).2 := by
  unfold Concrete.taskRelease
  cases hf : org.get req.id now with
  | none => exact Keep.id org
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Keep.id org
      | some t =>
          simp only [Option.map_some]
          split
          · exact Keep.id org
          · exact Keep.set (KeepDoc.refl org) (type_of_get hnd hf (by rfl) (by rfl)) taskarm

theorem taskHalt_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : TaskHaltReq) : Keep org (Concrete.taskHalt req now org).2 := by
  unfold Concrete.taskHalt
  cases hf : org.get req.id now with
  | none => exact Keep.id org
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Keep.id org
      | some t =>
          simp only [Option.map_some]
          split
          · exact Keep.id org
          · split
            · exact Keep.id org
            · exact Keep.set (KeepDoc.refl org) (type_of_get hnd hf (by rfl) (by rfl)) noarm

theorem taskContinue_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : TaskContinueReq) : Keep org (Concrete.taskContinue req now org).2 := by
  unfold Concrete.taskContinue
  cases hf : org.get req.id now with
  | none => exact Keep.id org
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Keep.id org
      | some t =>
          simp only [Option.map_some]
          split
          · exact Keep.id org
          · exact Keep.set (KeepDoc.refl org) (type_of_get hnd hf (by rfl) (by rfl)) taskarm

theorem handleExternal_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (req : Request) : Keep org (Concrete.handleExternal req now org).2 := by
  cases req with
  | promiseGet r => exact promiseGet_keep now r
  | promiseCreate r => exact promiseCreate_keep now r
  | promiseSettle r => exact promiseSettle_keep hnd now r
  | promiseRegisterCallback r => exact promiseRegisterCallback_keep hnd now r
  | promiseRegisterListener r => exact promiseRegisterListener_keep hnd now r
  | promiseSearch _ => exact Keep.id org
  | scheduleGet _ => exact Keep.id org
  | scheduleCreate _ => exact Keep.id org
  | scheduleDelete _ => exact Keep.id org
  | scheduleSearch _ => exact Keep.id org
  | taskGet r => exact taskGet_keep now r
  | taskCreate r => exact taskCreate_keep hnd now r
  | taskAcquire r => exact taskAcquire_keep hnd now r
  | taskFence r => exact taskFence_keep hnd now r
  | taskHeartbeat r => exact taskHeartbeat_keep hnd now r
  | taskSuspend r => exact taskSuspend_keep hnd now r
  | taskFulfill r => exact taskFulfill_keep hnd now r
  | taskRelease r => exact taskRelease_keep hnd now r
  | taskHalt r => exact taskHalt_keep hnd now r
  | taskContinue r => exact taskContinue_keep hnd now r
  | taskSearch _ => exact Keep.id org

theorem g1_type (now : Nat) (o : Object) : (g1 now o).promise.type = o.promise.type := by
  unfold g1 Concrete.processPromiseTimeout
  split
  · exact project_type _ _
  · rfl

theorem g2_type (now : Nat) (o : Object) : (g2 now o).promise.type = o.promise.type := by
  simp only [g2, listenerObj, Concrete.processListener]
  split
  · simp only [Option.map_some, Option.getD_some]
    exact project_type _ _
  · rfl

theorem g3_type (now : Nat) (org : Origin) (o : Object) : (g3 now org o).promise.type = o.promise.type := by
  simp only [g3, Concrete.processCallback]
  split
  · simp only [Option.getD_some]
    split <;> exact project_type _ _
  · rfl

theorem g4_type (now : Nat) (o : Object) : (g4 now o).promise.type = o.promise.type := by
  simp only [g4, Concrete.processLeaseTimeout]
  split <;> (try split) <;> first | rfl | exact project_type _ _

theorem g5_type (now : Nat) (o : Object) : (g5 now o).promise.type = o.promise.type := by
  simp only [g5, retryObj, Concrete.processRetryTimeout]
  split <;> (try split) <;> first | rfl | (simp only [Option.map_some, Option.getD_some]; exact project_type _ _)

theorem g5_id (now : Nat) (o : Object) : (g5 now o).id = o.id := by
  simp only [g5, retryObj, Concrete.processRetryTimeout]
  split <;> (try split) <;> rfl

theorem sweepObject_id (now : Nat) (org : Origin) (o : Object) : (Concrete.sweepObject now org o).obj.id = o.id := by
  rw [sweepObject_eq]
  show (g5 now (g4 now (g3 now org (g2 now (g1 now o))))).id = o.id
  rw [g5_id, g4_id, g3_id, g2_id, g1_id]

theorem sweepObject_type (now : Nat) (org : Origin) (o : Object) :
    (Concrete.sweepObject now org o).obj.promise.type = o.promise.type := by
  rw [sweepObject_eq]
  show (g5 now (g4 now (g3 now org (g2 now (g1 now o))))).promise.type = o.promise.type
  rw [g5_type, g4_type, g3_type, g2_type, g1_type]

theorem sweep_objects (now : Nat) (org : Origin) :
    (Concrete.sweep now org).org.objects = org.objects.map fun o => (Concrete.sweepObject now org o).obj := by
  simp only [Concrete.sweep, List.map_map]
  rfl

theorem sweep_nodup (now : Nat) {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) :
    ((Concrete.sweep now org).org.objects.map (·.id)).Nodup := by
  rw [sweep_objects, ids_map (fun o => sweepObject_id now org o)]
  exact hnd

theorem sweep_keep (now : Nat) (org : Origin) : Keep org (Concrete.sweep now org) := by
  refine ⟨fun t ht hk => ?_, fun o ho => ?_⟩
  · have ht' : t ∈ ((org.objects.map fun o => (Concrete.sweepObject now org o).obj).flatMap (·.timers)) := by
      have := (List.mem_filter.1 ht).1
      simpa [Concrete.sweep, List.map_map] using this
    obtain ⟨x, hx, htx⟩ := List.mem_flatMap.1 ht'
    obtain ⟨hi, hty⟩ := timers_kind htx hk
    refine ⟨x, ?_, hi.symm, hty⟩
    rw [sweep_objects]
    exact hx
  · refine ⟨(Concrete.sweepObject now org o).obj, ?_, sweepObject_id now org o, sweepObject_type now org o⟩
    rw [sweep_objects]
    exact List.mem_map_of_mem ho

theorem handle_keep {org : Origin} (hnd : (org.objects.map (·.id)).Nodup) (now : Nat) (ev : Concrete.Event) : Keep org (Concrete.handle ev now org).2 := by
  cases ev with
  | external req =>
      show Keep org ((Concrete.sweep now org).merge (Concrete.handleExternal req now (Concrete.sweep now org).org).2)
      exact (sweep_keep now org).merge (handleExternal_keep (sweep_nodup now hnd) now req)
  | internal _ => exact sweep_keep now org
  | stutter => exact Keep.id org

theorem applyAll_blob_source {H : Concrete.Hasher} :
    ∀ (es : List (Concrete.Effect H)) (s : Concrete.State) (p : Path),
      ((Concrete.applyAll s es).1.blob? p).isSome = true →
      (s.blob? p).isSome = true ∨ ∃ b c, Concrete.Effect.put p b c ∈ es
  | [], _, _, h => Or.inl h
  | e :: es, s, p, h => by
      simp only [Concrete.applyAll] at h
      cases he : e.apply s with
      | none =>
          rw [he] at h
          simp only at h
          exact Or.inl h
      | some s1 =>
          rw [he] at h
          simp only at h
          rcases applyAll_blob_source es s1 p h with h1 | ⟨b, c, hm⟩
          · cases e with
            | put q b c =>
                by_cases hpq : p = q
                · subst hpq
                  exact Or.inr ⟨b, c, List.mem_cons_self ..⟩
                · rw [Concrete.blob?_put_other he hpq] at h1
                  exact Or.inl h1
            | del q =>
                simp only [Concrete.Effect.apply, Option.some.injEq] at he
                subst he
                simp only [blob?_eq, blobIn_del] at h1
                split at h1
                · simp at h1
                · exact Or.inl h1
            | send a m =>
                simp only [Concrete.Effect.apply, Option.some.injEq] at he
                subst he
                exact Or.inl h1
          · exact Or.inr ⟨b, c, List.mem_cons_of_mem _ hm⟩

theorem arm_of_put {H : Concrete.Hasher} {name : String} {cond : Concrete.Cond H} {c : Commands} {t : Timer}
    {b : Blob} {cd : Concrete.Cond H} (h : Concrete.Effect.put (.timer t) b cd ∈ c.effects name cond) :
    t ∈ c.arm := by
  simp only [Concrete.Commands.effects, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ((⟨t', ht', heq⟩ | heq) | ⟨_, _, heq⟩) | ⟨⟨a, m⟩, _, heq⟩ <;> cases heq
  exact ht'

theorem Armed.run (H : Concrete.Hasher) (name : String) (c : Commands) (s : Concrete.State)
    (hs : Armed s) (hk : Keep (s.origin name) c) (horig : ∀ o ∈ c.org.objects, o.id.origin = name) :
    Armed (Concrete.applyAll s (c.effects name (Concrete.Cond.of H (s.blob? (.origin name))))).1 := by
  obtain ⟨h1, h2, -, -, -⟩ := run_state H name c s
  intro t ht hk'
  have hname : (Concrete.applyAll s (c.effects name (Concrete.Cond.of H (s.blob? (.origin name))))).1.origin name
      = c.org := by
    simp only [State.origin_eq, h1, originOf?]
  rcases applyAll_blob_source _ s (.timer t) ht with hold | ⟨b, cd, hm⟩
  · obtain ⟨o, ho, hoi, hot⟩ := hs t hold hk'
    by_cases e : t.id.origin = name
    · rw [e] at ho ⊢
      rw [hname]
      obtain ⟨o', ho', hi, hty⟩ := hk.doc o ho
      exact ⟨o', ho', hi.trans hoi, fun h => hot (hty.symm.trans h)⟩
    · rw [State.origin_eq, h2 _ e, ← State.origin_eq s t.id.origin]
      exact ⟨o, ho, hoi, hot⟩
  · obtain ⟨o, ho, hoi, hot⟩ := hk.arm t (arm_of_put hm) hk'
    have e : t.id.origin = name := by rw [← hoi]; exact horig o ho
    rw [e, hname]
    exact ⟨o, ho, hoi, hot⟩

theorem Armed.step (H : Concrete.Hasher) (ev : Concrete.Event) (now : Nat) {s : Concrete.State}
    (inv : Inv s) (inv' : Inv (Concrete.step H ev now s).2) (hs : Armed s) :
    Armed (Concrete.step H ev now s).2 := by
  cases ev with
  | external req =>
      cases ho : req.origin? with
      | none =>
          simp only [Concrete.step, ho]
          exact hs
      | some name =>
          have hst : (Concrete.step H (.external req) now s).2 =
              (Concrete.run H name (fun org => Concrete.handle (.external req) now org) s).2.1 := by
            simp only [Concrete.step, ho]
          rw [hst] at inv' ⊢
          rw [run_snd] at inv' ⊢
          refine Armed.run H name _ s hs (handle_keep (inv.origin_props name).2.1 now _) ?_
          have := (inv'.origin_props name).1
          simpa only [State.origin_eq, (run_state H name _ s).1, originOf?] using this
  | internal t =>
      by_cases hl : (s.blob? (.timer t)).isSome = true ∧ t.deadline ≤ now
      · have hst : (Concrete.step H (.internal t) now s).2 =
            (Concrete.run H t.id.origin (fun org => Concrete.handle (.internal t) now org) s).2.1 := by
          simp only [Concrete.step, if_pos hl]
        rw [hst] at inv' ⊢
        rw [run_snd] at inv' ⊢
        refine Armed.run H t.id.origin _ s hs (handle_keep (inv.origin_props t.id.origin).2.1 now _) ?_
        have := (inv'.origin_props t.id.origin).1
        simpa only [State.origin_eq, (run_state H t.id.origin _ s).1, originOf?] using this
      · simp only [Concrete.step, if_neg hl]
        exact hs
  | stutter => exact hs

theorem armed (H : Concrete.Hasher) (tr : Concrete.Trace) (valid : Concrete.Valid H tr)
    (init : (tr 0).state = Concrete.State.init) : ∀ n, Armed (tr n).state
  | 0 => by rw [init]; exact Armed.init
  | n + 1 => by
      have inv := (invariant H tr valid init n).1
      have inv' := (invariant H tr valid init (n + 1)).1
      rw [valid.state n] at inv' ⊢
      exact Armed.step H _ _ inv inv' (armed H tr valid init n)

end Refinement
