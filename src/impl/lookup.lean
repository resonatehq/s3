import impl.relation

namespace Refinement

open Protocol (Ident Message OutboxEntry Object PromiseObject TaskObject PromiseState TaskState)
open Concrete (Origin)

theorem bind_apply {α β : Type} (x : Abstract.H α) (f : α → Abstract.H β) (e : Abstract.Env) :
    (x >>= f) e = ((f (x e).1 e).1, (x e).2 ++ (f (x e).1 e).2) := rfl

theorem pure_apply {α : Type} (a : α) (e : Abstract.Env) : (pure a : Abstract.H α) e = (a, []) := rfl

theorem map_apply {α β : Type} (g : α → β) (x : Abstract.H α) (e : Abstract.Env) :
    (g <$> x) e = (g (x e).1, (x e).2) := by
  show (x >>= fun a => pure (g a)) e = _
  simp [bind_apply, pure_apply]

theorem ask_apply (e : Abstract.Env) : Abstract.ask e = (e, []) := rfl

theorem setPromise_apply (id : Ident) (p : PromiseObject) (e : Abstract.Env) :
    Abstract.setPromise id p e = ((), [.setPromise id p]) := rfl

theorem setTask_apply (id : Ident) (t : TaskObject) (e : Abstract.Env) :
    Abstract.setTask id t e = ((), [.setTask id t]) := rfl

theorem setMessage_apply (a : String) (m : Message) (e : Abstract.Env) :
    Abstract.setMessage a m e = ((), [.setMessage a m]) := rfl

def env (S : Abstract.State) : Abstract.Env := { state := S, mat := false }

def find (S : Abstract.State) (id : Ident) : Option Object :=
  S.objects.find? (·.id == id)

def Origin.find (org : Origin) (id : Ident) : Option Object :=
  org.objects.find? (·.id == id)

theorem find_id {S : Abstract.State} {id : Ident} {o : Object} (h : find S id = some o) : o.id = id := by
  have := List.find?_some h
  simpa using this


theorem get_eq (org : Origin) (id : Ident) (now : Nat) :
    org.get id now = (Origin.find org id).map (·.project now) := rfl

theorem getObject_apply (id : Ident) (S : Abstract.State) :
    Abstract.getObject id (env S) = (find S id, []) := rfl

theorem getObject_apply_mat (id : Ident) (S : Abstract.State) :
    Abstract.getObject id { env S with mat := true } = (find S id, []) := rfl

theorem readObject_false (id : Ident) (now : Nat) (S : Abstract.State) :
    Abstract.readObject id now (env S) = ((find S id).map (·.project now), []) := by
  unfold Abstract.readObject
  simp only [bind_apply, getObject_apply]
  cases h : find S id with
  | none => rfl
  | some o => rfl

theorem readTaskObject_false (id : Ident) (now : Nat) (S : Abstract.State) :
    Abstract.readTaskObject id now (env S) =
      ((find S id).bind fun o => if o.task.isSome then some (o.project now) else none, []) := by
  unfold Abstract.readTaskObject
  simp only [bind_apply, getObject_apply]
  cases h : find S id with
  | none => rfl
  | some o =>
      dsimp only
      by_cases ht : o.task.isSome = true
      · simp only [ht, ↓reduceIte, readObject_false, h]
        simp [ht]
      · simp only [ht, Bool.false_eq_true, ↓reduceIte, pure_apply]
        simp [ht]

def materialiseFx (id : Ident) (o o' : Object) : List Abstract.Effect :=
  (if o'.promise.state != o.promise.state then [.setPromise id o'.promise] else [])
  ++ (match o.task, o'.task with
      | some t, some u => if u.state != t.state then [.setTask id u] else []
      | _, _ => [])

theorem materialise_apply (id : Ident) (o o' : Object) (e : Abstract.Env) :
    Abstract.materialise id o o' e = ((), materialiseFx id o o') := by
  unfold Abstract.materialise materialiseFx
  simp only [bind_apply]
  rcases o.task with _ | t <;> rcases o'.task with _ | u <;> dsimp only <;>
    split <;> (try split) <;> simp [pure_apply, setPromise_apply, setTask_apply]

theorem touchObject_apply (id : Ident) (now : Nat) (S : Abstract.State) :
    Abstract.touchObject id now (env S) =
      match find S id with
      | none => (none, [])
      | some o => (some (o.project now), materialiseFx id o (o.project now)) := by
  unfold Abstract.touchObject Abstract.withMat Abstract.readObject
  simp only [bind_apply, getObject_apply_mat]
  cases h : find S id with
  | none => rfl
  | some o =>
      simp [bind_apply, ask_apply, materialise_apply, pure_apply]

theorem touchTaskObject_apply (id : Ident) (now : Nat) (S : Abstract.State) :
    Abstract.touchTaskObject id now (env S) =
      match find S id with
      | none => (none, [])
      | some o =>
          if o.task.isSome then (some (o.project now), materialiseFx id o (o.project now))
          else (none, []) := by
  unfold Abstract.touchTaskObject Abstract.withMat Abstract.readTaskObject
  simp only [bind_apply, getObject_apply_mat]
  cases h : find S id with
  | none => rfl
  | some o =>
      dsimp only
      by_cases ht : o.task.isSome = true
      · simp only [ht, ↓reduceIte]
        unfold Abstract.readObject
        simp [bind_apply, getObject_apply_mat, h, ask_apply, materialise_apply, pure_apply]
      · simp only [ht, Bool.false_eq_true, ↓reduceIte, pure_apply]
        simp

theorem viewTaskObject_apply (id : Ident) (now : Nat) (S : Abstract.State) :
    Abstract.viewTaskObject id now (env S) =
      ((find S id).bind fun o => if o.task.isSome then some (o.project now) else none, []) := by
  unfold Abstract.viewTaskObject Abstract.withMat
  exact readTaskObject_false id now S

theorem run_eq {α : Type} (act : Abstract.H α) (S : Abstract.State) :
    Abstract.run false act S = ((act (env S)).1, Abstract.applyAll S (act (env S)).2) := rfl

theorem withPromise_id (S : Abstract.State) (id : Ident) (p : PromiseObject) :
    (Abstract.Object.withPromise id p (find S id)).id = id := by
  cases h : find S id with
  | none => rfl
  | some o => simpa [Abstract.Object.withPromise] using find_id h

theorem find_setPromise_same (S : Abstract.State) (id : Ident) (p : PromiseObject) :
    find ((Abstract.Effect.setPromise id p).apply S) id =
      some (Abstract.Object.withPromise id p (find S id)) := by
  have h1 : ((Abstract.Object.withPromise id p (find S id)).id == id) = true := by
    simp [withPromise_id]
  simp only [find] at h1 ⊢
  simp only [Abstract.Effect.apply, List.find?_cons, h1]

theorem find?_filter_ne (l : List Object) (id id' : Ident) (h : id' ≠ id) :
    (l.filter (·.id != id)).find? (·.id == id') = l.find? (·.id == id') := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x.id = id'
      · have h1 : (x.id == id') = true := by simpa using hx
        have h2 : (x.id != id) = true := by simpa [hx] using h
        simp [h1, h2]
      · have h1 : (x.id == id') = false := by simpa using hx
        by_cases hp : x.id = id
        · have h2 : (x.id != id) = false := by simpa using hp
          simp [h1, h2, ih]
        · have h2 : (x.id != id) = true := by simpa using hp
          simp [h1, h2, ih]

theorem find_setPromise_other (S : Abstract.State) (id id' : Ident) (p : PromiseObject)
    (h : id' ≠ id) :
    find ((Abstract.Effect.setPromise id p).apply S) id' = find S id' := by
  have h1 : ((Abstract.Object.withPromise id p (find S id)).id == id') = false := by
    rw [withPromise_id]
    simpa using Ne.symm h
  simp only [find] at h1 ⊢
  simp only [Abstract.Effect.apply, List.find?_cons, h1]
  exact find?_filter_ne _ _ _ h

theorem find?_map_id (f : Object → Object) (hf : ∀ o, (f o).id = o.id) (l : List Object) (id : Ident) :
    (l.map f).find? (·.id == id) = (l.find? (·.id == id)).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.find?_cons, hf]
      cases x.id == id <;> simp [ih]

theorem find_setTask (S : Abstract.State) (id id' : Ident) (t : TaskObject) :
    find ((Abstract.Effect.setTask id t).apply S) id' =
      if id' = id then (find S id').map (fun o => { o with task := some t }) else find S id' := by
  simp only [find, Abstract.Effect.apply]
  rw [find?_map_id _ (fun o => by split <;> rfl)]
  cases hf : S.objects.find? (·.id == id') with
  | none => simp
  | some o =>
      have ho : o.id = id' := by simpa using List.find?_some hf
      simp only [Option.map_some]
      by_cases e : id' = id
      · have : (o.id == id) = true := by simp [ho, e]
        simp [this, e]
      · have : (o.id == id) = false := by simp [ho, e]
        simp [this, e]

theorem find_setMessage (S : Abstract.State) (a : String) (m : Message) (id : Ident) :
    find ((Abstract.Effect.setMessage a m).apply S) id = find S id := rfl

theorem write_present {org : Origin} {x : Object} (h : org.objects.any (·.id == x.id) = true) :
    (org.write x).objects = org.objects.map fun o => if o.id == x.id then x else o := by
  simp [Concrete.Origin.write, h]

theorem write_absent {org : Origin} {x : Object} (h : org.objects.any (·.id == x.id) = false) :
    (org.write x).objects = org.objects ++ [x] := by
  simp [Concrete.Origin.write, h]

theorem replace_id (x o : Object) : (if o.id == x.id then x else o).id = o.id := by
  split
  · rename_i e; exact (beq_iff_eq.1 e).symm
  · rfl

theorem find_write_same (org : Origin) (x : Object) :
    Origin.find (org.write x) x.id = some x := by
  unfold Origin.find
  by_cases h : org.objects.any (·.id == x.id) = true
  · rw [write_present h, find?_map_id _ (replace_id x)]
    obtain ⟨y, hy, hyx⟩ := List.any_eq_true.1 h
    cases hf : org.objects.find? (·.id == x.id) with
    | none =>
        rw [List.find?_eq_none] at hf
        exact absurd hyx (hf y hy)
    | some z =>
        have hz : z.id = x.id := by simpa using List.find?_some hf
        simp [hz]
  · have h' := eq_false_of_ne_true h
    rw [write_absent h', List.find?_append]
    have : org.objects.find? (·.id == x.id) = none := by
      rw [List.find?_eq_none]
      intro a ha hp
      exact List.any_eq_false.1 h' a ha hp
    simp [this]

theorem find_write_other (org : Origin) (x : Object) (id : Ident) (h : id ≠ x.id) :
    Origin.find (org.write x) id = Origin.find org id := by
  unfold Origin.find
  by_cases hp : org.objects.any (·.id == x.id) = true
  · rw [write_present hp, find?_map_id _ (replace_id x)]
    cases hf : org.objects.find? (·.id == id) with
    | none => rfl
    | some y =>
        have hy : y.id = id := by simpa using List.find?_some hf
        have : y.id ≠ x.id := fun e => h (hy.symm.trans e)
        simp [this]
  · have hp' := eq_false_of_ne_true hp
    rw [write_absent hp', List.find?_append]
    have : ([x].find? (·.id == id)) = none := by
      have : (x.id == id) = false := by simpa using Ne.symm h
      simp [this]
    rw [this, Option.or_none]

theorem mem_write {org : Origin} {x ob : Object} (hob : ob ∈ (org.write x).objects) :
    ob = x ∨ ob ∈ org.objects := by
  unfold Concrete.Origin.write at hob
  split at hob
  · simp only [List.mem_map] at hob
    obtain ⟨y, hy, rfl⟩ := hob
    split
    · exact Or.inl rfl
    · exact Or.inr hy
  · simp only [List.mem_append, List.mem_singleton] at hob
    rcases hob with hob | rfl
    · exact Or.inr hob
    · exact Or.inl rfl

theorem find_mem {org : Origin} {id : Ident} {o : Object} (h : Origin.find org id = some o) :
    o ∈ org.objects ∧ o.id = id := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

def Local (o : String) (org : Origin) (S : Abstract.State) : Prop :=
  ∀ id, id.origin = o → find S id = Origin.find org id

def Fx (o : String) : List Abstract.Effect → Prop
  | [] => True
  | .setPromise id _ :: fx => id.origin = o ∧ Fx o fx
  | .setTask id _ :: fx => id.origin = o ∧ Fx o fx
  | .setMessage _ _ :: fx => Fx o fx
  | .setSchedule _ :: _ => False
  | .delSchedule _ :: _ => False

theorem Fx_append (o : String) (a b : List Abstract.Effect) : Fx o (a ++ b) ↔ Fx o a ∧ Fx o b := by
  induction a with
  | nil => simp [Fx]
  | cons e es ih =>
      cases e <;> simp [Fx, ih, and_assoc]

def sendsOf : List Abstract.Effect → List (String × Message)
  | [] => []
  | .setMessage a m :: fx => (a, m) :: sendsOf fx
  | _ :: fx => sendsOf fx

theorem sendsOf_append (a b : List Abstract.Effect) : sendsOf (a ++ b) = sendsOf a ++ sendsOf b := by
  induction a with
  | nil => rfl
  | cons e es ih => cases e <;> simp [sendsOf, ih]

def sendsFold (ob : List OutboxEntry) : List (String × Message) → List OutboxEntry
  | [] => ob
  | (a, m) :: rest =>
      let entry := OutboxEntry.mk a m
      sendsFold (entry :: ob.filter (fun e => e.key != entry.key)) rest

theorem sendsFold_append (ob : List OutboxEntry) (a b : List (String × Message)) :
    sendsFold ob (a ++ b) = sendsFold (sendsFold ob a) b := by
  induction a generalizing ob with
  | nil => rfl
  | cons x xs ih => obtain ⟨a, m⟩ := x; simp [sendsFold, ih]

theorem applyAll_append (S : Abstract.State) (a b : List Abstract.Effect) :
    Abstract.applyAll S (a ++ b) = Abstract.applyAll (Abstract.applyAll S a) b := by
  induction a generalizing S with
  | nil => rfl
  | cons e es ih => simp [Abstract.applyAll, ih]

theorem applyAll_outbox (S : Abstract.State) (fx : List Abstract.Effect) :
    (Abstract.applyAll S fx).outbox = sendsFold S.outbox (sendsOf fx) := by
  induction fx generalizing S with
  | nil => rfl
  | cons e es ih =>
      cases e <;> simp [Abstract.applyAll, Abstract.Effect.apply, sendsOf, sendsFold, ih]

theorem applyAll_schedules {o : String} (S : Abstract.State) (fx : List Abstract.Effect) (h : Fx o fx) :
    (Abstract.applyAll S fx).schedules = S.schedules := by
  induction fx generalizing S with
  | nil => rfl
  | cons e es ih =>
      cases e with
      | setPromise i p => simp only [Abstract.applyAll]; rw [ih _ h.2]; rfl
      | setTask i t => simp only [Abstract.applyAll]; rw [ih _ h.2]; rfl
      | setMessage a m => simp only [Abstract.applyAll]; rw [ih _ h]; rfl
      | setSchedule c => simp [Fx] at h
      | delSchedule i => simp [Fx] at h

theorem applyAll_find_other {o : String} (S : Abstract.State) (fx : List Abstract.Effect) (h : Fx o fx)
    (id : Ident) (hid : id.origin ≠ o) :
    find (Abstract.applyAll S fx) id = find S id := by
  induction fx generalizing S with
  | nil => rfl
  | cons e es ih =>
      cases e with
      | setPromise i p =>
          obtain ⟨hi, hfx⟩ := h
          simp only [Abstract.applyAll]
          rw [ih _ hfx, find_setPromise_other _ _ _ _ (fun e => hid (by rw [e]; exact hi))]
      | setTask i t =>
          obtain ⟨hi, hfx⟩ := h
          simp only [Abstract.applyAll]
          rw [ih _ hfx, find_setTask, if_neg (fun e => hid (by rw [e]; exact hi))]
      | setMessage a m =>
          simp only [Abstract.applyAll]
          rw [ih _ h, find_setMessage]
      | setSchedule c => simp [Fx] at h
      | delSchedule i => simp [Fx] at h

theorem write_derived {o : String} {org : Origin} {x : Object}
    (h : ∀ ob ∈ org.objects, ob.id.origin = o) (hx : x.id.origin = o) :
    ∀ ob ∈ (org.write x).objects, ob.id.origin = o := by
  intro ob hob
  rcases mem_write hob with rfl | hob
  · exact hx
  · exact h ob hob

theorem nodup_append_single {α : Type} {l : List α} {w : α} (h : l.Nodup) (hw : w ∉ l) :
    (l ++ [w]).Nodup := by
  induction l with
  | nil => exact List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
  | cons x xs ih =>
      have h' := List.nodup_cons.1 h
      simp only [List.mem_cons, not_or] at hw
      refine List.nodup_cons.2 ⟨?_, ih h'.2 hw.2⟩
      intro hm
      rcases List.mem_append.1 hm with hm | hm
      · exact h'.1 hm
      · exact hw.1 (List.mem_singleton.1 hm).symm

theorem write_ids {org : Origin} {x : Object} (h : org.objects.any (·.id == x.id) = true) :
    (org.write x).objects.map (·.id) = org.objects.map (·.id) := by
  rw [write_present h, List.map_map]
  congr 1
  funext o
  exact replace_id x o

theorem write_nodup {org : Origin} {x : Object} (h : (org.objects.map (·.id)).Nodup) :
    ((org.write x).objects.map (·.id)).Nodup := by
  by_cases hp : org.objects.any (·.id == x.id) = true
  · rw [write_ids hp]; exact h
  · have hp' := eq_false_of_ne_true hp
    rw [write_absent hp', List.map_append, List.map_singleton]
    apply nodup_append_single h
    intro hm
    simp only [List.mem_map] at hm
    obtain ⟨y, hy, hyx⟩ := hm
    exact List.any_eq_false.1 hp' y hy (by simp [hyx])

theorem project_id (o : Object) (n : Nat) : (o.project n).id = o.id := rfl

theorem PromiseObject.project_pending (p : PromiseObject) (n : Nat)
    (h : (p.project n).state = .pending) : p.project n = p := by
  unfold PromiseObject.project at h ⊢
  by_cases hc : (p.state == PromiseState.pending) = true ∧ p.timeoutAt ≤ n
  · rw [if_pos hc] at h
    split at h <;> simp at h
  · rw [if_neg hc]

theorem view_pending (t : TaskObject) (p : PromiseObject) (h : p.state = .pending) : t.view p = t := by
  unfold TaskObject.view
  simp [h]

theorem project_pending_id (o : Object) (n : Nat)
    (h : (o.project n).promise.state = .pending) : o.project n = o := by
  have hp : o.promise.project n = o.promise := PromiseObject.project_pending _ _ h
  have hs : o.promise.state = .pending := by rw [← hp]; exact h
  cases o with
  | mk id p t =>
      simp only at hp hs
      simp [Object.project, hp, view_pending _ _ hs]

end Refinement
