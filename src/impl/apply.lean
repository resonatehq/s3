import impl.frame

namespace Apply

open ServerModel AbstractModel

abbrev Lookup := Ident → Option Object

def lookup (s : ServerState) : Lookup := fun j => s.objects.find? (·.id == j)

theorem Object.withPromise_id (id : Ident) (p : PromiseObject) (x : Option Object)
    (hx : ∀ ob, x = some ob → ob.id = id) : (Object.withPromise id p x).id = id := by
  cases x with
  | none => rfl
  | some ob => simpa [Object.withPromise] using hx ob rfl

theorem find?_id (s : ServerState) (id : Ident) :
    ∀ ob, s.objects.find? (·.id == id) = some ob → ob.id = id := fun ob h => by
  simpa using List.find?_some h

def applyFind (e : Effect) (lk : Lookup) : Lookup := fun j =>
  match e with
  | .setPromise id p => if j = id then some (Object.withPromise id p (lk id)) else lk j
  | .setTask id t    => (lk j).map fun ob => if ob.id == id then { ob with task := some t } else ob
  | _                => lk j

def lookupAfter : List Effect → Lookup → Lookup
  | [],      lk => lk
  | e :: es, lk => lookupAfter es (applyFind e lk)

theorem lookupAfter_append (a b : List Effect) (lk : Lookup) :
    lookupAfter (a ++ b) lk = lookupAfter b (lookupAfter a lk) := by
  induction a generalizing lk with
  | nil => rfl
  | cons e es ih => simp only [List.cons_append, lookupAfter, ih]

theorem lookup_apply (s : ServerState) (e : Effect) :
    lookup (e.apply s) = applyFind e (lookup s) := by
  funext j
  cases e with
  | setPromise id p =>
    simp only [lookup, Effect.apply, applyFind]
    by_cases hj : j = id
    · subst hj
      rw [List.find?_cons_of_pos (by simp [Object.withPromise_id _ _ _ (find?_id s j)])]
      simp
    · rw [List.find?_cons_of_neg (by simp [Object.withPromise_id _ _ _ (find?_id s id), Ne.symm hj])]
      rw [List.find?_filter]
      simp only [hj, ↓reduceIte]
      congr 1
      funext a
      by_cases ha : a.id = j
      · subst ha; simp [hj]
      · simp [ha]
  | setTask id t =>
    simp only [lookup, Effect.apply, applyFind, List.find?_map]
    congr 1
    congr 1
    funext a
    simp only [Function.comp]
    split <;> rfl
  | setSchedule c => rfl
  | delSchedule i => rfl
  | setMessage a m => rfl

theorem lookup_applyAll (s : ServerState) (fx : List Effect) :
    lookup (applyAll s fx) = lookupAfter fx (lookup s) := by
  induction fx generalizing s with
  | nil => rfl
  | cons e es ih => simp only [applyAll, lookupAfter, ih, lookup_apply]

def Lookup.wf (lk : Lookup) : Prop := ∀ j ob, lk j = some ob → ob.id = j

theorem lookup_wf (s : ServerState) : (lookup s).wf := by
  intro j ob h
  have := List.find?_some h
  simpa using this

theorem applyFind_wf {lk : Lookup} (hwf : lk.wf) (e : Effect) : (applyFind e lk).wf := by
  intro j ob h
  cases e with
  | setPromise id p =>
    simp only [applyFind] at h
    split at h
    · rename_i hj
      subst hj
      cases h; exact Object.withPromise_id _ _ _ (fun ob' h' => hwf _ ob' h')
    · exact hwf j ob h
  | setTask id t =>
    simp only [applyFind, Option.map_eq_some_iff] at h
    obtain ⟨ob', h1, h2⟩ := h
    have := hwf j ob' h1
    subst h2
    split <;> simpa
  | setSchedule c => exact hwf j ob h
  | delSchedule i => exact hwf j ob h
  | setMessage a m => exact hwf j ob h

theorem lookupAfter_wf {lk : Lookup} (hwf : lk.wf) (fx : List Effect) : (lookupAfter fx lk).wf := by
  induction fx generalizing lk with
  | nil => exact hwf
  | cons e es ih => exact ih (applyFind_wf hwf e)

def Agree (o : String) (lk lk' : Lookup) : Prop := ∀ j, j.origin = o → lk j = lk' j

theorem applyFind_congr {o : String} {lk lk' : Lookup} (h : Agree o lk lk') (e : Effect) :
    Agree o (applyFind e lk) (applyFind e lk') := by
  intro j hj
  cases e with
  | setPromise id p =>
    simp only [applyFind]
    split
    · rename_i hji; subst hji; rw [h j hj]
    · exact h j hj
  | setTask id t => simp only [applyFind]; rw [h j hj]
  | setSchedule c => exact h j hj
  | delSchedule i => exact h j hj
  | setMessage a m => exact h j hj

theorem lookupAfter_congr {o : String} {lk lk' : Lookup} (h : Agree o lk lk') (fx : List Effect) :
    Agree o (lookupAfter fx lk) (lookupAfter fx lk') := by
  induction fx generalizing lk lk' with
  | nil => exact h
  | cons e es ih => exact ih (applyFind_congr h e)

theorem applyFind_frame {o : String} {lk : Lookup} (hwf : lk.wf) {e : Effect}
    (hloc : Frame.Effect.Local o e) : ∀ j, j.origin ≠ o → applyFind e lk j = lk j := by
  intro j hj
  cases e with
  | setPromise id p =>
    simp only [applyFind]
    split
    · rename_i hji; subst hji; exact absurd hloc hj
    · rfl
  | setTask id t =>
    simp only [applyFind]
    cases hk : lk j with
    | none => rfl
    | some ob =>
      have hid := hwf j ob hk
      simp only [Option.map_some]
      have : (ob.id == id) = false := by
        rw [hid]
        cases hh : j == id
        · rfl
        · exact absurd (hloc ▸ (eq_of_beq hh) ▸ rfl) hj
      simp [this]
  | setSchedule c => rfl
  | delSchedule i => rfl
  | setMessage a m => rfl

theorem lookupAfter_frame {o : String} {lk : Lookup} (hwf : lk.wf) {fx : List Effect}
    (hloc : ∀ e ∈ fx, Frame.Effect.Local o e) : ∀ j, j.origin ≠ o → lookupAfter fx lk j = lk j := by
  induction fx generalizing lk with
  | nil => intros; rfl
  | cons e es ih =>
    intro j hj
    simp only [lookupAfter]
    rw [ih (applyFind_wf hwf e) (fun e' he' => hloc e' (List.mem_cons_of_mem _ he')) j hj]
    exact applyFind_frame hwf (hloc e (List.mem_cons_self ..)) j hj

theorem origins_apply {o : String} {s : ServerState} {e : Effect}
    (hloc : Frame.Effect.Local o e) (h : ∀ ob ∈ s.objects, ob.id.origin = o) :
    ∀ ob ∈ (e.apply s).objects, ob.id.origin = o := by
  intro ob hob
  cases e with
  | setPromise id p =>
    simp only [Effect.apply, List.mem_cons] at hob
    rcases hob with rfl | hob
    · rw [Object.withPromise_id _ _ _ (find?_id s id)]; exact hloc
    · exact h ob (List.mem_filter.mp hob).1
  | setTask id t =>
    simp only [Effect.apply, List.mem_map] at hob
    obtain ⟨ob', hob', rfl⟩ := hob
    have := h ob' hob'
    split <;> simpa
  | setSchedule c => exact h ob hob
  | delSchedule i => exact h ob hob
  | setMessage a m => exact h ob hob

theorem origins_applyAll {o : String} {s : ServerState} {fx : List Effect}
    (hloc : ∀ e ∈ fx, Frame.Effect.Local o e) (h : ∀ ob ∈ s.objects, ob.id.origin = o) :
    ∀ ob ∈ (applyAll s fx).objects, ob.id.origin = o := by
  induction fx generalizing s with
  | nil => exact h
  | cons e es ih =>
    exact ih (fun e' he' => hloc e' (List.mem_cons_of_mem _ he'))
      (origins_apply (hloc e (List.mem_cons_self ..)) h)

def sendsFold : List OutboxEntry → List (String × Message) → List OutboxEntry
  | ob, []             => ob
  | ob, (a, m) :: rest =>
      let entry := OutboxEntry.mk a m
      sendsFold (entry :: ob.filter (fun e => e.key != entry.key)) rest

theorem sendsFold_append (ob : List OutboxEntry) (a b : List (String × Message)) :
    sendsFold ob (a ++ b) = sendsFold (sendsFold ob a) b := by
  induction a generalizing ob with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨addr, m⟩
    simp only [List.cons_append, sendsFold, ih]

theorem outbox_apply (s : ServerState) (e : Effect) :
    (e.apply s).outbox = sendsFold s.outbox (Impl.sendsOf [e]) := by
  cases e <;> rfl

theorem outbox_applyAll (s : ServerState) (fx : List Effect) :
    (applyAll s fx).outbox = sendsFold s.outbox (Impl.sendsOf fx) := by
  induction fx generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [applyAll, ih, outbox_apply]
    cases e <;> rfl

theorem schedules_apply {o : String} (s : ServerState) {e : Effect}
    (hloc : Frame.Effect.Local o e) : (e.apply s).schedules = s.schedules := by
  cases e with
  | setSchedule c => exact absurd hloc id
  | delSchedule i => exact absurd hloc id
  | _ => rfl

theorem schedules_applyAll {o : String} (s : ServerState) {fx : List Effect}
    (hloc : ∀ e ∈ fx, Frame.Effect.Local o e) : (applyAll s fx).schedules = s.schedules := by
  induction fx generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [applyAll]
    rw [ih _ (fun e' he' => hloc e' (List.mem_cons_of_mem _ he')),
        schedules_apply s (hloc e (List.mem_cons_self ..))]

end Apply
