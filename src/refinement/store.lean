import impl.system

namespace Concrete

open Protocol (Message OutboxEntry Request Response)

variable {H : Hasher}

theorem Cond.of_holds (b : Option Blob) : (Cond.of H b).holds b = true := by
  cases b <;> simp [Cond.of, Cond.holds]

theorem Cond.of_holds_iff (a : Blob) (b : Option Blob) :
    (Cond.of H (some a)).holds b = true ↔ b = some a := by
  cases b with
  | none =>
      simp [Cond.of, Cond.holds]
  | some b =>
      simp only [Cond.of, Cond.holds, Option.map_some, beq_iff_eq, Option.some.injEq]
      exact ⟨fun h => H.inj b a h, fun h => congrArg H.hash h⟩

def Effect.unconditional : Effect H → Bool
  | .put _ _ .any =>
      true
  | .put _ _ _ =>
      false
  | .del _ =>
      true
  | .send _ _ =>
      true

theorem apply_unconditional {e : Effect H} (h : e.unconditional = true) (s : State) :
    ∃ s', e.apply s = some s' := by
  cases e with
  | put p b c =>
      cases c <;> simp [Effect.unconditional] at h
      exact ⟨{ s with bucket := (p, b) :: s.bucket.filter (·.1 != p) },
             by simp [Effect.apply, Cond.holds]⟩
  | del p =>
      exact ⟨_, rfl⟩
  | send a m =>
      exact ⟨_, rfl⟩

theorem applyAll_unconditional :
    ∀ (es : List (Effect H)) (s : State), (∀ e ∈ es, e.unconditional = true) →
      (applyAll s es).2 = true
  | [], _, _ =>
      rfl
  | e :: es, s, h => by
      obtain ⟨s', hs⟩ := apply_unconditional (h e (List.mem_cons_self ..)) s
      simp only [applyAll, hs]
      exact applyAll_unconditional es s' (fun e he => h e (List.mem_cons_of_mem _ he))

theorem applyAll_append (a b : List (Effect H)) (s : State) :
    applyAll s (a ++ b) =
      if (applyAll s a).2 then applyAll (applyAll s a).1 b else applyAll s a := by
  induction a generalizing s with
  | nil =>
      simp [applyAll]
  | cons e es ih =>
      simp only [List.cons_append, applyAll]
      cases e.apply s with
      | some s' =>
          exact ih s'
      | none =>
          simp

theorem blob?_put_other {s : State} {p q : Path} {b : Blob} {c : Cond H} {s' : State}
    (h : (Effect.put p b c).apply s = some s') (hne : q ≠ p) :
    s'.blob? q = s.blob? q := by
  simp only [Effect.apply] at h
  split at h
  · cases h
    have hq : ((p, b).1 == q) = false := by simpa using Ne.symm hne
    simp only [State.blob?, List.find?_cons, hq]
    congr 1
    induction s.bucket with
    | nil =>
        rfl
    | cons x xs ih =>
        by_cases hx : x.1 = q
        · have h1 : (x.1 == q) = true := by simpa using hx
          have h2 : (x.1 != p) = true := by simpa [hx] using hne
          simp [h1, h2]
        · have h1 : (x.1 == q) = false := by simpa using hx
          by_cases hp : x.1 = p
          · have h2 : (x.1 != p) = false := by simpa using hp
            simp [h1, h2, ih]
          · have h2 : (x.1 != p) = true := by simpa using hp
            simp [h1, h2, ih]
  · cases h

theorem applyAll_arm (name : String) :
    ∀ (ts : List Timer) (s : State),
      (applyAll s (ts.map fun t => Effect.put (H := H) (.timer t) .timer .any)).2 = true ∧
      (applyAll s (ts.map fun t => Effect.put (H := H) (.timer t) .timer .any)).1.blob?
        (.origin name) = s.blob? (.origin name)
  | [], _ =>
      ⟨rfl, rfl⟩
  | t :: ts, s => by
      obtain ⟨s', hs⟩ := apply_unconditional (e := Effect.put (H := H) (.timer t) .timer .any) rfl s
      simp only [List.map_cons, applyAll, hs]
      obtain ⟨h1, h2⟩ := applyAll_arm name ts s'
      exact ⟨h1, by rw [h2, blob?_put_other hs (by simp)]⟩

theorem applyAll_accepted (s : State) (name : String) (c : Commands) :
    (applyAll s (c.effects name (Cond.of H (s.blob? (.origin name))))).2 = true := by
  unfold Commands.effects
  obtain ⟨h1, h2⟩ := applyAll_arm (H := H) name c.arm s
  simp only [List.append_assoc, List.singleton_append]
  rw [applyAll_append, if_pos h1]
  have key : ∀ s1 : State,
      (Cond.of H (s.blob? (.origin name))).holds (s1.blob? (.origin name)) = true →
      (applyAll s1 (Effect.put (.origin name) (.origin c.org) (Cond.of H (s.blob? (.origin name))) ::
        (c.del.map (fun t => Effect.del (H := H) (.timer t)) ++
         c.send.map (fun (a, m) => Effect.send (H := H) a m)))).2 = true := by
    intro s1 hh
    simp only [applyAll, Effect.apply, hh, ↓reduceIte]
    apply applyAll_unconditional
    intro e he
    simp only [List.mem_append, List.mem_map] at he
    rcases he with ⟨_, _, rfl⟩ | ⟨⟨a, m⟩, _, rfl⟩ <;> rfl
  exact key _ (by rw [h2]; exact Cond.of_holds _)

theorem run_accepted (name : String) (f : Origin → α × Commands) (s : State) :
    (run H name f s).2.2 = true := by
  simp only [run, applyAll_accepted]

end Concrete
