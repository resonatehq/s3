import refinement.timers

namespace Refinement

open Concrete (Config Hasher Origin Commands Timer Path Blob Event)
open Protocol (Object)

structure Alike (s t : Concrete.State) : Prop where
  origin : ∀ name, s.origin name = t.origin name
  timer  : ∀ tm : Timer, s.blob? (.timer tm) = t.blob? (.timer tm)
  outbox : s.outbox = t.outbox

theorem Alike.refl (s : Concrete.State) : Alike s s := ⟨fun _ => rfl, fun _ => rfl, rfl⟩

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
      rw [List.filterMap_cons, List.filterMap_cons, h a (List.mem_cons_self ..),
        filterMap_congr' l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

variable {H : Hasher}

theorem arm_timer (tm : Timer) : ∀ (ts : List Timer) (s : Concrete.State),
    (Concrete.applyAll s (ts.map fun t => Concrete.Effect.put (H := H) (.timer t) .timer .any)).1.blob? (.timer tm) =
      if tm ∈ ts then some .timer else s.blob? (.timer tm)
  | [], _ => by simp [Concrete.applyAll]
  | t :: ts, s => by
      have hs : (Concrete.Effect.put (H := H) (Path.timer t) Blob.timer .any).apply s =
          some { s with bucket := (Path.timer t, Blob.timer) :: s.bucket.filter (·.1 != Path.timer t) } := by
        simp [Concrete.Effect.apply, Concrete.Cond.holds]
      simp only [List.map_cons, Concrete.applyAll, hs]
      rw [arm_timer tm ts]
      by_cases hm : tm ∈ ts
      · simp [hm]
      · by_cases he : tm = t
        · subst he
          simp [blob?_eq, blobIn_put]
        · have hne : Path.timer tm ≠ Path.timer t := fun h => he (Path.timer.inj h)
          simp only [List.mem_cons, he, hm, or_self, ↓reduceIte]
          rw [blob?_eq, blobIn_put, if_neg hne]
          rfl

theorem del_timer (tm : Timer) : ∀ (ts : List Timer) (s : Concrete.State),
    (Concrete.applyAll s (ts.map fun t => Concrete.Effect.del (H := H) (.timer t))).1.blob? (.timer tm) =
      if tm ∈ ts then none else s.blob? (.timer tm)
  | [], _ => by simp [Concrete.applyAll]
  | t :: ts, s => by
      simp only [List.map_cons, Concrete.applyAll, Concrete.Effect.apply]
      rw [del_timer tm ts]
      by_cases hm : tm ∈ ts
      · simp [hm]
      · by_cases he : tm = t
        · subst he
          simp [blob?_eq, blobIn_del]
        · have hne : Path.timer tm ≠ Path.timer t := fun h => he (Path.timer.inj h)
          simp only [List.mem_cons, he, hm, or_self, ↓reduceIte]
          rw [blob?_eq, blobIn_del, if_neg hne]
          rfl

theorem write_timer {cfg : Config} {name : String} {parts : List (List Object)} {cond : Concrete.Cond H}
    {objects : List Object} {s s' : Concrete.State} (hp : s.parts name = parts)
    (h : (Concrete.write H cfg name parts cond objects).apply s = some s') (tm : Timer) :
    s'.blob? (.timer tm) = s.blob? (.timer tm) := by
  rw [Concrete.write_apply cfg name parts cond objects hp] at h
  split at h
  · cases h
    rw [blob?_eq, blobIn_put, if_neg (by simp)]
    rfl
  · cases h

theorem timer_after (cfg : Config) (name : String) (c : Commands) (s : Concrete.State) (tm : Timer) :
    (Concrete.applyAll s (c.effects (Concrete.write H cfg name (s.parts name)
      (Concrete.Cond.of H (s.blob? (.origin name))) c.add))).1.blob? (.timer tm) =
      if tm ∈ c.del then none else if tm ∈ c.arm then some .timer else s.blob? (.timer tm) := by
  unfold Commands.effects
  obtain ⟨hA, sameA⟩ := timers_phase (H := H) (c.arm.map fun t => .put (.timer t) .timer .any) s
    (by intro e he; simp only [List.mem_map] at he; obtain ⟨t, _, rfl⟩ := he; trivial)
  have hAt := arm_timer (H := H) tm c.arm s
  obtain ⟨s1, hs1⟩ : ∃ s1, Concrete.applyAll s (c.arm.map fun t => Concrete.Effect.put (H := H) (.timer t) .timer .any) = (s1, true) :=
    ⟨_, Prod.ext rfl hA⟩
  rw [hs1] at sameA hAt
  simp only at sameA hAt
  have hp1 : s1.parts name = s.parts name := by
    unfold Concrete.State.parts; rw [sameA.blob]
  have hhold : (Concrete.Cond.of H (s.blob? (.origin name))).holds (s1.blob? (.origin name)) = true := by
    rw [sameA.blob]; exact Concrete.Cond.of_holds _
  obtain ⟨s2, hs2⟩ : ∃ s2, (Concrete.write H cfg name (s.parts name) (Concrete.Cond.of H (s.blob? (.origin name))) c.add).apply s1 = some s2 :=
    ⟨_, by rw [Concrete.write_apply cfg name _ _ _ hp1, if_pos hhold]⟩
  have h2t := write_timer hp1 hs2 tm
  have hDt := del_timer (H := H) tm c.del s2
  obtain ⟨hD, -⟩ := timers_phase (H := H) (c.del.map fun t => .del (.timer t)) s2
    (by intro e he; simp only [List.mem_map] at he; obtain ⟨t, _, rfl⟩ := he; trivial)
  obtain ⟨s3, hs3⟩ : ∃ s3, Concrete.applyAll s2 (c.del.map fun t => Concrete.Effect.del (H := H) (.timer t)) = (s3, true) :=
    ⟨_, Prod.ext rfl hD⟩
  rw [hs3] at hDt
  simp only at hDt
  obtain ⟨-, hS1, -⟩ := sends_phase (H := H) c.send s3
  simp only [List.append_assoc, List.singleton_append]
  rw [Concrete.applyAll_append, hs1, if_pos rfl, List.cons_append]
  simp only [Concrete.applyAll, hs2]
  rw [Concrete.applyAll_append, hs3, if_pos rfl, blob?_eq, hS1, ← blob?_eq, hDt, h2t, hAt]

theorem run_alike {α : Type} (cfg cfg' : Config) (name : String) (f : Origin → α × Commands)
    {s t : Concrete.State} (h : Alike s t) :
    (Concrete.run H cfg name f s).1 = (Concrete.run H cfg' name f t).1 ∧
    Alike (Concrete.run H cfg name f s).2.1 (Concrete.run H cfg' name f t).2.1 := by
  have horg : s.origin name = t.origin name := h.origin name
  refine ⟨by rw [run_fst, run_fst, horg], ?_⟩
  rw [run_snd, run_snd, horg]
  obtain ⟨h1, h2, h3, -, -, -⟩ := run_state H cfg name (f (t.origin name)).2 s
  obtain ⟨h1', h2', h3', -, -, -⟩ := run_state H cfg' name (f (t.origin name)).2 t
  rw [view_next] at h1 h1'
  refine ⟨fun m => ?_, fun tm => ?_, ?_⟩
  · by_cases hm : m = name
    · subst hm
      rw [h1, h1']
      show ((s.origin m).add _).current = ((t.origin m).add _).current
      rw [horg]
    · rw [State.origin_eq, h2 m hm, State.origin_eq (Concrete.applyAll t _).1, h2' m hm, ← State.origin_eq,
        ← State.origin_eq, h.origin m]
  · rw [timer_after, timer_after, h.timer tm]
  · rw [h3, h3', h.outbox]

theorem step_alike (cfg cfg' : Config) (ev : Event) (now : Nat) {s t : Concrete.State} (h : Alike s t) :
    (Concrete.step H cfg ev now s).1 = (Concrete.step H cfg' ev now t).1 ∧
    Alike (Concrete.step H cfg ev now s).2 (Concrete.step H cfg' ev now t).2 := by
  cases ev with
  | stutter => exact ⟨rfl, h⟩
  | external req =>
      cases ho : req.origin? with
      | none =>
          simp only [Concrete.step, ho]
          exact ⟨trivial, h⟩
      | some name =>
          simp only [Concrete.step, ho]
          obtain ⟨h1, h2⟩ := run_alike (H := H) cfg cfg' name (fun org => Concrete.handle (.external req) now org) h
          have hok := Concrete.run_accepted (H := H) cfg name (fun org => Concrete.handle (.external req) now org) s
          have hok' := Concrete.run_accepted (H := H) cfg' name (fun org => Concrete.handle (.external req) now org) t
          rcases hR : Concrete.run H cfg name (fun org => Concrete.handle (.external req) now org) s with ⟨r, s', ok⟩
          rcases hR' : Concrete.run H cfg' name (fun org => Concrete.handle (.external req) now org) t with ⟨r', t', ok'⟩
          rw [hR, hR'] at h1 h2
          rw [hR] at hok
          rw [hR'] at hok'
          simp only at h1 h2 hok hok'
          subst hok hok' h1
          exact ⟨rfl, h2⟩
  | internal tm =>
      rw [Concrete.step, Concrete.step, h.timer tm]
      by_cases hl : (t.blob? (.timer tm)).isSome = true ∧ tm.deadline ≤ now
      · rw [if_pos hl, if_pos hl]
        obtain ⟨h1, h2⟩ := run_alike (H := H) cfg cfg' tm.id.origin (fun org => Concrete.handle (.internal tm) now org) h
        have hok := Concrete.run_accepted (H := H) cfg tm.id.origin (fun org => Concrete.handle (.internal tm) now org) s
        have hok' := Concrete.run_accepted (H := H) cfg' tm.id.origin (fun org => Concrete.handle (.internal tm) now org) t
        rcases hR : Concrete.run H cfg tm.id.origin (fun org => Concrete.handle (.internal tm) now org) s with ⟨r, s', ok⟩
        rcases hR' : Concrete.run H cfg' tm.id.origin (fun org => Concrete.handle (.internal tm) now org) t with ⟨r', t', ok'⟩
        rw [hR, hR'] at h1 h2
        rw [hR] at hok
        rw [hR'] at hok'
        simp only at h1 h2 hok hok'
        subst hok hok' h1
        exact ⟨rfl, h2⟩
      · rw [if_neg hl, if_neg hl]
        exact ⟨rfl, h⟩

def transfer (H : Hasher) (cfg' : Config) (tr : Concrete.Trace) : Nat → Concrete.State
  | 0 => Concrete.State.init
  | n + 1 => (Concrete.step H cfg' (tr n).event (tr n).now (transfer H cfg' tr n)).2

def transferred (H : Hasher) (cfg' : Config) (tr : Concrete.Trace) : Concrete.Trace :=
  fun n => ⟨transfer H cfg' tr n, (tr n).event,
            (Concrete.step H cfg' (tr n).event (tr n).now (transfer H cfg' tr n)).1, (tr n).now⟩

theorem transferred_valid {cfg : Config} (cfg' : Config) {tr : Concrete.Trace} (valid : Concrete.Valid H cfg tr) :
    Concrete.Valid H cfg' (transferred H cfg' tr) := by
  intro n
  refine ⟨?_, valid.now n⟩
  rfl

theorem transfer_alike {cfg : Config} (cfg' : Config) {tr : Concrete.Trace} (valid : Concrete.Valid H cfg tr)
    (init : (tr 0).state = Concrete.State.init) : ∀ n, Alike (tr n).state (transfer H cfg' tr n)
  | 0 => by rw [init]; exact Alike.refl _
  | n + 1 => by
      rw [valid.state n]
      exact (step_alike cfg cfg' _ _ (transfer_alike cfg' valid init n)).2

theorem observe_transfer {cfg : Config} (cfg' : Config) {tr : Concrete.Trace} (valid : Concrete.Valid H cfg tr)
    (init : (tr 0).state = Concrete.State.init) (n : Nat) :
    Concrete.Frame.observe (transferred H cfg' tr n) = Concrete.Frame.observe (tr n) := by
  have hr : (Concrete.step H cfg' (tr n).event (tr n).now (transfer H cfg' tr n)).1 = (tr n).reply := by
    rw [valid.reply n]
    exact (step_alike cfg cfg' _ _ (transfer_alike cfg' valid init n)).1.symm
  unfold Concrete.Frame.observe
  simp only [transferred]
  rw [hr]

theorem observed_transfer {cfg : Config} (cfg' : Config) {tr : Concrete.Trace} (valid : Concrete.Valid H cfg tr)
    (init : (tr 0).state = Concrete.State.init) (n : Nat) :
    Concrete.observed (transferred H cfg' tr) n = Concrete.observed tr n := by
  unfold Concrete.observed
  rw [List.filterMap_map, List.filterMap_map]
  apply filterMap_congr'
  intro i _
  exact observe_transfer cfg' valid init i

theorem adds_invisible (H : Hasher) (cfg cfg' : Config) (tr : Concrete.Trace)
    (valid : Concrete.Valid H cfg tr) (init : (tr 0).state = Concrete.State.init) :
    ∃ tr' : Concrete.Trace,
      Concrete.Valid H cfg' tr' ∧
      (tr' 0).state = Concrete.State.init ∧
      ∀ k o, Concrete.nth tr k o ↔ Concrete.nth tr' k o := by
  refine ⟨transferred H cfg' tr, transferred_valid cfg' valid, rfl, ?_⟩
  intro k o
  unfold Concrete.nth
  simp only [observed_transfer cfg' valid init]

end Refinement
