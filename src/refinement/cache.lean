import refinement.refinement
import impl.cache

namespace Concrete.Cached

variable {H : Hasher}

def Frame.proj (f : Frame H) : Concrete.Frame :=
  ⟨f.state.state, f.event, f.reply, f.now⟩

def Frame.observe (f : Frame H) : Option Abstract.Observation :=
  f.proj.observe

def observed (tr : Trace H) (n : Nat) : List Abstract.Observation :=
  ((List.range n).map tr).filterMap Frame.observe

def nth (tr : Trace H) (k : Nat) (o : Abstract.Observation) : Prop :=
  ∃ n, (observed tr n)[k]? = some o

def proj (tr : Trace H) : Concrete.Trace :=
  fun n => (tr n).proj

end Concrete.Cached

namespace Refinement

open Concrete (Cached Hasher Origin Blob Path Commands Event Config attempt runCached stepCached)
open Protocol (Object)

def Sound {H : Hasher} (cs : Cached H) : Prop :=
  ∀ name parts etag, (name, parts, etag) ∈ cs.cache →
    cs.state.blob? (.origin name) = some (.origin parts) ∧ H.hash (.origin parts) = etag

def Tagged {H : Hasher} (cs : Cached H) : Prop :=
  ∀ name parts etag, (name, parts, etag) ∈ cs.cache → H.hash (.origin parts) = etag

def Agree {H : Hasher} (cs : Cached H) (name : String) : Prop :=
  cs.read name = (cs.state.parts name, Concrete.Cond.of H (cs.state.blob? (.origin name)))

def Docs (s s' : Concrete.State) : Prop :=
  (∀ m, s'.blob? (.origin m) = s.blob? (.origin m)) ∧ s'.outbox = s.outbox

theorem Sound.init (H : Hasher) : Sound (Cached.init H) :=
  fun _ _ _ h => (List.not_mem_nil h).elim

theorem Docs.refl (s : Concrete.State) : Docs s s := ⟨fun _ => rfl, rfl⟩

theorem read_sound {H : Hasher} {cs : Cached H} (h : Sound cs) (name : String) : Agree cs name := by
  unfold Agree Cached.read
  cases hf : cs.cache.find? (·.1 == name) with
  | none => rfl
  | some p =>
      obtain ⟨n, parts, etag⟩ := p
      have hn : n = name := by simpa using List.find?_some hf
      subst hn
      obtain ⟨hb, he⟩ := h n parts etag (List.mem_of_find?_eq_some hf)
      show (parts, Concrete.Cond.hash etag) = (cs.state.parts n, Concrete.Cond.of H (cs.state.blob? (.origin n)))
      unfold Concrete.State.parts
      simp only [hb, Concrete.Cond.of, he]

theorem read_absent {H : Hasher} {cs : Cached H} {name : String}
    (h : ∀ parts etag, (name, parts, etag) ∉ cs.cache) : Agree cs name := by
  unfold Agree Cached.read
  have hf : cs.cache.find? (·.1 == name) = none := by
    refine List.find?_eq_none.2 fun x hx => ?_
    obtain ⟨n, parts, etag⟩ := x
    intro hn
    have hn' : n = name := by simpa using hn
    subst hn'
    exact h parts etag hx
  rw [hf]

theorem read_cases {H : Hasher} (cs : Cached H) (name : String) :
    Agree cs name ∨ ∃ parts etag, (name, parts, etag) ∈ cs.cache ∧ cs.read name = (parts, .hash etag) := by
  unfold Agree Cached.read
  cases hf : cs.cache.find? (·.1 == name) with
  | none => exact Or.inl rfl
  | some p =>
      obtain ⟨n, parts, etag⟩ := p
      have hn : n = name := by simpa using List.find?_some hf
      subst hn
      exact Or.inr ⟨parts, etag, List.mem_of_find?_eq_some hf, rfl⟩

theorem read_of_hit {H : Hasher} {cs : Cached H} (ht : Tagged cs) {name : String} {parts : List (List Object)}
    {etag : H.Hash} (hm : (name, parts, etag) ∈ cs.cache) (hr : cs.read name = (parts, .hash etag))
    (hh : (Concrete.Cond.hash etag : Concrete.Cond H).holds (cs.state.blob? (.origin name)) = true) :
    Agree cs name := by
  have he := ht name parts etag hm
  have hb : cs.state.blob? (.origin name) = some (.origin parts) := by
    rw [← he] at hh
    exact (Concrete.Cond.of_holds_iff (.origin parts) _).1 hh
  unfold Agree
  rw [hr]
  unfold Concrete.State.parts
  simp only [hb, Concrete.Cond.of, he]

theorem read_true {H : Hasher} {cs : Cached H} (ht : Tagged cs) {name : String}
    (hh : (cs.read name).2.holds (cs.state.blob? (.origin name)) = true) : Agree cs name := by
  rcases read_cases cs name with hr | ⟨parts, etag, hm, hr⟩
  · exact hr
  · rw [hr] at hh
    simp only at hh
    exact read_of_hit ht hm hr hh

theorem forget_not_mem {H : Hasher} {cs : Cached H} {name : String} {parts : List (List Object)} {etag : H.Hash} :
    (name, parts, etag) ∉ cs.forget name := by
  intro hm
  have := (List.mem_filter.1 hm).2
  simp at this

theorem run_fst {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    (s : Concrete.State) : (Concrete.run H cfg name f s).1 = (f (s.origin name)).1 := by
  simp only [Concrete.run]

theorem run_snd {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    (s : Concrete.State) :
    (Concrete.run H cfg name f s).2.1 =
      (Concrete.applyAll s ((f (s.origin name)).2.effects (Concrete.write H cfg name (s.parts name)
        (Concrete.Cond.of H (s.blob? (.origin name))) (f (s.origin name)).2.add))).1 := by
  simp only [Concrete.run]

theorem attempt_of_read {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    {cs : Cached H} (hr : Agree cs name) :
    (attempt H cfg name f cs).1 = (Concrete.run H cfg name f cs.state).1 ∧
    (attempt H cfg name f cs).2.1 =
      { state := (Concrete.run H cfg name f cs.state).2.1,
        cache := (name, Concrete.next cfg (cs.state.parts name) (f (cs.state.origin name)).2.add,
                  H.hash (.origin (Concrete.next cfg (cs.state.parts name) (f (cs.state.origin name)).2.add))) ::
          cs.forget name } ∧
    (attempt H cfg name f cs).2.2 = true := by
  unfold Agree at hr
  simp only [attempt, Concrete.run, hr, Concrete.State.origin]
  rcases hf : f (Concrete.view (cs.state.parts name)) with ⟨a, c⟩
  have hok := Concrete.applyAll_accepted (H := H) cfg cs.state name c
  obtain ⟨-, -, -, -, -, hblob⟩ := run_state H cfg name c cs.state
  rcases hA : Concrete.applyAll cs.state (c.effects (Concrete.write H cfg name (cs.state.parts name)
    (Concrete.Cond.of H (cs.state.blob? (.origin name))) c.add)) with ⟨s', ok⟩
  rw [hA] at hok hblob
  simp only at hok hblob
  subst hok
  simp only [hblob]
  refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem attempt_cache {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    (cs : Cached H) (m : String) (parts : List (List Object)) (etag : H.Hash)
    (hm : (m, parts, etag) ∈ (attempt H cfg name f cs).2.1.cache) :
    (m = name ∧ etag = H.hash (.origin parts)) ∨ (m, parts, etag) ∈ cs.cache := by
  unfold attempt at hm
  rcases hr : cs.read name with ⟨p, cond⟩
  simp only [hr] at hm
  split at hm
  · simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (List.mem_filter.1 hm).1
  · exact Or.inr (List.mem_filter.1 hm).1

theorem attempt_tagged {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    {cs : Cached H} (h : Tagged cs) : Tagged (attempt H cfg name f cs).2.1 := by
  intro m parts etag hm
  rcases attempt_cache H cfg name f cs m parts etag hm with ⟨rfl, rfl⟩ | hm
  · rfl
  · exact h m parts etag hm

theorem applyAll_cons_refused {H : Hasher} (s : Concrete.State) (e : Concrete.Effect H)
    (rest : List (Concrete.Effect H)) (h : e.apply s = none) :
    Concrete.applyAll s (e :: rest) = (s, false) := by
  simp only [Concrete.applyAll, h]

theorem applyAll_refused (H : Hasher) (cfg : Config) (s : Concrete.State) (name : String)
    (parts : List (List Object)) (c : Commands) (cond : Concrete.Cond H)
    (h : cond.holds (s.blob? (.origin name)) = false) :
    (Concrete.applyAll s (c.effects (Concrete.write H cfg name parts cond c.add))).2 = false ∧
    Same s (Concrete.applyAll s (c.effects (Concrete.write H cfg name parts cond c.add))).1 := by
  unfold Commands.effects
  obtain ⟨hA, sameA⟩ := timers_phase (H := H) (c.arm.map fun t => .put (.timer t) .timer .any) s
    (by intro e he; simp only [List.mem_map] at he; obtain ⟨t, _, rfl⟩ := he; trivial)
  obtain ⟨s1, hs1⟩ : ∃ s1, Concrete.applyAll s (c.arm.map fun t => Concrete.Effect.put (H := H) (.timer t) .timer .any) = (s1, true) :=
    ⟨_, Prod.ext rfl hA⟩
  rw [hs1] at sameA
  simp only at sameA
  simp only [List.append_assoc, List.singleton_append]
  rw [Concrete.applyAll_append, hs1, if_pos rfl]
  have hh : cond.holds (s1.blob? (.origin name)) = false := by rw [sameA.blob, h]
  show (Concrete.applyAll s1 _).2 = false ∧ Same s (Concrete.applyAll s1 _).1
  rw [List.cons_append, applyAll_cons_refused s1 _ _ (Concrete.write_refused cfg name parts cond c.add hh)]
  exact ⟨rfl, sameA⟩

theorem attempt_miss {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    {cs : Cached H} {parts : List (List Object)} {etag : H.Hash} (hr : cs.read name = (parts, .hash etag))
    (hh : (Concrete.Cond.hash etag : Concrete.Cond H).holds (cs.state.blob? (.origin name)) = false) :
    (attempt H cfg name f cs).2.2 = false ∧
    Same cs.state (attempt H cfg name f cs).2.1.state ∧
    ∀ parts' etag', (name, parts', etag') ∉ (attempt H cfg name f cs).2.1.cache := by
  simp only [attempt, hr]
  rcases hf : f (Concrete.view parts) with ⟨a, c⟩
  obtain ⟨hA, same⟩ := applyAll_refused H cfg cs.state name parts c (.hash etag) hh
  rcases hAA : Concrete.applyAll cs.state (c.effects (Concrete.write H cfg name parts (.hash etag) c.add)) with ⟨s', ok⟩
  rw [hAA] at hA same
  simp only at hA same
  subst hA
  refine ⟨rfl, same, fun parts' etag' hm => ?_⟩
  have hm' : (name, parts', etag') ∈ cs.forget name := hm
  exact forget_not_mem hm'

theorem attempt_dichotomy {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    {cs : Cached H} (ht : Tagged cs) :
    ((cs.read name).2.holds (cs.state.blob? (.origin name)) = true →
      (attempt H cfg name f cs).1 = (Concrete.run H cfg name f cs.state).1 ∧
      (attempt H cfg name f cs).2.1.state = (Concrete.run H cfg name f cs.state).2.1 ∧
      (attempt H cfg name f cs).2.2 = true) ∧
    ((cs.read name).2.holds (cs.state.blob? (.origin name)) = false →
      (attempt H cfg name f cs).2.2 = false ∧
      Same cs.state (attempt H cfg name f cs).2.1.state ∧
      ∀ parts etag, (name, parts, etag) ∉ (attempt H cfg name f cs).2.1.cache) := by
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := attempt_of_read H cfg name f (read_true ht hh)
    exact ⟨h1, by rw [h2], h3⟩
  · rcases read_cases cs name with hr | ⟨parts, etag, hm, hr⟩
    · unfold Agree at hr
      rw [hr] at hh
      simp only at hh
      rw [Concrete.Cond.of_holds] at hh
      cases hh
    · rw [hr] at hh
      simp only at hh
      exact attempt_miss H cfg name f hr hh

theorem runCached_of_ok {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    (cs : Cached H) (h : (attempt H cfg name f cs).2.2 = true) :
    runCached H cfg name f cs = attempt H cfg name f cs := by
  unfold runCached
  rcases hA : attempt H cfg name f cs with ⟨a, cs', ok⟩
  rw [hA] at h
  simp only at h
  subst h
  rfl

theorem run_docs {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    {s s' : Concrete.State} (h : Same s s') :
    (Concrete.run H cfg name f s').1 = (Concrete.run H cfg name f s).1 ∧
    Docs (Concrete.run H cfg name f s).2.1 (Concrete.run H cfg name f s').2.1 := by
  have horg : s'.origin name = s.origin name := by
    rw [State.origin_eq, State.origin_eq, h.blob]
  have hparts : s'.parts name = s.parts name := by
    unfold Concrete.State.parts; rw [h.blob]
  obtain ⟨-, h2, h3, -, -, h1⟩ := run_state H cfg name (f (s.origin name)).2 s
  obtain ⟨-, h2', h3', -, -, h1'⟩ := run_state H cfg name (f (s'.origin name)).2 s'
  rw [horg] at h1' h2' h3'
  refine ⟨by rw [run_fst, run_fst, horg], fun m => ?_, ?_⟩
  · rw [run_snd, run_snd, horg]
    by_cases hm : m = name
    · subst hm; rw [h1, h1', hparts]
    · rw [h2 m hm, h2' m hm, h.blob]
  · rw [run_snd, run_snd, horg, h3, h3', h.out]

theorem parts_of_blob {s : Concrete.State} {name : String} {parts : List (List Object)}
    (h : s.blob? (.origin name) = some (.origin parts)) : s.parts name = parts := by
  unfold Concrete.State.parts
  rw [h]

theorem agree_after {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    (s : Concrete.State) (rest : List (String × List (List Object) × H.Hash)) :
    Agree ({ state := (Concrete.run H cfg name f s).2.1,
             cache := (name, Concrete.next cfg (s.parts name) (f (s.origin name)).2.add,
                       H.hash (.origin (Concrete.next cfg (s.parts name) (f (s.origin name)).2.add))) :: rest } : Cached H)
      name := by
  unfold Agree Cached.read
  simp only [List.find?_cons, beq_self_eq_true]
  obtain ⟨-, -, -, -, -, h1⟩ := run_state H cfg name (f (s.origin name)).2 s
  show (Concrete.next cfg (s.parts name) (f (s.origin name)).2.add,
      Concrete.Cond.hash (H.hash (.origin (Concrete.next cfg (s.parts name) (f (s.origin name)).2.add)))) =
    ((Concrete.run H cfg name f s).2.1.parts name, Concrete.Cond.of H ((Concrete.run H cfg name f s).2.1.blob? (.origin name)))
  rw [run_snd, parts_of_blob h1, h1]
  rfl

theorem runCached_any {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    {cs : Cached H} (ht : Tagged cs) :
    (runCached H cfg name f cs).2.2 = true ∧
    (runCached H cfg name f cs).1 = (Concrete.run H cfg name f cs.state).1 ∧
    Docs (Concrete.run H cfg name f cs.state).2.1 (runCached H cfg name f cs).2.1.state ∧
    Tagged (runCached H cfg name f cs).2.1 ∧
    Agree (runCached H cfg name f cs).2.1 name := by
  have hd := attempt_dichotomy H cfg name f ht
  cases hh : (cs.read name).2.holds (cs.state.blob? (.origin name)) with
  | true =>
      have hr := read_true ht hh
      obtain ⟨h1, h2, h3⟩ := attempt_of_read H cfg name f hr
      rw [runCached_of_ok H cfg name f cs h3, h2]
      refine ⟨h3, h1, ?_, ?_, agree_after H cfg name f cs.state _⟩
      · exact Docs.refl _
      · rw [← h2]; exact attempt_tagged H cfg name f ht
  | false =>
      obtain ⟨hok, hsame, hnot⟩ := hd.2 hh
      have htag' : Tagged (attempt H cfg name f cs).2.1 := attempt_tagged H cfg name f ht
      have hr' : Agree (attempt H cfg name f cs).2.1 name := read_absent hnot
      obtain ⟨h1, h2, h3⟩ := attempt_of_read H cfg name f hr'
      obtain ⟨hf, hdocs⟩ := run_docs H cfg name f hsame
      have hrun : runCached H cfg name f cs = attempt H cfg name f (attempt H cfg name f cs).2.1 := by
        unfold runCached
        rcases hA : attempt H cfg name f cs with ⟨a, cs', ok⟩
        rw [hA] at hok
        simp only at hok
        subst hok
        rfl
      rw [hrun, h2]
      refine ⟨h3, h1.trans hf, hdocs, ?_, agree_after H cfg name f _ _⟩
      rw [← h2]
      exact attempt_tagged H cfg name f htag'

theorem runCached_eq {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    {cs : Cached H} (h : Sound cs) :
    (runCached H cfg name f cs).1 = (Concrete.run H cfg name f cs.state).1 ∧
    (runCached H cfg name f cs).2.1.state = (Concrete.run H cfg name f cs.state).2.1 ∧
    (runCached H cfg name f cs).2.2 = (Concrete.run H cfg name f cs.state).2.2 := by
  obtain ⟨h1, h2, h3⟩ := attempt_of_read H cfg name f (read_sound h name)
  rw [runCached_of_ok H cfg name f cs h3, h2, h3, Concrete.run_accepted]
  exact ⟨h1, rfl, rfl⟩

theorem runCached_sound {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    {cs : Cached H} (h : Sound cs) : Sound (runCached H cfg name f cs).2.1 := by
  obtain ⟨-, h2, h3⟩ := attempt_of_read H cfg name f (read_sound h name)
  rw [runCached_of_ok H cfg name f cs h3, h2, run_snd]
  intro m parts etag hm
  obtain ⟨-, hb2, -, -, -, hb1⟩ := run_state H cfg name (f (cs.state.origin name)).2 cs.state
  simp only [List.mem_cons, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | hm
  · exact ⟨hb1, rfl⟩
  · obtain ⟨hmem, hne⟩ := List.mem_filter.1 hm
    have hne' : m ≠ name := by simpa using hne
    obtain ⟨hb, he⟩ := h m parts etag hmem
    refine ⟨?_, he⟩
    show (Concrete.applyAll _ _).1.blob? (.origin m) = _
    rw [hb2 m hne']
    exact hb

theorem stepCached_eq (H : Hasher) (cfg : Config) (ev : Event) (now : Nat) {cs : Cached H} (h : Sound cs) :
    (stepCached H cfg ev now cs).1 = (Concrete.step H cfg ev now cs.state).1 ∧
    (stepCached H cfg ev now cs).2.state = (Concrete.step H cfg ev now cs.state).2 ∧
    Sound (stepCached H cfg ev now cs).2 := by
  cases ev with
  | external req =>
      cases ho : req.origin? with
      | none =>
          simp only [stepCached, Concrete.step, ho]
          exact ⟨trivial, trivial, h⟩
      | some name =>
          simp only [stepCached, Concrete.step, ho]
          have heq := runCached_eq H cfg name (fun org => Concrete.handle (.external req) now org) h
          have hs := runCached_sound H cfg name (fun org => Concrete.handle (.external req) now org) h
          rcases hR : runCached H cfg name (fun org => Concrete.handle (.external req) now org) cs with ⟨r, cs', ok⟩
          rcases hS : Concrete.run H cfg name (fun org => Concrete.handle (.external req) now org) cs.state
            with ⟨r', s', ok'⟩
          rw [hR, hS] at heq
          rw [hR] at hs
          simp only at heq hs
          obtain ⟨rfl, h2, rfl⟩ := heq
          exact ⟨rfl, h2, hs⟩
  | internal t =>
      simp only [stepCached, Concrete.step]
      split
      · have heq := runCached_eq H cfg t.id.origin (fun org => Concrete.handle (.internal t) now org) h
        have hs := runCached_sound H cfg t.id.origin (fun org => Concrete.handle (.internal t) now org) h
        rcases hR : runCached H cfg t.id.origin (fun org => Concrete.handle (.internal t) now org) cs with ⟨r, cs', ok⟩
        rcases hS : Concrete.run H cfg t.id.origin (fun org => Concrete.handle (.internal t) now org) cs.state
          with ⟨r', s', ok'⟩
        rw [hR, hS] at heq
        rw [hR] at hs
        simp only at heq hs
        obtain ⟨rfl, h2, rfl⟩ := heq
        exact ⟨rfl, h2, hs⟩
      · exact ⟨rfl, rfl, h⟩
  | stutter =>
      exact ⟨rfl, rfl, h⟩

theorem stepCached_any (H : Hasher) (cfg : Config) (now : Nat) (req : Protocol.Request) (name : String)
    (ho : req.origin? = some name) {cs : Cached H} (ht : Tagged cs) :
    (stepCached H cfg (.external req) now cs).1 = (Concrete.step H cfg (.external req) now cs.state).1 ∧
    Docs (Concrete.step H cfg (.external req) now cs.state).2 (stepCached H cfg (.external req) now cs).2.state ∧
    Tagged (stepCached H cfg (.external req) now cs).2 ∧
    Agree (stepCached H cfg (.external req) now cs).2 name := by
  simp only [stepCached, Concrete.step, ho]
  have ha := runCached_any H cfg name (fun org => Concrete.handle (.external req) now org) ht
  have hok' := Concrete.run_accepted (H := H) cfg name (fun org => Concrete.handle (.external req) now org) cs.state
  rcases hR : runCached H cfg name (fun org => Concrete.handle (.external req) now org) cs with ⟨r, cs', ok⟩
  rcases hS : Concrete.run H cfg name (fun org => Concrete.handle (.external req) now org) cs.state with ⟨r', s', ok'⟩
  rw [hR, hS] at ha
  rw [hS] at hok'
  simp only at ha hok'
  obtain ⟨rfl, rfl, hdocs, htag, hagree⟩ := ha
  subst hok'
  exact ⟨rfl, hdocs, htag, hagree⟩

theorem stepCached_any_timer (H : Hasher) (cfg : Config) (now : Nat) (t : Concrete.Timer) {cs : Cached H}
    (hl : (cs.state.blob? (.timer t)).isSome ∧ t.deadline ≤ now) (ht : Tagged cs) :
    (stepCached H cfg (.internal t) now cs).1 = (Concrete.step H cfg (.internal t) now cs.state).1 ∧
    Docs (Concrete.step H cfg (.internal t) now cs.state).2 (stepCached H cfg (.internal t) now cs).2.state ∧
    Tagged (stepCached H cfg (.internal t) now cs).2 ∧
    Agree (stepCached H cfg (.internal t) now cs).2 t.id.origin := by
  simp only [stepCached, Concrete.step]
  rw [if_pos hl, if_pos hl]
  have ha := runCached_any H cfg t.id.origin (fun org => Concrete.handle (.internal t) now org) ht
  have hok' := Concrete.run_accepted (H := H) cfg t.id.origin (fun org => Concrete.handle (.internal t) now org) cs.state
  rcases hR : runCached H cfg t.id.origin (fun org => Concrete.handle (.internal t) now org) cs with ⟨r, cs', ok⟩
  rcases hS : Concrete.run H cfg t.id.origin (fun org => Concrete.handle (.internal t) now org) cs.state
    with ⟨r', s', ok'⟩
  rw [hR, hS] at ha
  rw [hS] at hok'
  simp only at ha hok'
  obtain ⟨rfl, rfl, hdocs, htag, hagree⟩ := ha
  subst hok'
  exact ⟨rfl, hdocs, htag, hagree⟩

theorem sound_all {H : Hasher} {cfg : Config} {tr : Cached.Trace H} (hv : Cached.Valid H cfg tr)
    (h0 : (tr 0).state = Cached.init H) : ∀ n, Sound (tr n).state
  | 0 => by rw [h0]; exact Sound.init H
  | n + 1 => by
      have hst : (tr (n + 1)).state = (stepCached H cfg (tr n).event (tr n).now (tr n).state).2 := by
        rw [(hv n).1]
      rw [hst]
      exact (stepCached_eq H cfg _ _ (sound_all hv h0 n)).2.2

theorem proj_valid {H : Hasher} {cfg : Config} {tr : Cached.Trace H} (hv : Cached.Valid H cfg tr)
    (h0 : (tr 0).state = Cached.init H) : Concrete.Valid H cfg (Cached.proj tr) := by
  intro n
  obtain ⟨h1, h2, -⟩ := stepCached_eq H cfg (tr n).event (tr n).now (sound_all hv h0 n)
  have hr : (tr n).reply = (stepCached H cfg (tr n).event (tr n).now (tr n).state).1 := by rw [(hv n).1]
  have hs : (tr (n + 1)).state = (stepCached H cfg (tr n).event (tr n).now (tr n).state).2 := by rw [(hv n).1]
  refine ⟨?_, (hv n).2⟩
  show Concrete.step H cfg (tr n).event (tr n).now (tr n).state.state = ((tr n).reply, (tr (n + 1)).state.state)
  rw [hr, hs, h1, h2]

theorem observed_proj {H : Hasher} (tr : Cached.Trace H) (n : Nat) :
    Concrete.observed (Cached.proj tr) n = Cached.observed tr n := by
  unfold Concrete.observed Cached.observed Cached.proj
  rw [List.filterMap_map, List.filterMap_map]
  rfl

theorem nth_proj {H : Hasher} (tr : Cached.Trace H) (k : Nat) (o : Abstract.Observation) :
    Cached.nth tr k o ↔ Concrete.nth (Cached.proj tr) k o := by
  unfold Cached.nth Concrete.nth
  simp only [observed_proj]

theorem refinesCached (H : Hasher) (cfg : Config) (tr : Cached.Trace H)
    (valid : Cached.Valid H cfg tr) (init : (tr 0).state = Cached.init H) :
    ∃ tr' : Abstract.Trace,
      Abstract.Valid false tr' ∧
      (tr' 0).state = Abstract.State.init ∧
      ∀ k o, Cached.nth tr k o ↔ Abstract.nth tr' k o := by
  have hinit : (Cached.proj tr 0).state = Concrete.State.init := by
    show (tr 0).state.state = _
    rw [init]
    rfl
  obtain ⟨tr', h1, h2, h3⟩ := refines H cfg (Cached.proj tr) (proj_valid valid init) hinit
  exact ⟨tr', h1, h2, fun k o => (nth_proj tr k o).trans (h3 k o)⟩

end Refinement
