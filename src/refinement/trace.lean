import refinement.simulation

namespace Refinement

section Flat

variable {α : Type}

def shift (b : Nat → List α) : Nat → List α := fun n => b (n + 1)

def flat (b : Nat → List α) (hb : ∀ n, 0 < (b n).length) (m : Nat) : α :=
  if h : m < (b 0).length then (b 0)[m]
  else flat (shift b) (fun n => hb (n + 1)) (m - (b 0).length)
termination_by m
decreasing_by
  have := hb 0
  omega

theorem flat_lt (b : Nat → List α) (hb : ∀ n, 0 < (b n).length) {m : Nat} (h : m < (b 0).length) :
    flat b hb m = (b 0)[m] := by
  rw [flat, dif_pos h]

theorem flat_ge (b : Nat → List α) (hb : ∀ n, 0 < (b n).length) {m : Nat} (h : (b 0).length ≤ m) :
    flat b hb m = flat (shift b) (fun n => hb (n + 1)) (m - (b 0).length) := by
  rw [flat, dif_neg (by omega)]

theorem flat_add (b : Nat → List α) (hb : ∀ n, 0 < (b n).length) (j : Nat) :
    flat b hb ((b 0).length + j) = flat (shift b) (fun n => hb (n + 1)) j := by
  rw [flat_ge b hb (by omega)]
  congr 1
  omega

def start (b : Nat → List α) : Nat → Nat
  | 0 => 0
  | n + 1 => start b n + (b n).length

theorem start_shift (b : Nat → List α) : ∀ n, start b (n + 1) = (b 0).length + start (shift b) n
  | 0 => by simp [start]
  | n + 1 => by
      show start b (n + 1) + (b (n + 1)).length = (b 0).length + (start (shift b) n + (shift b n).length)
      rw [start_shift b n]
      unfold shift
      omega

theorem start_ge (b : Nat → List α) (hb : ∀ n, 0 < (b n).length) : ∀ n, n ≤ start b n
  | 0 => Nat.le_refl 0
  | n + 1 => by
      have := hb n
      have := start_ge b hb n
      simp only [start]
      omega

theorem flat_start (b : Nat → List α) (hb : ∀ n, 0 < (b n).length) :
    ∀ n i (h : i < (b n).length), flat b hb (start b n + i) = (b n)[i]
  | 0, i, h => by
      simp only [start, Nat.zero_add]
      exact flat_lt b hb h
  | n + 1, i, h => by
      rw [start_shift, Nat.add_assoc, flat_add]
      exact flat_start (shift b) (fun n => hb (n + 1)) n i h

theorem flat_pairs {P : α → α → Prop} :
    ∀ (b : Nat → List α) (hb : ∀ n, 0 < (b n).length),
      (∀ n i (h : i + 1 < (b n).length), P (b n)[i] (b n)[i + 1]) →
      (∀ n, P ((b n).getLast (List.ne_nil_of_length_pos (hb n)))
              ((b (n + 1)).head (List.ne_nil_of_length_pos (hb (n + 1))))) →
      ∀ m, P (flat b hb m) (flat b hb (m + 1))
  | b, hb, hin, hbd, m => by
      by_cases h1 : m + 1 < (b 0).length
      · rw [flat_lt b hb h1, flat_lt b hb (by omega)]
        exact hin 0 m h1
      · by_cases h2 : m + 1 = (b 0).length
        · rw [flat_lt b hb (by omega), flat_ge b hb (by omega), h2, Nat.sub_self]
          rw [flat_lt (shift b) _ (hb 1)]
          have e1 : (b 0)[m] = (b 0).getLast (List.ne_nil_of_length_pos (hb 0)) := by
            rw [List.getLast_eq_getElem]
            congr 1
            omega
          have e2 : (shift b 0)[0]'(hb 1) = (b 1).head (List.ne_nil_of_length_pos (hb 1)) := by
            rw [List.head_eq_getElem]
            rfl
          rw [e1, e2]
          exact hbd 0
        · have hle : (b 0).length ≤ m := by omega
          rw [flat_ge b hb hle, flat_ge b hb (by omega)]
          have e : m + 1 - (b 0).length = (m - (b 0).length) + 1 := by omega
          rw [e]
          exact flat_pairs (shift b) (fun n => hb (n + 1)) (fun n i h => hin (n + 1) i h) (fun n => hbd (n + 1))
            (m - (b 0).length)
termination_by _ _ _ _ m => m
decreasing_by
  have := hb 0
  omega

theorem range_add_map {β : Type} (f : Nat → β) (a : Nat) :
    ∀ k, (List.range (a + k)).map f = (List.range a).map f ++ (List.range k).map (fun i => f (a + i))
  | 0 => by simp
  | k + 1 => by
      rw [← Nat.add_assoc, List.range_succ, List.map_append, range_add_map f a k, List.range_succ,
        List.map_append, List.append_assoc]
      rfl

theorem range_block (b : Nat → List α) (hb : ∀ n, 0 < (b n).length) (n : Nat) :
    (List.range (b n).length).map (fun i => flat b hb (start b n + i)) = b n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact flat_start b hb n i h2

end Flat

def frames (now : Nat) : Abstract.State → List Abstract.Event → List Abstract.Frame
  | _, [] => []
  | S, ev :: evs =>
      ⟨S, ev, (Abstract.step false ev now S).1, now⟩ :: frames now (Abstract.step false ev now S).2 evs

theorem frames_length (now : Nat) : ∀ (S : Abstract.State) (l : List Abstract.Event),
    (frames now S l).length = l.length
  | _, [] => rfl
  | S, ev :: evs => by simp [frames, frames_length now _ evs]

theorem frames_append (now : Nat) : ∀ (S : Abstract.State) (l : List Abstract.Event) (ev : Abstract.Event),
    frames now S (l ++ [ev]) =
      frames now S l ++
        [⟨(Abstract.exec false (l.map (·, now)) S).2, ev,
          (Abstract.step false ev now (Abstract.exec false (l.map (·, now)) S).2).1, now⟩]
  | S, [], ev => rfl
  | S, e :: l, ev => by
      simp only [List.cons_append, frames, List.map_cons, exec_cons]
      rw [frames_append now _ l ev]

theorem frames_head (now : Nat) (S : Abstract.State) (l : List Abstract.Event) (h : frames now S l ≠ []) :
    ((frames now S l).head h).state = S := by
  cases l with
  | nil => exact absurd rfl h
  | cons ev evs => rfl

theorem frames_head_now (now : Nat) (S : Abstract.State) (l : List Abstract.Event) (h : frames now S l ≠ []) :
    ((frames now S l).head h).now = now := by
  cases l with
  | nil => exact absurd rfl h
  | cons ev evs => rfl

theorem frames_pairs (now : Nat) : ∀ (l : List Abstract.Event) (S : Abstract.State) (i : Nat)
    (h : i + 1 < (frames now S l).length),
    Abstract.step false (frames now S l)[i].event (frames now S l)[i].now (frames now S l)[i].state =
      ((frames now S l)[i].reply, (frames now S l)[i + 1].state) ∧
    (frames now S l)[i].now ≤ (frames now S l)[i + 1].now
  | [], _, _, h => by simp [frames] at h
  | ev :: l, S, 0, h => by
      cases l with
      | nil => simp [frames] at h
      | cons ev' l => exact ⟨rfl, Nat.le_refl _⟩
  | ev :: l, S, i + 1, h => by
      simp only [frames, List.getElem_cons_succ]
      exact frames_pairs now l _ i (by simpa [frames] using h)

theorem frames_observe (now : Nat) : ∀ (l : List Abstract.Event) (S : Abstract.State),
    (frames now S l).filterMap Abstract.Frame.observe =
      observations now l (Abstract.exec false (l.map (·, now)) S).1
  | [], _ => rfl
  | ev :: l, S => by
      simp only [List.map_cons, exec_cons]
      cases ev with
      | external req =>
          cases hr : (Abstract.step false (.external req) now S).1 with
          | external res =>
              simp only [frames, List.filterMap_cons, Abstract.Frame.observe, hr, observations]
              rw [frames_observe now l]
          | internal =>
              simp only [frames, List.filterMap_cons, Abstract.Frame.observe, hr, observations]
              exact frames_observe now l _
          | stutter =>
              simp only [frames, List.filterMap_cons, Abstract.Frame.observe, hr, observations]
              exact frames_observe now l _
      | internal trg =>
          simp only [frames, List.filterMap_cons, Abstract.Frame.observe, observations]
          exact frames_observe now l _
      | stutter =>
          simp only [frames, List.filterMap_cons, Abstract.Frame.observe, observations]
          exact frames_observe now l _

theorem exec_length (mat : Bool) : ∀ (w : List (Abstract.Event × Nat)) (S : Abstract.State),
    (Abstract.exec mat w S).1.length = w.length
  | [], _ => rfl
  | (ev, n) :: w, S => by
      simp only [exec_cons, List.length_cons]
      rw [exec_length mat w]

theorem observations_stutter (now : Nat) : ∀ (evs : List Abstract.Event) (rs : List Abstract.Reply),
    evs.length = rs.length →
    observations now (evs ++ [.stutter]) (rs ++ [.stutter]) = observations now evs rs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | ev :: evs, r :: rs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.cons_append]
      cases ev <;> cases r <;> simp only [observations] <;> rw [observations_stutter now evs rs h]

theorem step_stutter (now : Nat) (S : Abstract.State) :
    Abstract.step false .stutter now S = (.stutter, S) := rfl

theorem observed_succ (tr : Concrete.Trace) (n : Nat) :
    Concrete.observed tr (n + 1) = Concrete.observed tr n ++ (Concrete.Frame.observe (tr n)).toList := by
  simp only [Concrete.observed, List.range_succ, List.map_append, List.filterMap_append, List.map_cons,
    List.map_nil, List.filterMap_cons, List.filterMap_nil]
  cases Concrete.Frame.observe (tr n) <;> rfl

theorem aobserved_block (b : Nat → List Abstract.Frame) (hb : ∀ n, 0 < (b n).length) (n : Nat) :
    Abstract.observed (flat b hb) (start b (n + 1)) =
      Abstract.observed (flat b hb) (start b n) ++ (b n).filterMap Abstract.Frame.observe := by
  simp only [Abstract.observed, start, range_add_map, List.filterMap_append, range_block]

theorem aobserved_prefix (tr : Abstract.Trace) (M : Nat) :
    ∀ k, Abstract.observed tr M <+: Abstract.observed tr (M + k)
  | 0 => List.prefix_rfl
  | k + 1 => by
      rw [← Nat.add_assoc]
      refine (aobserved_prefix tr M k).trans ?_
      simp only [Abstract.observed, List.range_succ, List.map_append, List.filterMap_append]
      exact List.prefix_append _ _

end Refinement
