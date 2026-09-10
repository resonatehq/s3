import «03-theorems».«system»

namespace Abstract

open Abstract

def wLag : List (Event × Nat) :=
  [ (.external (.taskCreate { pid := "p0", ttl := 100, action := { id := oid "x", timeoutAt := 250, param := {}, tags := tgtTags } }), 100),
    (.external (.taskGet { id := oid "x" }), 300),
    (.internal (.taskLeaseTimeout { id := oid "x" }), 300),
    (.internal (.taskRetryTimeout { id := oid "x" }), 300) ]

def b1 : List (Event × Nat) :=
  [ (.external (.promiseCreate { id := oid "a", timeoutAt := 1000, param := {}, tags := extTags }), 100),
    (.external (.taskCreate { pid := "p0", ttl := 100, action := { id := oid "x", timeoutAt := 2000, param := {}, tags := tgtTags } }), 100),
    (.external (.taskSuspend { id := oid "x", version := 1, actions := [{ awaited := oid "a", awaiter := oid "x" }] }), 120),
    (.external (.promiseSettle { id := oid "a", state := .resolved, value := {} }), 200),
    (.internal (.callback { awaited := oid "a", awaiter := oid "x" }), 200),
    (.external (.taskGet { id := oid "x" }), 210),
    (.internal (.taskRetryTimeout { id := oid "x" }), 210),
    (.external (.taskAcquire { id := oid "x", version := 1, pid := "p2", ttl := 50 }), 220),
    (.external (.taskFulfill { id := oid "x", version := 2, action := { id := oid "x", state := .resolved, value := {} } }), 230) ]

def b2 : List (Event × Nat) :=
  [ (.external (.promiseCreate { id := oid "a", timeoutAt := 1000, param := {}, tags := extTags }), 100),
    (.external (.taskCreate { pid := "p0", ttl := 100, action := { id := oid "x", timeoutAt := 300, param := {}, tags := tgtTags } }), 100),
    (.external (.taskSuspend { id := oid "x", version := 1, actions := [{ awaited := oid "a", awaiter := oid "x" }] }), 120),
    (.external (.taskGet { id := oid "x" }), 500),
    (.external (.taskHalt { id := oid "x" }), 500) ]

def b3 : List (Event × Nat) :=
  [ (.external (.promiseCreate { id := oid "tm", timeoutAt := 300, param := {}, tags := timerTags }), 100),
    (.external (.promiseGet { id := oid "tm" }), 500),
    (.external (.promiseRegisterListener { awaited := oid "tm", address := "https://l" }), 500),
    (.external (.promiseSettle { id := oid "tm", state := .rejected, value := {} }), 500),
    (.external (.promiseCreate { id := oid "tm", timeoutAt := 9999, param := {}, tags := [] }), 600) ]

def b4 : List (Event × Nat) :=
  [ (.external (.taskCreate { pid := "p0", ttl := 100, action := { id := oid "y", timeoutAt := 300, param := {}, tags := tgtTags } }), 100),
    (.external (.taskRelease { id := oid "y", version := 1 }), 150),
    (.external (.taskCreate { pid := "p1", ttl := 100, action := { id := oid "y", timeoutAt := 300, param := {}, tags := tgtTags } }), 500) ]

def b5 : List (Event × Nat) :=
  [ (.external (.taskCreate { pid := "p0", ttl := 1000, action := { id := oid "x", timeoutAt := 2000, param := {}, tags := tgtTags } }), 100),
    (.external (.taskFence { id := oid "x", version := 1, action := .create { id := oid "c", timeoutAt := 3000, param := {}, tags := extTags } }), 200),
    (.external (.taskFence { id := oid "x", version := 1, action := .settle { id := oid "c", state := .resolved, value := {} } }), 300),
    (.external (.taskFence { id := oid "x", version := 1, action := .settle { id := oid "x", state := .resolved, value := {} } }), 400),
    (.external (.taskFence { id := oid "x", version := 1, action := .settle { id := oid "c", state := .resolved, value := {} } }), 2500) ]

def b6 : List (Event × Nat) :=
  [ (.external (.promiseCreate { id := oid "a", timeoutAt := 250, param := {}, tags := extTags }), 100),
    (.external (.taskGet { id := oid "a" }), 500),
    (.external (.taskHalt { id := oid "a" }), 500),
    (.external (.promiseGet { id := oid "a" }), 500) ]

def kernelsResp : List Event :=
  [ .external (.promiseCreate { id := oid "a", timeoutAt := 250, param := {}, tags := extTags }),
    .external (.taskCreate { pid := "p0", ttl := 100, action := { id := oid "x", timeoutAt := 250, param := {}, tags := tgtTags } }),
    .external (.taskSuspend { id := oid "x", version := 1, actions := [{ awaited := oid "a", awaiter := oid "x" }] }),
    .external (.promiseSettle { id := oid "a", state := .resolved, value := {} }),
    .external (.promiseGet { id := oid "a" }),
    .external (.taskGet { id := oid "x" }),
    .external (.taskHalt { id := oid "x" }),
    .internal (.promiseTimeout { id := oid "a" }),
    .internal (.callback { awaited := oid "a", awaiter := oid "x" }),
    .internal (.taskLeaseTimeout { id := oid "x" }),
    .internal (.taskRetryTimeout { id := oid "x" }) ]

def seqsLenA (ks : List Event) : Nat → List (List Event)
  | 0 => [[]]
  | n + 1 => (seqsLenA ks n).flatMap (fun s => ks.map (fun k => s ++ [k]))

def seqsUpToA (ks : List Event) (n : Nat) : List (List Event) :=
  (List.range (n + 1)).flatMap (seqsLenA ks)

def instantiateA (ks : List Event) : List (Event × Nat) :=
  ks.mapIdx (fun i st => (st, 100 * (i + 1)))

end Abstract
