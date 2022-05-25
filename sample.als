open util/ordering[Snapshot] as snapshot
open util/boolean

sig Value extends univ {}
sig Snapshot extends univ { conf: set StateLabel, taken: set TransitionLabel, stable: one boolean/Bool,
    events: set EventLabel, Root_v1: set Value, Root_v2: set Value }

/***************************** STATE SPACE ************************************/
abstract sig StateLabel extends univ {}
abstract sig SystemState extends StateLabel {}
abstract sig Root extends SystemState {}
abstract sig Root_A extends Root {}
one sig Root_A_A1 extends Root_A {}
one sig Root_A_A2 extends Root_A {}
abstract sig Root_B extends Root {}
abstract sig EventLabel extends univ {}
abstract sig EnvironmentEvent extends EventLabel {}
abstract sig InternalEvent extends EventLabel {}
one sig Root_ev0 extends EnvironmentEvent {}
one sig Root_ev1 extends InternalEvent {}
one sig Root_ev2 extends InternalEvent {}
abstract sig TransitionLabel extends univ {}
one sig Root_B_t3 extends TransitionLabel {}
one sig Root_A_A1_t1 extends TransitionLabel {}
one sig Root_A_A2_t2 extends TransitionLabel {}

pred stable[s: Snapshot]{ s.(Snapshot <: stable) = boolean/True }

// // Predicates for the _Root_B_t3 transition.
pred pre_Root_B_t3[s: Snapshot]{
    Root_B in s.(Snapshot <: conf) and
    { ! {stable[s]} or
    Root_ev2 in s.(Snapshot <: events) }
}

pred pos_Root_B_t3[s,s_next: Snapshot]{
    s_next.(Snapshot <: conf) = { { s.(Snapshot <: conf) - Root_B } + Root_B } and
    s_next.(Snapshot <: Root_v1) = s.(Snapshot <: Root_v2) and
    s_next.(Snapshot <: Root_v2) = s.(Snapshot <: Root_v2) and
    (testIfNextStable[s, s_next, Root_B_t3, none] => 
        stable[s_next] and
        (stable[s] => 
            { s_next.(Snapshot <: events) & InternalEvent } = none
         else 
            { s_next.(Snapshot <: events) & InternalEvent } = { none + { InternalEvent & s.(Snapshot <: events) } }
        )
     else 
        ! {stable[s_next]} and
        (stable[s] => 
            { s_next.(Snapshot <: events) & InternalEvent } = none and
            { s_next.(Snapshot <: events) & EnvironmentEvent } = { s.(Snapshot <: events) & EnvironmentEvent }
         else 
            s_next.(Snapshot <: events) = { s.(Snapshot <: events) + none }
        )
    )
}

pred semantics_Root_B_t3[s,s_next: Snapshot]{
    (stable[s] => 
        s_next.(Snapshot <: taken) = Root_B_t3
     else 
        s_next.(Snapshot <: taken) = { s.(Snapshot <: taken) + Root_B_t3 } and
        no s.(Snapshot <: taken) & Root_B_t3
    )
}

pred Root_B_t3[s,s_next: Snapshot]{ pre_Root_B_t3[s] and pos_Root_B_t3[s, s_next] and semantics_Root_B_t3[s, s_next] }

pred enabledAfterStep_Root_B_t3[_s,s: Snapshot, t: TransitionLabel, genEvents: set InternalEvent]{
    Root_B in s.(Snapshot <: conf) and
    (stable[_s] => 
        no t & Root_B_t3 and
        Root_ev2 in { { _s.(Snapshot <: events) & EnvironmentEvent } + genEvents }
     else 
        no { _s.(Snapshot <: taken) + t } & Root_B_t3 and
        Root_ev2 in { _s.(Snapshot <: events) + genEvents }
    )
}

// // Predicates for the _Root_A_A1_t1 transition.
pred pre_Root_A_A1_t1[s: Snapshot]{
    Root_A_A1 in s.(Snapshot <: conf) and
    (stable[s] =>  Root_ev0 in { s.(Snapshot <: events) & EnvironmentEvent }  else  Root_ev0 in s.(Snapshot <: events) ) and
    s.(Snapshot <: Root_v2) = s.(Snapshot <: Root_v1)
}

pred pos_Root_A_A1_t1[s,s_next: Snapshot]{
    s_next.(Snapshot <: conf) = { { s.(Snapshot <: conf) - Root_A_A1 } + Root_A_A2 } and
    s_next.(Snapshot <: Root_v1) = s.(Snapshot <: Root_v1) and
    s_next.(Snapshot <: Root_v2) = s.(Snapshot <: Root_v2) and
    (testIfNextStable[s, s_next, Root_A_A1_t1, Root_ev2] => 
        stable[s_next] and
        (stable[s] => 
            { s_next.(Snapshot <: events) & InternalEvent } = Root_ev2
         else 
            { s_next.(Snapshot <: events) & InternalEvent } = { Root_ev2 + { InternalEvent & s.(Snapshot <: events) } }
        )
     else 
        ! {stable[s_next]} and
        (stable[s] => 
            { s_next.(Snapshot <: events) & InternalEvent } = Root_ev2 and
            { s_next.(Snapshot <: events) & EnvironmentEvent } = { s.(Snapshot <: events) & EnvironmentEvent }
         else 
            s_next.(Snapshot <: events) = { s.(Snapshot <: events) + Root_ev2 }
        )
    ) and
    Root_ev2 in s_next.(Snapshot <: events)
}

pred semantics_Root_A_A1_t1[s,s_next: Snapshot]{
    (stable[s] => 
        s_next.(Snapshot <: taken) = Root_A_A1_t1
     else 
        s_next.(Snapshot <: taken) = { s.(Snapshot <: taken) + Root_A_A1_t1 } and
        no s.(Snapshot <: taken) & { Root_A_A1_t1 + Root_A_A2_t2 }
    )
}

pred Root_A_A1_t1[s,s_next: Snapshot]{
    pre_Root_A_A1_t1[s] and
    pos_Root_A_A1_t1[s, s_next] and
    semantics_Root_A_A1_t1[s, s_next]
}

pred enabledAfterStep_Root_A_A1_t1[_s,s: Snapshot, t: TransitionLabel, genEvents: set InternalEvent]{
    Root_A_A1 in s.(Snapshot <: conf) and
    s.(Snapshot <: Root_v2) = s.(Snapshot <: Root_v1) and
    (stable[_s] => 
        no t & { Root_A_A1_t1 + Root_A_A2_t2 } and
        Root_ev0 in { { _s.(Snapshot <: events) & EnvironmentEvent } + genEvents }
     else 
        no { _s.(Snapshot <: taken) + t } & { Root_A_A1_t1 + Root_A_A2_t2 } and
        Root_ev0 in { _s.(Snapshot <: events) + genEvents }
    )
}

// // Predicates for the _Root_A_A2_t2 transition.
pred pre_Root_A_A2_t2[s: Snapshot]{
    Root_A_A2 in s.(Snapshot <: conf) and
    { ! {stable[s]} or
    Root_ev2 in s.(Snapshot <: events) }
}

pred pos_Root_A_A2_t2[s,s_next: Snapshot]{
    s_next.(Snapshot <: conf) = { { s.(Snapshot <: conf) - Root_A_A2 } + Root_A_A1 } and
    s_next.(Snapshot <: Root_v2) = s.(Snapshot <: Root_v2) and
    s_next.(Snapshot <: Root_v1) = s.(Snapshot <: Root_v1) and
    (testIfNextStable[s, s_next, Root_A_A2_t2, Root_ev1] => 
        stable[s_next] and
        (stable[s] => 
            { s_next.(Snapshot <: events) & InternalEvent } = Root_ev1
         else 
            { s_next.(Snapshot <: events) & InternalEvent } = { Root_ev1 + { InternalEvent & s.(Snapshot <: events) } }
        )
     else 
        ! {stable[s_next]} and
        (stable[s] => 
            { s_next.(Snapshot <: events) & InternalEvent } = Root_ev1 and
            { s_next.(Snapshot <: events) & EnvironmentEvent } = { s.(Snapshot <: events) & EnvironmentEvent }
         else 
            s_next.(Snapshot <: events) = { s.(Snapshot <: events) + Root_ev1 }
        )
    ) and
    Root_ev1 in s_next.(Snapshot <: events)
}

pred semantics_Root_A_A2_t2[s,s_next: Snapshot]{
    (stable[s] => 
        s_next.(Snapshot <: taken) = Root_A_A2_t2
     else 
        s_next.(Snapshot <: taken) = { s.(Snapshot <: taken) + Root_A_A2_t2 } and
        no s.(Snapshot <: taken) & { Root_A_A1_t1 + Root_A_A2_t2 }
    )
}

pred Root_A_A2_t2[s,s_next: Snapshot]{
    pre_Root_A_A2_t2[s] and
    pos_Root_A_A2_t2[s, s_next] and
    semantics_Root_A_A2_t2[s, s_next]
}

pred enabledAfterStep_Root_A_A2_t2[_s,s: Snapshot, t: TransitionLabel, genEvents: set InternalEvent]{
    Root_A_A2 in s.(Snapshot <: conf) and
    (stable[_s] => 
        no t & { Root_A_A1_t1 + Root_A_A2_t2 } and
        Root_ev2 in { { _s.(Snapshot <: events) & EnvironmentEvent } + genEvents }
     else 
        no { _s.(Snapshot <: taken) + t } & { Root_A_A1_t1 + Root_A_A2_t2 } and
        Root_ev2 in { _s.(Snapshot <: events) + genEvents }
    )
}

/* Overview 
 * init[] determines whether a snapshot is initial,
 * small_step [s,s_next] determines if a pair of Snapshots is a small step,
*/
pred init[s: Snapshot]{
    s.(Snapshot <: conf) = { Root_A_A1 + Root_B } and
    no s.(Snapshot <: taken) and
    no s.(Snapshot <: events) & InternalEvent and
    stable[s]
}

// Evaluates to true if the next Snapshot is stable. The next Snapshot will be stable if no more transitions will
// be enabled after taking the current transition 
pred testIfNextStable[s,s_next: Snapshot, t: TransitionLabel, genEvents: set InternalEvent]{
    ! {enabledAfterStep_Root_B_t3[s, s_next, t, genEvents]} and
    ! {enabledAfterStep_Root_A_A1_t1[s, s_next, t, genEvents]} and
    ! {enabledAfterStep_Root_A_A2_t2[s, s_next, t, genEvents]}
}

pred small_step[s,s_next: Snapshot]{ { Root_B_t3[s, s_next] or Root_A_A1_t1[s, s_next] or Root_A_A2_t2[s, s_next] } }

// Test whether two consequtive Snapshots are equal. Two Snapshots are equal if they have the same set of active
// control states, events generated, transitions taken in the big step, and system variables 
pred equals[s,s_next: Snapshot]{
    s_next.(Snapshot <: conf) = s.(Snapshot <: conf) and
    s_next.(Snapshot <: events) = s.(Snapshot <: events) and
    s_next.(Snapshot <: taken) = s.(Snapshot <: taken) and
    s_next.(Snapshot <: Root_v1) = s.(Snapshot <: Root_v1) and
    s_next.(Snapshot <: Root_v2) = s.(Snapshot <: Root_v2)
}

// Test whether any transitions are enabled. A transition is enabled if the Snapshot satisfies its pre-condition
pred isEnabled[s: Snapshot]{ { pre_Root_B_t3[s] or pre_Root_A_A1_t1[s] or pre_Root_A_A2_t2[s] } }

/* This fact defines the following:
   Consequtive snapshots that have the same set of active control states, events generated, transitions taken in the big step, and system variables are equal
*/
fact different_atoms { (all  s,s_next: one Snapshot | equals[s, s_next] => { s = s_next }) }

/* Create a Trace for the Model. This fact defines the following: 
   The first Snapshot in the ordering module should conforn to the initial conditions.
   A small step must be taken by consequetive Snapshots in the ordering module.
   A Snapshot that has not completed a big step (i.e. is not stable) must take a next step.
   The last Snapshot in a trace must be stable.
*/
fact traces {
    init[snapshot/first] and
    (all  s: one Snapshot | ! {s in snapshot/last} => small_step[s, s. (snapshot/next)]) and
    (all  s: one Snapshot | ! {stable[s]} => some s. (snapshot/next))
}

assert t1_is_taken {
    (all 
        s: one Snapshot | Root_ev1 in s.(Snapshot <: events) and
        (Snapshot <: Root_v1) = (Snapshot <: Root_v2) => (some 
            s_next: one s. (*(snapshot/next)) | Root_A_A1_t1 in s_next.(Snapshot <: taken)))
}

check t1_is_taken for 3 Snapshot, 4 Value, 2 EventLabel, 3 StateLabel, 2 StateLabel, 3 TransitionLabel, 4 EventLabel


