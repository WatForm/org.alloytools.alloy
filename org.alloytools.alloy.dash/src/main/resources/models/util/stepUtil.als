/*******************************************************************************
 * Title: stepUtil.als
 * Authors: Jose Serna - jserna@uwaterloo.ca
 *
 * Notes: This module helps defining step relations for transition systems.
 *        Several axioms are included to get a significant model.
 *
 ******************************************************************************/

module util/stepUtil[S]

    one sig Step {
        initial: some S,
        next_step: S -> S,
        equality:  S -> S
    }

    // These functions must be defined by the calling code
    /** Define the elements that represent the initial state of the system */
    fun initial: S { Step.initial }
    /** Define the next state relation */
    fun nextStep: S -> S { Step.next_step }
    /** Define the criteria to consider two elements as equal */
    fun equals: S->S { Step.equality }

/****************************** EVENT SPACE ***********************************/
    abstract sig EventLabel {}
    abstract sig EnvironmentEvent, InternalEvent extends EventLabel {}


    // The system is always in some state
    //assert check_some_conf {
    //    ctl_mc[ag[{s: S | some s.conf}]]
    //}
