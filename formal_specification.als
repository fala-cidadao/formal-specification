module falaCidadao

------------------------------------------------------------------------------------------
---------------                       Fala, Cidadão!                       ---------------
------------------------------------------------------------------------------------------


------------------------------------------------------------------------------------------
--------------->                         Signatures                       <---------------
------------------------------------------------------------------------------------------

abstract sig User {
  problems: set Problem
}

sig Citizen extends User { }
sig Administrator extends User { }

sig Problem {
  comments: set Comment,
  state: one State
}

sig Comment {
  owner: one User
}

sig State {
  actualStatus: one Status,
  nextStatus: one Status,
}

abstract sig Status { }
sig InAnalysis, OnHold, InProgress, Concluded extends Status { }

------------------------------------------------------------------------------------------
--------------->                       Functions                          <---------------
------------------------------------------------------------------------------------------

fun getProblems [u: User]: set Problem {
  u.problems
}

------------------------------------------------------------------------------------------
--------------->                      Predicates                          <---------------
------------------------------------------------------------------------------------------

pred actualStatusIsInAnalysis [s: State] {
  s.actualStatus in InAnalysis
}

pred nextStatusIsOnHold [s: State] {
  s.nextStatus in OnHold
}

pred actualStatusIsOnHold [s: State] {
  s.actualStatus in OnHold
}

pred nextStatusIsInProgress [s: State] {
  s.nextStatus in InProgress
}

pred actualStatusIsInProgress [s: State] {
  s.actualStatus in InProgress
}

pred nextStatusIsConcluded [s: State] {
  s.nextStatus in Concluded
}

pred actualStatusIsConcluded [s: State] {
  s.actualStatus in Concluded
}

------------------------------------------------------------------------------------------
--------------->                         Facts                            <---------------
------------------------------------------------------------------------------------------

fact onlyCitizensCanCreateProblems {
  all a: Administrator | #getProblems[a] = 0
}

fact eachProblemHasOnlyOneCreator {
  all p: Problem | one p.~problems
}

fact commentsOnlyExistInOneProblem {
  all c: Comment | one c.~comments
}

fact stateOnlyExistInOneProblem {
  all s: State | some s.~state
}

// fact statusOnlyExistInOneState {
//   all s: Status | some s.~actualStatus && some s.~nextStatus
// }

fact eachCommentHasOnlyOneOwner {
  all u: User | one u.~owner
}

fact actualStatusIsInAnalysisNextIsOnHold {
  all s: State | actualStatusIsInAnalysis[s] implies nextStatusIsOnHold[s]
}

fact actualStatusIsOnHoldNextIsInProgress {
  all s: State | actualStatusIsOnHold[s] implies nextStatusIsInProgress[s]
}

fact actualStatusIsInProgressNextIsConcluded {
  all s: State | actualStatusIsInProgress[s] implies nextStatusIsConcluded[s]
}

fact actualStatusIsConcludedNextIsConcluded {
  all s: State | actualStatusIsConcluded[s] implies nextStatusIsConcluded[s]
}

------------------------------------------------------------------------------------------
--------------->                        Asserts                           <---------------
------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------
--------------->                         Checks                           <---------------
------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------
--------------->                         Show                             <---------------
------------------------------------------------------------------------------------------
pred show [] {}
run show for 4 but 2 Problem