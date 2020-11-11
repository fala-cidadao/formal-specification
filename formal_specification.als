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

sig Citizen, Administrator extends User { }

sig Problem {
  comments: set Comment,
  state: State
}

sig Comment {
  owner: one User
}

sig State {
  actualStatus: Status,
  nextStatus: Status
}

abstract sig Status { }
sig InAnalysis, OnHold, InProgress, Concluded extends Status { }

------------------------------------------------------------------------------------------
--------------->                       Functions                          <---------------
------------------------------------------------------------------------------------------

fun getProblems [u: User]: set Problem {
  Problem & u.problems
}

fun getActualStatus [s: State]: Status {
  s.actualStatus
}

fun getNextStatus [s: State]: Status {
  s.nextStatus
}

------------------------------------------------------------------------------------------
--------------->                      Predicates                          <---------------
------------------------------------------------------------------------------------------

pred actualStatusIsInAnalysis [s: State] {
  getActualStatus[s] in InAnalysis
}

pred nextStatusIsOnHold [s: State] {
  getNextStatus[s] in OnHold
}

pred actualStatusIsOnHold [s: State] {
  getActualStatus[s] in OnHold
}

pred nextStatusIsInProgress [s: State] {
  getNextStatus[s] in InProgress
}

pred actualStatusIsInProgress [s: State] {
  getActualStatus[s] in InProgress
}

pred nextStatusIsConcluded [s: State] {
  getNextStatus[s] in Concluded
}

pred actualStatusIsConcluded [s: State] {
  getActualStatus[s] in Concluded
}

pred show [] {}

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
  all s: State | one s.~state
}

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

assert testOnlyCitizensCanCreateProblems {
  all a: Administrator | #a.problems = 0
}

assert testEachProblemHasOnlyOneCreator {
  all p: Problem | #(p.~problems) = 1
}

assert testCommentsOnlyExistInOneProblem {
  all c: Comment | #(c.~comments) = 1
}

assert testStateOnlyExistInOneProblem {
  all s: State | #(s.~state) = 1
}

assert testEachCommentHasOnlyOneOwner {
  all u: User | #(u.~owner) = 1
}

assert testActualStatusIsInAnalysisNextIsOnHold {
  all s: State | (getActualStatus[s] in InAnalysis) <=> (getNextStatus[s] in OnHold)
}

assert testActualStatusIsOnHoldNextIsInProgress {
  all s: State | (getActualStatus[s] in OnHold) <=> (getNextStatus[s] in InProgress)
}

assert testActualStatusIsInProgressNextIsConcluded {
  all s: State | (getActualStatus[s] in InProgress) => (getNextStatus[s] in Concluded)
}

assert testActualStatusIsConcludedNextIsConcluded {
  all s: State | (getActualStatus[s] in Concluded) => (getNextStatus[s] in Concluded)
}

------------------------------------------------------------------------------------------
--------------->                         Checks                           <---------------
------------------------------------------------------------------------------------------

check testOnlyCitizensCanCreateProblems for 50
check testEachProblemHasOnlyOneCreator for 50
check testCommentsOnlyExistInOneProblem for 50
check testStateOnlyExistInOneProblem for 50
check testEachCommentHasOnlyOneOwner for 50
check testActualStatusIsInAnalysisNextIsOnHold for 50
check testActualStatusIsOnHoldNextIsInProgress for 50
check testActualStatusIsInProgressNextIsConcluded for 50
check testActualStatusIsConcludedNextIsConcluded for 50

------------------------------------------------------------------------------------------
--------------->                         Show                             <---------------
------------------------------------------------------------------------------------------
run show for 20