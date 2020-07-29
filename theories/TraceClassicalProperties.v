From Coq Require Import Classical.
From CoindTraces Require Import SsrExport Traces TraceProperties.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section TraceClassicalProperties.

Context {A B : Type}.

Local Notation trace := (@trace A B).

Lemma not_infinite_finite : forall tr : trace,
 ~ infinite tr -> finite tr.
Proof.
move => tr Hnot.
pose proof (classic (finite tr)) as Hinf.
case: Hinf => Hinf //.
case: Hnot.
exact: not_finite_infinite.
Qed.

Lemma finite_infinite : forall tr : trace,
 finite tr \/ infinite tr.
Proof.
move => tr.
pose proof (classic (finite tr)) as Hinf.
case: Hinf => Hinf; first by left.
right.
exact: not_finite_infinite.
Qed.

End TraceClassicalProperties.
