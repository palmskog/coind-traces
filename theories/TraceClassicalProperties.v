From Coq Require Import Classical.
From CoindTraces Require Import SsrExport Traces TraceProperties.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section TraceClassicalProperties.

Context {A B : Type}.

Local Notation trace := (@trace A B).

Lemma not_infiniteT_finiteT : forall tr : trace,
 ~ infiniteT tr -> finiteT tr.
Proof.
move => tr Hnot.
pose proof (classic (finiteT tr)) as Hinf.
case: Hinf => Hinf //.
case: Hnot.
exact: not_finiteT_infiniteT.
Qed.

Lemma finiteT_infiniteT : forall tr : trace,
 finiteT tr \/ infiniteT tr.
Proof.
move => tr.
pose proof (classic (finiteT tr)) as Hinf.
case: Hinf => Hinf; first by left.
right.
exact: not_finiteT_infiniteT.
Qed.

End TraceClassicalProperties.
