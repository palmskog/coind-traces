From CoindTraces Require Import SsrExport.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Ltac invs h := inversion h; subst => {h}.

Section Traces.

Context {A : Type}.

CoInductive trace : Type  :=
| Tnil : A -> trace
| Tcons : A -> trace -> trace.

Definition trace_decompose (tr: trace): trace :=
match tr with
| Tnil st => Tnil st
| Tcons a tr' => Tcons a tr'
end.

Lemma trace_destr:
forall tr, tr = trace_decompose tr.
Proof. case => //=. Qed.

CoInductive bisim: trace -> trace -> Prop :=
| bisim_nil: forall st,
  bisim (Tnil st) (Tnil st)
| bisim_cons: forall e tr tr',
  bisim tr tr' ->
  bisim (Tcons e tr) (Tcons e tr').

Lemma bisim_refl : forall tr, bisim tr tr. 
Proof. 
cofix CIH. case.
- move => st. by apply bisim_nil. 
- move => st tr.
  apply bisim_cons.
  exact: CIH.
Qed.

Lemma bisim_sym : forall tr1 tr2, bisim tr1 tr2 -> bisim tr2 tr1. 
Proof.
cofix CIH. case. 
- move => s tr2 h1. invs h1.  by apply: bisim_nil.  
- move => s tr0 tr1 h1. invs h1.
  apply: bisim_cons.
  exact: (CIH _ _ H2).
Qed.

Lemma bisim_trans : forall tr1 tr2 tr3,
bisim tr1 tr2 -> bisim tr2 tr3 -> bisim tr1 tr3. 
Proof.
cofix CIH. case.  
- move => st tr0 tr1 h1 h2. invs h1. invs h2. by apply: bisim_nil.
- move => st tr0 tr1 tr2 h1 h2. invs h1. invs h2.
  apply: bisim_cons.
  exact: (CIH _ _ _ H2 H3).
Qed.

CoFixpoint trace_append (tr tr': trace): trace :=
match tr with
| Tnil st => tr'
| Tcons e tr0 => Tcons e (trace_append tr0 tr')
end.

Infix "+++" := trace_append (at level 60, right associativity).

Lemma trace_append_nil: forall st tr, (Tnil st) +++ tr = tr.
Proof. 
move => st tr.
rewrite [Tnil st +++ tr]trace_destr.
by case tr.
Qed.

Lemma trace_append_cons: forall e tr tr',
 (Tcons e tr) +++ tr' = Tcons e (tr +++ tr').
Proof.
move => st tr tr'.
rewrite [Tcons st tr +++ tr']trace_destr.
by case tr.
Qed.

Lemma trace_eq_append: forall tr1 tr2 tr3 tr4, 
 bisim tr1 tr2 -> bisim tr3 tr4 -> bisim (tr1 +++ tr3) (tr2 +++ tr4).
Proof. 
cofix CIH. case. 
- move => st1 tr1 tr2 tr3 h1 h2. invs h1.
  do 2 rewrite trace_append_nil.
  exact: h2.
- move => st tr1 tr2 tr3 tr4 h1 h2. invs h1. 
  do 2 rewrite trace_append_cons.
  apply: bisim_cons.
  exact: (CIH _ _ _ _ H2 h2).
Qed.

Definition hd tr :=
match tr with Tnil st => st | Tcons st tr0 => st end.

Lemma bisim_hd: forall tr0 tr1, bisim tr0 tr1 -> hd tr0 = hd tr1. 
Proof. 
move => tr0 tr1 h0. by invs h0.
Qed.

End Traces.
