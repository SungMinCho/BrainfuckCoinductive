Require Import ZArith.
Require Import paco.

Inductive instruction : Type :=
| iEnd : instruction
| iLeft : instruction -> instruction
| iRight : instruction -> instruction
| iInc : instruction -> instruction
| iDec : instruction -> instruction
| iRead : instruction -> instruction
| iWrite : instruction -> instruction
| iLoop : instruction -> instruction -> instruction.

Notation "'End'" := iEnd.
Notation "'Left' x" := (iLeft x) (at level 35, right associativity).
Notation "'Right' x" := (iRight x) (at level 35, right associativity).
Notation "'Inc' x" := (iInc x) (at level 35, right associativity).
Notation "'Dec' x" := (iDec x) (at level 35, right associativity).
Notation "'Read' x" := (iRead x) (at level 35, right associativity).
Notation "'Write' x" := (iWrite x) (at level 35, right associativity).
Notation "[ x ] y" := (iLoop x y) (at level 35, right associativity).

Fixpoint seq i1 i2 :=
match i1 with
| End => i2
| Left t => Left (seq t i2)
| Right t => Right (seq t i2)
| Inc t => Inc (seq t i2)
| Dec t => Dec (seq t i2)
| Read t => Read (seq t i2)
| Write t => Write (seq t i2)
| [ x ] y => [ x ] (seq y i2)
end.

Notation "x ; y" := (seq x y) (at level 39).

Definition add1 := (Read Right Read Left [ Dec Right Inc Left End ] Right Write End).

Definition add2 := (Right Read Left Read [ Dec Right Inc Left End ] Right Write End).

CoInductive stream (T:Type) :=
| Nil : stream T
| Cons : T -> stream T -> stream T.

Implicit Arguments Nil [T].
Implicit Arguments Cons [T].

Inductive event : Type :=
| eTau : event
| eRead : Z -> event
| eWrite : Z -> event.

Inductive events_eq_gen events_eq : stream event -> stream event -> Prop :=
| es_nil_nil : events_eq_gen events_eq Nil Nil
| es_left_tau : forall s1 s2 (R:events_eq s1 s2), events_eq_gen events_eq (Cons eTau s1) s2
| es_right_tau : forall s1 s2 (R:events_eq s1 s2), events_eq_gen events_eq s1 (Cons eTau s2)
| es_read_same : forall n s1 s2 (R:events_eq s1 s2), events_eq_gen events_eq (Cons (eRead n) s1) (Cons (eRead n) s2)
| es_write_same : forall n s1 s2 (R:events_eq s1 s2), events_eq_gen events_eq (Cons (eWrite n) s1) (Cons (eWrite n) s2).
Hint Constructors events_eq_gen.

Definition events_eq := paco2 events_eq_gen bot2.
Lemma events_eq_gen_monotone : monotone2 events_eq_gen.
Proof. pmonauto. Qed.

CoFixpoint taus : stream event := Cons eTau taus.

Definition stream_destr T (s:stream T) := 
match s with Nil => Nil | Cons h t => Cons h t end.

Implicit Arguments stream_destr [T].

Lemma stream_destr_eq : forall T (s:stream T), s = stream_destr s.
Proof. destruct s; auto. Qed.

Implicit Arguments stream_destr_eq [T].

Example taus_taus : events_eq taus taus.
Proof.
pcofix CIH.
pfold.
rewrite stream_destr_eq at 1. rewrite stream_destr_eq.
constructor. left. pfold. constructor. right. auto.
Qed.

Example nil_nil : events_eq Nil Nil.
Proof.
pcofix CIH.
pfold.
constructor.
Qed.

CoFixpoint p1 := (Cons (eWrite 1) p1).
CoFixpoint p2 := (Cons (eWrite 1) (Cons eTau p2)).

Example p1p2: events_eq p1 p2.
Proof.
  pcofix CIH.
  pfold.
  rewrite stream_destr_eq.
  rewrite stream_destr_eq at 1.
  constructor.
  constructor.
  pfold.
  constructor.
  auto.
Qed.


(* i used stream that can be finite. but it doesn't matter *)
Inductive memory : Type :=
| _memory : stream Z -> Z -> stream Z -> memory.

Inductive state : Type :=
| _state : instruction -> memory -> stream Z -> state. (* stream Z = input stream *)

Open Scope Z.

Inductive step : state -> event -> state -> Prop :=
| step_left : forall t l ls c rs is,
    step (_state (Left t) (_memory (Cons l ls) c rs) is)
         eTau
         (_state t (_memory ls l (Cons c rs)) is)
| step_right : forall t ls c r rs is,
    step (_state (Right t) (_memory ls c (Cons r rs)) is)
         eTau
         (_state t (_memory (Cons c ls) r rs) is)
| step_inc : forall t ls c rs is,
    step (_state (Inc t) (_memory ls c rs) is)
         eTau
         (_state t (_memory ls (c+1) rs) is)
| step_dec : forall t ls c rs is,
    step (_state (Dec t) (_memory ls c rs) is)
         eTau
         (_state t (_memory ls (c-1) rs) is)
| step_read : forall t ls c rs n ns,
    step (_state (Read t) (_memory ls c rs) (Cons n ns))
         (eRead n)
         (_state t (_memory ls n rs) ns)
| step_write : forall t ls c rs is,
    step (_state (Write t) (_memory ls c rs) is)
         (eWrite c)
         (_state t (_memory ls c rs) is)
| step_loopzero : forall x y ls rs is,
    step (_state ([ x ] y) (_memory ls 0 rs) is)
         eTau
         (_state y (_memory ls 0 rs) is)
| step_loopnonzero : forall x y ls c rs is,
    c <> 0 ->
    step (_state ([ x ] y ) (_memory ls c rs) is)
         eTau
         (_state (x ; [ x ] y) (_memory ls c rs) is).

Inductive steps : state -> stream event -> Prop :=
| steps0 : forall m is, steps (_state End m is) Nil
| steps1 : forall i i' m m' is is' e es,
    step (_state i m is) e (_state i' m' is') ->
    steps (_state i' m' is') es ->
    steps (_state i m is) (Cons e es).

CoFixpoint zeroes : stream Z := Cons 0 zeroes.
Definition memory_init := _memory zeroes 0 zeroes.