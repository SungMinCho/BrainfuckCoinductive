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
| eRead : nat -> event
| eWrite : nat -> event.

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
Hint Resolve events_eq_gen_monotone.

Theorem events_eq_left_tau : forall e1 e2, events_eq e1 e2 -> events_eq (Cons eTau e1) e2.
Proof.
  intros. pfold. punfold H.
Qed.

Theorem events_eq_right_tau : forall e1 e2, events_eq e1 e2 -> events_eq e1 (Cons eTau e2).
Proof.
  intros. pfold. punfold H.
Qed.

Theorem events_eq_read_same : forall n e1 e2, events_eq e1 e2 ->
                                         events_eq (Cons (eRead n) e1) (Cons (eRead n) e2).
Proof.
  intros. pfold. punfold H.
Qed.

Theorem events_eq_write_same : forall n e1 e2, events_eq e1 e2 ->
                                          events_eq (Cons (eWrite n) e1) (Cons (eWrite n) e2).
Proof.
  intros. pfold. punfold H.
Qed.

Hint Resolve events_eq_left_tau events_eq_right_tau events_eq_read_same events_eq_write_same.

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
| _memory : stream nat -> nat -> stream nat -> memory.

Inductive state : Type :=
| _state : instruction -> memory -> stream nat -> state. (* stream nat = input stream *)

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
         (_state t (_memory ls (S c) rs) is)
| step_dec0 : forall t ls rs is,
    step (_state (Dec t) (_memory ls 0 rs) is)
         eTau
         (_state t (_memory ls 0 rs) is)
| step_decs : forall t ls c rs is,
    step (_state (Dec t) (_memory ls (S c) rs) is)
         eTau
         (_state t (_memory ls c rs) is)
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
    step (_state ([ x ] y ) (_memory ls (S c) rs) is)
         eTau
         (_state (x ; [ x ] y) (_memory ls (S c) rs) is).

Inductive steps : state -> stream event -> Prop :=
| steps0 : forall m is, steps (_state End m is) Nil
| steps1 : forall i i' m m' is is' e es,
    step (_state i m is) e (_state i' m' is') ->
    steps (_state i' m' is') es ->
    steps (_state i m is) (Cons e es).

CoFixpoint zeroes : stream nat := Cons 0 zeroes.
Definition memory_init := _memory zeroes 0 zeroes.

Ltac inv H := inversion H; subst.

Theorem adding : forall ls rs n m is es,
    steps (_state ([Dec Right Inc Left End] Right Write End)
                  (_memory ls n (Cons m rs)) is)
          es ->
    events_eq es (Cons (eWrite (n+m)) Nil).
Proof.
  induction n; intros.
  repeat (match goal with [H:steps _ _ |- _] => inv H; clear H end;
          match goal with [H:step _ _ _ |- _] => inv H; clear H end).
  assert (H0m: 0+m = m). omega. rewrite H0m. clear H0m.
  inv H5.
  pcofix CIH. repeat (pfold; repeat constructor). inv H3.
  match goal with [H:steps _ _ |- _] => inv H; clear H end;
  match goal with [H:step _ _ _ |- _] => inv H; clear H end.
  match goal with [H:steps _ _ |- _] => inv H; clear H end;
  match goal with [H:step _ _ _ |- _] => inv H; clear H end.
  match goal with [H:steps _ _ |- _] => inv H; clear H end;
  match goal with [H:step _ _ _ |- _] => inv H; clear H end.
  match goal with [H:steps _ _ |- _] => inv H; clear H end;
  match goal with [H:step _ _ _ |- _] => inv H; clear H end.
  match goal with [H:steps _ _ |- _] => inv H; clear H end;
  match goal with [H:step _ _ _ |- _] => inv H; clear H end.
  apply IHn in H5.
  assert (n + S m = S n + m). omega. rewrite H in H5. clear H. simpl in *.
  auto 10.
Qed.

Theorem add1_works : forall n m es,
    steps (_state add1 memory_init (Cons n (Cons m Nil))) es ->
          events_eq es (Cons (eRead n) (Cons (eRead m) (Cons (eWrite (n + m)) Nil))).
Proof.
  intros.
  unfold add1 in *.
  inv H. inv H4; clear H4.
  inv H5. inv H4; clear H4.
  inv H6. inv H4; clear H4.
  inv H8. inv H4; clear H4.
  rewrite stream_destr_eq in H7.
  inv H7; clear H7.
  apply adding in H9.
  clear H5 H H8 H6.
  auto.
Qed.