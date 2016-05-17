Require Import ZArith.
Require Import paco.

Inductive instruction : Type :=
| iEnd : instruction
| iLeft : instruction -> instruction
| iRight : instruction -> instruction
| iInc : instruction -> instruction
| iDec : instruction -> instruction
| iRead : instruction -> instruction
| iPrint : instruction -> instruction
| iLoop : instruction -> instruction -> instruction.

Notation "'End'" := iEnd.
Notation "'Left' x" := (iLeft x) (at level 35, right associativity).
Notation "'Right' x" := (iRight x) (at level 35, right associativity).
Notation "'Inc' x" := (iInc x) (at level 35, right associativity).
Notation "'Dec' x" := (iDec x) (at level 35, right associativity).
Notation "'Read' x" := (iRead x) (at level 35, right associativity).
Notation "'Print' x" := (iPrint x) (at level 35, right associativity).
Notation "[ x ] y" := (iLoop x y) (at level 35, right associativity).

Fixpoint seq i1 i2 :=
match i1 with
| End => i2
| Left t => Left (seq t i2)
| Right t => Right (seq t i2)
| Inc t => Inc (seq t i2)
| Dec t => Dec (seq t i2)
| Read t => Read (seq t i2)
| Print t => Print (seq t i2)
| [ x ] y => [ x ] (seq y i2)
end.

Notation "x ; y" := (seq x y) (at level 39).

Definition add1 := (Read Right Read Left [ Dec Right Inc Left End ] Right Print End).

Definition add2 := (Right Read Left Read [ Dec Right Inc Left End ] Right Print End).

CoInductive stream (T:Type) :=
| Nil : stream T
| Cons : T -> stream T -> stream T.

Implicit Arguments Nil [T].
Implicit Arguments Cons [T].

Inductive event : Type :=
| eTau : event
| eRead : Z -> event
| ePrint : Z -> event.

Inductive events_eq_gen events_eq : stream event -> stream event -> Prop :=
| es_nil_nil : events_eq_gen events_eq Nil Nil
| es_left_tau : forall s1 s2 (R:events_eq s1 s2), events_eq_gen events_eq (Cons eTau s1) s2
| es_right_tau : forall s1 s2 (R:events_eq s1 s2), events_eq_gen events_eq s1 (Cons eTau s2)
| es_read_same : forall n s1 s2 (R:events_eq s1 s2), events_eq_gen events_eq (Cons (eRead n) s1) (Cons (eRead n) s2)
| es_print_same : forall n s1 s2 (R:events_eq s1 s2), events_eq_gen events_eq (Cons (ePrint n) s1) (Cons (ePrint n) s2).
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

(* i used stream that can be finite. but it doesn't matter *)
Inductive memory : Type :=
| _memory : stream Z -> Z -> stream Z -> memory.

Open Scope Z.

Inductive behavior : instruction -> memory -> stream event -> Prop :=
| beh_end : forall m, behavior End m Nil
| beh_left : forall t l ls c rs es,
             behavior t (_memory ls l (Cons c rs)) es
          -> behavior (Left t) (_memory (Cons l ls) c rs) es
| beh_right : forall t ls c r rs es,
              behavior t (_memory (Cons c ls) r rs) es
           -> behavior (Right t) (_memory ls c (Cons r rs)) es
| beh_inc : forall t ls c rs es,
            behavior t (_memory ls (c+1) rs) es
            -> behavior (Inc t) (_memory ls c rs) es
| beh_dec : forall t ls c rs es,
            behavior t (_memory ls (c-1) rs) es
            -> behavior (Inc t) (_memory ls c rs) es
| beh_read : forall t ls c rs es n,
             behavior t (_memory ls n rs) es
             -> behavior (Read t) (_memory ls c rs) (Cons (eRead n) es)
| beh_print : forall t ls c rs es,
             behavior t (_memory ls c rs) es
             -> behavior (Print t) (_memory ls c rs) (Cons (ePrint c) es)
| beh_loop_zero : forall x t ls c rs es,
                  behavior t (_memory ls c rs) es
                  -> c = 0
                  -> behavior ([ x ] t) (_memory ls c rs) es
| beh_loop_nonzero : forall x t ls c rs es,
                     behavior (x ; [ x ] t) (_memory ls c rs) es
                     -> c <> 0
                     -> behavior ([ x ] t) (_memory ls c rs) es.

CoFixpoint zeroes : stream Z := Cons 0 zeroes.
Definition memory_init := _memory zeroes 0 zeroes.


Lemma add1_works : forall es : stream event, behavior add1 memory_init es ->
                   exists n m, events_eq es (Cons (eRead n) (Cons (eRead m) (Cons (ePrint (n+m)) Nil))).
Proof.
intros.
repeat (match goal with [H:behavior _ _ _ |- _] => inversion H;subst;clear H end).
exists 0. exists n0.
assert (0 + n0 = n0). ring. rewrite H.
repeat (pfold; repeat constructor).
Qed.





