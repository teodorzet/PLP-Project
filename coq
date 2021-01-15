Require Import String.
Require Import Coq.Lists.List.



Inductive Variabile := a | b | c | s | i | n | x.
Inductive DataType := int | bin.

Scheme Equality for Variabile.

Inductive exp :=
| avar : Variabile -> exp
| anum : nat -> exp
| aplus : exp -> exp -> exp
| amul : exp -> exp -> exp
| amin : exp -> exp -> exp
| adiv : exp -> exp -> exp
| amod : exp -> exp -> exp
| apow : exp -> exp -> exp.

Coercion avar : Variabile >-> exp.
Coercion anum : nat >-> exp.
Notation "A +' B" := (aplus A B) (at level 59, right associativity).
Notation "A *' B" := (amul A B) (at level 58, left associativity).
Notation "A -' B" := (amin A B) (at level 59, right associativity).
Notation "A /' B" := (adiv A B) (at level 57, left associativity).
Notation "A %' B" := (amod A B) (at level 55).
Notation "'pow' A @ B" := (apow A B) (at level 54).

Inductive bexp :=
| btrue : bexp
| bfalse : bexp
| bneg : bexp -> bexp
| band : bexp -> bexp -> bexp
| bless : exp -> exp -> bexp
| bequal : exp -> exp -> bexp
| bmore : exp -> exp -> bexp
| bdiff : exp -> exp -> bexp
| bor : bexp -> bexp -> bexp.

Notation "! A" := (bneg A) (at level 52, left associativity).
Notation "A <' B" := (bless A B) (at level 57).
Notation "A =' B" := (bequal A B) (at level 57).
Notation "A >' B" := (bmore A B) (at level 57).
Notation "A 'and'' B" := (band A B) (at level 53, left associativity).
Notation "A <!> B" := (bdiff A B) (at level 52).
Notation "A 'or'' B" := (bor A B) (at level 51).


Inductive op :=
| declar : DataType -> Variabile -> op
| assig : Variabile -> exp -> op
| seq : op -> op -> op
| whil : bexp -> op -> op
| ifthen : bexp -> op -> op -> op
| fordo : bexp -> op -> op -> op
| fmake : string -> op -> op
| fcall : string -> op
| brk : op -> op.

Notation "T ~ A" := (declar T A) (at level 79).
Notation "A ::= B" := (assig A B) (at level 80).
Notation "A ;; B" := (seq A B) (at level 98, left associativity).
Notation "'while' A B" := (whil A B) (at level 96, A at level 9).
Notation "'ifs' X 'then' A 'else' B" := (ifthen X A B) (at level 97).
Notation "'fors' A # B # X" := (fordo A B X) (at level 96).
Notation "A '() {' B '}'" := (fmake A B) (at level 98).
Notation "A '()'" := (fcall A) (at level 99).
Notation "A 'break'" := (brk A) (at level 101).


Definition ecuation :=
  int ~ x ;; 
  int ~ s ;;
  int ~ i ;;
  x ::= 5 ;;
  s ::= 0 ;;
  x ::= pow x @ 3  ;;
  i ::= 0 ;;
  fors (i <' 4) # (i ::= i +' 1) #
  (s ::= s +' x ;;
   x ::= x +' i 
   break
  ) ;;
  ifs (s <!> 10) then (s ::= s +' 100) else (s ::= 0).

(* lista valori *)

Definition Env := Variabile -> nat.
Check Variabile_beq.
Require Import Coq.ZArith.Zpower.
Require Import Wf_nat ZArith_base Zcomplements.
Require Export Zpow_def.

Definition update (env : Env)
           (var : Variabile) (value : nat) : Env :=
  fun var' => if (Variabile_beq var' var)
              then value
              else (env var').

Fixpoint eval (a : exp) (env : Env) : nat :=
  match a with
  | avar var => env var
  | anum x' => x'
  | aplus a1 a2 => (eval a1 env) + (eval a2 env)
  | amul a1 a2 => (eval a1 env) * (eval a2 env)
  | amin a1 a2 => (eval a1 env) - (eval a2 env)
  | adiv a1 a2 => Nat.div (eval a1 env) (eval a2 env)
  | amod a1 a2 => Nat.modulo (eval a1 env) (eval a2 env)
  | apow var p => Z.to_nat (Zpower_nat (Z.of_nat (eval var env)) (eval p env))
  end.

Definition morefn (val1 : nat) (val2 : nat) : bool :=
  if (Nat.leb val1 val2)
  then false
  else true.

Definition notequal (val1 : nat) (val2 : nat) : bool :=
  if (Nat.eqb val1 val2)
  then false
  else true.

Fixpoint beval (b : bexp) (env : Env) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | bneg b' => negb (beval b' env)
  | band a1 a2 => andb (beval a1 env) (beval a2 env)
  | bless a1 a2 => Nat.leb (eval a1 env) (eval a2 env)
  | bequal a1 a2 => Nat.eqb (eval a1 env) (eval a2 env)
  | bmore a1 a2 => morefn (eval a1 env) (eval a2 env)
  | bdiff a1 a2 => notequal (eval a1 env) (eval a2 env)
  | bor a1 a2 => orb (beval a1 env) (beval a2 env)
  end.

Import ListNotations.
Section Lists.


Variable l : list Variabile.
Variable f : list string.
Variable k : list string.

Check count_occ.
Check count_occ string_dec.
Check Variabile.
Print Variabile.

Reserved Notation "A =[ S ]=> N" (at level 60).


Inductive aeval : exp -> Env -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n 
| var : forall v sigma, avar v =[ sigma ]=> (sigma v) 
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| minus : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 - i2 ->
    a1 -' a2 =[sigma]=> n
| divide : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = Nat.div i1 i2 ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = Nat.modulo i1 i2 ->
    a1 %' a2 =[sigma]=> n
| power : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = Z.to_nat (Zpower_nat (Z.of_nat i1) i2) ->
    apow a1 a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Hint Constructors aeval.

Require Extraction.
Extraction Language Haskell.
(*Recursive Extraction eval.*)

Reserved Notation "B ={ S }=> B'" (at level 70).

Inductive bevall : bexp -> Env -> bool -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.leb i1 i2 ->
    a1 <' a2 ={ sigma }=> b
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bneg b) ={ sigma }=> false
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bneg b) ={ sigma }=> true
| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    band b1 b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false
| e_ortrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    bor b1 b2 ={ sigma }=> true
| e_orfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    b2 ={ sigma }=> false ->
    bor b1 b2 ={ sigma }=> false
| e_dif : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = notequal i1 i2 ->
    a1 <!> a2 ={ sigma }=> b
| e_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.eqb i1 i2 ->
    a1 =' a2 ={ sigma }=> b 

where "B ={ S }=> B'" := (bevall B S B').


Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Check update.
Inductive stmt : op -> Env -> Env -> Prop :=
| e_assignment: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x ::= a) -{ sigma }-> sigma'

| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->

    (s1 ;; s2) -{ sigma }-> sigma2
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    whil b s -{ sigma }-> sigma

| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    whil b s -{ sigma }-> sigma'

| e_ifelsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthen b s1 s2 -{ sigma }-> sigma'

| e_ifelsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthen b s1 s2 -{ sigma }-> sigma'

| e_forstrue : forall b p s sigma sigma',
    b ={ sigma }=> true ->
    s -{ sigma }-> sigma' ->
    p -{ sigma }-> sigma' ->
    fordo b p s -{ sigma }-> sigma'

| e_forsfalse : forall b p s sigma,
    b ={ sigma }=> false ->
    fordo b p s -{ sigma }-> sigma

| break_while : forall b s sigma sigma',
    brk s -{ sigma }-> sigma' ->
    whil b s -{ sigma }-> sigma

| break_fors : forall b p s sigma sigma',
    brk s -{ sigma }-> sigma' ->
    fordo b p s -{ sigma }-> sigma

where "s -{ sigma }-> sigma'" := (stmt s sigma sigma').

Definition sum1 :=
  n ::= 1 ;;
  s ::= 0 ;;
  ifthen ( 2 <' n ) (s ::= 1) (s ::= 2)
  ;; s ::= pow s @ 2.

Compute (stmt sum1).

Definition sum2 :=
  n ::= 1 ;;
  i ::= 0 ;;
  fordo (i <' 5) (i ::= i +' 1) (n ::= n +' 2).

Definition state0 := fun (x : Variabile) => 0.

Example eval_sum1 :
  exists state, sum1 -{ state0 }-> state /\ state s = 4.
Proof.
  eexists.
  split.
  - unfold sum1.
    + eapply e_seq.
      ++ eapply e_seq.
       +++ eapply e_seq.
        ** eapply e_assignment; eauto.
        ** eapply e_assignment; eauto.
       +++ eapply e_ifelsefalse.
        ** eapply e_lessthan; auto.
        ** eapply e_assignment; eauto.
      ++ eapply e_assignment; eauto.
  - simpl. unfold update. simpl. reflexivity.
Qed.

Definition sum3 :=
  n ::= 0 ;;
  i ::= 0 ;;
  while (i <' 3)
  (
  n ::= n +' i ;;
  ifthen (i =' 2) (n ::= n +' i break) ( n ::= n +' i)
  ).

(*Example eval_sum3 :
  exists state, sum3 -{ state0 }-> state /\ state n = 6.
Proof.
  eexists.
  split.
  - unfold sum1.
    + eapply e_seq.
      ++ eapply e_seq.
        ** eapply e_assignment; eauto.
        ** eapply e_assignment; eauto.
       ++ eapply e_whiletrue; auto.
        ** eapply e_lessthan; auto.
        ** eapply e_seq; eauto.
        *** eapply e_seq; eauto.
        **** eapply e_assignment; eauto.
        **** eapply e_ifelsefalse; eauto.
        ***** eapply e_equal; eauto.
        ***** eapply e_assignment; eauto.
        *** eapply e_whiletrue; auto.
        **** eapply e_lessthan; auto.
        **** eapply e_seq; eauto.
        ***** eapply e_seq; eauto.
        ****** eapply e_assignment; eauto.
        ****** eapply e_ifelsefalse; eauto.
        ******* eapply e_equal; eauto.
        ******* eapply e_assignment; eauto.
        ***** eapply e_whiletrue; auto.
        ****** eapply e_lessthan; auto.
        ****** eapply e_seq; eauto.
        ******* eapply e_seq; eauto.
        ******** eapply e_assignment; eauto.
        ******** eapply e_ifelsetrue; eauto.
        ********* eapply e_equal; eauto.
        ********** eapply e_true; eauto.
  - simpl. unfold update. simpl. reflexivity.
Qed.*)


Fixpoint execute (o : op) (env : Env) (gas : nat) : Env :=
  match gas with
  | 0 => env
  | S gas' => match o with
              | assig a exp => update env a (eval exp env)
              | seq A B => execute B (execute A env gas') gas'
              | whil cond A => if (beval cond env)
                               then execute (A ;; (whil cond A)) env gas'
                               else env
              | ifthen cond A B => if (beval cond env)
                                   then execute A env gas'
                                   else execute B env gas'
              | fordo cond step A => if (beval cond env)
                                     then execute (A ;; step ;; (fordo cond step A)) env gas'
                                     else env
              | brk A => env
              end
  end.


