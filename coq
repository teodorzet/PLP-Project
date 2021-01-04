Require Import String.
Require Import Coq.Lists.List.

Inductive Variabile := a | b | c | s | i | n | x.
Inductive DataType := int | bin.

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
Notation "A +' B" := (aplus A B) (at level 60, right associativity).
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
| fcall : string -> op.

Notation "T ~ A" := (declar T A) (at level 79).
Notation "A ::= B" := (assig A B) (at level 80).
Notation "A ;; B" := (seq A B) (at level 98, left associativity).
Notation "'while' A B" := (whil A B) (at level 96, A at level 9).
Notation "'ifs' X 'then' A 'else' B" := (ifthen X A B) (at level 97).
Notation "'fors' A # B # X" := (fordo A B X) (at level 96).
Notation "A '() {' B '}'" := (fmake A B) (at level 98).
Notation "A '()'" := (fcall A) (at level 99).


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
   x ::= x +' i) ;;
  ifs (s <!> 10) then (s ::= s +' 100) else (s ::= 0).
  
(* lista valori *)

Definition Env := Variabile -> nat.
Scheme Equality for Variabile.
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
Variable n : list string.

Definition alloc (env : Env) (var : Variabile) (type : DataType) : bool :=
  if (count_occ l var > 0)
  then false
  else concat var l.

Fixpoint execute (o : op) (env : Env) (gas : nat) : Env :=
  match gas with
  | 0 => env
  | S gas' => match o with
              | declar var type => alloc env var type
              | assig var exp => update env var (eval exp env)
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
              | fmake name A => concat name n, concat A f
              | fcall name => if (count_occ n name >0)
                              then execute (nth (nth
              end
  end.

