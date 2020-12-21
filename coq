Require Import String.

Inductive Variabile := a | b | c | s | i | n | x.
Inductive DataType := int | bool.

Inductive exp :=
| atype : DataType -> exp
| avar : Variabile -> exp
| anum : nat -> exp
| aplus : exp -> exp -> exp
| amul : exp -> exp -> exp
| amin : exp -> exp -> exp
| adiv : exp -> exp -> exp
| amod : exp -> exp -> exp
| apow : exp -> exp -> exp.

Coercion atype : DataType >-> exp.
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
| bor : exp -> exp -> bexp.

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
| fordo : op -> bexp -> op -> op -> op.

Notation "T ~ A" := (declar T A) (at level 79).
Notation "A ::= B" := (assig A B) (at level 80).
Notation "A ;; B" := (seq A B) (at level 98, left associativity).
Notation "'while' A B" := (whil A B) (at level 96, A at level 9).
Notation "'ifs' X 'then' A 'else' B" := (ifthen X A B) (at level 97).
Notation "'fors' A # B # C # X" := (fordo A B C X) (at level 96).


Definition ecuation :=
  int ~ x ;; 
  int ~ s ;;
  int ~ i ;;
  x ::= 5 ;;
  s ::= 0 ;;
  x ::= pow x @ 3  ;;
  fors (i ::= 0) # (i <' 4) # (i ::= i +' 1) #
  (s ::= s +' x ;;
   x ::= x +' i) ;;
  ifs (s <!> 10) then (s ::= s +' 100) else (s ::= 0).
  

