Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Strings.String.

Module parameters.
  Parameter ReplID :Set.
  Parameter SessID : Set.
  Parameter OperName : Set.
  Parameter Value : Set.
  Definition SeqNo := nat.
  Record  Effect : Set :=  mkEffect { name:string; sess : SessID; seq : SeqNo; oper : OperName; val:Value}.
  Definition Relation := relation Effect.
  Definition Exec_A := (Ensemble Effect).
  Definition Store := ReplID -> Exec_A.
  Parameter Compute: Exec_A -> OperName -> Value.
  Parameter dom : Store -> (Ensemble ReplID).  
End parameters.


