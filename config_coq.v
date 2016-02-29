Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import parametes_coq.

Module  Config.
  Import parameters.
  Inductive ConsCls:Type :=
  |ec: ConsCls
  |cc: ConsCls
  |sc: ConsCls.
  
  Inductive op_cls : Type := |mkop_cls: OperName -> ConsCls -> op_cls.
(*An operation tagged with its consistency class*)
  Definition session := list op_cls.
  Inductive Soup_Ing : Type := |mkSoup_Ing : SessID -> SeqNo -> session -> Soup_Ing.
  Definition SessSoup := (Ensemble Soup_Ing).

  Inductive My_Ing_Union (S:SessSoup) (I:Soup_Ing) : Soup_Ing -> Prop :=
  | Union_introl :forall x: Soup_Ing, In Soup_Ing S x -> ~ (x=I) ->  My_Ing_Union S I x
  | Union_intror :forall x: Soup_Ing, ~In Soup_Ing S x -> x=I   -> My_Ing_Union S I x.

  
    
  Notation " S  '|||'  I " :=  (Union Soup_Ing S ((Singleton Soup_Ing) I))(at level 80).  (*Add an ingredient to the soup*)
(**)

End Config.