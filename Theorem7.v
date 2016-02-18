Require Import case_coq.
Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import parametes_coq.
Require Import config_coq.
Require Import oper_semantic_coq.
Require Import axioms_coq.
Require Import theorems_coq.
Require Import contract_definition.
Require Import contract_subs.
Require Import contract_Eval.
Import Config.
Import parameters.
Import Operational_Semantics.


Definition Models (Ex:Exec) (cont:contract_Contract) (eff:Effect) : Prop := contract_Eval cont Ex eff (contract_free_number cont).
Notation " A '|=' B " := (Models A B) (at level 30).



Variable Ex:Exec.
Variable ψ : contract_Contract.


Check Ex |= ψ.



Definition CausCons (Θ:Store)(Ex:Exec):= 
                                        forall(r: ReplID)(a η:Effect), ((Θ r) η) -> (Ex-A a) -> ((Ex-hbo) a η) -> ((Θ r) a). 


Definition Store_Contr (τ:ConsCls):=
  match τ with
    |ec => forall(a b:Effect), (Ex-hbo a b)/\(Ex-vis b η') -> (Ex-vis a η') 
    |cc => forall(a:Effect),   (Ex-hbo a η')              -> (Ex-vis a η')
    |sc => 
  end.










Theorem theorem7 : 