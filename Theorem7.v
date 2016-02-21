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
Require Import lemma5.
Import Config.
Import parameters.
Import Operational_Semantics.

Variable m n:EffVar.
Infix " '#-->' " := contract_prop_implication (at level 80).
Infix " '#\/#' " := contract_prop_disjunction (at level 70).
Infix " '#/\#' " := contract_prop_conjunction (at level 60).
Notation " 'Sameobj' " := contract_sameobj.
Notation " 'Vis' " := contract_vis.
Notation " 'Equi' " := contract_equi.
Notation " 'PROP:'  ":= contract_prop_varvar (at level 90).
Notation " 'CONTR:'  ":=contract_free_cons (at level 95).
Notation " 'ALL'  ":=(contract_untyped_cons) (at level 96).

Definition Store_Contr (τ:ConsCls):contract_Contract:=
  match τ with
    |sc =>ALL  m (CONTR: ((PROP: Sameobj m η'') #-->
                                         ((PROP: Vis m η'') #\/#
                                          (PROP: Vis η'' m) #\/#
                                          (PROP: Equi m η''))))
    |cc => ALL m (CONTR: ((PROP: Sameobj m η'') #--> (PROP: Vis m η'')))
    |ec => ALL m (ALL n (CONTR: ((PROP: Hbo m n) #/\# (PROP: Vis n η'') #--> (PROP: Vis m η''))))
  end.

Definition CausCons (Θ:Store)(Ex:Exec):= 
                                        forall(r: ReplID)(a η:Effect), ((Θ r) η) -> (Ex-A a) -> ((Ex-hbo) a η) -> ((Θ r) a). 


Definition Models (Ex:Exec) (cont:contract_Contract) (eff:Effect) : Prop :=
  contract_Eval cont Ex eff (contract_free_number cont).
Notation " A '|=' B " := (Models A B) (at level 30).


Notation " 'Ψ' " := Store_Contr.

Theorem theorem7 : forall  (Ex Ex':Exec)(Θ Θ':Store)(Σ: SessSoup)(τ: ConsCls)(ss:SessID)
                      (ii:SeqNo)(σσ:session)(η:Effect) (op: OperName),
                     (WF Ex) -> (CausCons Θ Ex) ->
                     [[Ex,Θ,(Σ+soup+(mkSoup_Ing ss ii ((mkop_cls op τ)::σσ))) --η-->  Ex' ,Θ' , (Σ+soup+(mkSoup_Ing ss (ii+1) σσ)) ]]
                     -> WF Ex'/\ (Ex'|=Store_Contr τ) η.

Proof. intros Ex Ex' θ θ' Σ τ s i σ η op.
       intros HWF HCausCons. intro H.
       split.
       -Case"Proof of Well-Formedness of Ex'". 
        destruct H.
                +exact HWF.
                +apply Lemma5 in H1. exact H1. exact HWF.
                +apply Lemma5 in H1. exact H1. exact HWF.
                +apply Lemma5 in H0. exact H0. exact HWF.
               
       -Case"Proof of E'|=Ψτ". 
        destruct H.
           +admit.
           +SCase "[EC]".
            clear Σ s i σ.


        


        
        intuition.        
Qed.