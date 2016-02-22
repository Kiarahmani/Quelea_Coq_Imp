Require Import case_coq.
Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Tactics.
Require Import parametes_coq.
Require Import config_coq.
Require Import oper_semantic_coq.
Require Import axioms_coq.
Require Import theorems_coq.
Require Import contract_definition.
Require Import contract_subs.
Require Import contract_Eval.
Require Import lemma5.
Require Import Stlc.
Require Import Imp.
Require Import Equiv.
Import STLC.
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





Theorem Injection_Help : forall Σ0 Σ ss ii opp s i op τ0 τ oplist σ,
  (Σ0 +soup+  mkSoup_Ing ss ii (mkop_cls opp τ0 :: oplist)) =
  (Σ +soup+  mkSoup_Ing s i (mkop_cls op τ :: σ)) ->
                                                 σ=oplist /\ τ=τ0 /\ opp=op /\ i=ii /\ s=ss /\ Σ=Σ0.
Proof. admit. Qed.



Definition Store_Contr (τ:ConsCls):contract_Contract:=
  match τ with
    |sc =>ALL  m (CONTR: ((PROP: Sameobj m η'') #-->
                                         ((PROP: Vis m η'') #\/#
                                          (PROP: Vis η'' m) #\/#
                                          (PROP: Equi m η''))))
    |cc => ALL m (CONTR: ((PROP: Sameobj m η'') #--> (PROP: Vis m η'')))
    |ec => ALL m (ALL n (CONTR: ((PROP: Hbo m n) #/\# (PROP: Vis n η'') #--> (PROP: Vis m η''))))
  end.
Notation " 'Ψ' " := Store_Contr.


Definition CausCons (Θ:Store)(Ex:Exec):= 
                                        forall(r: ReplID)(a η:Effect), ((Θ r) η) -> (Ex-A a) -> ((Ex-hbo) a η) -> ((Θ r) a). 


Definition Models (Ex:Exec) (cont:contract_Contract) (eff:Effect) : Prop :=
  contract_Eval cont Ex eff (contract_free_number cont).
Notation " A '|=' B " := (Models A B) (at level 30).



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
                +apply Lemma5 in H0. exact H0. exact HWF.
                +apply Lemma5 in H1. exact H1. exact HWF.
                +apply Lemma5 in H0. exact H0. exact HWF.
               
       -Case"Proof of E'|=Ψτ".
        inversion H.
        +admit.
        +apply Injection_Help in H0. intuition; subst; clear H H1.
         unfold Models.   cut ( (contract_free_number (Ψ ec)) = 3). intro cut. rewrite cut. *
         unfold Store_Contr.   compute.   contract_free_number.