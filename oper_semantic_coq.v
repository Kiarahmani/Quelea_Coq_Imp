Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import parametes_coq.
Require Import config_coq.

Module Operational_Semantics.
Import Config.
Import parameters.
(*Specific Union for EFFVIS Rule*)
Parameter equality_repl_id: ReplID->ReplID->bool. (*CHANGE this to a more general rule    #!#!##!*)
Definition Store_Union  (Θ:Store) (r:ReplID) (η:Effect) (rcheck : ReplID): Exec_A   :=
if (equality_repl_id r rcheck) then (Θ rcheck) else (Θ rcheck).
(*Return inverse of a relation in Effects*)
Inductive rtrn_invs (rel:Relation) (n:Effect) : Ensemble Effect  :=
first: forall m:Effect, (rel n m) -> (rtrn_invs rel n) m.
(*Equality between two Ensemble*)
Definition Set_Equi (A:Type) (E1 E2: Ensemble A) : Prop :=
(Included A E1 E2)/\(Included A E2 E1).
Inductive Exec : Type :=
|E : Exec_A->  Relation -> Relation -> Relation -> Exec.
Definition return_vis (Ex:Exec): Relation := 
match Ex with 
|(E AA rr1 rr2 rr3) => rr1
end.
Definition return_so (Ex:Exec): Relation := 
match Ex with 
|(E AA rr1 rr2 rr3) => rr2
end.
Definition return_samobj (Ex:Exec): Relation := 
match Ex with 
|(E AA rr1 rr2 rr3) => rr3
end.
Notation "Ex -vis" := (return_vis Ex) (at level 0).
Notation "Ex -so" := (return_so Ex) (at level 0).
Notation "Ex -sameobj" := (return_samobj Ex) (at level 0).
(*The last three relations are parameters for each execution, but*)
Definition Rel_Closure (r:Relation):= clos_trans Effect r.
Definition Rel_Union (r1 r2 :Relation) (a b :Effect):Prop  :=  r1 a b \/ r2 a b.
Definition Rel_Intersect (r1 r2 :Relation) (a b :Effect):Prop  :=  r1 a b /\ r2 a b.
Definition return_A (Ex:Exec) := match Ex with
|(E A vis so sameobj) => A
end.
Definition hb (Ex:Exec) : Relation :=
Rel_Closure (Rel_Union Ex-vis Ex-so).
Definition soo (Ex:Exec) : Relation := (Rel_Intersect Ex-so Ex-sameobj).
Definition hbo (Ex: Exec) : Relation := (Rel_Closure (Rel_Union (soo Ex) (Ex-vis))).
Notation "Ex -A" := (return_A Ex) ( at level 0).
Notation "Ex -soo" := (soo Ex) (at level 0).
Notation "Ex -hb" := (hb Ex) (at level 0).
Notation "Ex -hbo" := (hbo Ex) (at level 0).


(*op_key is a tuple of the form <s,i,op>. Each Effect has an op_key*)
Inductive op_key : Type:=
|op_key_cons: SessID->SeqNo->OperName -> op_key.
Notation " '<' s , i , op '>' " := (op_key_cons s i op) (at level 0, op at level 20).

(********************************************************************************************************************************)
(*************************************************Auxiliary Reduction [OPER]************************************************)

Reserved Notation "'['  Θ '|-' A , C '~' r '~>' B , n ']'" (at level 80,Θ at level 10).
Inductive Aux_Reduct (Θ:Store) (r: ReplID) : Exec -> op_key -> Exec -> Effect -> Prop :=
OPER :  forall   (A A': Exec_A) (v: Value) 
                                (vis so sameobj vis' so' sameobj' : Relation) 
                                (s:SessID)(i:SeqNo) (op:OperName) (η η': Effect),

              (Compute (Θ r) op)=v -> 
              η.(sess)=s /\ η.(seq)=i /\ η.(val)=v /\ η.(oper)=op  ->
              (forall eff, ((A eff) /\ eff.(sess)=s /\ eff.(seq) = i-1) <-> eff=η' ) ->
               (forall eff,(A eff \/ eff=η )<->(A' eff)) ->
              (forall (eff eff':Effect), (vis' eff eff')<->((((Θ r) eff)/\eff'=η)\/((A eff/\ A eff')/\(vis eff eff')))) ->
              (forall (eff eff':Effect), (so' eff eff') <-> ((((so eff η') \/ (eff=η'))/\(eff'=η)) \/ (so eff eff'))) ->
              (forall eff eff', A' eff-> A' eff'-> (sameobj' eff eff')) 

                                                 ->[ Θ |- (E A vis so sameobj), <s,i,op>   ~r~>  (E A' vis' so' sameobj') ,η]
where "'[' Θ |- A , C '~' r '~>' B , n ']'" := (Aux_Reduct Θ r A C B n).






(*Operational Semantics - Figure 8*)
(*********************************************************************************************)

Variable Error_opcls:op_cls. (*Default return value if the session is empty *)
Reserved Notation "'[[' A , B , C '--' n '-->' A' , B' , C' ']]'" (at level 0, n at level 200).
Inductive Progress (η:Effect) :  Exec->Store->SessSoup ->Exec -> Store -> SessSoup ->Prop :=     

|EFFVIS: forall (Σ: SessSoup) ( Θ Θ' :Store) (Ex:Exec) (r:ReplID),
                                                                      (forall x:ReplID,(Θ' x)=(Store_Union Θ r η x))->
                                                                      (Included Effect (Union Effect (rtrn_invs Ex-vis η) (rtrn_invs Ex-so η)) (Θ r))->
                                                                      (Ex-A η)->
                                                                       ~((Θ r)η)                                                                          
                                                                                ->[[Ex,Θ,Σ --η-->  Ex ,Θ' ,Σ ]]

|EC: forall (τ:ConsCls) (Θ:Store)(Σ: SessSoup)(Ex Ex':Exec)(ss:SessID)(ii:SeqNo) 
                             (opp:OperName)(opcls:op_cls)(r:ReplID) (oplist:session), 
       ((τ=ec) -> [Θ |- Ex, <ss,ii,opp> ~r~> Ex', η] ->
                                                                                [[Ex,Θ,Σ+soup+ (mkSoup_Ing ss ii ((mkop_cls opp τ)::oplist))  --η-->  Ex' ,Θ ,Σ+soup+(mkSoup_Ing ss (ii+1) oplist ) ]]       )            


|CC: forall (τ:ConsCls)(Ex Ex':Exec) (Θ:Store)(Σ: SessSoup)(ing1 ing2:Soup_Ing)(r:ReplID)
                         (ss:SessID)(ii:SeqNo)(opp:OperName),  
                                                                                (τ=cc)->
                                                                                (Included Effect (rtrn_invs Ex'-so η) (Θ r))->
                                                                                ([ Θ |- Ex, <ss,ii,opp> ~r~> Ex', η])
                                                                                                    ->[[Ex,Θ,Σ+soup+ing1 --η-->  Ex' ,Θ ,Σ+soup+ing2 ]]


|SC: forall (τ:ConsCls)(Ex Ex':Exec) (Θ Θ':Store)(Σ: SessSoup)(ing1 ing2:Soup_Ing)(r:ReplID)
                          (ss:SessID)(ii:SeqNo)(opp:OperName),  
                                                                                 (τ=sc)->
                                                                                 ([Θ|-Ex, <ss,ii,opp> ~r~> Ex', η])->
                                                                                 (Included Effect (Ex-A)(Θ r))->
                                                                                 (Included ReplID (dom Θ) (dom Θ') /\ Included ReplID (dom Θ') (dom Θ)) ->
                                                                                 forall r':ReplID, ((dom Θ') r') ->  
                                                                                                (Set_Equi Effect (Θ' r') (Union Effect (Θ r')  (Singleton Effect η)))
                                                                                                                           ->[[Ex,Θ,Σ+soup+ing1 --η-->  Ex' ,Θ' ,Σ+soup+ing2 ]]

where " '[['  E , Θ , Σ  '--' η '-->'  F , T ,  S ']]' " := (Progress η E Θ Σ F T S).







End Operational_Semantics.