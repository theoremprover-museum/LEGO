(* proof that the fresh var v is not necessary in par_red1_beta *)

Module pred1 Import par_red1;

Inductive [pred1 : Trm->Trm->Prop]  Relation
Constructors 
[pr1_refl_sort : {s:SS} pred1 (sort s) (sort s)]
[pr1_refl_par : {p:PP} pred1 (par p) (par p)]

[pr1_beta:{U|Trm}{vclU:Vclosed U}{A,A'|Trm}{premA:pred1 A A'}
               {u|VV}{B,B'|Trm}{p|PP}
               {noccB:is_ff (poccur p B)}
               {premB:pred1 (alpha p u B) B'}
                pred1 (app (lda u U B) A) (psub A' p B')]

[pr1_pi:{A,A'|Trm}{premA:pred1 A A'} 
              {u,v|VV}{B,B'|Trm}{p|PP} 
              {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
              {premB:pred1 (alpha p u B) (alpha p v B')} 
               pred1 (pi u A B) (pi v A' B')]

[pr1_lda:{A,A'|Trm}{premA:pred1 A A'} 
               {u,v|VV}{B,B'|Trm}{p|PP} 
               {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
               {premB:pred1 (alpha p u B) (alpha p v B')} 
                pred1 (lda u A B) (lda v A' B')]

[pr1_app:{A,A'|Trm}{premA:pred1 A A'} 
                {B,B'|Trm}{premB:pred1 B B'} 
                 pred1 (app A B) (app A' B')];


Goal vsub_psubvsub:
     {p|PP}{b|Trm}(is_ff (poccur p b))->
     {a:Trm}{v:VV}Q (vsub a v b) (psub a p (vsub (par p) v b));
intros p;
Refine not_pocc_Trec [p|PP][b:Trm]
     {a:Trm}{v:VV}Q (vsub a v b) (psub a p (vsub (par p) v b));
(* sort *)
intros; Refine Q_refl;
(* var *)
intros; Expand vsub Trec; Refine tt_or_ff (VVeq v n);
  intros eqvn; Qrepl eqvn; Expand psub Trec; Qrepl PPrefl p; Refine Q_refl;
  intros neqvn; Qrepl neqvn; Refine Q_refl;
(* par *)
intros; Expand vsub psub Trec; Qrepl noccP; Refine Q_refl;
(* pi *)
intros;
Equiv Q (pi ? (vsub ???) (if ?? (vsub ???)))
        (pi ? (psub ?? (vsub ???)) (psub ?? (if ?? (vsub ???))));
Refine tt_or_ff (VVeq v n);
  intros eqvn; Qrepl eqvn; Qrepl Trm_eq_subst (not_pocc_psub_eq_lem noccB a);
     Qrepl ihA a v; Refine Q_refl;
  intros neqvn; Qrepl neqvn; Qrepl ihA a v; Qrepl ihB a v; Refine Q_refl;
(* lda *)
intros;
Equiv Q (lda ? (vsub ???) (if ?? (vsub ???)))
        (lda ? (psub ?? (vsub ???)) (psub ?? (if ?? (vsub ???))));
Refine tt_or_ff (VVeq v n);
  intros eqvn; Qrepl eqvn; Qrepl Trm_eq_subst (not_pocc_psub_eq_lem noccB a);
     Qrepl ihA a v; Refine Q_refl;
  intros neqvn; Qrepl neqvn; Qrepl ihA a v; Qrepl ihB a v; Refine Q_refl;
(* app *)
intros;
Equiv Q (app (vsub ???) (vsub ???))
        (app (psub ?? (vsub ???)) (psub ?? (vsub ???)));
Qrepl ihA a v; Qrepl ihB a v; Refine Q_refl;
Save;


Goal pred1_par_red1:
     {a,b|Trm}(pred1 a b)->par_red1 a b;
Refine pred1_elim [a,b:Trm]par_red1 a b;
(* sort *)
intros; Refine par_red1_refl_sort;
(* par *)
intros; Refine par_red1_refl_par;
(* beta *)
intros; Refine shape_lemma p B'; intros v Bv h; Refine h; intros; 
Qrepl Trm_eq_subst H; Qrepl Q_sym (vsub_psubvsub H1 A' v);
Refine par_red1_beta; Immed; Qrepl Q_sym (Trm_eq_subst H); Assumption;
(* pi *)
intros; Refine par_red1_pi; Immed;
(* lda *)
intros; Refine par_red1_lda; Immed;
(* app *)
intros; Refine par_red1_app; Immed;
Save;


Goal par_red1_pred1:
     {a,b|Trm}(par_red1 a b)->pred1 a b;
Refine par_red1Rec [a,b:Trm]pred1 a b;
(* sort *)
intros; Refine pr1_refl_sort;
(* par *)
intros; Refine pr1_refl_par;
(* beta *)
intros; Qrepl vsub_psubvsub noccB' A' v; Refine pr1_beta; Immed;
(* pi *)
intros; Refine pr1_pi; Immed;
(* lda *)
intros; Refine pr1_lda; Immed;
(* app *)
intros; Refine pr1_app; Immed;
Save;
