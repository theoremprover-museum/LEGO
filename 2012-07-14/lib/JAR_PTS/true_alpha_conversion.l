Module true_alpha_conversion Import alpha_inversion alpha_conversion;

Goal {v,u:VV}{M|Trm}(aVclosed M)->
     {q|PP}{C|Trm}(is_ff (poccur q C))->
                  (is_tt (Trm_eq M (alpha q v C)))->
      Ex [D:Trm] and (is_ff (poccur q D))
                     (alpha_conv M (alpha q u D));
intros __;
Refine aVclosedRec [M|Trm][_:aVclosed M]
                   {q|PP}{C|Trm}{nocc:is_ff (poccur q C)}
                   {eq:is_tt (Trm_eq M (alpha q v C))}
       Ex [D:Trm] and (is_ff (poccur q D))
                      (alpha_conv M (alpha q u D));

(* sort *)
intros;Refine ExIn (sort s);Refine pair;
Refine Q_refl;Refine alpha_conv_refl; Refine Vclosed_sort;

(* par *)
intros;Refine alpha_par_nocc_character; Immed;
intros case_par;Refine case_par;
   intros neqPP eqC;Refine ExIn (par p);Refine pair;
   Qrepl pocc_par_lem q p;Immed;
   Refine alpha_conv_refl; Refine Vclosed_par;
intros case_var;Refine ExIn (var u);Refine pair;
   Refine Q_refl;
   Qrepl Trm_eq_subst eq;Qrepl Trm_eq_subst case_var;
   Equiv alpha_conv (if ???) (if ???);
   Qrepl VVrefl v;Qrepl VVrefl u;
   Refine alpha_conv_refl; Refine Vclosed_par;

(* pi *)
intros;Refine alpha_pi_nocc_character;Immed;
intros AA BB hh;Refine hh;
intros eqC eqAA noccAA;Refine ihA;Immed;
intros AAA hAAA;Refine hAAA;
intros noccAAA alphaAAA;

Refine tt_or_ff (VVeq n v);
intros case;Qrepl case;
   intros eqBB noccBB;Refine ihB q noccBB;
   Qrepl VVdecide case;Qrepl Trm_eq_subst eqBB;Refine Trm_eq_refl;
   intros BBB hBBB;Refine hBBB;
   intros noccBBB alphaBBB;Refine ExIn (pi u AAA BBB);Refine pair;
   Refine pocc_split_lem2;Immed;
   Equiv alpha_conv ? (pi ? (alpha ???) (if ?? (alpha ???)));
   Qrepl VVrefl u;Refine alpha_conv_pi;Immed;
   Qrepl Trm_eq_subst eqBB;Immed;

intros case;Qrepl case;
   intros eqBB noccBB;Refine fresh_params_lem1p q BB1;
   intros r rFresh;Refine rFresh;
   intros neqP noccrBB;Refine ihB r;
   Refine q;Refine (alpha r n BB1);
   Refine not_pocc_vsub_lem noccBB;
   Qrepl pocc_par_lem q r;Qrepl PPsym q r;Immed;
   Qrepl Q_sym (Trm_eq_subst (alpha_commutes_alpha case r q BB1));
   Qrepl Trm_eq_subst eqBB;Refine Trm_eq_refl;
   intros BBB1;Refine shape_lemma r BBB1;
   intros m BBB shapeBBB;Refine shapeBBB;
   intros eqBBB noccrBBB;Qrepl Trm_eq_subst eqBBB;
   intros hBBB;Refine hBBB;
   intros noccBBB alphaBBB;Refine ExIn (pi m AAA BBB);Refine pair;
   Refine pocc_split_lem2;Refine +1 not_pocc_vsub_lem2;Immed;
   Equiv alpha_conv ? (pi ? (alpha ???) (if ?? (alpha ???)));
   Refine tt_or_ff (VVeq u m);
   intros case';Qrepl case';Equiv alpha_conv ? (pi ? (alpha ???) BBB);
      Refine alpha_conv_pi;Immed;
      Qrepl Trm_eq_subst eqBB;Refine not_pocc_vsub_lem noccrBB;
      Qrepl pocc_par_lem r q;Immed;
      Qrepl Q_sym (Trm_eq_subst (alpha_idempotent case' q r BBB));Immed;

   intros case';Qrepl case';Equiv alpha_conv ? (pi ? (alpha ???) (alpha ???));
      Refine alpha_conv_pi;Immed;
      Qrepl Trm_eq_subst eqBB;Refine not_pocc_vsub_lem noccrBB;
      Qrepl pocc_par_lem r q;Immed;
      Refine not_pocc_vsub_lem noccrBBB;
      Qrepl pocc_par_lem r q;Immed;
      Qrepl Q_sym (Trm_eq_subst (alpha_commutes_alpha case' q r BBB));Immed;

(* lda *)
intros;Refine alpha_lda_nocc_character;Immed;
intros AA BB hh;Refine hh;
intros eqC eqAA noccAA;Refine ihA;Immed;
intros AAA hAAA;Refine hAAA;
intros noccAAA alphaAAA;

Refine tt_or_ff (VVeq n v);
intros case;Qrepl case;
   intros eqBB noccBB;Refine ihB q noccBB;
   Qrepl VVdecide case;Qrepl Trm_eq_subst eqBB;Refine Trm_eq_refl;
   intros BBB hBBB;Refine hBBB;
   intros noccBBB alphaBBB;Refine ExIn (lda u AAA BBB);Refine pair;
   Refine pocc_split_lem2;Immed;
   Equiv alpha_conv ? (lda ? (alpha ???) (if ?? (alpha ???)));
   Qrepl VVrefl u;Refine alpha_conv_lda;Immed;
   Qrepl Trm_eq_subst eqBB;Immed;

intros case;Qrepl case;
   intros eqBB noccBB;Refine fresh_params_lem1p q BB1;
   intros r rFresh;Refine rFresh;
   intros neqP noccrBB;Refine ihB r;
   Refine q;Refine (alpha r n BB1);
   Refine not_pocc_vsub_lem noccBB;
   Qrepl pocc_par_lem q r;Qrepl PPsym q r;Immed;
   Qrepl Q_sym (Trm_eq_subst (alpha_commutes_alpha case r q BB1));
   Qrepl Trm_eq_subst eqBB;Refine Trm_eq_refl;
   intros BBB1;Refine shape_lemma r BBB1;
   intros m BBB shapeBBB;Refine shapeBBB;
   intros eqBBB noccrBBB;Qrepl Trm_eq_subst eqBBB;
   intros hBBB;Refine hBBB;
   intros noccBBB alphaBBB;Refine ExIn (lda m AAA BBB);Refine pair;
   Refine pocc_split_lem2;Refine +1 not_pocc_vsub_lem2;Immed;
   Equiv alpha_conv ? (lda ? (alpha ???) (if ?? (alpha ???)));
   Refine tt_or_ff (VVeq u m);
   intros case';Qrepl case';Equiv alpha_conv ? (lda ? (alpha ???) BBB);
      Refine alpha_conv_lda;Immed;
      Qrepl Trm_eq_subst eqBB;Refine not_pocc_vsub_lem noccrBB;
      Qrepl pocc_par_lem r q;Immed;
      Qrepl Q_sym (Trm_eq_subst (alpha_idempotent case' q r BBB));Immed;

   intros case';Qrepl case';Equiv alpha_conv ? (lda ? (alpha ???) (alpha ???));
      Refine alpha_conv_lda;Immed;
      Qrepl Trm_eq_subst eqBB;Refine not_pocc_vsub_lem noccrBB;
      Qrepl pocc_par_lem r q;Immed;
      Refine not_pocc_vsub_lem noccrBBB;
      Qrepl pocc_par_lem r q;Immed;
      Qrepl Q_sym (Trm_eq_subst (alpha_commutes_alpha case' q r BBB));Immed;

(* app *)
intros;Refine alpha_app_nocc_character;Immed;
intros AA BB hh;Refine hh;
intros eqC eqAA noccAA;Refine ihA;Immed;
intros AAA hAAA;Refine hAAA;
intros noccAAA alphaAAA;
(* no case split here *)
intros eqBB noccBB;Refine ihB;Immed;
intros BBB hBBB;Refine hBBB;
intros noccBBB alphaBBB;Refine ExIn (app AAA BBB);Refine pair;
Refine pocc_split_lem2;Immed;
Equiv alpha_conv ? (app (alpha ???) (alpha ???));
Refine alpha_conv_app;Immed;

Save true_alpha_conv_lem;

Goal {B|Trm}{p|PP}(is_ff (poccur p B))->
     {v|VV}(Vclosed (alpha p v B))->
     {u:VV}
     Ex [C:Trm] and (is_ff (poccur p C))
                    (alpha_conv (alpha p v B) (alpha p u C));
intros;Refine true_alpha_conv_lem v;
Refine Vclosed_aVclosed;Immed;
Refine Trm_eq_refl;
Save true_alpha_conv_lemma;

Goal true_alpha_conv_pi:
     {v|VV}{A,B|Trm}(Vclosed (pi v A B))->
     {u:VV} Ex [C:Trm] alpha_conv (pi v A B) (pi u A C);
intros;Refine Vclosed_pi_lem;Immed;
intros vclA vclB;Refine fresh_params_lem1 B;
intros q noccB;Refine true_alpha_conv_lemma;Immed;
intros C hypC;Refine hypC;
intros noccC alphaBC;Refine ExIn C;
Refine alpha_conv_pi;Refine alpha_conv_refl;Immed;
Save;

Goal true_alpha_conv_lda:
     {v|VV}{A,B|Trm}(Vclosed (lda v A B))->
     {u:VV} Ex [C:Trm] alpha_conv (lda v A B) (lda u A C);
intros;Refine Vclosed_lda_lem;Immed;
intros vclA vclB;Refine fresh_params_lem1 B;
intros q noccB;Refine true_alpha_conv_lemma;Immed;
intros C hypC;Refine hypC;
intros noccC alphaBC;Refine ExIn C;
Refine alpha_conv_lda;Refine alpha_conv_refl;Immed;
Save;
