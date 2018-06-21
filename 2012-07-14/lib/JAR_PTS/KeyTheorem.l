Module KeyTheorem Import No_pi_redexes preKeyTheorem;

Goal {V,M,N,M',N'|Trm}{v|VV}
     {redM:par_redn M (lda v V M')}{redN:par_redn N N'}
      par_redn (app M N) (vsub N' v M');
intros;Refine fresh_params_lem1 M';
intros p noccM';Refine par_redn_Vclosed redM;
intros vclM vclLda;Refine Vclosed_lda_lem vclLda;
intros vclV vclM';Refine par_redn_Vclosed redN;
intros vclN vclN';
Refine par_redn_trans;Refine +1 par_redn_app;Immed;
Refine par_redn_red1;Refine par_red1_beta; 
Refine +1 par_red1_refl;Refine +5 par_red1_refl;
Immed;
Save par_redn_parks_beta;

(*************** the Key Theorem ****************)

[KeyTheorem [G:Cxt][a,b,B:Trm][s:SS][BG:BindingCxt]
           = and3 (par_bp_redn B (PiOf BG (sort s)))
                  (par_redn a (LdaOf BG b))
                  (gts (CxtOf BG G) (BindingSub BG b) (sort s))];

Goal {G0|Cxt}{M0,A0|Trm}(gts G0 M0 A0)->{A1|Trm}(ots G0 M0 A1)->
      or (conv_bp A0 A1)
         (Ex3 [M1:Trm][s:SS][BG:BindingCxt]KeyTheorem G0 M0 M1 A1 s BG);
intros;
Refine gtsRec [G:Cxt][a,A:Trm][_:gts G a A]{B|Trm}{wB:ots G a B}
       or (conv_bp A B)
          (Ex3 [b:Trm][s:SS][BG:BindingCxt]
           and4 (WellFormed BG)
                (par_bp_redn B (PiOf BG (sort s)))
                (par_redn a (LdaOf BG b))
                (gts (CxtOf BG G) (BindingSub BG b) (sort s)));
Immed;

(* Ax *) 
intros;Refine ots_gen_sort wB; 
intros s hyp; Qrepl fst hyp; 
Refine inr;Refine Ex3In (sort s1) s nilBCxt;
(*****************)
Refine pair4 (Q_refl ?) (par_bp_redn_refl ?) (par_redn_refl (Vclosed_sort ?)) (Ax (snd hyp));
(*****************)

(* Start *) 
intros;Refine fst (orr_character (GBeq ? ?) (GBoccur ? ?)) (ots_gen_par wB); 
intros case;Qrepl snd (Q_resp_bnd_proj (GBeq_subst case));
            Refine inl;Refine conv_bp_refl;
intros case;Refine B_contradiction;Refine +1 GBoccur_Poccur_lem case;Immed;

(* vWeak *)
intros; Refine fst (orr_character (GBeq ? ?) (GBoccur ? ?)) (ots_gen_par wB); 
[wvalG : wValid G = wValid_tail (ots_wValid_lem wB)];
intros case;Refine B_contradiction;Immed;
            Refine free_params_lem l_prem;Refine inl;
            Qrepl pocc_par_lem p n;Qrepl PPsym p n;
            Refine fst (fst (andd_character ? ?) case);
intros case;Refine l_ih (oPar wvalG case);
intros convDB;Refine inl;Immed;
intros ktB;Refine inr;Refine ktB;
intros p' s0 BG hypKT;Refine hypKT;
intros wfBG redPi redLda j;Refine Ex3In p' s0 BG; Refine pair4;Immed;
[eqP = par_redn_par_character redLda];
[eqBG = BCxt_par_character eqP];
Equiv gts ? (BindingSub ? (LdaOf nilBCxt p')) ?;
Qrepl Q_sym eqBG;Qrepl Trm_eq_subst eqP;Qrepl eqBG;
Refine vWeak noccG ? r_prem;
Qrepl Q_sym (Trm_eq_subst eqP);Qrepl eqBG;
Equiv gts (CxtOf nilBCxt ?) (BindingSub nilBCxt p') ?;
Qrepl Q_sym eqBG;Immed;

(* sWeak *) 
intros; Refine ots_gen_sort wB; 
[wvalG = wValid_tail (ots_wValid_lem wB)];
intros s' hypS;Qrepl (fst hypS);
Refine l_ih (oSrt wvalG (snd hypS));
intros convDB;Refine inl;Immed;
intros ktB;Refine inr;Refine ktB;
intros p' s0 BG hypKT;Refine hypKT;
intros wfBG redPi redLda j;Refine Ex3In p' s0 BG;Refine pair4;Immed;
[eqS = par_bp_redn_sort_character redPi];
[eqT = par_redn_sort_character redLda];
[eqBG = BCxt_sort_character eqS];
Equiv gts ? (BindingSub ? (LdaOf nilBCxt p')) (PiOf nilBCxt (sort s0));
Qrepl Q_sym eqBG;Qrepl Trm_eq_subst eqS;Qrepl Trm_eq_subst eqT;Qrepl eqBG;
Refine sWeak noccG ? r_prem;
Qrepl Q_sym (Trm_eq_subst eqS);Qrepl Q_sym (Trm_eq_subst eqT);Qrepl eqBG;
Equiv gts (CxtOf nilBCxt ?) (BindingSub nilBCxt p') (sort s0);
Qrepl Q_sym eqBG;Immed;

(* Pi *) 
intros; Refine aots_gen_pi wB; 
intros sA sB s hyp;Refine hyp;
intros r hypX hypY eq;Qrepl Trm_eq_subst eq;
[noccG = and4_out1 (wValid_gen (gts_wValid_lem r_prem))];
Claim and (Ex [A':Trm]and (par_redn A A')
                          (gts G A' (sort sA)))
          (Ex [B':Trm]and (par_redn (alpha p n B) B')
                          (gts (CONS (Gb p A) G) B' (sort sB)));
Refine ?+1;
intros lemA lemB;Refine lemA;
intros A' hypA;Refine lemB;
intros B0;Refine shape_lemma p B0;
intros x B' shapeB;Refine shapeB;
intros eqB noccB';Qrepl Trm_eq_subst eqB;
intros hypB;Refine inr;Refine Ex3In (pi x A' B') s nilBCxt;
Refine pair4 (Q_refl ?);
Refine par_bp_redn_refl;
Refine par_redn_pi (fst hypA) noccB noccB';
Refine fst hypB;
Refine Pi r noccB' (snd hypA);
Refine gtsCR (snd hypB) (rednCxtCONS ? (rednCxt_refl (wValid_VclCxt (gts_wValid_lem l_prem))));
Refine pair (Q_refl ?) (fst hypA);
Refine pair;

Refine hypX;
intros X lemX;Refine lemX;
intros oX redX;
[vclX = snd (ots_Vclosed_lem oX)];
Refine l_ih oX;

intros cX;
[cSS = conv_bp_trans cX vclX (conv_bp_redn redX)];
Qrepl Q_sym (SSdecide (conv_bp_sort_sort_lem cSS));
Refine ExIn A;Refine pair (par_redn_refl (fst (gts_Vclosed_lem l_prem))) l_prem;

intros ktX;Refine ktX;
intros A' s' BG hypKT;Refine hypKT;
intros wfBG redX' redA j;
[eqBG = BCxt_red_sort_character vclX redX redX'];
[redXs = Q_subst eqBG ([BG:BindingCxt] par_bp_redn X (PiOf BG (sort s'))) redX'];
[cSS = conv_bp_trans (conv_bp_sym(conv_bp_redn redXs)) vclX (conv_bp_redn redX)];
Qrepl Q_sym (SSdecide (conv_bp_sort_sort_lem cSS));
Refine ExIn A';
Equiv and (par_redn ? (LdaOf nilBCxt ?))
          (gts (CxtOf nilBCxt ?) (BindingSub nilBCxt ?) ?);
Qrepl Q_sym eqBG;Refine pair redA j;

Refine hypY;
intros w Y lemY;Refine lemY;
intros wfY oY redY;
[vclY = snd (ots_Vclosed_lem (oY noccG))];
Refine r_ih (oY noccG);

intros cY;
[cSS = conv_bp_trans cY vclY (conv_bp_redn (redY|?))];
Qrepl Q_sym (SSdecide (conv_bp_sort_sort_lem cSS));
Refine ExIn (alpha p n B);Refine pair (par_redn_refl (fst (gts_Vclosed_lem r_prem))) r_prem;

intros ktY;Refine ktY;
intros B' s' BG hypKT;Refine hypKT;
intros wfBG redY' redB j;
[eqBG = BCxt_red_sort_character vclY (redY|?) redY'];
[redYs = Q_subst eqBG
      ([BG:BindingCxt] par_bp_redn (alpha p w Y) (PiOf BG (sort s'))) redY'];
[cSS = conv_bp_trans (conv_bp_sym(conv_bp_redn redYs)) vclY (conv_bp_redn (redY|?))];
Qrepl Q_sym (SSdecide (conv_bp_sort_sort_lem cSS));
Refine ExIn B';
Equiv and (par_redn ? (LdaOf nilBCxt ?))
          (gts (CxtOf nilBCxt ?) (BindingSub nilBCxt ?) ?);
Qrepl Q_sym eqBG;Refine pair redB j;

(* Lda *) 
intros; Refine aots_gen_lda wB; 
intros x B' hyp;Refine hyp;
intros wfB' jB eqB;Qrepl Trm_eq_subst eqB;
[noccG = and4_out1 (wValid_gen (gts_wValid_lem l_prem))];
[noccB' = B_contrapos (wfB' |?) noccG];
Refine l_ih (jB noccG);

intros convDB;Refine inl;Refine conv_bp_pi (conv_bp_refl ?);Immed;
              Refine +1 Vclosed_pi (fst (Vclosed_pi_lem ?+0));
              Refine fst (gts_Vclosed_lem r_prem);
              Refine +1 snd (ots_Vclosed_lem (jB noccG));

intros ktB;Refine inr;Refine ktB;
intros a0 s0 BG hypKT;Refine hypKT;
intros wfBG redPi redLda j;Refine BCxt_Trm_shape_lemma BG a0 p;
intros y a1 BK shapes;Refine shapes;
intros nocc_a1 eq_a nocc_BK eqBG Bnocc;
[ypA : BindingCxt = unit (Lgb y p A)][BH : BindingCxt = append BK ypA];
Refine Ex3In a1 s0 BH;Refine pair4;

Refine WellFormed_combine_lem;Expand WellFormed;
Qrepl and3_out3 (Bvsub_lemma (par p) y BK);Qrepl Q_sym eqBG;Immed;

Qrepl PiOf_append_lem BK ypA (sort s0);
Refine par_bp_redn_pi (par_bp_redn_refl ?) noccB';
Refine fst (Bnocc (Q_refl ff : is_ff (poccur ? (sort ?))));
Qrepl and3_out2 (Bvsub_fresh_var_lemma (Vclosed_par p) nocc_BK) (sort s0);
Qrepl Q_sym eqBG;Immed;

Qrepl LdaOf_append_lem BK ypA a1;
Refine par_redn_lda (par_redn_refl (fst (Vclosed_pi_lem (fst (gts_Vclosed_lem r_prem))))) noccM;
Refine snd (Bnocc nocc_a1);
Qrepl and3_out3 (Bvsub_fresh_var_lemma (Vclosed_par p) nocc_BK) a1;
Qrepl Q_sym eqBG;Qrepl Q_sym (Trm_eq_subst eq_a);Immed;

Qrepl BindingSub_append_lem BK ypA a1;
Qrepl and3_out1 (Bvsub_fresh_var_lemma (Vclosed_par p) nocc_BK) a1;
Qrepl and3_out1 (Bvsub_lemma (par p) y BK) (alpha p y a1);
Qrepl CxtOf_alpha_lemma G (Lgb y p A) nocc_BK;
Qrepl Q_sym eqBG;Qrepl Q_sym (Trm_eq_subst eq_a);Immed;

(* App *) 
intros; Refine ots_gen_app wB; 
intros P hyp;Refine hyp;
intros jP red_hyp eqA;Qrepl Trm_eq_subst eqA;
[vclP = snd (gts_Vclosed_lem l_prem)];
[vclL = fst (gts_Vclosed_lem r_prem)];
[vclP' = snd (ots_Vclosed_lem jP)];
Refine l_ih jP;

intros cP;Refine inl;
Refine conv_bp_trans (conv_bp_sym (conv_bp_redn ?)) (Vclosed_app vclP vclL);
Refine par_bp_redn_red1;Refine no_bp_par_bp_red1;Refine no_bp_red1_pcon;
Refine conv_bp_app vclP vclP' cP vclL vclL (conv_bp_refl ?);

intros ktB;Refine inr;Refine ktB;
intros m s BG hypKT;Refine hypKT;
intros wfBG redPi redLda j;Refine red_hyp;
intros u U X Y red_hyp';Refine red_hyp';
intros redP jL redX;Refine BCxt_red_pi_character vclP' redPi redP;
intros lgb BK eqBK;Refine WellFormed_split_lem BK lgb (Q_subst eqBK WellFormed wfBG);
intros wfBK noccBK;

[v = VarOf lgb][p = NamOf lgb][C = TypOf lgb][a = vsub L v m];
[vpC : BindingCxt = unit lgb][BH : BindingCxt = Bvsub L v BK];

(* in the harder case, we now introduce the following argument, which
   obviates the need for any appeal to van Daalen/Jutting 's EQV relation *)

[jLda : gts G (lda v C (LdaOf BK m)) (pi n A B)
      = Q_subst (LdaOf_append_lem BK vpC m) ([X:Trm]gts G X (pi n A B))
                (Q_subst eqBK ([BG:BindingCxt]gts G (LdaOf BG m) (pi n A B))
                         (gtsSR l_prem redLda))];

Refine gts_gen_lda jLda;
intros s' D q w hypLda;Refine hypLda;
intros noccLda noccD jPi j' convPi;Refine gts_gen_pi jPi;
intros s1 s2 s3 r hypPi;Refine hypPi;
intros rule jC noccD' jD convS;

[convCA : conv C A = fst (convCR_pi_lem convPi)];
[jLC : gts G L C = tCnv (conv_sym convCA) r_prem jC];

(* this last, jLC : gts G L C, was the much sought-after conclusion
   previously obtained via the EQV relation and the No_pi_redexes
   property. Now we proceed as before *)

Refine Ex3In a s BH;Refine pair4;

Expand WellFormed;Qrepl Q_sym (and3_out3 (Bvsub_lemma L v BK));Refine wfBK;

Refine par_bp_redn_trans (par_bp_redn_app redPi (par_bp_redn_refl ?));
Qrepl eqBK;Qrepl PiOf_append_lem BK vpC (sort s);
Qrepl Q_sym (and3_out2 (Bvsub_fresh_var_lemma vclL noccBK) (sort s)); 
Refine par_bp_redn_red1;Refine no_bp_par_bp_red1;Refine no_bp_red1_pcon;

(********************* changed for VClosed **************************)
Qrepl Q_sym (and3_out3 (Bvsub_fresh_var_lemma vclL noccBK) m); 
Refine par_redn_parks_beta;
Refine +1 Q_subst (LdaOf_append_lem BK vpC m) (par_redn ?)
	 (Q_subst eqBK ([BG:BindingCxt]par_redn ? (LdaOf BG ?)) redLda);
Refine par_redn_refl vclL;

[jBK : gts (CxtOf (append BK vpC) G) (BindingSub (append BK vpC) m) (sort s)
     = Q_subst eqBK ([BG:BindingCxt]gts (CxtOf BG G) (BindingSub BG m) ?) j];
[valBK : Valid (CxtOf (append BK vpC) G) = Ex2In ? ? (gts ?) jBK];

Refine Valid_BCxt_subst_lemma valBK noccBK vclL;

intros +1 noccG;Refine free_params_lem1 jLda noccG;
intros nocclda noccpi;Refine pocc_combine_lem nocclda;
intros;Immed;

intros noccBKm exK;Refine exK;
intros K hypK;Refine hypK;
intros eqK eqKsub;Qrepl eqKsub;
Qrepl Q_sym (and3_out1 (Bvsub_lemma L v BK) (vsub L v m));
Qrepl Q_sym (and3_out1 (Bvsub_fresh_var_lemma vclL noccBK) m);
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L v noccBKm));
Qrepl Q_sym (BindingSub_append_lem BK vpC m);
Equiv gts (append (map (GBsub L p) K) G) (psub L p ?) (psub L p (sort s));
Refine substitution_lem jLC;Qrepl Q_sym eqK;Immed;

(* tCnv *) 
intros; Refine l_ih wB;
intros convDB;Refine inl;
              Refine conv_bp_trans (conv_bp_sym (conv_conv_bp sc))
                                  (snd (gts_Vclosed_lem l_prem))
                                   convDB;
intros ktB;Refine inr;Refine ktB;

intros case;Refine inl;Immed;
intros case;Refine inr;Refine case;
intros b s BG hypKT;Refine hypKT;
intros wf rB ra j';Refine Ex3In;Refine +3 pair3;Immed;
Save ots_KeyTheorem;

Goal {G|Cxt}{a,A|Trm}{j:gts G a A}
     {B|Trm}{oj:ots G a B}{s|SS}{r:par_bp_redn B (sort s)}
      Ex [a0:Trm]and (gts G a0 (sort s)) (par_redn a a0);
intros;Refine ots_KeyTheorem j oj;
[vclA : Vclosed A = snd (gts_Vclosed_lem j)];
[vclB : Vclosed B = snd (ots_Vclosed_lem oj)];
intros convA;Refine ExIn a;
             Refine pair ? (par_redn_refl (fst (gts_Vclosed_lem j)));
             Refine gtsPR j;
             Refine well_typed_No_pi_redexes_pred j;
             Refine conv_bp_sort_character
                (conv_bp_sym (conv_bp_trans convA vclB (conv_bp_redn r))) vclA;
intros ktA;Refine ktA;
intros a0 s0 BG hypKT;
[eqBG : Q BG nilBCxt = BCxt_red_sort_character vclB r (and3_out1 hypKT)];
[hypkt : and3 (par_bp_redn B (sort s0)) (par_redn a a0) (gts G a0 (sort s0))
       = Q_subst eqBG (KeyTheorem G a a0 B s0) hypKT];
Refine hypkt;
intros rB ra j0;
[eqS : is_tt (SSeq s s0) = conv_bp_sort_sort_lem
         (conv_bp_trans (conv_bp_sym (conv_bp_redn r)) vclB (conv_bp_redn rB))];
Refine ExIn a0;Qrepl SSdecide eqS;
Refine pair;Immed;
Save ots_KeyTheorem_Corollary;
