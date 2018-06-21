Module functional Import subject_reduction conversion_cut;


[conv_unique_types =
     {G|Cxt}{M,A|Trm}(gts G M A)->{B|Trm}(gts G M B)->conv A B];
Goal types_unicity: {f:Functional}conv_unique_types;
intros _; [f_ax=fst f][f_rl=snd f];     
Refine gtsRec [G|Cxt][M,A|Trm][_:gts G M A]{B|Trm}{j:gts G M B}conv A B;
(* Ax *)
intros;Refine gts_gen_sort j;
intros s hypS;Refine hypS;
intros axS cS;Qrepl SSdecide (f_ax sc axS);Immed;
(* Start *)
intros;Refine gts_gen_par j;
intros A' hypA;Refine hypA;
intros occA cA;
Qrepl GBoccur_wValid_functional (gts_wValid_lem j)
                                (hd_GBoccur_lem (Gb p A) G) occA;
Immed;
(* vWeak *)
intros;Refine gts_gen_par j;
intros B' hypB;Refine hypB;
intros occB cB;Refine fst (orr_character ? (GBoccur ? ?)) occB;
intros case;Refine B_contradiction ? (fst (free_params_lem1 l_prem noccG));
            Qrepl pocc_par_lem p n;
            Qrepl fst (Q_resp_bnd_proj (GBeq_subst case));Refine PPrefl;
intros case;[j' = vStartLem l_prem case];
            [vclB' = snd (gts_Vclosed_lem j')];
            Refine conv_trans (l_ih j') cB;
(* sWeak *)
intros;Refine gts_gen_sort j;
intros s hypS;Refine hypS;
intros occS cS;Refine conv_trans (l_ih (sStartLem l_prem occS)) cS;
(* Pi *)
intros;Refine apts_gen_pi j;
intros s1' s2' s3' gen_hyp;Refine gen_hyp;
intros sc' jA jB cB;
[noccG : is_ff (Poccur p G) = CxtCorrect0 r_prem];
Claim rl s1' s2' s3;
Qrepl Q_sym (SSdecide (f_rl sc' ?+1));
Qrepl +1 Q_sym (SSdecide (conv_sort_sort_lem (l_ih jA)));
Qrepl +1 Q_sym (SSdecide (conv_sort_sort_lem (r_ih (jB noccG))));
Immed;
(* Lda *)
intros;Refine apts_gen_lda j;
intros s' B' v gen_hyp;Refine gen_hyp;
intros jPi jB cPi;
[vclPi : Vclosed (pi m A B) = fst (gts_Vclosed_lem r_prem)];
[vclPi' : Vclosed (pi v A B') = fst (gts_Vclosed_lem jPi)];
[noccG : is_ff (Poccur p G) = CxtCorrect0 l_prem];
Refine conv_trans;
Refine +1 conv_pi (conv_refl ?); Immed;
Refine Vclosed_pi_lem (fst (gts_Vclosed_lem r_prem)); intros; Immed;
Refine free_params_lem1 jPi noccG; intros h _; 
Refine pocc_combine_lem h; intros; Immed;
Refine l_ih;Refine jB;Immed;
(* App *)
intros;Refine gts_gen_app j;
intros A' B' v gen_hyp;Refine gen_hyp;
intros jA jB cPi;Refine fresh_params_lem2 B B';
intros q qFresh;Refine qFresh;
intros noccB noccB';Refine convCR_pi_lem;Refine +6 l_ih;
[vclL = fst (gts_Vclosed_lem r_prem)];
[vclPi = snd (gts_Vclosed_lem l_prem)];
[vclPi' = snd (gts_Vclosed_lem jB)];
Immed;
intros cA cB;Refine conv_trans;Immed;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n noccB));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L v noccB'));
Refine psub_resp_conv;Immed;
(* tCnv *)
intros;Refine conv_trans (conv_sym sc) (l_ih j);
Save;

%\VerbFileOpen subject_expansion
Goal subject_expansion:
     {UT:conv_unique_types}
     {G|Cxt}{M,N,A,B|Trm}{r:par_redn M N}{j:gts G N A}{j':gts G M B}
     gts G M A;
%\VerbFileClos subject_expansion
intros;
[vcl' : Vclosed B = snd (gts_Vclosed_lem j')];
[c : conv A B = UT j (gtsSR j' r)];
Refine type_correctness j;
intros s hypS;Refine hypS;
intros case_sort;Qrepl Trm_eq_subst case_sort;
Refine gtsPR j';Refine conv_sort_character;
Qrepl Q_sym (Trm_eq_subst case_sort);Immed;
intros case_type;Refine tCnv;Refine +2 conv_sym;Immed;
Save;

Goal {f:Functional}
     {G|Cxt}{M,N,A,B|Trm}{r:par_redn M N}{j:gts G N A}{j':gts G M B}gts G M A;
intros; Refine subject_expansion; Refine types_unicity f; Immed;
Save subject_expansion_functional;

(* a nice lemma; holds for all beta-gts by typing lemma,
 *  but I only prove it for functional beta-gts *)
%\VerbFileOpen beta_gts_levels
Goal beta_gts_levels :
     {f:Functional}
     {G|Cxt}{M,E|Trm}(gts G M E)->{A,D|Trm}(conv E A)->(gts G A D)->
     Ex [s:SS] par_redn D (sort s);
%\VerbFileClos beta_gts_levels
intros; Refine type_correctness H; intros; Refine H3;
  intros h; Refine gts_gen_sort|G|t|D; Refine gtsSR H2;
    Refine conv_sort_character; Qrepl Q_sym (Trm_eq_subst h); Immed;
    intros; Refine ExIn t1; Refine conv_sort_character (snd H4);
  intros g; Refine ExIn t; Refine convCR H1; intros; Refine H4; intros;
    Refine conv_sort_character; Refine types_unicity f|G|t1|(sort t) ?|D;
    Refine gtsSR g H5; Refine gtsSR H2 H6;
Save;
