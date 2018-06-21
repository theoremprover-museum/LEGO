Module sf_typSyn Import asdsf tcp;

[ruledsort [s1:SS] = Ex2 [s2,s3:SS] rl s1 s2 s3];
[ruledsorts [s1,s2:SS] = Ex [s3:SS] rl s1 s2 s3];

Goal Cxt_Trm_WF_ind:
     {f:{G:Cxt}{M:Trm}NN}
     {C:{G:Cxt}{M:Trm}Prop}
     {wf_ih:{G:Cxt}{M:Trm}{ih:{g:Cxt}{m:Trm}(Lt (f g m) (f G M))->C g m}C G M}
     {G:Cxt}{M:Trm}C G M;
intros;
Refine complete_induction [n:NN]{G:Cxt}{M:Trm}(Q n (f G M))->C G M;
intros; Refine wf_ih;
intros; Refine H; Refine f g m; Qrepl H1; Refine H2; Refine Q_refl;
Refine +1 Q_refl;
Save;

[Cxt_ln : {G:Cxt}NN = LLrec ([_:LL|GB]NN) Z
                            ([b:GB][_:Cxt][ih:NN]add (lngth (typOf b)) ih)];
[Cxt_Trm_ln [G:Cxt][M:Trm] : NN = add (lngth M) (Cxt_ln G)];


Goal sf_typSyn:
     {sf:semiFull}{f:Functional}
     {dt:{s:SS}decidable (typedsort s)}
     {dr:{s:SS}decidable (ruledsort s)}
     {drs:{s1,s2:SS}decidable (ruledsorts s1 s2)}
     {ndc:normalizing_decides_cnv}
     {gtn:gts_term_Normalizing}
     {G:Cxt}{M:Trm}decidable (sdsfTS G M);
intros _______; Expand sdsfTS;
(* induct on the sum of the lengths of the terms in context and subject *)
Refine Cxt_Trm_WF_ind Cxt_Trm_ln
           ([G:Cxt][M:Trm]or (sdsfTS G M) (not (sdsfTS G M)));
Expand sdsfTS;
Claim {M:Trm}{K:Cxt}
     {wf_ih:{g:Cxt}{m:Trm}(Lt (Cxt_Trm_ln g m) (Cxt_Trm_ln K M))->
                or (Ex ([A:Trm]sdsf g m A)) (not (Ex ([A:Trm]sdsf g m A)))}
     or (Ex ([A:Trm]sdsf K M A)) (not (Ex ([A:Trm]sdsf K M A)));
intros; Refine ?7; Immed;
Refine Trec [M:Trm]{K:Cxt}
     {wf_ih:{g:Cxt}{m:Trm}(Lt (Cxt_Trm_ln g m) (Cxt_Trm_ln K M))->
                or (Ex ([A:Trm]sdsf g m A)) (not (Ex ([A:Trm]sdsf g m A)))}
     or (Ex ([A:Trm]sdsf K M A)) (not (Ex ([A:Trm]sdsf K M A)));
(* sort *)
intros;
(* secondary induction on K *)
Refine NIL_or_CONS K;
(* K is Nil *)
intros Knil; Qrepl Knil; Refine dt s; 
intros tss; Refine inl; Refine tss; intros t th;
  Refine ExIn (sort t); Refine sdsfAx th;
intros ntss; Refine inr; Intros h; Refine ntss; Refine h; intros t th;
  Refine sdsf_gen_sort th; intros u uh; Refine ExIn u; Refine and3_out2 uh;
(* K is CONS *)
intros Kcons; Refine Kcons; intros x xs xxsh; Qrepl xxsh;
(* 16 cases: Poccur is decidable
 *           dRTS decides redX;
 *           wf_ih decides l_prem and r_prem;
 *)
Refine tt_or_ff (Poccur (namOf x) xs);
intros xinxs; Refine inr; Expand not; Qrepl PROD_surj_pair x; intros exh;
Refine exh; intros A Ah; Refine sdsf_wVal xinxs Ah;
intros xfresh;
(* parameter is fresh now *)
Refine wf_ih xs (sort s); Qrepl xxsh;
Equiv Lt (S (Cxt_ln ?)) (S (add (lngth ?) (Cxt_ln ?)));
Refine fst (Lt_resp_S ??); Refine lngth_is_S (typOf x); intros nx eqnx;
Qrepl eqnx; Refine Lt_add_S_left;
intros +1 nlph; Refine inr; Expand not; intros;
Refine H; intros A Ah; Refine sdsf_gen_sort Ah; intros t th;
Refine nlph; Refine ExIn (sort t);
Refine th; intros; Refine H3;
intros hh; Refine NIL_not_CONS (Q_sym hh);
intros hh; Refine hh; intros; Refine H4; intros;
Refine new_eqCxtLem H5; intros; Qrepl H12; Immed;
(* l_prem derivable now *)
intros lph; Refine lph; intros D lp;
Refine wf_ih xs (typOf x); Qrepl xxsh;
Equiv Lt (add (lngth ?) (Cxt_ln ?)) (add one (add (lngth ?) (Cxt_ln ?)));
Refine Lt_incl_S;
intros +1 nrph; Refine inr; Expand not; intros;
Refine H; intros X Xh; Refine sdsf_gen_sort Xh; intros t th;
Refine nrph; Refine th; intros; Refine H3;
intros hh; Refine NIL_not_CONS (Q_sym hh);
intros hh; Refine hh; intros; Refine H4; intros; Refine ExIn u;
Refine new_eqCxtLem H5; intros; Qrepl H12; Qrepl H11; Immed;
(* r_prem derivable now *)
intros rph; Refine rph; intros X rp;
Refine gts_type_decides_RedToSort gtn|X;
   Refine Ex2In xs (typOf x); Refine sdsf_gts sf rp1;
intros +1 nRTSX; Refine inr; Refine contrapos; Refine +2 nRTSX;
intros h; Refine h; intros Y Yh; Refine sdsf_gen_sort Yh; intros t th;
Refine th; intros; Refine H2;
intros hh; Refine NIL_not_CONS (Q_sym hh);
intros hh; Refine hh; intros; Refine H3; intros;
Refine new_eqCxtLem H4; intros; Refine ExIn w;
Refine conv_sort_character;
Refine conv_trans; Refine u; Refine conv_sym; Refine conv_redn H6;
Refine sdsf_unique_types f ? rp1;
Qrepl H11; Qrepl H10; Immed;
(* redX derivable now *)
intros redX; Refine redX; intros u uh;
(* so whole judgement is derivable! *)
Refine inl; Refine ExIn D;
Qrepl PROD_surj_pair x; Refine sdsfsWeak; Immed;

(* var *)
intros; Refine inr; Intros h; Refine h; intros X Xh;
Refine sdsf_Vclosed Xh; intros; Refine Vclosed_var_lem; Immed;

(* par *)
intros;
(* we want to do case analysis on whether the last parameter in K is
 * n or not.  In order to see that K is a CONS, we first analyse
 * K as NIL or CONS
 *)
Refine NIL_or_CONS K;
intros Knil; Refine inr; Intros H; Refine H; intros X Xh; Refine tt_not_ff;
Claim is_tt (poccur n (par n));
Qrepl Q_sym (free_params_lem (sdsf_gts sf Xh) (inl ?+1)); Qrepl Knil;
Refine Q_refl; Equiv is_tt (orr (PPeq n n) ff); Qrepl PPrefl n; Refine Q_refl;
(* K is (CONS b KK) *)
intros pKc; Refine pKc; intros b KK; intros Kc;
(* work on r_prem, shared by Start and vWeak *)
Refine wf_ih KK (typOf b); Qrepl Kc; Refine Lt_incl_S;
intros +1 nKKnA; Refine inr; Refine contrapos ? nKKnA;
Qrepl Kc; Qrepl GB_surj_pair b; intros pKnX;
Equiv Ex ([A:Trm]sdsf KK (typOf b) A);
Refine pKnX; intros X KnX;
Refine sdsf_cxt_hd_typing KnX; intros; Refine ExIn t;
Refine fst H;
intros hhh; Refine hhh; intros X sdKKbX;
(* now (typOf b) has a type, X.  Does X reduce to a sort? *)
Refine gts_type_decides_RedToSort gtn|X;
Refine Ex2In KK (typOf b); Refine sdsf_gts sf sdKKbX;
intros +1 nKKnA; Refine inr; Refine contrapos ? nKKnA;
Qrepl Kc; Qrepl GB_surj_pair b; intros pKnX;
Refine pKnX; intros Y KnY;
Refine sdsf_cxt_hd_typing KnY; intros; Refine ExIn s;
Refine conv_sort_character;
Refine conv_trans (?:conv (sort s) t) (?:conv t X);
Refine conv_sym; Refine conv_redn;
Refine snd H; Refine sdsf_unique_types f (fst H) sdKKbX;
intros rtsX; Refine rtsX; intros u redXu;
(* now X reduces to some sort; analyse n = (namOf b) *)
Refine tt_or_ff (PPeq n (namOf b));
(*  n = (namOf b) is Start rule *)
intros eqnb;
Refine tt_or_ff (Poccur (namOf b) KK);
intros binKK; Refine inr; Qrepl Kc; Qrepl PROD_surj_pair b; Intros exh;
Refine exh; intros A Ah; Refine sdsf_wVal binKK Ah; intros bfresh;
(* now n is fresh; can choose positive disjunct *)
Refine inl; Refine ExIn (typOf b);
Qrepl Kc; Qrepl GB_surj_pair b; Qrepl PPdecide eqnb;
Refine sdsfStart bfresh redXu sdKKbX;
(** n =\= (namOf b) is vWeak rule; check l_prem **)
intros neqnb; Refine wf_ih KK (par n); Qrepl Kc;
Refine add_resp_Lt_right; Equiv Lt ? (add ? (Cxt_ln KK));
Refine lngth_is_S (typOf b); intros; Qrepl H; Refine Lt_add_S_left;
(* assume left premise fails *)
intros +1 nsdsfKKn; Refine inr; Refine contrapos ? nsdsfKKn;
Qrepl Kc; Qrepl GB_surj_pair b; intros exKn; Refine exKn; intros A sdKnA;
Refine ExIn A; Refine sdsf_gen_par sdKnA;
  intros; Refine H; intros; Refine H1; intros;
    Refine new_eqCxtLem H2; intros; Refine tt_not_ff;
    Qrepl Q_sym neqnb; Qrepl Q_sym H6; Refine Q_sym (PPrefl ?);
  intros; Refine H; intros; Refine H1; intros;
    Refine new_eqCxtLem H2; intros; Qrepl H11; Immed;
(* left prem succeeds; check (typOf b) is fresh *)
intros; Refine tt_or_ff (Poccur (namOf b) KK);
intros binKK; Refine inr; Qrepl Kc; Qrepl PROD_surj_pair b; Intros exh;
Refine exh; intros A Ah; Refine sdsf_wVal binKK Ah; intros bfresh;
(* now n is fresh; can choose positive disjunct *)
Refine inl; Qrepl Kc; Refine H; intros A sdKKnA; Refine ExIn A;
Qrepl GB_surj_pair b; Refine sdsfvWeak bfresh redXu sdKKnA sdKKbX;

(* pi *)
intros;
(* choose p not in K and not in B *)
Refine fresh_params_lem1G K B; intros p pg; Refine pg; intros pK pB;
(* check left prem *)
Refine wf_ih K A; Refine add_resp_Lt_left; Refine Lt_add_S_right;
intros +1 nrph; Refine inr; Refine contrapos ? nrph; intros;
Refine H; intros X Xh; Refine sdsf_gen_pi Xh;
intros XX YY u1 u2 u3 m h; Refine h; intros;
Refine ExIn XX; Immed;
(* l_prem derivable now; does X red to a sort? *)
intros lph; Refine lph; intros X lp;
Refine gts_type_decides_RedToSort gtn|X;
   Refine Ex2In K A; Refine sdsf_gts sf lp;
intros +1 nRTSX; Refine inr; Refine contrapos; Refine +2 nRTSX;
intros h; Refine h; intros Y Yh; Refine sdsf_gen_pi Yh;
intros XX YY u1 u2 u3 m g; Refine g; intros; Refine ExIn u1;
Refine conv_sort_character;
Refine conv_trans ? (sdsf_unique_types f H lp);
Refine conv_sym; Refine conv_redn; Immed;
(* redX derivable now *)
intros redX; Refine redX; intros t1 t1h;
(* check right premise *)
Refine wf_ih (CONS (Gb p A) K) (vsub (par p) n B);
Equiv Lt (add ? (add (lngth A) (Cxt_ln ?)))
         (S (add (add (lngth ?) (lngth ?)) ?));
Qrepl alpha_preserves_lngth B p n; Qrepl addCommute (lngth B) (lngth A);
Qrepl addAssocR (lngth A) (Cxt_ln K) (lngth B); Refine  Lt_incl_S;
intros +1 nrph; Refine inr; Refine contrapos ? nrph; intros;
Refine H; intros X Xh; Refine sdsf_gen_pi Xh;
intros XX YY u1 u2 u3 m h; Refine h; intros;
Refine ExIn (alpha p m YY); Refine H2; Immed;
(* r_prem derivable now; does Y red to a sort? *)
intros rph; Refine rph; intros Y rp;
Refine gts_type_decides_RedToSort gtn|Y;
   Refine Ex2In (CONS (Gb p A) K) (vsub (par p) n B); Refine sdsf_gts sf rp1;
intros +1 nRTSY; Refine inr; Refine contrapos; Refine +2 nRTSY;
intros h; Refine h; intros Y Yh; Refine sdsf_gen_pi Yh;
intros YY ZZ u1 u2 u3 m g; Refine g; intros; Refine ExIn u2;
Refine conv_sort_character;
Refine conv_trans ? (sdsf_unique_types f (H1 pK) rp1);
Refine conv_sym; Refine conv_redn; Refine H3 pK;
(* redY derivable now *)
intros redY; Refine redY; intros t2 t2h;
(* is there a rule (t1,t2,t3) *)
Refine drs t1 t2;
intros +1 nrst1t2; Refine inr; Refine contrapos; Refine +2 nrst1t2;
intros h; Refine h; intros W Wh; Refine sdsf_gen_pi Wh;
intros WW ZZ u1 u2 u3 m g; Refine g; intros; Refine ExIn u3;
Claim is_tt (SSeq t1 u1); Claim is_tt (SSeq t2 u2); 
Qrepl SSdecide ?+1; Qrepl SSdecide ?+2; Immed;
Refine conv_sort_sort_lem;
Refine conv_trans (conv_sym (conv_redn t1h));
Refine conv_trans ? (conv_redn H2);
Refine sdsf_unique_types f lp H;
Refine conv_sort_sort_lem;
Refine conv_trans (conv_sym (conv_redn t2h));
Refine conv_trans ? (conv_redn (H3 pK));
Refine sdsf_unique_types f rp1 (H1 pK);
(* there is a rule: choose positive disjunct *)
intros rlt; Refine inl; Refine rlt; intros t3 t3h; Refine ExIn (sort t3);
Refine sdsfPi t3h pB t1h t2h lp rp1;

(* lda *)
intros;
(* choose p not in K or B *)
Refine fresh_params_lem1G K B; intros p pg; Refine pg; intros pK pB;
(* check right prem *)
Refine wf_ih K A; Refine add_resp_Lt_left; Refine Lt_add_S_right;
intros +1 nlph; Refine inr; Refine contrapos ? nlph; intros;
Refine H; intros X Xh; Refine sdsf_gen_lda Xh;
intros BB XX u1 u2 u3 m h; Refine h; intros; Refine ExIn XX; Immed;
(* r_prem derivable now; does X red to a sort? *)
intros rph; Refine rph; intros X rp;
Refine gts_type_decides_RedToSort gtn|X;
   Refine Ex2In K A; Refine sdsf_gts sf rp1;
intros +1 nRTSX; Refine inr; Refine contrapos; Refine +2 nRTSX;
intros h; Refine h; intros Y Yh; Refine sdsf_gen_lda Yh;
intros XX YY u1 u2 u3 m g; Refine g; intros; Refine ExIn u1;
Refine conv_sort_character;
Refine conv_trans ? (sdsf_unique_types f H1 rp1);
Refine conv_sym; Refine conv_redn; Immed;
(* redX derivable now: is there a rule *)
intros redX; Refine redX; intros t1 t1h;
Refine dr t1;
intros +1 nrst1; Refine inr; Refine contrapos; Refine +2 nrst1;
intros h; Refine h; intros W Wh; Refine sdsf_gen_lda Wh;
intros WW ZZ u1 u2 u3 m g; Refine g; intros; Refine Ex2In u2 u3;
Claim is_tt (SSeq t1 u1); Qrepl SSdecide ?+1; Immed;
Refine conv_sort_sort_lem;
Refine conv_trans (conv_sym (conv_redn t1h));
Refine conv_trans ? (conv_redn H4);
Refine sdsf_unique_types f rp1 H1;
(* there is a rule *)
intros rlt; Refine rlt; intros t2 t3 t23h;
(* check left premise *)
Refine wf_ih (CONS (Gb p A) K) (vsub (par p) n B);
Equiv Lt (add ? (add (lngth A) (Cxt_ln ?)))
         (S (add (add (lngth ?) (lngth ?)) ?));
Qrepl alpha_preserves_lngth B p n; Qrepl addCommute (lngth B) (lngth A);
Qrepl addAssocR (lngth A) (Cxt_ln K) (lngth B); Refine  Lt_incl_S;
intros +1 nlph; Refine inr; Refine contrapos ? nlph; intros;
Refine H; intros Z Zh; Refine sdsf_gen_lda Zh;
intros ZZ YY u1 u2 u3 m h; Refine h; intros;
Refine ExIn (alpha p m ZZ); Refine H1 pK;
(* some left premise is derivable; use shape lemma *)
intros h; Refine h; intros A1 A1h;
Refine shape_lemma p A1; intros u BB g; Refine g; intros eqA1 pBB;
(* must split at the typedsort condition! *)
Refine tt_or_ff (isSrt (alpha p u BB1));
(* BB1 is a sort *)
intros BBinSS; Refine isSrt_lem BBinSS; intros t eqBBt;
Refine dt t; intros +1; Refine inr; Refine contrapos ? H; intros k;
Refine k; intros Z Zh; Refine sdsf_gen_lda Zh;
intros ZZ YY u1 u2 u3 m hh; Refine hh; intros;
Claim conv (vsub (par p) m ZZ) (sort t);
Claim (is_tt (soccur t ZZ))->typedsort t; Refine ?+2;
Refine socc_vsub_lem2
          (par_redn_sort_socc_lem (conv_sort_character (conv_sym ?+1)));
intros kk; Refine tt_not_ff (Q_sym kk); intros; Immed;
Qrepl Q_sym (Trm_eq_subst eqBBt); Qrepl Q_sym (Trm_eq_subst eqA1);
Refine sdsf_unique_types f (H1 pK) A1h;
intros tinZZ;
Refine sdsf_typedsort_maybe_in_right (?:sdsf K (lda n A B) (pi m A ZZ));
Qrepl Q_sym H6; Refine Zh; Refine socc_split_lem (inr tinZZ); Refine Q_refl;
(* now can synthesise result for BB1 a sort *)
intros typedt; Refine inl; Refine ExIn (pi u A BB1);
Refine sdsfLda t23h ?? pBB t1h;
Qrepl Trm_eq_subst (Trm_eq_alpha_sort_lem eqBBt);
intros s; intros; Qrepl Q_sym (SSdecide H); Immed;
Qrepl +1 Q_sym (Trm_eq_subst eqA1); Immed;
(* synthesize the result for BB1 not a sort *)
intros nBBinSS; Refine inl; Refine ExIn (pi u A BB1);
Refine sdsfLda t23h ?? pBB t1h;
intros; Refine sdsf_typedsort_maybe_in_right A1h;
Qrepl Trm_eq_subst eqA1; Qrepl Trm_eq_subst H; Qrepl socc_sort_lem t t;
  Refine SSrefl;
Qrepl Trm_eq_subst eqA1; Qrepl Trm_eq_sym (sort t) (alpha p u BB1);
   Refine isnotSrt_lem nBBinSS;
Qrepl +1 Q_sym (Trm_eq_subst eqA1); Immed;

(* app *)
intros;
(* left prem *)
Refine wf_ih K A;
Equiv Lt (add (lngth ?) (Cxt_ln ?))
         (S (add (add (lngth ?) (lngth ?)) (Cxt_ln ?)));
Qrepl addCommute (lngth B) (lngth A);
Qrepl addAssocR (lngth A) (Cxt_ln K) (lngth B); Refine Lt_add_S_left;
intros +1; Refine inr; Refine contrapos ? H; intros h;
Refine h; intros C Ch; Refine sdsf_gen_app Ch; intros;
Refine H1; intros; Refine ExIn t; Immed;
(* left prem derivable now *)
intros plp; Refine plp; intros X lpd;
(* right prem *)
Refine wf_ih K B;
Equiv Lt (add (lngth ?) (Cxt_ln ?))
         (S (add (add (lngth ?) (lngth ?)) (Cxt_ln ?)));
Qrepl addAssocR (lngth B) (Cxt_ln K) (lngth A); Refine Lt_add_S_left;
intros +1; Refine inr; Refine contrapos ? H; intros h;
Refine h; intros C Ch; Refine sdsf_gen_app Ch; intros;
Refine H1; intros; Refine ExIn s; Immed;
(* right prem derivable now *)
intros prp; Refine prp; intros Y rpd;
(* redX condition *)
Refine gts_type_decides_RedToPi gtn|X;
    Refine Ex2In K A; Refine sdsf_gts sf lpd;
intros +1 nRTP; Refine inr; Refine contrapos ? nRTP; intros h;
Refine h; intros C Ch; Refine sdsf_gen_app Ch; intros;
Refine H; intros; Refine conv_pi_character (?:conv (pi w u v) X);
Refine conv_trans ? (sdsf_unique_types f H1 lpd);
Refine conv_sym; Refine conv_redn H3;
intros; Refine H6; intros; Refine Ex3In t1 s1 u1; Refine H7;
(* redX derivable *)
intros pRTPX; Refine pRTPX; intros AA BB w RTPX;
(* cnv condition *)
(* note that AA is normalizing by red_normalizing_pi_subterms_normalizing,
 * so don't really need to prove that AA has a type
 *)
Refine gts_type_term_decides_cnv gtn ndc|Y|AA;
Refine Ex2In K B; Refine sdsf_gts sf rpd;
  (* to see AA has a type, use use PR, type_correctness and pi-generation *)
Refine type_correctness (gtsPR (sdsf_gts sf lpd) RTPX);
intros s shyp; Refine shyp;
  intros eqpis; Refine tt_not_ff (Q_sym eqpis);
  intros gtsG1pis; Refine gts_gen_pi gtsG1pis; intros t1 t2 t3 p hyp;
    Refine hyp; intros; Refine Ex2In K (sort t1); Refine H1;
(* fail if not cnv Y AA *)
intros +1 nCYA; Refine inr; Refine contrapos ? nCYA; intros h;
Refine h; intros C Ch; Refine sdsf_gen_app Ch; intros;
Refine H; intros;
Refine cnv_trans ? (fst (cnvCR_pi (?:cnv (pi w AA BB1) (pi w1 u v))));
Refine cnv_trans ? H4; Refine cnv_conv (sdsf_unique_types f rpd H2);
Refine cnv_conv;
Refine sdsf_Vclosed lpd; Refine sdsf_Vclosed H1; intros;
Refine conv_trans (conv_sym (conv_redn RTPX));
Refine conv_trans (sdsf_unique_types f lpd H1) (conv_redn H3);
(* cnv condition derivable *)
intros sc; Refine inl; Refine ExIn (vsub B w BB1); Refine sdsfApp; Immed;
Save;


[gtsTS [G:Cxt][M:Trm] = Ex [A:Trm] gts G M A];

Goal gts_typSyn:
     {sf:semiFull}{f:Functional}
     {cf:cnv_full_below}{cpt:cnv_preserves_typedsort_dn}{cp:cnv_pi}
     {dt:{s:SS}decidable (typedsort s)}
     {dr:{s:SS}decidable (ruledsort s)}
     {drs:{s1,s2:SS}decidable (ruledsorts s1 s2)}
     {ndc:normalizing_decides_cnv}
     {gtn:gts_term_Normalizing}
     {G:Cxt}{M:Trm}decidable (gtsTS G M);
intros; Refine sf_typSyn; Immed;
intros h; Refine inl; Refine h; intros;
   Refine ExIn t; Refine sdsf_gts; Immed;
intros h; Refine inr; Refine contrapos ? h; intros g; Refine g; intros;
   Refine gts_sdsf; Immed; intros X Xh; Refine ExIn X; Refine fst Xh;
Save gts_typSyn;

Goal decide_gts:
     {sf:semiFull}{f:Functional}
     {cfb:cnv_full_below}{cpt:cnv_preserves_typedsort_dn}{cp:cnv_pi}
     {crt:cnv_range_typedsort}
     {dt:{s:SS}decidable (typedsort s)}
     {dr:{s:SS}decidable (ruledsort s)}
     {drs:{s1,s2:SS}decidable (ruledsorts s1 s2)}
     {ndc:normalizing_decides_cnv}
     {gtn:gts_term_Normalizing}
     {G:Cxt}{M,A:Trm}decidable (gts G M A);
intros; Refine decide_sdsfTS_decide_gts; Immed;
Refine sf_typSyn; Immed;
Save decide_gts;
