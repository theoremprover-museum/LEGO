Module sf_partial Import asdsf decide_red_cnv sf_typSyn;

(* given some partial algorithms, compute a partial algorithm
 * for type synthesis of sdsf
 *)


%\VerbFileOpen opt_sdsfTypSyn
Inductive [opt_sdsfTypSyn:Cxt->Trm->Prop]  NoReductions Constructors
  [sdsfSYN_some:{G|Cxt}{M,A|Trm}{j:sdsf G M A}opt_sdsfTypSyn G M]
  [sdsfSYN_none:{G:Cxt}{M:Trm}opt_sdsfTypSyn G M];
%\VerbFileClos opt_sdsfTypSyn


%\VerbFileOpen partial_sdsf_typSyn
Goal partial_sdsf_typSyn:
     {sf:semiFull}
     {gtn:gts_term_Normalizing}
     {dt:{s:SS}decidable (typedsort s)}
     {dr:{s:SS}decidable (ruledsort s)}
     {drs:{s1,s2:SS}decidable (ruledsorts s1 s2)}
     {ndc:normalizing_decides_cnv}
     {G:Cxt}{M:Trm}opt_sdsfTypSyn G M;
%\VerbFileClos partial_sdsf_typSyn
intros ______;
[dRTS = gts_type_decides_RedToSort gtn];
[dRTP = gts_type_decides_RedToPi gtn];
Refine Cxt_Trm_WF_ind Cxt_Trm_ln ([G:Cxt][M:Trm]opt_sdsfTypSyn G M);
%\VerbFileOpen partial_sdsf_typSyn_Claim
Claim {M:Trm}{G:Cxt}({g:Cxt}{m:Trm}(Lt (Cxt_Trm_ln g m) (Cxt_Trm_ln G M))->
                        opt_sdsfTypSyn g m)->opt_sdsfTypSyn G M;
%\VerbFileClos partial_sdsf_typSyn_Claim
intros; Refine ?3; Immed;
Refine Trec [M:Trm]{G:Cxt}{wf_ih:{g:Cxt}{m:Trm}
                (Lt (Cxt_Trm_ln g m) (Cxt_Trm_ln G M))->opt_sdsfTypSyn g m}
       opt_sdsfTypSyn G M;

(* sort *)
intros;
(* secondary induction on G *)
Refine NIL_or_CONS G;
(* G is Nil: axiom rule *)
intros Gnil; Qrepl Gnil;
Refine dt s;
intros tss; Refine tss; intros t th; Refine sdsfSYN_some (sdsfAx th);
intros; Refine sdsfSYN_none;
(* G is CONS: sWeak rule *)
intros Gcons; Refine Gcons; intros b K bKh; Qrepl bKh;
(* fail if parameter not fresh *)
Refine tt_or_ff (Poccur (namOf b) K);
intros binK; Refine sdsfSYN_none;
intros bfresh;
(* fail if left premiss not derivable *)
Refine opt_sdsfTypSyn_elim [L:Cxt][N:Trm][_:opt_sdsfTypSyn L N]
              (Q L K)->(Q N (sort s))->opt_sdsfTypSyn (CONS b K) (sort s);
intros +1; Refine sdsfSYN_none;
Refine +3 wf_ih K (sort s); Next +1; Qrepl bKh;
Equiv Lt (S (Cxt_ln ?)) (S (add (lngth ?) (Cxt_ln ?)));
Refine fst (Lt_resp_S ??); Refine lngth_is_S (typOf b); intros nb eqnb;
Qrepl eqnb; Refine Lt_add_S_left;
Refine +1 Q_refl; Refine +1 Q_refl; intros;
(* fail if right premiss not derivable *)
Refine opt_sdsfTypSyn_elim [L:Cxt][N:Trm][_:opt_sdsfTypSyn L N]
              (Q L K)->(Q N (typOf b))->opt_sdsfTypSyn (CONS b K) (sort s);
intros +1; Refine sdsfSYN_none;
Refine +3 wf_ih K (typOf b); Next +1; Qrepl bKh;
Equiv Lt (add (lngth ?) (Cxt_ln ?)) (add one (add (lngth ?) (Cxt_ln ?)));
Refine Lt_incl_S;
Refine +1 Q_refl; Refine +1 Q_refl; intros;
(* fail if A1 doesn't reduce to a sort *)
Refine dRTS|A1; Refine Ex2In G2 M1; Refine sdsf_gts sf j1;
intros +1; Refine sdsfSYN_none;
intros rtsA1; Refine rtsA1; intros t redA1t;
(* can synthesise the answer *)
Qrepl PROD_surj_pair b;
Refine sdsfSYN_some (sdsfsWeak bfresh redA1t ??);
Qrepl +1 Q_sym H; Qrepl +1 Q_sym H1; 
Qrepl +2 Q_sym H2; Qrepl +2 Q_sym H3; Immed;

(* var *)
intros; Refine sdsfSYN_none;

(* par *)
intros;
(* we want to do case analysis on whether the last parameter in G is
 * n or not.  In order to see that G is a CONS, we first analyse
 * G as NIL or CONS
 *)
Refine NIL_or_CONS G;
intros Gnil; Refine sdsfSYN_none;
(* G is (CONS b K) *)
intros Gcons; Refine Gcons; intros b K eqGbK; Qrepl eqGbK; 
(* analyse n = (namOf b) *)
Refine tt_or_ff (PPeq n (namOf b));
(*  n = (namOf b) is Start rule *)
intros eqnb;
(* fail if parameter not fresh *)
Refine tt_or_ff (Poccur (namOf b) K);
intros binK; Refine sdsfSYN_none;
intros bfresh;
(* fail if premiss not derivable *)
Refine opt_sdsfTypSyn_elim [L:Cxt][N:Trm][_:opt_sdsfTypSyn L N]
              (Q L K)->(Q N (typOf b))->opt_sdsfTypSyn (CONS b K) (par n);
intros +1; Refine sdsfSYN_none;
Refine +3 wf_ih K (typOf b); Next +1;
Qrepl eqGbK; Equiv Lt ? (add (lngth ?) (Cxt_ln ?));
Refine lngth_is_S (par n); intros ln eqln; Qrepl eqln; Refine Lt_add_S_left;
Refine +1 Q_refl; Refine +1 Q_refl; intros;
(* fail if the type of (typOf b) doesn't reduce to a sort *)
Refine dRTS|A; Refine Ex2In G1 M; Refine sdsf_gts sf j;
intros +1; Refine sdsfSYN_none;
(* can synthesize answer *)
intros rtsA; Refine rtsA; intros t redAt;
Qrepl PROD_surj_pair b; Qrepl (PPdecide eqnb);
Refine sdsfSYN_some (sdsfStart bfresh redAt ?);
Qrepl Q_sym H; Qrepl Q_sym H1; Immed;
(* n <> (namOf b) is vWeak rule *)
intros neqnb;
Refine tt_or_ff (Poccur (namOf b) K);
intros binK; Refine sdsfSYN_none;
intros bfresh;
(* fail if left premiss not derivable *)
Refine opt_sdsfTypSyn_elim [L:Cxt][N:Trm][_:opt_sdsfTypSyn L N]
              (Q L K)->(Q N (par n))->opt_sdsfTypSyn (CONS b K) (par n);
intros +1; Refine sdsfSYN_none;
Refine +3 wf_ih K (par n); Next +1; Qrepl eqGbK;
Equiv Lt (S (Cxt_ln ?)) (S (add (lngth ?) (Cxt_ln ?)));
Refine fst (Lt_resp_S ??); Refine lngth_is_S (typOf b); intros nb eqnb;
Qrepl eqnb; Refine Lt_add_S_left;
Refine +1 Q_refl; Refine +1 Q_refl; intros;
(* fail if right premiss not derivable *)
Refine opt_sdsfTypSyn_elim [L:Cxt][N:Trm][_:opt_sdsfTypSyn L N]
              (Q L K)->(Q N (typOf b))->opt_sdsfTypSyn (CONS b K) (par n);
intros +1; Refine sdsfSYN_none;
Refine +3 wf_ih K (typOf b); Next +1; Qrepl eqGbK;
Equiv Lt (add (lngth ?) (Cxt_ln ?)) (add one (add (lngth ?) (Cxt_ln ?)));
Refine Lt_incl_S;
Refine +1 Q_refl; Refine +1 Q_refl; intros;
(* fail if A1 doesn't reduce to a sort *)
Refine dRTS|A1; Refine Ex2In G2 M1; Refine sdsf_gts sf j1;
intros +1; Refine sdsfSYN_none;
(* can synthesise the answer *)
intros rtsA1; Refine rtsA1; intros t redA1t;
Qrepl PROD_surj_pair b;
Refine sdsfSYN_some (sdsfvWeak bfresh redA1t ??);
Qrepl +1 Q_sym H; Qrepl +1 Q_sym H1; 
Qrepl +2 Q_sym H2; Qrepl +2 Q_sym H3; Immed;

(* pi *)
intros;
(* pick a fresh parameter: must be fresh for G or algorithm is incomplete! *)
Refine fresh_params_lem1G G B; intros p pGB; Refine pGB; intros pG pB;
(* fail if left premiss not derivable *)
Refine opt_sdsfTypSyn_elim [L:Cxt][N:Trm][_:opt_sdsfTypSyn L N]
              (Q L G)->(Q N A)->opt_sdsfTypSyn G (pi n A B);
intros +1; Refine sdsfSYN_none;
Refine +3 wf_ih G A; Next +1; 
Equiv Lt ? (S (add (add (lngth ?) (lngth ?)) (Cxt_ln ?)));
Qrepl addCommute (lngth B) (lngth A);
Qrepl addAssocR (lngth A) (Cxt_ln G) (lngth B); Refine Lt_add_S_left;
Refine +1 Q_refl; Refine +1 Q_refl; intros;
(* fail if right premiss not derivable *)
Refine opt_sdsfTypSyn_elim [L:Cxt][N:Trm][_:opt_sdsfTypSyn L N]
          (Q L (CONS (Gb p A) G))->(Q N (vsub (par p) n B))->
             opt_sdsfTypSyn G (pi n A B);
intros +1; Refine sdsfSYN_none;
Refine +3 wf_ih (CONS (Gb p A) G) (vsub (par p) n B); Next +1;
Equiv Lt (add (lngth ?) (add (lngth ?) (Cxt_ln ?)))
         (S (add (add (lngth ?) (lngth ?)) (Cxt_ln ?)));
Qrepl alpha_preserves_lngth B p n; Qrepl addCommute (lngth B) (lngth A);
Qrepl addAssocR (lngth A) (Cxt_ln G) (lngth B); Refine Lt_incl_S;
Refine +1 Q_refl; Refine +1 Q_refl; intros;
(* fail if A1 doesn't reduce to a sort *)
Refine dRTS|A1; Refine Ex2In G1 M; Refine sdsf_gts sf j;
intros +1; Refine sdsfSYN_none;
intros rtsA1; Refine rtsA1; intros s redA1s;
(* fail if A2 doesn't reduce to a sort *)
Refine dRTS|A2; Refine Ex2In G2 M1; Refine sdsf_gts sf j1;
intros +1; Refine sdsfSYN_none;
intros rtsA2; Refine rtsA2; intros s1 redA2s1;
(* fail if no rule applies *)
Refine drs s s1;
intros +1; Refine sdsfSYN_none;
intros rss; Refine rss; intros s3 rule;
(* can synthesise the answer *)
Refine sdsfSYN_some (sdsfPi rule pB ????);
Refine +2 redA1s; Refine +1 redA2s1;
Qrepl Q_sym H; Qrepl Q_sym H1; Qrepl +1 Q_sym H2; Qrepl +1 Q_sym H3; Immed;

(* lda *)
intros;
(* pick parameter not in B or G *)
Refine fresh_params_lem1G G B; intros p ph; Refine ph; intros pG pB;
(* fail if left premiss not derivable *)
Refine opt_sdsfTypSyn_elim [L:Cxt][N:Trm][_:opt_sdsfTypSyn L N]
          (Q L (CONS (Gb p A) G))->(Q N (vsub (par p) n B))->
             opt_sdsfTypSyn G (lda n A B);
intros +1; Refine sdsfSYN_none;
Refine +3 wf_ih (CONS (Gb p A) G) (vsub (par p) n B); Next +1;
Equiv Lt (add (lngth ?) (add (lngth ?) (Cxt_ln ?)))
         (S (add (add (lngth ?) (lngth ?)) (Cxt_ln ?)));
Qrepl alpha_preserves_lngth B p n; Qrepl addCommute (lngth B) (lngth A);
Qrepl addAssocR (lngth A) (Cxt_ln G) (lngth B); Refine Lt_incl_S;
Refine +1 Q_refl; Refine +1 Q_refl; intros;
(* fail if right premiss not derivable *)
Refine opt_sdsfTypSyn_elim [L:Cxt][N:Trm][_:opt_sdsfTypSyn L N]
              (Q L G)->(Q N A)->opt_sdsfTypSyn G (lda n A B);
intros +1; Refine sdsfSYN_none;
Refine +3 wf_ih G A; Next +1; 
Equiv Lt ? (S (add (add (lngth ?) (lngth ?)) (Cxt_ln ?)));
Qrepl addCommute (lngth B) (lngth A);
Qrepl addAssocR (lngth A) (Cxt_ln G) (lngth B); Refine Lt_add_S_left;
Refine +1 Q_refl; Refine +1 Q_refl; intros;
(* fail if A2 doesn't reduce to a sort *)
Refine dRTS|A2; Refine Ex2In G2 M1; Refine sdsf_gts sf j1;
intros +1; Refine sdsfSYN_none;
intros rtsA2; Refine rtsA2; intros s redA2s;
(* fail if no rule applies *)
Refine dr s; intros +1; Refine sdsfSYN_none;
intros rss; Refine rss; intros s2 s3 rule;
(* use shape_lemma on A1 *)
Refine shape_lemma p A1; intros u BB h; Refine h; intros eqA1 pBB;
(* must split at the typedsort condition! *)
Refine tt_or_ff (isSrt BB1);
(* BB1 is a sort *)
intros BBinSS; Refine isSrt_lem BBinSS; intros t eqBBt;
Refine dt t; intros +1; Refine sdsfSYN_none;
intros tst; Refine tst; intros ss ssh;
(* synthesize the result for BB1 a sort *)
Refine sdsfSYN_some (sdsfLda rule ? pB pBB ???);
Refine +3 redA2s; Refine u;
intros; Claim is_tt (Trm_eq (sort t1) (sort t)); Qrepl SSdecide ?+1;
 Qrepl +1 Q_sym (Trm_eq_subst H4); Immed;
Qrepl Q_sym H; Qrepl Q_sym H1; Qrepl Q_sym (Trm_eq_subst eqA1);
Qrepl +1 Q_sym H2; Qrepl +1 Q_sym H3; Immed;
(* synthesize the result for BB1 not a sort *)
intros nBBinSS;
Refine sdsfSYN_some (sdsfLda rule ? pB pBB ???);
Refine +3 redA2s; Refine u;
intros; Refine tt_not_ff; Qrepl Q_sym nBBinSS;
   Qrepl (Trm_eq_subst H4); Refine Q_refl;
Qrepl Q_sym H; Qrepl Q_sym H1; Qrepl Q_sym (Trm_eq_subst eqA1);
Qrepl +1 Q_sym H2; Qrepl +1 Q_sym H3; Immed;

(* app *)
intros;
(* fail if left premiss not derivable *)
Refine opt_sdsfTypSyn_elim [L:Cxt][N:Trm][_:opt_sdsfTypSyn L N]
              (Q L G)->(Q N A)->opt_sdsfTypSyn G (app A B);
intros +1; Refine sdsfSYN_none;
Refine +3 wf_ih G A; Next +1; 
Equiv Lt ? (S (add (add (lngth ?) (lngth ?)) (Cxt_ln ?)));
Qrepl addCommute (lngth B) (lngth A);
Qrepl addAssocR (lngth A) (Cxt_ln G) (lngth B); Refine Lt_add_S_left;
Refine +1 Q_refl; Refine +1 Q_refl; intros;
(* fail if right premiss not derivable *)
Refine opt_sdsfTypSyn_elim [L:Cxt][N:Trm][_:opt_sdsfTypSyn L N]
            (Q L G)->(Q N B)->opt_sdsfTypSyn G (app A B);
intros +1; Refine sdsfSYN_none;
Refine +3 wf_ih G B; Next +1;
Equiv Lt ? (S (add (add (lngth ?) (lngth ?)) (Cxt_ln ?)));
Qrepl addAssocR (lngth B) (Cxt_ln G) (lngth A); Refine Lt_add_S_left;
Refine +1 Q_refl; Refine +1 Q_refl; intros;
(* fail if A1 doesn't reduce to a pi *)
Refine dRTP|A1;
Refine Ex2In G1 M; Refine sdsf_gts sf j;
intros +1; Refine sdsfSYN_none;
intros rtpA1; Refine rtpA1; intros C D u redA1pi;
(* fail if A2 doesn't cnv to C *)
Refine gts_type_term_decides_cnv gtn ndc|A2|C; intros +3;
Refine sdsfSYN_none;
Refine Ex2In G2 M1; Refine sdsf_gts sf j1;
  (* to see C has a type use PR, type_correctness and pi-generation *)
Refine type_correctness (gtsPR (sdsf_gts sf j) redA1pi);
intros s shyp; Refine shyp;
  intros eqpis; Refine tt_not_ff (Q_sym eqpis);
  intros gtsG1pis; Refine gts_gen_pi gtsG1pis; intros t1 t2 t3 p hyp;
    Refine hyp; intros; Refine Ex2In G1 (sort t1); Refine H5;
intros;
(* can synthesize result *)
Refine sdsfSYN_some (sdsfApp redA1pi H4 ??);
Qrepl Q_sym H; Qrepl Q_sym H1; Immed;
Qrepl Q_sym H2; Qrepl Q_sym H3; Immed;
Save;
