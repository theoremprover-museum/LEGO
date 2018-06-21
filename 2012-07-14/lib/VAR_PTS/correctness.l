Module correctness
Import generation apts thinning cut;

%\VerbFileOpen correct_type
[correct_type [G:Cxt][A:Trm] = Ex [s:SS] or (is_tt (Trm_eq A (sort s)))
                                            (gts G A (sort s))];
%\VerbFileClos correct_type

(* correctness of types *)
%\VerbFileOpen type_correctness
Goal type_correctness: {G|Cxt}{M,A|Trm}(gts G M A)->correct_type G A;
%\VerbFileClos type_correctness
intros;
Refine gtsRec [G:Cxt][M,A:Trm][_:gts G M A]
       Ex [s:SS]or (is_tt (Trm_eq A (sort s))) (gts G A (sort s));
Immed;
(* ax *)
intros;Refine ExIn s2;Refine inl;Refine Trm_eq_refl;
(* start *)
intros;Refine ExIn s;Refine inr;Refine weakening;Immed;
(* vWeak *)
intros;Refine l_ih;
intros s1 cases;Refine cases;
intros case_sort;Refine ExIn s1;Refine inl;Immed;
intros case_type;Refine ExIn s1;Refine inr;Refine weakening;Immed;
(* sWeak *)
intros;Refine l_ih;
intros s1 cases;Refine cases;
intros case_sort;Refine ExIn s1;Refine inl;Immed;
intros case_type;Refine ExIn s1;Refine inr;Refine weakening;Immed;
(* pi *)
intros;Refine ExIn s3;Refine inl;Refine Trm_eq_refl;
(* lda *)
intros;Refine ExIn s;Refine inr;Immed;
(* app *)
intros;Refine l_ih;
intros s1 cases;Refine cases;
intros case_sort;Refine tt_not_ff;Refine Q_sym;Immed;
intros case_type;Refine gts_gen_pi case_type;
intros s2 s3 s4 p hyp;Refine ExIn s3;Refine inr;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n (and5_out3 hyp)));
Refine cut_rule r_prem ? (and5_out4 hyp);
(* cnv *)
intros;Refine ExIn s;Refine inr;Immed;
Save;

Goal {G|Cxt}{u|VV}{M,A,B|Trm}(gts G M (pi u A B))->
      Ex [s:SS]gts G (pi u A B) (sort s);
intros;Refine type_correctness H;
intros s hyp;Refine hyp;
intros case;Refine tt_not_ff (Q_sym case);
intros case;Refine ExIn s;Immed;
Save type_correctness_pi;

(*** A better correctness theorem requires decidability ***)

(** NOTICE  (not (topsort s)) =
            (not {t:SS}not (ax s t)) => 
            (not not Ex[t:SS]ax s t) =/=> (Ex[t:SS]ax s t) = typedsort s
**)

Goal ({s:SS}decidable (typedsort s))->{s:SS}decidable (topsort s);
Expand topsort typedsort;
intros dBs s; Refine dBs s;
intros bs; Refine inr; Intros h; Refine bs; intros t axst; Refine h bs;
intros nBs; Refine inl; Immed;
Save decideTopsortLem;

%\VerbFileOpen decideTypedsort_type_correctness
Goal decideTypedsort_type_correctness:
     {dTs:{s:SS}decidable (typedsort s)}
     {G|Cxt}{M,A|Trm}{d:gts G M A}
     Ex [s:SS]or (and (is_tt (Trm_eq A (sort s))) (topsort s))
                 (gts G A (sort s));
%\VerbFileClos decideTypedsort_type_correctness
intros; Refine type_correctness d; intros t tSpec; Refine tSpec;
(* A is a sort; case on A is a typedsort or not *)
Refine dTs t;
intros tst eqAt; Refine tst; intros s sSpec;
Refine ExIn s; Refine inr; Qrepl Trm_eq_subst eqAt; Refine sStartLem; Immed;
intros ntst eqAt; Refine ExIn t; Refine inl;
Refine pair eqAt ntst;
(* G|-A:t, so we are done *)
intros h; Refine ExIn t; Refine inr; Refine h;
Save;

(*********??????????????
Goal {dTs:{s:SS}decidable (typedsort s)}
     {G|Cxt}{M,A|Trm}{d:gts G M A}
     {s|SS}(par_redn A (sort s))->gts G M (sort s);
intros;
Refine decideTypedsort_type_correctness dTs d; intros t thyp; Refine thyp;
intros case; Claim is_tt (Trm_eq (sort s) A);
  Qrepl Trm_eq_subst ?+1; Immed; Qrepl Trm_eq_subst (fst case);
  Refine par_redn_sort_character; Qrepl Trm_eq_sym (sort s) (sort t);
  Qrepl Q_sym (Trm_eq_subst (fst case)); Immed;
intros case; Refine tCnv ? d; Refine +1 conv_redn;
*****************************)
