Module conversion_cut
Import conversion abstract_cnv;

(***  cut in `conv' for `cnv'  ***)

(*  prove the cnv properties for conv *)

Goal conv_red1: {A,B|Trm}(par_red1 A B)->conv A B;
intros; Refine conv_redn; Refine par_redn_red1; Immed;
Save;

Goal conv_red1_sym: {A,B|Trm}(par_red1 A B)->conv B A;
intros; Refine conv_sym; Refine conv_red1; Immed;
Save;

(* the order of A, A' in conclusion matters *)
Goal cOnvCR_pi_lem:
     {u,v|VV}{A,A',B,B'|Trm}{c:conv (pi u A B) (pi v A' B')}
      and (conv A' A) ({q:PP}conv (alpha q u B) (alpha q v B'));
intros; Refine pair (conv_sym ?);
Refine convCR_pi_lem; Immed; intros; Immed;
Refine convCR_pi_lem; Immed; intros; Immed;
Save;

Goal conv_sort_character_l:
     {s|SS}{A|Trm}{c:conv A (sort s)}Ex [t:SS] par_redn A (sort t);
intros; Refine ExIn s; Refine conv_sort_character; Refine conv_sym; Immed;
Save;

Goal conv_sort_character_r:
     {s|SS}{B|Trm}{c:conv (sort s) B}Ex [t:SS] par_redn B (sort t);
intros; Refine ExIn s; Refine conv_sort_character; Immed;
Save;

Goal conv_pi_character_l:
     {A,Bl,Br|Trm}{v|VV}{c:conv A (pi v Bl Br)}
     Ex3 [u:VV][Al,Ar:Trm] par_redn A (pi u Al Ar);
intros; Refine conv_pi_character|v|Bl|Br|A; Refine conv_sym c; intros;
Refine H; intros; Refine Ex3In u t s; Immed;
Save;


%\VerbFileOpen conv_cut
Cut [cnv=conv]
    [cnv_refl=conv_refl]
    [cnv_trans=conv_trans]
    [psub_resp_cnv=psub_resp_conv]
    [cnv_red1=conv_red1]
    [cnv_red1_sym=conv_red1_sym]
    [cnvCR_pi=cOnvCR_pi_lem]
    [cnv_Vclosed=conv_Vclosed]
    [cnv_sort_character_l=conv_sort_character_l]
    [cnv_sort_character_r=conv_sort_character_r]
    [cnv_pi_character_l=conv_pi_character_l];
%\VerbFileClos conv_cut


(* now show conv has the special properties of cnv *)

Goal crt : cnv_range_typedsort;
Expand cnv_range_typedsort; intros; Refine inl;
Refine conv_sort_sort_lem; Immed;
Save;

Goal cptd : cnv_preserves_typedsort_dn;
Expand cnv_preserves_typedsort_dn; intros;
Qrepl SSdecide (conv_sort_sort_lem H); Immed;
Save;

(***************************
Goal cp : cnv_pi;
Expand cnv_pi; intros; Refine conv_pi; Refine conv_sym; Immed;
Save;

Goal cfb : cnv_full_below;
Expand cnv_full_below; intros; Refine ExIn t3;
Refine pair ? (conv_refl (Vclosed_sort ?));
Qrepl SSdecide (conv_sort_sort_lem cv1);
Qrepl SSdecide (conv_sort_sort_lem cv2); Immed;
Save;
*********************)
