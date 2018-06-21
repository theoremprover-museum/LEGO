Module artificial-break
Import conversion_cut;

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
