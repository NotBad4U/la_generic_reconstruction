require open Stdlib.Prop;
require open Stdlib.Set;
require open Stdlib.Eq;
require open Stdlib.Z;
require open lambdapi.Classic;
require open lambdapi.Alethe;
require open lambdapi.Simplify;
require open lambdapi.Rare;
require open lambdapi.LiaAC;


symbol x : El (int);
symbol y : El (int);
symbol p_2 ≔ ((x + y) < 1);
symbol p_3 ≔ (x + y);
symbol p_4 ≔ (¬ ((x = 2)));
symbol p_5 ≔ (x = 2);
symbol p_7 ≔ (0 = y);
symbol p_9 ≔ (3 < x);
symbol p_10 ≔ (¬ ((3 < x)));

symbol a0 : $\pid$ ((p_2 ∨ᶜ (3 < x)) ⟇ ▩);

symbol a1 : $\pid$ (p_5 ⟇ ▩);

symbol a2 : $\pid$ (p_7 ⟇ ▩);

opaque symbol t2 : $\pid$ ((¬ (p_9))  ⟇ p_4 ⟇ ▩) ≔ 
begin
have Hla : $\pid$ (((¬ ((3 < x))) ∨ᶜ (¬ ((x = 2)))) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    try rewrite Zinv_lt_eq;
    rewrite Z_diff_gt_Z0_eq ((— 3)) ((— x));
    rewrite Z_diff_eq_Z0_eq (x) (2);
    rewrite Zgt_le_succ_r_eq (((— 3) - (— x))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— 3) - (— x))) ((0 + 1));
    rewrite Zmult_eq_compat_eq ((— 1)) ((x - 2)) (0);
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H0;
    apply ¬ᶜᵢ;
    assume H1;
    set H0l' ≔ (1 * ((— 3) - (— x)));
    set H0r' ≔ (1 * (0 + 1));
    set H1l' ≔ ((— 1) * (x - 2));
    set H1r' ≔ ((— 1) * 0);
    have H1': $\pic$ (H1l' ≥ H1r') { refine Z_eq_implies_ge H1 }; remove H1;
    have contra : $\pic$ ((⇓ (⇑ (H0l' + H1l'))) ≥ (⇓ (⇑ (H0r' + H1r')))) {
        rewrite ⇓_⇑;
        rewrite ⇓_⇑;
        apply (Zsum_geq_s H0l' H0r' H1l' H1r' H0 H1');
    };
    apply (⇒ᶜₑ' contra);
    apply trivial;
};
simplify;
rewrite or_identity_r;
apply ($\pid$ₗ Hla);
end;


opaque symbol t3 : $\pid$ (p_10 ⟇ ▩) ≔ 
begin
have a1_t2 : $\pid$ (p_10 ⟇ ▩) {
    have t2_perm : $\pic$ ((⟇_to_∨ᶜ_rw ((¬ ((3 < x)))  ⟇ (¬ ((x = 2))) ⟇ ▩)) = (⟇_to_∨ᶜ_rw ((¬ ((x = 2)))
             ⟇ (¬ ((3 < x)))
            ⟇ ▩))) {
        apply (cl_perm_correct ((¬ ((3 < x)))  ⟇ (¬ ((x = 2))) ⟇ ▩) ((¬ ((x = 2)))  ⟇ (¬ ((3 < x))) ⟇ ▩));
        apply trivial;
    };
    apply resolutionₗ a1 (subst_equiv_clause ((¬ ((3 < x)))  ⟇ (¬ ((x = 2))) ⟇ ▩) ((¬ ((x = 2)))
         ⟇ (¬ ((3 < x)))
        ⟇ ▩) t2_perm t2);
};
refine a1_t2;
end;

opaque symbol t4 : $\pid$ (p_2 ⟇ ▩) ≔ 
begin
have t1_t3 : $\pid$ (p_2 ⟇ ▩) {
    have t1_perm : $\pic$ ((⟇_to_∨ᶜ_rw (((x + y) < 1)  ⟇ (3 < x) ⟇ ▩)) = (⟇_to_∨ᶜ_rw ((3 < x)  ⟇ ((x + y) < 1) ⟇ ▩))) {
        apply (cl_perm_correct (((x + y) < 1)  ⟇ (3 < x) ⟇ ▩) ((3 < x)  ⟇ ((x + y) < 1) ⟇ ▩));
        apply trivial;
    };
    apply resolutionₗ (subst_equiv_clause (((x + y) < 1)  ⟇ (3 < x) ⟇ ▩) ((3 < x)
         ⟇ ((x + y) < 1)
        ⟇ ▩) t1_perm t1) t3;
};
refine t1_t3;
end;

opaque symbol t5 : $\pid$ ((¬ (((x + y) < 1)))  ⟇ (¬ ((x = 2)))  ⟇ (¬ ((0 = y))) ⟇ ▩) ≔ 
begin
have Hla : $\pid$ (((¬ (((x + y) < 1))) ∨ᶜ (¬ ((x = 2))) ∨ᶜ (¬ ((0 = y)))) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    try rewrite Zinv_lt_eq;
    rewrite Z_diff_gt_Z0_eq ((— (x + y))) ((— 1));
    rewrite Z_diff_eq_Z0_eq (x) (2);
    rewrite Z_diff_eq_Z0_eq (0) (y);
    rewrite Zgt_le_succ_r_eq (((— (x + y)) - (— 1))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (x + y)) - (— 1))) ((0 + 1));
    rewrite Zmult_eq_compat_eq (1) ((x - 2)) (0);
    rewrite Zmult_eq_compat_eq ((— 1)) ((0 - y)) (0);
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H0;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H1;
    apply ¬ᶜᵢ;
    assume H2;
    set H0l' ≔ (1 * ((— (x + y)) - (— 1)));
    set H0r' ≔ (1 * (0 + 1));
    set H1l' ≔ (1 * (x - 2));
    set H1r' ≔ (1 * 0);
    set H2l' ≔ ((— 1) * (0 - y));
    set H2r' ≔ ((— 1) * 0);
    have H1': $\pic$ (H1l' ≥  H1r') { refine Z_eq_implies_ge H1 }; remove H1;
    have H2': $\pic$ (H2l' ≥  H2r') { refine Z_eq_implies_ge H2 }; remove H2;
    have contra : $\pic$ ((⇓ (⇑ (H0l' + H1l' + H2l'))) ≥ (⇓ (⇑ (H0r' + H1r' + H2r')))) {
        rewrite ⇓_⇑;
        rewrite ⇓_⇑;
        apply (Zsum_geq_s H0l' H0r' (H1l' + H2l') (H1r' + H2r') H0 (Zsum_geq_s H1l' H1r' H2l' H2r' H1' H2'));
    };
    apply (⇒ᶜₑ' contra);
    apply trivial;
};
simplify;
rewrite or_identity_r;
apply ($\pid$ₗ Hla);
end;

opaque symbol t6 : $\pid$ ▩ ≔ 
begin
have t5_t4 : $\pid$ (p_4  ⟇ (¬ (p_7)) ⟇ ▩) {
    apply resolutionᵣ t5 t4;
};
have t5_t4_a1 : $\pid$ ((¬ (p_7)) ⟇ ▩) {
    apply resolutionᵣ t5_t4 a1;
};
have t5_t4_a1_a2 : $\pid$ ▩ {
    apply resolutionᵣ t5_t4_a1 a2;
};
refine t5_t4_a1_a2;
end;
