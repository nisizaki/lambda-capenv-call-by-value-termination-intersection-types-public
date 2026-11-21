theory Examples
  imports Capture
begin

section \<open>Examples (CBV, \<open>\<lambda>\<^sub>c\<^sub>a\<^sub>p\<^sub>e\<^sub>n\<^sub>v\<close> without \<open>id\<close>)\<close>

text \<open>
  Variables: \<open>x = 0\<close>, \<open>y = 1\<close>, \<open>z = 2\<close>.  A composition \<open>M\<circ>N\<close> is \<open>Comp M N\<close> and the
  empty environment \<open>()\<close> is \<open>Nil\<close>.  \<open>\<Omega>\<close> is \<open>Omega\<close> from \<open>Capture\<close>: built from closures,
  since a bare \<open>(\<lambda>x.xx)(\<lambda>x.xx)\<close> is stuck.
\<close>

definition K :: trm where "K = Comp (Lam 0 (Lam 1 (Var 0))) Nil"

subsection \<open>Clashes: normal forms that are not fireballs\<close>

lemma not_fb_Nil_App: "\<not> fb (App Nil N)"
  by (simp add: fb_App_iff)

lemma not_fb_Lam_App: "\<not> fb (App (Lam x B) N)"
  by (simp add: fb_App_iff)

lemma not_fb_Clo_App: "\<not> fb (App (Comp (Lam x B) L) N)"
  by (simp add: fb_App_iff)

lemma not_fb_VarNil_App: "\<not> fb (App (Comp (Var y) Nil) N)"
  by (auto simp: fb_App_iff elim: inert.cases)

text \<open>\<open>x\<circ>()\<close>: a variable looked up in the empty environment.\<close>

theorem clash_var_nil: "\<not> Typ (Comp (Var 0) Nil)"
  by (rule clash_not_Typ[OF NF_Var_Nil not_fb_Var_Nil])

text \<open>\<open>() y\<close>: the empty environment applied.\<close>

theorem clash_nil_app: "\<not> Typ (App Nil (Var 1))"
  by (rule clash_not_Typ[OF _ not_fb_Nil_App])
     (auto simp: normal_def cbv_def elim!: sig.cases beta.cases)

text \<open>\<open>(\<lambda>x.x) y\<close>: a bare abstraction applied (only closures are applied).\<close>

theorem clash_bare_lam: "\<not> Typ (App (Lam 0 (Var 0)) (Var 1))"
  by (rule clash_not_Typ[OF _ not_fb_Lam_App])
     (auto simp: normal_def cbv_def elim!: sig.cases beta.cases)

text \<open>\<open>((\<lambda>x.x)\<circ>()) (y\<circ>())\<close>: the argument is a clash, so no \<open>\<beta>\<^sub>v\<close> step is possible.\<close>

theorem clash_clo_clash_arg:
  "\<not> Typ (App (Comp (Lam 0 (Var 0)) Nil) (Comp (Var 1) Nil))"
  by (rule clash_not_Typ[OF _ not_fb_Clo_App])
     (auto simp: normal_def cbv_def not_fb_Var_Nil elim!: sig.cases beta.cases)

text \<open>\<open>(y\<circ>()) \<Omega>\<close>: a clash in function position blocks the reduction of the argument.\<close>

theorem clash_VarNil_Omega: "\<not> Typ (App (Comp (Var 1) Nil) Omega)"
  by (rule clash_not_Typ[OF _ not_fb_VarNil_App])
     (auto simp: normal_def cbv_def Omega_def dw_def not_fb_Var_Nil elim!: sig.cases beta.cases)

subsection \<open>Fireballs are typable\<close>

theorem Typ_fb: "fb M \<Longrightarrow> Typ M"
  using CFN_sig_fb main_characterization by blast

theorem Typ_var_nil_arg: "Typ (App (Var 0) Nil)"
  by (rule Typ_fb) (simp add: fb_App_iff IVar FNil)

theorem Typ_var_lam_arg: "Typ (App (Var 0) (Lam 1 (Var 1)))"
  by (rule Typ_fb) (simp add: fb_App_iff IVar FLam)

theorem Typ_clo_nil: "Typ (Comp (Lam 0 (Var 0)) Nil)"
  by (rule Typ_fb) (rule FClo)

subsection \<open>Divergence\<close>

lemma loop_no_NF:
  assumes b: "M \<rightarrow>\<^sub>\<beta> M1" and s: "sig\<^sup>*\<^sup>* M1 M"
  shows "\<not> (M \<rightarrow>\<^sub>v\<^sup>* N \<and> NF N)"
proof
  assume h: "M \<rightarrow>\<^sub>v\<^sup>* N \<and> NF N"
  from steps_cd[of M N] h obtain k where c: "cd M k N" by blast
  from cd_fwd_beta[OF b c] obtain j where k: "k = Suc j" and c1: "cd M1 j N" by blast
  have c2: "cd M j N" by (rule cd_fwd_sig_steps[OF s c1])
  have "Suc j = j" using cd_det[OF c[unfolded k] c2] by (rule conjunct1)
  then show False by simp
qed

text \<open>\<open>\<Omega>\<close> returns to itself through a \<open>\<beta>\<^sub>v\<close> step plus \<open>\<sigma>\<close>-steps: it has no normal form,
  hence is not strongly normalizing, and it is not typable.\<close>

theorem Omega_diverges:
  "\<not> (\<exists>N. Omega \<rightarrow>\<^sub>v\<^sup>* N \<and> NF N)"
  "\<not> SN_at cbv Omega"
  "\<not> Typ Omega"
proof -
  show nonf: "\<not> (\<exists>N. Omega \<rightarrow>\<^sub>v\<^sup>* N \<and> NF N)"
    using loop_no_NF[OF Omega_loop] by blast
  show "\<not> SN_at cbv Omega" using SN_normalizes nonf by blast
  show "\<not> Typ Omega" by (rule Omega_not_Typ)
qed

subsection \<open>Call-by-value: arguments are evaluated, abstractions are values\<close>

theorem K_Omega_not_Typ: "\<not> Typ (App K Omega)"
proof -
  have b: "App K Omega \<rightarrow>\<^sub>\<beta> App K (Comp (App (Var 0) (Var 0)) (Extn (Comp dw Nil) 0 Nil))"
    by (rule AppR[OF _ Omega_loop(1)]) (simp add: K_def FClo)
  have s: "sig\<^sup>*\<^sup>* (App K (Comp (App (Var 0) (Var 0)) (Extn (Comp dw Nil) 0 Nil))) (App K Omega)"
    by (rule sig_steps_lift[OF sig.AppR Omega_loop(2)])
  show ?thesis using loop_not_CFN[OF b s] main_characterization by blast
qed

theorem K_lam_Omega_Typ: "Typ (App K (Lam 2 Omega))"
proof -
  let ?R = "Comp (Lam 1 (Var 0)) (Extn (Lam 2 Omega) 0 Nil)"
  have b: "App K (Lam 2 Omega) \<rightarrow>\<^sub>\<beta> ?R"
    unfolding K_def by (rule Beta) (rule FLam)
  have "NF ?R"
  proof (rule fb_NF[OF FClo])
    show "sig_normal ?R"
      by (auto simp: normal_def Omega_def dw_def elim!: sig.cases)
  qed
  moreover have "App K (Lam 2 Omega) \<rightarrow>\<^sub>v\<^sup>* ?R"
    using beta_imp_cbv[OF b] by (rule r_into_rtranclp)
  ultimately have "CFN (App K (Lam 2 Omega))" using FClo unfolding CFN_def by blast
  then show ?thesis using main_characterization by blast
qed

subsection \<open>Lazy environments\<close>

text \<open>\<open>z\<circ>((\<Omega>/x)\<cdot>cap [z])\<close> with \<open>x \<noteq> z\<close>: the diverging component is never looked up.\<close>

theorem lazy_env_Typ: "Typ (Comp (Var 2) (Extn Omega 0 (cap [2])))"
  by (rule cap_lazy_env(3)) simp

theorem lazy_env_Typ_general: "x \<noteq> z \<Longrightarrow> Typ (Comp (Var z) (Extn Omega x (cap [z])))"
  by (rule cap_lazy_env(3))

end
