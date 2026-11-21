theory Soundness
  imports Completeness
begin

section \<open>Soundness: \<open>Typ M \<Longrightarrow> CFN M\<close>\<close>

text \<open>
  Realizability as for call-by-value \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> (arrows quantify over normalizing
  arguments; sets are closed under forward and backward reduction).  The basic lemma
  has two forms: \<open>M \<circ> e\<close> in an environment context \<open>CE C\<close>, \<open>M\<close> itself at top level.
\<close>

subsection \<open>Normal forms of some shapes\<close>

lemma NF_Var: "NF (Var x)"
  by (auto simp: normal_def cbv_def elim: sig.cases beta.cases)

lemma NF_App_inert:
  assumes i: "inert I" and ni: "NF I" and f: "fb F" and nf: "NF F"
  shows "NF (App I F)"
proof (rule normalI)
  fix Q
  show "\<not> App I F \<rightarrow>\<^sub>v Q"
  proof
    assume "App I F \<rightarrow>\<^sub>v Q"
    then consider "App I F \<rightarrow>\<^sub>\<sigma> Q" | "App I F \<rightarrow>\<^sub>\<beta> Q" by (auto simp: cbv_def)
    then show False
    proof cases
      case 1
      then show False
        using ni nf by (cases rule: sig.cases) (auto simp: normal_def cbv_def)
    next
      case 2
      then show False
        using ni nf i inert_not_Lam inert_not_Clo
        by (cases rule: beta.cases) (auto simp: normal_def cbv_def)
    qed
  qed
qed

lemma NF_Comp_inert:
  assumes i: "inert I" and ni: "NF I"
  shows "NF (Comp (Var x) I)"
proof (rule normalI)
  fix Q
  show "\<not> Comp (Var x) I \<rightarrow>\<^sub>v Q"
  proof
    assume "Comp (Var x) I \<rightarrow>\<^sub>v Q"
    then consider "Comp (Var x) I \<rightarrow>\<^sub>\<sigma> Q" | "Comp (Var x) I \<rightarrow>\<^sub>\<beta> Q" by (auto simp: cbv_def)
    then show False
    proof cases
      case 1
      then show False
        using ni i inert_not_Extn
        by (cases rule: sig.cases) (auto simp: normal_def cbv_def elim: sig.cases)
    next
      case 2
      then show False
        using ni by (cases rule: beta.cases) (auto simp: normal_def cbv_def)
    qed
  qed
qed

lemma CFN_sig_fb: "fb M \<Longrightarrow> CFN M"
proof -
  assume f: "fb M"
  obtain N where s: "sig\<^sup>*\<^sup>* M N" and n: "sig_normal N" using sig_nf by blast
  have "fb N" using sig_steps_fb[OF s f] .
  then show "CFN M" using fb_NF[OF _ n] sig_steps_cbv[OF s] by (auto simp: CFN_def)
qed

lemma CFN_Lam: "CFN (Lam x M)" by (rule CFN_sig_fb[OF FLam])
lemma CFN_Extn: "CFN (Extn M x N)" by (rule CFN_sig_fb[OF FExtn])
lemma CFN_Clo: "CFN (Comp (Lam x M) e)" by (rule CFN_sig_fb[OF FClo])

text \<open>Weak neutral terms.\<close>

inductive wneu :: "trm \<Rightarrow> bool" where
  "wneu (Var x)"
| "wneu M \<Longrightarrow> CFN N \<Longrightarrow> wneu (App M N)"
| "wneu M \<Longrightarrow> wneu (Comp (Var x) M)"

lemma wneu_reduces: "wneu M \<Longrightarrow> \<exists>I. M \<rightarrow>\<^sub>v\<^sup>* I \<and> NF I \<and> inert I"
proof (induction rule: wneu.induct)
  case (1 x)
  then show ?case using NF_Var IVar by blast
next
  case (2 M N)
  then obtain I where r1: "M \<rightarrow>\<^sub>v\<^sup>* I" and n1: "NF I" and i: "inert I" by blast
  from 2 obtain F where r2: "N \<rightarrow>\<^sub>v\<^sup>* F" and n2: "NF F" and f: "fb F" by (auto simp: CFN_def)
  have "App M N \<rightarrow>\<^sub>v\<^sup>* App I N" by (rule cbv_steps_AppL[OF r1])
  moreover have "App I N \<rightarrow>\<^sub>v\<^sup>* App I F" by (rule cbv_steps_AppR[OF FInert[OF i] r2])
  moreover have "NF (App I F)" by (rule NF_App_inert[OF i n1 f n2])
  moreover have "inert (App I F)" using i f by (rule IApp)
  ultimately show ?case by (meson rtranclp_trans)
next
  case (3 M x)
  then obtain I where r1: "M \<rightarrow>\<^sub>v\<^sup>* I" and n1: "NF I" and i: "inert I" by blast
  have "Comp (Var x) M \<rightarrow>\<^sub>v\<^sup>* Comp (Var x) I" by (rule cbv_steps_VarR[OF r1])
  moreover have "NF (Comp (Var x) I)" by (rule NF_Comp_inert[OF i n1])
  moreover have "inert (Comp (Var x) I)" using i by (rule IComp)
  ultimately show ?case by blast
qed

lemma wneu_CFN: "wneu M \<Longrightarrow> CFN M"
  using wneu_reduces FInert by (auto simp: CFN_def)

subsection \<open>Interpretation of types\<close>

fun I :: "ty \<Rightarrow> trm set" where
  "I (TV n) = {M. CFN M}"
| "I Om = UNIV"
| "I (Arr A B) = {M. CFN M \<and> (\<forall>N \<in> I A. CFN N \<longrightarrow> App M N \<in> I B)}"
| "I (Inter A B) = I A \<inter> I B"
| "I (Env m ob) =
     {e. ((m \<noteq> [] \<or> ob) \<longrightarrow> CFN e) \<and>
         (\<forall>x S. map_of (map (\<lambda>(y, A). (y, I A)) m) x = Some S \<longrightarrow> Comp (Var x) e \<in> S)}"

lemma I_Env:
  "e \<in> I (Env m ob) \<longleftrightarrow>
     ((m \<noteq> [] \<or> ob) \<longrightarrow> CFN e) \<and> (\<forall>x A. map_of m x = Some A \<longrightarrow> Comp (Var x) e \<in> I A)"
  by (simp add: map_of_map_dep) blast

declare I.simps(5) [simp del]

lemma I_back: "M \<rightarrow>\<^sub>v M' \<Longrightarrow> M' \<in> I A \<Longrightarrow> M \<in> I A"
proof (induction A arbitrary: M M')
  case (TV n) then show ?case using CFN_back by simp
next
  case Om then show ?case by simp
next
  case (Arr A B)
  have "CFN M" using Arr.prems CFN_back by simp
  moreover have "App M N \<in> I B" if "N \<in> I A" "CFN N" for N
  proof -
    have "App M' N \<in> I B" using Arr.prems that by simp
    then show ?thesis using Arr.IH(2)[OF cbv_AppL[OF Arr.prems(1)]] by blast
  qed
  ultimately show ?case by simp
next
  case (Inter A B) then show ?case by simp
next
  case (Env m ob)
  have "Comp (Var x) M \<in> I A" if l: "map_of m x = Some A" for x A
  proof -
    have xa: "(x, A) \<in> set m" using l by (rule map_of_SomeD)
    have sn: "A \<in> Basic_BNFs.snds (x, A)" by simp
    have c: "Comp (Var x) M' \<in> I A" using Env.prems(2) l by (simp add: I_Env)
    show ?thesis by (rule Env.IH[OF xa sn cbv_VarR[OF Env.prems(1)] c])
  qed
  then show ?case using Env.prems CFN_back by (simp add: I_Env)
qed

lemma I_back_steps: "M \<rightarrow>\<^sub>v\<^sup>* M' \<Longrightarrow> M' \<in> I A \<Longrightarrow> M \<in> I A"
  by (induction rule: converse_rtranclp_induct) (auto intro: I_back)

lemma I_fwd: "M \<rightarrow>\<^sub>v M' \<Longrightarrow> M \<in> I A \<Longrightarrow> M' \<in> I A"
proof (induction A arbitrary: M M')
  case (TV n) then show ?case using CFN_fwd by simp
next
  case Om then show ?case by simp
next
  case (Arr A B)
  have "CFN M'" using Arr.prems CFN_fwd by simp
  moreover have "App M' N \<in> I B" if "N \<in> I A" "CFN N" for N
  proof -
    have "App M N \<in> I B" using Arr.prems that by simp
    then show ?thesis using Arr.IH(2)[OF cbv_AppL[OF Arr.prems(1)]] by blast
  qed
  ultimately show ?case by simp
next
  case (Inter A B) then show ?case by simp
next
  case (Env m ob)
  have "Comp (Var x) M' \<in> I A" if l: "map_of m x = Some A" for x A
  proof -
    have xa: "(x, A) \<in> set m" using l by (rule map_of_SomeD)
    have sn: "A \<in> Basic_BNFs.snds (x, A)" by simp
    have c: "Comp (Var x) M \<in> I A" using Env.prems(2) l by (simp add: I_Env)
    show ?thesis by (rule Env.IH[OF xa sn cbv_VarR[OF Env.prems(1)] c])
  qed
  then show ?case using Env.prems CFN_fwd by (simp add: I_Env)
qed

lemma I_fwd_steps: "M \<rightarrow>\<^sub>v\<^sup>* M' \<Longrightarrow> M \<in> I A \<Longrightarrow> M' \<in> I A"
  by (induction rule: rtranclp_induct) (auto intro: I_fwd)

lemma I_ess: "ess A \<Longrightarrow> M \<in> I A \<Longrightarrow> CFN M"
proof (induction A arbitrary: M)
  case (TV n) then show ?case by simp
next
  case Om then show ?case by simp
next
  case (Arr A B) then show ?case by simp
next
  case (Inter A B)
  then show ?case by (cases "ess A") simp_all
next
  case (Env m ob)
  then show ?case by (simp add: I_Env)
qed

lemma wneu_I: "wneu M \<Longrightarrow> M \<in> I A"
proof (induction A arbitrary: M)
  case (TV n) then show ?case using wneu_CFN by simp
next
  case Om then show ?case by simp
next
  case (Arr A B)
  then show ?case using wneu_CFN wneu.intros(2) by simp
next
  case (Inter A B) then show ?case by simp
next
  case (Env m ob)
  have "Comp (Var x) M \<in> I A" if l: "map_of m x = Some A" for x A
  proof -
    have xa: "(x, A) \<in> set m" using l by (rule map_of_SomeD)
    have sn: "A \<in> Basic_BNFs.snds (x, A)" by simp
    have w: "wneu (Comp (Var x) M)" using Env.prems by (rule wneu.intros(3))
    show ?thesis by (rule Env.IH[OF xa sn w])
  qed
  then show ?case using Env.prems wneu_CFN by (simp add: I_Env)
qed

lemma Var_I: "Var x \<in> I A"
  by (rule wneu_I) (rule wneu.intros(1))

subsection \<open>Monotonicity\<close>

lemma I_mono: "A \<preceq> B \<Longrightarrow> I A \<subseteq> I B"
proof (induction rule: sub.induct)
  case (s_arr A' A B B')
  then show ?case by auto
next
  case (s_env m' m ob' ob)
  show ?case
  proof
    fix e
    assume e: "e \<in> I (Env m ob)"
    have cf: "CFN e" if "m' \<noteq> [] \<or> ob'"
    proof -
      have "m \<noteq> [] \<or> ob"
      proof (cases "m' = []")
        case True then show ?thesis using that s_env.hyps by auto
      next
        case False
        then obtain p ps where "m' = p # ps" by (cases m') auto
        then have "map_of m' (fst p) = Some (snd p)" by (cases p) simp
        then obtain A where "map_of m (fst p) = Some A" using s_env.IH by blast
        then show ?thesis by auto
      qed
      then show ?thesis using e by (simp add: I_Env)
    qed
    moreover have "Comp (Var x) e \<in> I A'" if l: "map_of m' x = Some A'" for x A'
    proof -
      obtain A where "map_of m x = Some A" and "I A \<subseteq> I A'"
        using s_env.IH l by blast
      then show ?thesis using e by (auto simp: I_Env)
    qed
    ultimately show "e \<in> I (Env m' ob')" by (simp add: I_Env)
  qed
next
  case (s_emeet m1 o1 m2 o2)
  show ?case
  proof
    fix e
    assume "e \<in> I (Inter (Env m1 o1) (Env m2 o2))"
    then have e1: "e \<in> I (Env m1 o1)" and e2: "e \<in> I (Env m2 o2)" by simp_all
    have cf: "CFN e" if "emeet m1 m2 \<noteq> [] \<or> o1 \<or> o2"
      using that e1 e2 by (auto simp: I_Env emeet_def)
    moreover have "Comp (Var x) e \<in> I A" if l: "map_of (emeet m1 m2) x = Some A" for x A
    proof (cases "map_of m1 x")
      case None
      then have "map_of m2 x = Some A" using l by (simp add: map_of_emeet)
      then show ?thesis using e2 by (simp add: I_Env)
    next
      case (Some A1)
      show ?thesis
      proof (cases "map_of m2 x")
        case None
        then have "A = A1" using l Some by (simp add: map_of_emeet)
        then show ?thesis using e1 Some by (simp add: I_Env)
      next
        case (Some A2)
        then have "A = Inter A1 A2" using l \<open>map_of m1 x = Some A1\<close> by (simp add: map_of_emeet)
        then show ?thesis using e1 e2 Some \<open>map_of m1 x = Some A1\<close> by (simp add: I_Env)
      qed
    qed
    ultimately show "e \<in> I (Env (emeet m1 m2) (o1 \<or> o2))" by (simp add: I_Env)
  qed
next
  case s_omenv
  then show ?case by (auto simp: I_Env)
qed auto

subsection \<open>Realizers\<close>

lemma CFN_Nil: "CFN Nil" by (rule CFN_sig_fb[OF FNil])

lemma Nil_I: "Nil \<in> I (Env [] True)"
  by (simp add: I_Env CFN_Nil)

lemma Extn_I:
  assumes n: "N \<in> I A" and e: "e \<in> I (Env m ob)"
  shows "Extn N x e \<in> I (Env ((x, A) # m) ob)"
proof -
  have "Comp (Var y) (Extn N x e) \<in> I B" if l: "map_of ((x, A) # m) y = Some B" for y B
  proof (cases "y = x")
    case True
    then have "B = A" using l by simp
    then show ?thesis using True I_back[OF sig_imp_cbv[OF sig.VarRef] n] by simp
  next
    case False
    then have "map_of m y = Some B" using l by simp
    then have "Comp (Var y) e \<in> I B" using e by (simp add: I_Env)
    moreover have "Comp (Var y) (Extn N x e) \<rightarrow>\<^sub>v Comp (Var y) e"
      using False by (simp add: sig_imp_cbv sig.VarSkip)
    ultimately show ?thesis using I_back by blast
  qed
  then show ?thesis using CFN_Extn by (simp add: I_Env)
qed

subsection \<open>Basic lemma\<close>

lemma basic:
  "\<Gamma> \<turnstile> M : A \<Longrightarrow>
     (case \<Gamma> of CE C \<Rightarrow> (\<forall>e \<in> I C. Comp M e \<in> I A) | CT m \<Rightarrow> M \<in> I A)"
proof (induction rule: hasty.induct)
  case (TVar \<Gamma> m x A)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
    proof (clarsimp simp: CE)
      fix e assume e: "e \<in> I C"
      from TVar.hyps(1) obtain ob where "C \<preceq> Env m ob" using CE by auto
      then have "e \<in> I (Env m ob)" using I_mono e by blast
      then show "Comp (Var x) e \<in> I A" using TVar.hyps(2) by (simp add: I_Env)
    qed
  next
    case (CT m0) then show ?thesis by (simp add: Var_I)
  qed
next
  case (TLam C m ob x A M B)
  have key: "\<forall>e \<in> I C. Comp (Lam x M) e \<in> I (Arr A B)"
  proof
    fix e assume e: "e \<in> I C"
    have em: "e \<in> I (Env m ob)" using I_mono[OF TLam.hyps(1)] e by blast
    have fl: "fb (Comp (Lam x M) e)" by (rule FClo)
    have app: "\<forall>N \<in> I A. CFN N \<longrightarrow> App (Comp (Lam x M) e) N \<in> I B"
    proof (intro ballI impI)
      fix N assume n: "N \<in> I A" and cn: "CFN N"
      from cn obtain F where r: "N \<rightarrow>\<^sub>v\<^sup>* F" and f: "fb F" by (auto simp: CFN_def)
      have nF: "F \<in> I A" by (rule I_fwd_steps[OF r n])
      have "Extn F x e \<in> I (Env ((x, A) # m) ob)" by (rule Extn_I[OF nF em])
      then have "Comp M (Extn F x e) \<in> I B" using TLam.IH by force
      then have "App (Comp (Lam x M) e) F \<in> I B"
        by (rule I_back[OF beta_imp_cbv[OF beta.Beta[OF f]]])
      then show "App (Comp (Lam x M) e) N \<in> I B"
        using I_back_steps[OF cbv_steps_AppR[OF FClo r]] by blast
    qed
    show "Comp (Lam x M) e \<in> I (Arr A B)" using app CFN_Clo by simp
  qed
  then show ?case by simp
next
  case (TCode \<Gamma> x M)
  show ?case
  proof (cases \<Gamma>)
    case (CE C) then show ?thesis by (simp add: CFN_Clo)
  next
    case (CT m) then show ?thesis by (simp add: CFN_Lam)
  qed
next
  case (TNil \<Gamma>)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
      using I_back[OF sig_imp_cbv[OF sig.DNil] Nil_I] by (simp add: CE)
  next
    case (CT m) then show ?thesis using Nil_I by simp
  qed
next
  case (TApp \<Gamma> M A B N)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
    proof (clarsimp simp: CE)
      fix e assume e: "e \<in> I C"
      then have m: "Comp M e \<in> I (Arr A B)" and n: "Comp N e \<in> I A" using TApp.IH CE by auto
      have cn: "CFN (Comp N e)" by (rule I_ess[OF TApp.hyps(3) n])
      from m n cn have "App (Comp M e) (Comp N e) \<in> I B" by simp
      then show "Comp (App M N) e \<in> I B" using I_back[OF sig_imp_cbv[OF sig.DApp]] by blast
    qed
  next
    case (CT m)
    then have m: "M \<in> I (Arr A B)" and n: "N \<in> I A" using TApp.IH by auto
    have cn: "CFN N" by (rule I_ess[OF TApp.hyps(3) n])
    from m n cn show ?thesis using CT by simp
  qed
next
  case (TExtn \<Gamma> M A N m ob x)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
    proof (clarsimp simp: CE)
      fix e assume e: "e \<in> I C"
      then have "Comp M e \<in> I A" "Comp N e \<in> I (Env m ob)" using TExtn.IH CE by auto
      then have "Extn (Comp M e) x (Comp N e) \<in> I (Env ((x, A) # m) ob)" by (rule Extn_I)
      then show "Comp (Extn M x N) e \<in> I (Env ((x, A) # m) ob)"
        using I_back[OF sig_imp_cbv[OF sig.DExtn]] by blast
    qed
  next
    case (CT m0)
    then have "M \<in> I A" "N \<in> I (Env m ob)" using TExtn.IH by auto
    then show ?thesis using CT by (simp add: Extn_I)
  qed
next
  case (TComp \<Gamma> N D M A)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
    proof (clarsimp simp: CE)
      fix e assume e: "e \<in> I C"
      have n: "Comp N e \<in> I D" using TComp.IH(1) e CE by auto
      have "Comp M (Comp N e) \<in> I A" using TComp.IH(2) n by auto
      then show "Comp (Comp M N) e \<in> I A" using I_back[OF sig_imp_cbv[OF sig.Ass]] by blast
    qed
  next
    case (CT m)
    then have n: "N \<in> I D" using TComp.IH(1) by simp
    then show ?thesis using TComp.IH(2) CT by auto
  qed
next
  case (TOm \<Gamma> M)
  show ?case by (cases \<Gamma>) simp_all
next
  case (TInter \<Gamma> M A B)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    then show ?thesis using TInter.IH by simp
  next
    case (CT m)
    then show ?thesis using TInter.IH by simp
  qed
next
  case (TSub \<Gamma> M A B)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
    proof (clarsimp simp: CE)
      fix e assume e: "e \<in> I C"
      have "Comp M e \<in> I A" using TSub.IH e CE by simp
      then show "Comp M e \<in> I B" using I_mono[OF TSub.hyps(2)] by blast
    qed
  next
    case (CT m)
    then have "M \<in> I A" using TSub.IH by simp
    then show ?thesis using CT I_mono[OF TSub.hyps(2)] by auto
  qed
qed

theorem soundness: "Typ M \<Longrightarrow> CFN M"
proof -
  assume "Typ M"
  then obtain m A where t: "CT m \<turnstile> M : A" and e: "ess A" by (auto simp: Typ_def)
  have "M \<in> I A" using basic[OF t] by simp
  then show "CFN M" by (rule I_ess[OF e])
qed

end
