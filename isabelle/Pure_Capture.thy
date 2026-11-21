theory Pure_Capture
  imports Main_Results Lambda
begin

section \<open>Pure \<open>\<lambda>\<close>-terms with \<open>M\<circ>cap xs\<close> versus open call-by-value\<close>

subsection \<open>Pure terms, free variables, readback\<close>

fun pure :: "trm \<Rightarrow> bool" where
  "pure (Var x) = True"
| "pure (Lam x M) = pure M"
| "pure (App M N) = (pure M \<and> pure N)"
| "pure _ = False"

fun fvp :: "trm \<Rightarrow> var set" where
  "fvp (Var x) = {x}"
| "fvp (Lam x M) = fvp M - {x}"
| "fvp (App M N) = fvp M \<union> fvp N"
| "fvp Nil = {}"
| "fvp (Extn M x L) = {}"
| "fvp (Comp M L) = {}"

definition junk :: dB where "junk = DAbs (DVar 0)"

lemma subst_junk [simp]: "junk[s/k] = junk"
  by (simp add: junk_def)

fun rb :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> dB" and rbe :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> (var \<Rightarrow> dB)" where
  "rb (Var x) \<rho> = \<rho> x"
| "rb (Lam x M) \<rho> = DAbs (rb M ((\<lambda>y. lift (\<rho> y) 0)(x := DVar 0)))"
| "rb (App M N) \<rho> = DApp (rb M \<rho>) (rb N \<rho>)"
| "rb (Comp M L) \<rho> = rb M (rbe L \<rho>)"
| "rb Nil \<rho> = junk"
| "rb (Extn M x L) \<rho> = junk"
| "rbe (Var x) \<rho> = \<rho>"
| "rbe (Lam x M) \<rho> = \<rho>"
| "rbe (App M N) \<rho> = \<rho>"
| "rbe (Comp L1 L2) \<rho> = rbe L1 (rbe L2 \<rho>)"
| "rbe Nil \<rho> = (\<lambda>y. junk)"
| "rbe (Extn M x L) \<rho> = (rbe L \<rho>)(x := rb M \<rho>)"

lemma rb_subst:
  "(\<forall>\<sigma> s k. (rb M \<sigma>)[s/k] = rb M (\<lambda>y. (\<sigma> y)[s/k])) \<and>
   (\<forall>\<sigma> s k. rbe M (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe M \<sigma> y)[s/k]))"
proof (induction M)
  case (Var x)
  then show ?case by simp
next
  case (Lam x M)
  have "(rb (Lam x M) \<sigma>)[s/k] = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])" for \<sigma> s k
  proof -
    have fe: "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1])
            = (\<lambda>y. lift ((\<sigma> y)[s/k]) 0)(x := DVar 0)"
      by (rule ext) (simp add: lift_subst_lt)
    have "(rb (Lam x M) \<sigma>)[s/k]
        = DAbs ((rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[lift s 0 / k + 1])"
      by simp
    also have "\<dots> = DAbs (rb M (\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1]))"
      using Lam.IH by simp
    also have "\<dots> = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])"
      by (simp only: fe rb.simps)
    finally show ?thesis .
  qed
  then show ?case by simp
next
  case (App M N)
  then show ?case by simp
next
  case Nil
  then show ?case by (auto intro!: ext)
next
  case (Extn M x L)
  have "rbe (Extn M x L) (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe (Extn M x L) \<sigma> y)[s/k])" for \<sigma> s k
    using Extn.IH by (auto intro!: ext)
  then show ?case by simp
next
  case (Comp M L)
  then show ?case by simp
qed

lemma beta_rb:
  "(rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[t/0] = rb M (\<sigma>(x := t))"
proof -
  have "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[t/0]) = \<sigma>(x := t)"
    by (rule ext) simp
  then show ?thesis
    using rb_subst[of M] by simp
qed

lemma rb_fv:
  "pure M \<Longrightarrow> (\<forall>y \<in> fvp M. \<rho> y = \<rho>' y) \<Longrightarrow> rb M \<rho> = rb M \<rho>'"
proof (induction M arbitrary: \<rho> \<rho>')
  case (Var x) then show ?case by simp
next
  case (Lam x M)
  have "\<forall>y \<in> fvp M. ((\<lambda>y. lift (\<rho> y) 0)(x := DVar 0)) y = ((\<lambda>y. lift (\<rho>' y) 0)(x := DVar 0)) y"
  proof
    fix y assume y: "y \<in> fvp M"
    show "((\<lambda>y. lift (\<rho> y) 0)(x := DVar 0)) y = ((\<lambda>y. lift (\<rho>' y) 0)(x := DVar 0)) y"
    proof (cases "y = x")
      case True then show ?thesis by simp
    next
      case False
      then have "y \<in> fvp (Lam x M)" using y by simp
      then show ?thesis using Lam.prems False by simp
    qed
  qed
  then show ?case using Lam.IH Lam.prems by simp
next
  case (App M N) then show ?case by auto
qed simp_all

subsection \<open>Evaluation results\<close>

fun lookup :: "trm \<Rightarrow> var \<Rightarrow> trm option" where
  "lookup (Extn S x E) y = (if x = y then Some S else lookup E y)"
| "lookup _ y = None"

fun edom :: "trm \<Rightarrow> var set" where
  "edom (Extn S x E) = insert x (edom E)"
| "edom _ = {}"

inductive inS :: "trm \<Rightarrow> bool" and inE :: "trm \<Rightarrow> bool" where
  SVar: "inS (Var x)"
| SApp: "inS S1 \<Longrightarrow> inS S2 \<Longrightarrow> inS (App S1 S2)"
| SClo: "pure (Lam x P) \<Longrightarrow> inE E \<Longrightarrow> fvp (Lam x P) \<subseteq> edom E \<Longrightarrow> inS (Comp (Lam x P) E)"
| ENil: "inE Nil"
| EExt: "inS S \<Longrightarrow> inE E \<Longrightarrow> inE (Extn S x E)"

lemma inE_Extn: "inE (Extn S x E) \<Longrightarrow> inS S \<and> inE E"
  by (auto elim: inE.cases)

lemma inS_clo:
  assumes "inS S1" "fb S1" "\<not> inert S1"
  obtains x P E where "S1 = Comp (Lam x P) E" "pure (Lam x P)" "inE E" "fvp (Lam x P) \<subseteq> edom E"
  using assms(2,1,3)
proof (cases rule: fb_cases)
  case inert then show ?thesis using assms by simp
next
  case (lam x B) then show ?thesis using assms by (auto elim: inS.cases)
next
  case (clo x B L)
  from assms(1)[unfolded clo(1)] have "inE L \<and> pure (Lam x B) \<and> fvp (Lam x B) \<subseteq> edom L"
    by (auto elim: inS.cases simp del: fvp.simps)
  then show ?thesis using clo that by blast
next
  case nil then show ?thesis using assms by (auto elim: inS.cases)
next
  case (extn N x L) then show ?thesis using assms by (auto elim: inS.cases)
qed

lemma pure_sig_normal: "pure M \<Longrightarrow> sig_normal M"
proof (induction M)
  case (Lam x M)
  show ?case
  proof (rule normalI)
    fix N show "\<not> Lam x M \<rightarrow>\<^sub>\<sigma> N"
    proof
      assume "Lam x M \<rightarrow>\<^sub>\<sigma> N"
      then show False using Lam by (auto elim: sig.cases simp: normal_def)
    qed
  qed
next
  case (App M N)
  show ?case
  proof (rule normalI)
    fix P show "\<not> App M N \<rightarrow>\<^sub>\<sigma> P"
    proof
      assume "App M N \<rightarrow>\<^sub>\<sigma> P"
      then show False using App by (auto elim: sig.cases simp: normal_def)
    qed
  qed
qed (auto simp: normal_def elim: sig.cases)

lemma normal_App: "sig_normal a \<Longrightarrow> sig_normal b \<Longrightarrow> sig_normal (App a b)"
  by (auto simp: normal_def elim: sig.cases)

lemma inS_inE_normal:
  shows "inS S \<Longrightarrow> sig_normal S" and "inE E \<Longrightarrow> sig_normal E"
proof (induction rule: inS_inE.inducts)
  case (SVar x) then show ?case by (simp add: normal_def)
next
  case (SApp S1 S2) show ?case using SApp(3,4) by (rule normal_App)
next
  case (SClo x P E)
  show ?case
  proof (rule normalI)
    fix N show "\<not> Comp (Lam x P) E \<rightarrow>\<^sub>\<sigma> N"
    proof
      assume s: "Comp (Lam x P) E \<rightarrow>\<^sub>\<sigma> N"
      show False
      using s proof (cases rule: sig.cases)
        case (CompL M')
        then show ?thesis using pure_sig_normal[OF SClo(1)] by (auto simp: normal_def)
      next
        case (CompR M')
        then show ?thesis using SClo(4) by (auto simp: normal_def)
      qed
    qed
  qed
next
  case ENil then show ?case by (simp add: normal_def)
next
  case (EExt S E x)
  show ?case
  proof (rule normalI)
    fix N show "\<not> Extn S x E \<rightarrow>\<^sub>\<sigma> N"
    proof
      assume s: "Extn S x E \<rightarrow>\<^sub>\<sigma> N"
      show False
      using s proof (cases rule: sig.cases)
        case (ExtnL M') then show ?thesis using EExt(3) by (auto simp: normal_def)
      next
        case (ExtnR M') then show ?thesis using EExt(4) by (auto simp: normal_def)
      qed
    qed
  qed
qed

subsection \<open>Evaluation\<close>

fun eval :: "trm \<Rightarrow> trm \<Rightarrow> trm" where
  "eval (Var y) E = the (lookup E y)"
| "eval (App P Q) E = App (eval P E) (eval Q E)"
| "eval (Lam x P) E = Comp (Lam x P) E"
| "eval _ E = Nil"

lemma sig_steps_AppL: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> sig\<^sup>*\<^sup>* (App M N) (App M' N)"
  by (rule sig_steps_lift[of "\<lambda>P. App P N"]) (auto intro: sig.AppL)

lemma sig_steps_AppR: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> sig\<^sup>*\<^sup>* (App L M) (App L M')"
  by (rule sig_steps_lift[of "\<lambda>P. App L P"]) (auto intro: sig.AppR)

lemma var_lookup:
  "inE E \<Longrightarrow> y \<in> edom E \<Longrightarrow>
     \<exists>S. lookup E y = Some S \<and> inS S \<and> sig\<^sup>*\<^sup>* (Comp (Var y) E) S"
proof (induction E)
  case (Extn S0 x E1)
  from inE_Extn[OF Extn.prems(1)] have s0: "inS S0" and e1: "inE E1" by blast+
  show ?case
  proof (cases "x = y")
    case True
    then show ?thesis using s0 sig.VarRef[of y S0 E1] by auto
  next
    case False
    then have "y \<in> edom E1" using Extn.prems(2) by simp
    from Extn.IH(2)[OF e1 this] obtain S where
      S: "lookup E1 y = Some S" "inS S" "sig\<^sup>*\<^sup>* (Comp (Var y) E1) S" by blast
    have "sig (Comp (Var y) (Extn S0 x E1)) (Comp (Var y) E1)" using sig.VarSkip[OF False] .
    then have "sig\<^sup>*\<^sup>* (Comp (Var y) (Extn S0 x E1)) S"
      using S(3) by (meson converse_rtranclp_into_rtranclp)
    then show ?thesis using False S by auto
  qed
qed (auto elim: inE.cases)

lemma eval_ok:
  "pure P \<Longrightarrow> fvp P \<subseteq> edom E \<Longrightarrow> inE E \<Longrightarrow>
     inS (eval P E) \<and> sig\<^sup>*\<^sup>* (Comp P E) (eval P E)"
proof (induction P arbitrary: E)
  case (Var y)
  then have "y \<in> edom E" by simp
  from var_lookup[OF Var.prems(3) this] show ?case by auto
next
  case (Lam x P)
  have pp: "pure (Lam x P)" using Lam.prems(1) by simp
  have "inS (Comp (Lam x P) E)"
    by (rule SClo[OF pp Lam.prems(3) Lam.prems(2)])
  then show ?case by simp
next
  case (App P1 P2)
  from App.prems have p: "pure P1" "pure P2" and f: "fvp P1 \<subseteq> edom E" "fvp P2 \<subseteq> edom E"
    by auto
  from App.IH(1)[OF p(1) f(1) App.prems(3)] App.IH(2)[OF p(2) f(2) App.prems(3)]
  have i1: "inS (eval P1 E)" and r1: "sig\<^sup>*\<^sup>* (Comp P1 E) (eval P1 E)"
    and i2: "inS (eval P2 E)" and r2: "sig\<^sup>*\<^sup>* (Comp P2 E) (eval P2 E)" by blast+
  have "sig\<^sup>*\<^sup>* (Comp (App P1 P2) E) (App (Comp P1 E) (Comp P2 E))"
    using sig.DApp by blast
  also have "sig\<^sup>*\<^sup>* (App (Comp P1 E) (Comp P2 E)) (App (eval P1 E) (Comp P2 E))"
    using sig_steps_AppL[OF r1] .
  also have "sig\<^sup>*\<^sup>* (App (eval P1 E) (Comp P2 E)) (App (eval P1 E) (eval P2 E))"
    using sig_steps_AppR[OF r2] .
  finally show ?case using i1 i2 by (auto intro: SApp)
qed simp_all

lemma snf_eval:
  assumes "pure P" "fvp P \<subseteq> edom E" "inE E"
  shows "snf (Comp P E) = eval P E"
  using eval_ok[OF assms] inS_inE_normal(1) snf_unique by blast

lemma rbe_lookup:
  "inE E \<Longrightarrow> lookup E y = Some S \<Longrightarrow> rbe E \<rho> y = rb S \<rho>"
proof (induction E)
  case (Extn S0 x E1)
  then show ?case using inE_Extn by (cases "x = y") auto
qed auto

lemma rb_eval:
  "pure P \<Longrightarrow> fvp P \<subseteq> edom E \<Longrightarrow> inE E \<Longrightarrow> rb (Comp P E) \<rho> = rb (eval P E) \<rho>"
proof (induction P arbitrary: E)
  case (Var y)
  then have "y \<in> edom E" by simp
  from var_lookup[OF Var.prems(3) this] obtain S where
    S: "lookup E y = Some S" by blast
  then show ?case using rbe_lookup[OF Var.prems(3) S] by simp
next
  case (Lam x P) then show ?case by simp
next
  case (App P1 P2)
  then show ?case by simp
qed simp_all

lemma rb_fb:
  shows "inS S \<Longrightarrow> (inert S \<longrightarrow> dinert (rb S DVar)) \<and> (fb S \<longrightarrow> dfb (rb S DVar))"
    and "inE E \<Longrightarrow> True"
proof (induction rule: inS_inE.inducts)
  case (SVar x) then show ?case by (auto intro: dinert_dfb.intros)
next
  case (SApp S1 S2)
  then show ?case
    by (auto simp: inert_App_iff fb_App_iff dinert_DApp_iff intro: dinert_dfb.intros)
next
  case (SClo x P E)
  then show ?case by (auto simp: dinert_dfb.intros)
qed simp_all

subsection \<open>Head steps\<close>

lemma snf_AppL: "sig_normal S2 \<Longrightarrow> snf (App A S2) = App (snf A) S2"
proof -
  assume n: "sig_normal S2"
  have "sig\<^sup>*\<^sup>* (App A S2) (App (snf A) S2)" using sig_steps_AppL[OF snf_spec[THEN conjunct1]] .
  moreover have "sig_normal (App (snf A) S2)" using normal_App snf_spec n by blast
  ultimately show ?thesis using snf_unique by blast
qed

lemma snf_AppR: "sig_normal L \<Longrightarrow> snf (App L A) = App L (snf A)"
proof -
  assume n: "sig_normal L"
  have "sig\<^sup>*\<^sup>* (App L A) (App L (snf A))" using sig_steps_AppR[OF snf_spec[THEN conjunct1]] .
  moreover have "sig_normal (App L (snf A))" using normal_App snf_spec n by blast
  ultimately show ?thesis using snf_unique by blast
qed

lemma head_step:
  shows "inS S \<Longrightarrow> fb S \<or> (\<exists>S'. S \<rightarrow>\<^sub>\<beta> S' \<and> inS (snf S') \<and> rb S DVar \<rightarrow>\<^sub>f rb (snf S') DVar)"
    and "inE E \<Longrightarrow> True"
proof (induction rule: inS_inE.inducts)
  case (SVar x) then show ?case by simp
next
  case (SClo x P E) then show ?case by (simp add: FClo)
next
  case (SApp S1 S2)
  note n1 = inS_inE_normal(1)[OF SApp(1)] and n2 = inS_inE_normal(1)[OF SApp(2)]
  show ?case
  proof (cases "fb S1")
    case False
    with SApp(3) obtain S1' where
      b: "S1 \<rightarrow>\<^sub>\<beta> S1'" and i: "inS (snf S1')" and r: "rb S1 DVar \<rightarrow>\<^sub>f rb (snf S1') DVar"
      by blast
    have "App S1 S2 \<rightarrow>\<^sub>\<beta> App S1' S2" using b by (rule beta.AppL)
    moreover have "snf (App S1' S2) = App (snf S1') S2" using snf_AppL[OF n2] .
    moreover have "inS (App (snf S1') S2)" using i SApp(2) by (rule inS_inE.SApp)
    moreover have "rb (App S1 S2) DVar \<rightarrow>\<^sub>f rb (App (snf S1') S2) DVar"
      using r by (simp add: vappL)
    ultimately show ?thesis by (auto simp: snf_AppL[OF n2])
  next
    case f1: True
    show ?thesis
    proof (cases "fb S2")
      case False
      with SApp(4) obtain S2' where
        b: "S2 \<rightarrow>\<^sub>\<beta> S2'" and i: "inS (snf S2')" and r: "rb S2 DVar \<rightarrow>\<^sub>f rb (snf S2') DVar"
        by blast
      have ba: "App S1 S2 \<rightarrow>\<^sub>\<beta> App S1 S2'" using f1 b by (rule beta.AppR)
      have sa: "snf (App S1 S2') = App S1 (snf S2')" using snf_AppR[OF n1] .
      have ia: "inS (App S1 (snf S2'))" using SApp(1) i by (rule inS_inE.SApp)
      have "dfb (rb S1 DVar)" using rb_fb(1)[OF SApp(1)] f1 by blast
      then have "rb (App S1 S2) DVar \<rightarrow>\<^sub>f rb (App S1 (snf S2')) DVar"
        using r by (simp add: vappR)
      then show ?thesis using ba sa ia by auto
    next
      case f2: True
      show ?thesis
      proof (cases "inert S1")
        case True
        then show ?thesis using f2 by (simp add: fb_App_iff)
      next
        case False
        from inS_clo[OF SApp(1) f1 False] obtain x P E where
          S1: "S1 = Comp (Lam x P) E" and pp: "pure (Lam x P)" and ie: "inE E"
          and fv: "fvp (Lam x P) \<subseteq> edom E" by blast
        let ?E' = "Extn S2 x E"
        have pP: "pure P" using pp by simp
        have ie': "inE ?E'" using SApp(2) ie by (rule EExt)
        have fv': "fvp P \<subseteq> edom ?E'" using fv by auto
        have b: "App S1 S2 \<rightarrow>\<^sub>\<beta> Comp P ?E'" using S1 f2 by (simp add: beta.Beta)
        have sn: "snf (Comp P ?E') = eval P ?E'" using snf_eval[OF pP fv' ie'] .
        have isv: "inS (eval P ?E')" using eval_ok[OF pP fv' ie'] by blast
        have f: "dfb (rb S2 DVar)" using rb_fb(1)[OF SApp(2)] f2 by blast
        have step: "DApp (DAbs (rb P ((\<lambda>y. lift (rbe E DVar y) 0)(x := DVar 0)))) (rb S2 DVar)
              \<rightarrow>\<^sub>f (rb P ((\<lambda>y. lift (rbe E DVar y) 0)(x := DVar 0)))[rb S2 DVar/0]"
          by (rule vbeta[OF f])
        have "(rb P ((\<lambda>y. lift (rbe E DVar y) 0)(x := DVar 0)))[rb S2 DVar/0]
              = rb (eval P ?E') DVar"
          using beta_rb[of P "rbe E DVar" x "rb S2 DVar"] rb_eval[OF pP fv' ie', of DVar]
          by simp
        then have "rb (App S1 S2) DVar \<rightarrow>\<^sub>f rb (eval P ?E') DVar"
          using step S1 by simp
        then show ?thesis using b sn isv by auto
      qed
    qed
  qed
qed simp_all

lemma cd_imp_lam_VN: "cd S k N \<Longrightarrow> inS S \<Longrightarrow> lam_VN (rb S DVar)"
proof (induction k arbitrary: S)
  case 0
  have nb: "normal beta (snf S)" using 0(1) by (cases rule: cd.cases) auto
  have sn': "snf S = S" using snf_unique[OF rtranclp.rtrancl_refl inS_inE_normal(1)[OF 0(2)]] .
  from head_step(1)[OF 0(2)] show ?case
  proof
    assume "fb S"
    then have "dfb (rb S DVar)" using rb_fb(1)[OF 0(2)] by blast
    then have "normal vred (rb S DVar)" using dfb_normal by blast
    then show ?thesis by (auto simp: lam_VN_def)
  next
    assume "\<exists>S'. S \<rightarrow>\<^sub>\<beta> S' \<and> inS (snf S') \<and> rb S DVar \<rightarrow>\<^sub>f rb (snf S') DVar"
    then show ?thesis using nb sn' by (auto simp: normal_def)
  qed
next
  case (Suc m)
  have sn': "snf S = S" using snf_unique[OF rtranclp.rtrancl_refl inS_inE_normal(1)[OF Suc(3)]] .
  from Suc(2) obtain N1 where b1: "snf S \<rightarrow>\<^sub>\<beta> N1" and c1: "cd N1 m N"
    by (auto elim: cd.cases)
  from head_step(1)[OF Suc(3)] show ?case
  proof
    assume "fb S"
    then show ?thesis using b1 sn' fb_no_beta by auto
  next
    assume "\<exists>S'. S \<rightarrow>\<^sub>\<beta> S' \<and> inS (snf S') \<and> rb S DVar \<rightarrow>\<^sub>f rb (snf S') DVar"
    then obtain S' where b: "S \<rightarrow>\<^sub>\<beta> S'" and i: "inS (snf S')"
      and r: "rb S DVar \<rightarrow>\<^sub>f rb (snf S') DVar" by blast
    have "S' = N1" using beta_det b b1 sn' by simp
    moreover have "snf (snf S') = snf S'"
      using snf_unique[OF rtranclp.rtrancl_refl inS_inE_normal(1)[OF i]] .
    ultimately have "cd (snf S') m N" using cd_snf[OF c1] by simp
    from Suc.IH[OF this i] have "lam_VN (rb (snf S') DVar)" .
    then show ?thesis using r by (auto simp: lam_VN_def intro: converse_rtranclp_into_rtranclp)
  qed
qed

lemma CFN_imp_lam_VN_S: "inS S \<Longrightarrow> CFN S \<Longrightarrow> lam_VN (rb S DVar)"
  using steps_cd cd_imp_lam_VN by (fastforce simp: CFN_def)

lemma vdist_imp_CFN_S: "vdist (rb S DVar) n \<Longrightarrow> inS S \<Longrightarrow> CFN S"
proof (induction n arbitrary: S)
  case 0
  show ?case
  proof (cases "fb S")
    case True
    then show ?thesis using fb_NF inS_inE_normal(1)[OF 0(2)] by (auto simp: CFN_def)
  next
    case False
    from head_step(1)[OF 0(2)] False obtain S' where "rb S DVar \<rightarrow>\<^sub>f rb (snf S') DVar" by blast
    then show ?thesis using 0(1) vdist_step by blast
  qed
next
  case (Suc n)
  show ?case
  proof (cases "fb S")
    case True
    then show ?thesis using fb_NF inS_inE_normal(1)[OF Suc(3)] by (auto simp: CFN_def)
  next
    case False
    from head_step(1)[OF Suc(3)] False obtain S' where
      b: "S \<rightarrow>\<^sub>\<beta> S'" and i: "inS (snf S')" and r: "rb S DVar \<rightarrow>\<^sub>f rb (snf S') DVar" by blast
    from vdist_step[OF Suc(2) r] have "vdist (rb (snf S') DVar) n" by simp
    then have "CFN (snf S')" using Suc.IH i by blast
    then have "CFN S'" using CFN_back_steps sig_steps_cbv snf_spec by blast
    then show ?thesis using CFN_back beta_imp_cbv b by blast
  qed
qed

lemma lam_VN_imp_CFN_S: "lam_VN (rb S DVar) \<Longrightarrow> inS S \<Longrightarrow> CFN S"
  using lam_VN_vdist vdist_imp_CFN_S by blast

subsection \<open>The main theorem\<close>

lemma cap_inE: "inE (cap xs)"
  by (induction xs) (auto simp: cap_def intro: ENil EExt SVar)

lemma cap_edom: "edom (cap xs) = set xs"
  by (induction xs) (auto simp: cap_def)

lemma cap_lookup: "y \<in> set xs \<Longrightarrow> lookup (cap xs) y = Some (Var y)"
proof (induction xs)
  case (Cons z zs) then show ?case by (cases "z = y") (auto simp: cap_def)
qed simp

theorem pure_cap_characterization:
  assumes "pure M" "fvp M \<subseteq> set xs"
  shows "lam_VN (rb M DVar) \<longleftrightarrow> CFN (Comp M (cap xs))"
    and "CFN (Comp M (cap xs)) \<longleftrightarrow> CFSN (Comp M (cap xs))"
    and "CFSN (Comp M (cap xs)) \<longleftrightarrow> Typ (Comp M (cap xs))"
proof -
  let ?E = "cap xs"
  have fv: "fvp M \<subseteq> edom ?E" using assms(2) cap_edom by simp
  note ok = eval_ok[OF assms(1) fv cap_inE]
  let ?S = "eval M ?E"
  have rbeq: "rb (Comp M ?E) DVar = rb M DVar"
  proof -
    have "rb (Comp M ?E) DVar = rb M (rbe ?E DVar)" by simp
    also have "\<dots> = rb M DVar"
    proof (rule rb_fv[OF assms(1)])
      show "\<forall>y\<in>fvp M. rbe ?E DVar y = DVar y"
      proof
        fix y assume "y \<in> fvp M"
        then have "y \<in> set xs" using assms(2) by blast
        then show "rbe ?E DVar y = DVar y"
          using rbe_lookup[OF cap_inE cap_lookup] by simp
      qed
    qed
    finally show ?thesis .
  qed
  have cfn: "CFN (Comp M ?E) \<longleftrightarrow> CFN ?S"
    using ok CFN_back_steps CFN_fwd_steps sig_steps_cbv by blast
  have "lam_VN (rb M DVar) \<longleftrightarrow> lam_VN (rb (Comp M ?E) DVar)" using rbeq by simp
  also have "\<dots> \<longleftrightarrow> lam_VN (rb ?S DVar)"
    using rb_eval[OF assms(1) fv cap_inE] by simp
  also have "\<dots> \<longleftrightarrow> CFN ?S"
    using CFN_imp_lam_VN_S lam_VN_imp_CFN_S ok by blast
  finally show "lam_VN (rb M DVar) \<longleftrightarrow> CFN (Comp M ?E)" using cfn by simp
  show "CFN (Comp M ?E) \<longleftrightarrow> CFSN (Comp M ?E)" by (rule CFN_iff_CFSN)
  show "CFSN (Comp M ?E) \<longleftrightarrow> Typ (Comp M ?E)"
    using main_characterization_SN by simp
qed

theorem pure_cap_main:
  assumes "pure M" "fvp M \<subseteq> set xs"
  shows "lam_VN (rb M DVar) \<longleftrightarrow> CFN (Comp M (cap xs))"
    and "lam_VN (rb M DVar) \<longleftrightarrow> CFSN (Comp M (cap xs))"
    and "lam_VN (rb M DVar) \<longleftrightarrow> Typ (Comp M (cap xs))"
  using pure_cap_characterization[OF assms] by blast+

subsection \<open>Necessity of the free-variable condition\<close>

lemma Var_cap_Nil_NF: "NF (Comp (Var y) (cap []))"
proof (rule normalI)
  fix N
  show "\<not> Comp (Var y) (cap []) \<rightarrow>\<^sub>v N"
    by (auto simp: cap_def cbv_def elim: sig.cases beta.cases)
qed

lemma Var_cap_Nil_not_fb: "\<not> fb (Comp (Var y) (cap []))"
  by (auto simp: cap_def elim: fb.cases inert.cases)

theorem fv_condition_necessary:
  "pure (Var y)" "\<not> fvp (Var y) \<subseteq> set []"
  "lam_VN (rb (Var y) DVar)"
  "\<not> CFN (Comp (Var y) (cap []))"
  "\<not> CFSN (Comp (Var y) (cap []))"
  "\<not> Typ (Comp (Var y) (cap []))"
proof -
  show "pure (Var y)" "\<not> fvp (Var y) \<subseteq> set []" by simp_all
  have "normal vred (DVar y)" by (auto simp: normal_def elim: vred.cases)
  then show "lam_VN (rb (Var y) DVar)" by (auto simp: lam_VN_def)
  show c: "\<not> CFN (Comp (Var y) (cap []))"
  proof
    assume "CFN (Comp (Var y) (cap []))"
    then obtain N where "Comp (Var y) (cap []) \<rightarrow>\<^sub>v\<^sup>* N" "fb N" by (auto simp: CFN_def)
    then show False
      using normal_rtranclp[OF Var_cap_Nil_NF] Var_cap_Nil_not_fb by blast
  qed
  show "\<not> CFSN (Comp (Var y) (cap []))" using c CFN_iff_CFSN by blast
  show "\<not> Typ (Comp (Var y) (cap []))" using c main_characterization by blast
qed

end
