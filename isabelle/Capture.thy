theory Capture
  imports Main_Results
begin

section \<open>Capture environments (CBV version)\<close>

text \<open>
  \<open>cap xs\<close> is \<open>(x\<^sub>1/x\<^sub>1)\<cdot>(\<dots>\<cdot>((x\<^sub>n/x\<^sub>n)\<cdot>()))\<close>.  \<open>capE xs E\<close> is the same with
  components \<open>x\<^sub>i\<circ>E\<close> (the result of pushing \<open>E\<close> through \<open>cap xs\<close>).
  A composition \<open>M\<circ>N\<close> is \<open>Comp M N\<close>.  Types of paper \<open>\<Gamma> \<turnstile> x\<^sub>i : B\<^sub>i\<close> are
  \<open>\<Gamma> \<turnstile> Var x\<^sub>i : B\<^sub>i\<close>, given as \<open>list_all2\<close> over the lists \<open>xs\<close> and \<open>Bs\<close>.
\<close>

definition capE :: "var list \<Rightarrow> trm \<Rightarrow> trm" where
  "capE xs E = foldr (\<lambda>x e. Extn (Comp (Var x) E) x e) xs Nil"

lemma cap_Nil [simp]: "cap [] = Nil" by (simp add: cap_def)
lemma cap_Cons [simp]: "cap (x # xs) = Extn (Var x) x (cap xs)" by (simp add: cap_def)
lemma capE_Nil [simp]: "capE [] E = Nil" by (simp add: capE_def)
lemma capE_Cons [simp]: "capE (x # xs) E = Extn (Comp (Var x) E) x (capE xs E)"
  by (simp add: capE_def)

lemma list_all2_cong_set:
  "(\<forall>x\<in>set xs. \<forall>B. P x B = Q x B) \<Longrightarrow> list_all2 P xs Bs = list_all2 Q xs Bs"
proof (induction xs arbitrary: Bs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases Bs) auto
qed

subsection \<open>Omega and divergence\<close>

definition dw :: trm where "dw = Lam 0 (App (Var 0) (Var 0))"

text \<open>
  \<open>\<Omega>\<close> must be built from closures: the bare \<open>(\<lambda>x.xx)(\<lambda>x.xx)\<close> is a normal clash.
\<close>

definition Omega :: trm where "Omega = App (Comp dw Nil) (Comp dw Nil)"

lemma cd_fwd_sig_steps: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> cd M n E \<Longrightarrow> cd M' n E"
  by (induction rule: rtranclp_induct) (auto intro: cd_fwd_sig)

lemma loop_not_CFN:
  assumes b: "M \<rightarrow>\<^sub>\<beta> M1" and s: "sig\<^sup>*\<^sup>* M1 M"
  shows "\<not> CFN M"
proof
  assume "CFN M"
  then obtain N where r: "M \<rightarrow>\<^sub>v\<^sup>* N" and n: "NF N" by (auto simp: CFN_def)
  from steps_cd[OF r n] obtain k where c: "cd M k N" by blast
  from cd_fwd_beta[OF b c] obtain j where k: "k = Suc j" and c1: "cd M1 j N" by blast
  have c2: "cd M j N" by (rule cd_fwd_sig_steps[OF s c1])
  have "Suc j = j" using cd_det[OF c[unfolded k] c2] by (rule conjunct1)
  then show False by simp
qed

lemma Omega_loop:
  "Omega \<rightarrow>\<^sub>\<beta> Comp (App (Var 0) (Var 0)) (Extn (Comp dw Nil) 0 Nil)"
  "sig\<^sup>*\<^sup>* (Comp (App (Var 0) (Var 0)) (Extn (Comp dw Nil) 0 Nil)) Omega"
proof -
  let ?e = "Extn (Comp dw Nil) 0 Nil"
  have e: "Omega = App (Comp (Lam 0 (App (Var 0) (Var 0))) Nil) (Comp dw Nil)"
    by (simp add: Omega_def dw_def)
  show "Omega \<rightarrow>\<^sub>\<beta> Comp (App (Var 0) (Var 0)) ?e"
    unfolding e by (rule Beta) (simp add: dw_def FClo)
  have 1: "Comp (App (Var 0) (Var 0)) ?e \<rightarrow>\<^sub>\<sigma> App (Comp (Var 0) ?e) (Comp (Var 0) ?e)"
    by (rule sig.DApp)
  have 2: "App (Comp (Var 0) ?e) (Comp (Var 0) ?e) \<rightarrow>\<^sub>\<sigma> App (Comp dw Nil) (Comp (Var 0) ?e)"
    by (rule sig.AppL[OF sig.VarRef])
  have 3: "App (Comp dw Nil) (Comp (Var 0) ?e) \<rightarrow>\<^sub>\<sigma> App (Comp dw Nil) (Comp dw Nil)"
    by (rule sig.AppR[OF sig.VarRef])
  show "sig\<^sup>*\<^sup>* (Comp (App (Var 0) (Var 0)) ?e) Omega"
    unfolding Omega_def using 1 2 3
    by (meson converse_rtranclp_into_rtranclp rtranclp.rtrancl_refl)
qed

theorem Omega_not_Typ: "\<not> Typ Omega"
  using loop_not_CFN[OF Omega_loop] main_characterization by blast

lemma Omega_Om: "\<Gamma> \<turnstile> Omega : Om" by (rule TOm)

subsection \<open>Proposition 9.1: typing of cap\<close>

theorem cap_typing:
  "list_all2 (\<lambda>x B. \<Gamma> \<turnstile> Var x : B) xs Bs \<Longrightarrow> \<Gamma> \<turnstile> cap xs : Env (zip xs Bs) True"
proof (induction xs arbitrary: Bs)
  case Nil
  then show ?case by (simp add: TNil)
next
  case (Cons x xs)
  then obtain B Bs' where bs: "Bs = B # Bs'" and h: "\<Gamma> \<turnstile> Var x : B"
    and t: "list_all2 (\<lambda>x B. \<Gamma> \<turnstile> Var x : B) xs Bs'" by (cases Bs) auto
  have "\<Gamma> \<turnstile> Extn (Var x) x (cap xs) : Env ((x, B) # zip xs Bs') True"
    by (rule TExtn[OF h Cons.IH[OF t]])
  then show ?case by (simp add: bs)
qed

theorem cap_typing_provides:
  "provides \<Gamma> m \<Longrightarrow> \<forall>x\<in>set xs. map_of m x \<noteq> None \<Longrightarrow>
     \<Gamma> \<turnstile> cap xs : Env (map (\<lambda>x. (x, the (map_of m x))) xs) True"
proof (induction xs)
  case Nil
  then show ?case by (simp add: TNil)
next
  case (Cons x xs)
  then obtain A where a: "map_of m x = Some A" by auto
  have h: "\<Gamma> \<turnstile> Var x : A" by (rule TVar[OF Cons.prems(1) a])
  have "\<Gamma> \<turnstile> Extn (Var x) x (cap xs) :
           Env ((x, A) # map (\<lambda>x. (x, the (map_of m x))) xs) True"
    by (rule TExtn[OF h Cons.IH[OF Cons.prems(1)]]) (use Cons.prems(2) in auto)
  then show ?case by (simp add: a)
qed

subsection \<open>Proposition 9.2: reduction of capture environments\<close>

lemma cap_hit: "y \<in> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Var y)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "y = x")
    case True
    then show ?thesis by (simp add: sig.VarRef r_into_rtranclp)
  next
    case False
    then have "y \<in> set xs" using Cons.prems by simp
    from Cons.IH[OF this] have r: "sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Var y)" .
    have s: "Comp (Var y) (cap (x # xs)) \<rightarrow>\<^sub>\<sigma> Comp (Var y) (cap xs)"
      using False by (simp add: sig.VarSkip)
    show ?thesis using s r by (rule converse_rtranclp_into_rtranclp)
  qed
qed

lemma cap_miss: "y \<notin> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Comp (Var y) Nil)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have ne: "y \<noteq> x" and nm: "y \<notin> set xs" by auto
  have s: "Comp (Var y) (cap (x # xs)) \<rightarrow>\<^sub>\<sigma> Comp (Var y) (cap xs)"
    using ne by (simp add: sig.VarSkip)
  show ?case using s Cons.IH[OF nm] by (rule converse_rtranclp_into_rtranclp)
qed

lemma capE_hit: "y \<in> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (capE xs E)) (Comp (Var y) E)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "y = x")
    case True
    then show ?thesis by (simp add: sig.VarRef r_into_rtranclp)
  next
    case False
    then have "y \<in> set xs" using Cons.prems by simp
    from Cons.IH[OF this] have r: "sig\<^sup>*\<^sup>* (Comp (Var y) (capE xs E)) (Comp (Var y) E)" .
    have s: "Comp (Var y) (capE (x # xs) E) \<rightarrow>\<^sub>\<sigma> Comp (Var y) (capE xs E)"
      using False by (simp add: sig.VarSkip)
    show ?thesis using s r by (rule converse_rtranclp_into_rtranclp)
  qed
qed

lemma capE_miss: "y \<notin> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (capE xs E)) (Comp (Var y) Nil)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have ne: "y \<noteq> x" and nm: "y \<notin> set xs" by auto
  have s: "Comp (Var y) (capE (x # xs) E) \<rightarrow>\<^sub>\<sigma> Comp (Var y) (capE xs E)"
    using ne by (simp add: sig.VarSkip)
  show ?case using s Cons.IH[OF nm] by (rule converse_rtranclp_into_rtranclp)
qed

theorem cap_sigma: "sig\<^sup>*\<^sup>* (Comp (cap xs) E) (capE xs E)"
proof (induction xs)
  case Nil
  then show ?case by (simp add: sig.DNil r_into_rtranclp)
next
  case (Cons x xs)
  have s: "Comp (cap (x # xs)) E \<rightarrow>\<^sub>\<sigma> Extn (Comp (Var x) E) x (Comp (cap xs) E)"
    by (simp add: sig.DExtn)
  have r: "sig\<^sup>*\<^sup>* (Extn (Comp (Var x) E) x (Comp (cap xs) E)) (Extn (Comp (Var x) E) x (capE xs E))"
    by (rule sig_steps_lift[OF sig.ExtnR Cons.IH])
  show ?case using s r by (simp add: converse_rtranclp_into_rtranclp)
qed

theorem cap_sigma_lookup:
  "y \<in> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Var y)"
  "y \<in> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (Comp (cap xs) E)) (Comp (Var y) E)"
  "y \<notin> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Comp (Var y) Nil)"
  "y \<notin> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (Comp (cap xs) E)) (Comp (Var y) Nil)"
proof -
  assume h: "y \<in> set xs"
  show "sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Var y)" by (rule cap_hit[OF h])
  have "sig\<^sup>*\<^sup>* (Comp (Var y) (Comp (cap xs) E)) (Comp (Var y) (capE xs E))"
    by (rule sig_steps_lift[OF sig.CompR cap_sigma])
  then show "sig\<^sup>*\<^sup>* (Comp (Var y) (Comp (cap xs) E)) (Comp (Var y) E)"
    using capE_hit[OF h] by (rule rtranclp_trans)
next
  assume h: "y \<notin> set xs"
  show "sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Comp (Var y) Nil)" by (rule cap_miss[OF h])
  have "sig\<^sup>*\<^sup>* (Comp (Var y) (Comp (cap xs) E)) (Comp (Var y) (capE xs E))"
    by (rule sig_steps_lift[OF sig.CompR cap_sigma])
  then show "sig\<^sup>*\<^sup>* (Comp (Var y) (Comp (cap xs) E)) (Comp (Var y) Nil)"
    using capE_miss[OF h] by (rule rtranclp_trans)
qed

lemma NF_Var_Nil: "NF (Comp (Var y) Nil)"
  by (auto simp: normal_def cbv_def elim!: sig.cases beta.cases)

lemma not_fb_Var_Nil: "\<not> fb (Comp (Var y) Nil)"
proof
  assume "fb (Comp (Var y) Nil)"
  then show False by (cases rule: fb_cases) (auto elim: inert.cases)
qed

subsection \<open>Proposition 9.3: non-captured variables clash\<close>

theorem cap_clash:
  assumes "y \<notin> set xs"
  shows "Comp (Var y) (cap xs) \<rightarrow>\<^sub>v\<^sup>* N \<and> NF N \<longleftrightarrow> N = Comp (Var y) Nil"
    and "\<not> fb (Comp (Var y) Nil)"
    and "\<not> CFN (Comp (Var y) (cap xs))"
    and "\<not> CFSN (Comp (Var y) (cap xs))"
    and "\<not> Typ (Comp (Var y) (cap xs))"
proof -
  have r0: "Comp (Var y) (cap xs) \<rightarrow>\<^sub>v\<^sup>* Comp (Var y) Nil"
    by (rule sig_steps_cbv[OF cap_miss[OF assms]])
  have eq: "\<And>N. Comp (Var y) (cap xs) \<rightarrow>\<^sub>v\<^sup>* N \<and> NF N \<longleftrightarrow> N = Comp (Var y) Nil"
  proof (rule iffI)
    fix N
    assume "Comp (Var y) (cap xs) \<rightarrow>\<^sub>v\<^sup>* N \<and> NF N"
    then show "N = Comp (Var y) Nil" using NF_unique[OF _ _ r0 NF_Var_Nil] by blast
  next
    fix N
    assume "N = Comp (Var y) Nil"
    then show "Comp (Var y) (cap xs) \<rightarrow>\<^sub>v\<^sup>* N \<and> NF N" using r0 NF_Var_Nil by simp
  qed
  show "Comp (Var y) (cap xs) \<rightarrow>\<^sub>v\<^sup>* N \<and> NF N \<longleftrightarrow> N = Comp (Var y) Nil" by (rule eq)
  show "\<not> fb (Comp (Var y) Nil)" by (rule not_fb_Var_Nil)
  show ncfn: "\<not> CFN (Comp (Var y) (cap xs))"
  proof
    assume "CFN (Comp (Var y) (cap xs))"
    then obtain N where n1: "Comp (Var y) (cap xs) \<rightarrow>\<^sub>v\<^sup>* N" "NF N" and n2: "fb N"
      by (auto simp: CFN_def)
    from eq[of N] n1 have "N = Comp (Var y) Nil" by blast
    with n2 show False using not_fb_Var_Nil by simp
  qed
  show "\<not> CFSN (Comp (Var y) (cap xs))" using ncfn CFN_iff_CFSN by blast
  show "\<not> Typ (Comp (Var y) (cap xs))" using ncfn main_characterization by blast
qed

subsection \<open>Lemma 9.4: generation for cap\<close>

fun envf :: "ty \<Rightarrow> var \<Rightarrow> ty option" where
  "envf (Env m ob) y = map_of m y"
| "envf (Inter A B) y =
     (case envf A y of
        Some A' \<Rightarrow> Some (case envf B y of Some B' \<Rightarrow> Inter A' B' | None \<Rightarrow> A')
      | None \<Rightarrow> envf B y)"
| "envf (TV n) y = None"
| "envf Om y = None"
| "envf (Arr A B) y = None"

text \<open>Auxiliary: subtyping preserves environment look-ups.\<close>

lemma sub_envf: "A \<preceq> B \<Longrightarrow> \<forall>y X. envf B y = Some X \<longrightarrow> (\<exists>Y. envf A y = Some Y \<and> Y \<preceq> X)"
proof (induction rule: sub.induct)
  case (s_refl A)
  then show ?case by (blast intro: sub.s_refl)
next
  case (s_trans A B C)
  show ?case
  proof (intro allI impI)
    fix y X assume "envf C y = Some X"
    with s_trans(4) obtain Y where "envf B y = Some Y" "Y \<preceq> X" by blast
    with s_trans(3) obtain Z where "envf A y = Some Z" "Z \<preceq> Y" by blast
    then show "\<exists>Y. envf A y = Some Y \<and> Y \<preceq> X"
      using \<open>Y \<preceq> X\<close> by (blast intro: sub.s_trans)
  qed
next
  case (s_il A B)
  show ?case
  proof (intro allI impI)
    fix y X assume h: "envf A y = Some X"
    show "\<exists>Y. envf (Inter A B) y = Some Y \<and> Y \<preceq> X"
    proof (cases "envf B y")
      case None
      then show ?thesis using h by (auto intro: sub.s_refl)
    next
      case (Some B')
      then show ?thesis using h by (auto intro: sub.s_il)
    qed
  qed
next
  case (s_ir A B)
  show ?case
  proof (intro allI impI)
    fix y X assume h: "envf B y = Some X"
    show "\<exists>Y. envf (Inter A B) y = Some Y \<and> Y \<preceq> X"
    proof (cases "envf A y")
      case None
      then show ?thesis using h by (auto intro: sub.s_refl)
    next
      case (Some A')
      then show ?thesis using h by (auto intro: sub.s_ir)
    qed
  qed
next
  case (s_glb C A B)
  show ?case
  proof (intro allI impI)
    fix y X assume h: "envf (Inter A B) y = Some X"
    show "\<exists>Y. envf C y = Some Y \<and> Y \<preceq> X"
    proof (cases "envf A y")
      case None
      then have "envf B y = Some X" using h by simp
      then show ?thesis using s_glb(4) by blast
    next
      case (Some A')
      note hA = Some
      show ?thesis
      proof (cases "envf B y")
        case None
        then have "X = A'" using h hA by simp
        then show ?thesis using s_glb(3) hA by blast
      next
        case (Some B')
        note hB = Some
        then have x: "X = Inter A' B'" using h hA by simp
        from s_glb(3) hA obtain Y1 where "envf C y = Some Y1" "Y1 \<preceq> A'" by blast
        moreover from s_glb(4) hB obtain Y2 where "envf C y = Some Y2" "Y2 \<preceq> B'" by blast
        ultimately show ?thesis using x by (auto intro: sub.s_glb)
      qed
    qed
  qed
next
  case (s_arr A' A B B')
  then show ?case by simp
next
  case (s_env m' m ob' ob)
  show ?case using s_env by (simp only: envf.simps) blast
next
  case (s_emeet m1 o1 m2 o2)
  then show ?case by (auto simp: map_of_emeet split: option.splits intro: sub.s_refl)
next
  case s_top
  then show ?case by simp
next
  case s_omenv
  then show ?case by simp
qed

lemma sub_env_fields: "Env R ob \<preceq> Env m ob' \<Longrightarrow> fields_le R m"
  using sub_envf unfolding fields_le_def by fastforce

theorem gen_Cap:
  "\<Gamma> \<turnstile> cap xs : D \<Longrightarrow>
     \<exists>Bs. list_all2 (\<lambda>x B. \<Gamma> \<turnstile> Var x : B) xs Bs \<and> Env (zip xs Bs) True \<preceq> D"
proof (induction xs arbitrary: D)
  case Nil
  then show ?case using gen_Nil by simp
next
  case (Cons x xs)
  from gen_Extn[of \<Gamma> "Var x" x "cap xs" D] Cons.prems
  obtain B m ob where b: "\<Gamma> \<turnstile> Var x : B" and t: "\<Gamma> \<turnstile> cap xs : Env m ob"
    and s: "Env ((x, B) # m) ob \<preceq> D" by auto
  from Cons.IH[OF t] obtain Bs where l: "list_all2 (\<lambda>x B. \<Gamma> \<turnstile> Var x : B) xs Bs"
    and s1: "Env (zip xs Bs) True \<preceq> Env m ob" by blast
  have fl: "fields_le (zip xs Bs) m" by (rule sub_env_fields[OF s1])
  have "Env ((x, B) # zip xs Bs) True \<preceq> Env ((x, B) # m) ob"
  proof (rule s_env)
    show "\<forall>y A'. map_of ((x, B) # m) y = Some A' \<longrightarrow>
            (\<exists>A. map_of ((x, B) # zip xs Bs) y = Some A \<and> A \<preceq> A')"
    proof (intro allI impI)
      fix y A' assume h: "map_of ((x, B) # m) y = Some A'"
      show "\<exists>A. map_of ((x, B) # zip xs Bs) y = Some A \<and> A \<preceq> A'"
      proof (cases "y = x")
        case True
        then show ?thesis using h by (auto intro: sub.s_refl)
      next
        case False
        then have "map_of m y = Some A'" using h by simp
        with fl obtain A where "map_of (zip xs Bs) y = Some A" "A \<preceq> A'"
          unfolding fields_le_def by blast
        then show ?thesis using False by auto
      qed
    qed
  qed simp
  then have "Env ((x, B) # zip xs Bs) True \<preceq> D" using s by (rule s_trans)
  moreover have "list_all2 (\<lambda>x B. \<Gamma> \<turnstile> Var x : B) (x # xs) (B # Bs)" using b l by simp
  ultimately show ?case by (auto intro: exI[of _ "B # Bs"])
qed

subsection \<open>Proposition 9.5: locality\<close>

theorem cap_local:
  "\<Gamma> \<turnstile> Comp M (cap xs) : A \<longleftrightarrow>
     (\<exists>Bs. list_all2 (\<lambda>x B. \<Gamma> \<turnstile> Var x : B) xs Bs \<and> CE (Env (zip xs Bs) True) \<turnstile> M : A)"
proof
  assume "\<Gamma> \<turnstile> Comp M (cap xs) : A"
  then obtain D where d: "\<Gamma> \<turnstile> cap xs : D" and m: "CE D \<turnstile> M : A" by (blast dest: gen_Comp)
  from gen_Cap[OF d] obtain Bs where l: "list_all2 (\<lambda>x B. \<Gamma> \<turnstile> Var x : B) xs Bs"
    and s: "Env (zip xs Bs) True \<preceq> D" by blast
  have "CE (Env (zip xs Bs) True) \<turnstile> M : A" by (rule narrowing[OF m]) (simp add: s)
  with l show "\<exists>Bs. list_all2 (\<lambda>x B. \<Gamma> \<turnstile> Var x : B) xs Bs \<and> CE (Env (zip xs Bs) True) \<turnstile> M : A"
    by blast
next
  assume "\<exists>Bs. list_all2 (\<lambda>x B. \<Gamma> \<turnstile> Var x : B) xs Bs \<and> CE (Env (zip xs Bs) True) \<turnstile> M : A"
  then obtain Bs where l: "list_all2 (\<lambda>x B. \<Gamma> \<turnstile> Var x : B) xs Bs"
    and m: "CE (Env (zip xs Bs) True) \<turnstile> M : A" by blast
  show "\<Gamma> \<turnstile> Comp M (cap xs) : A" by (rule TComp[OF cap_typing[OF l] m])
qed

subsection \<open>Corollary 9.6: the parent environment is not retained\<close>

theorem cap_nonretain_1:
  assumes "\<forall>x\<in>set xs. \<forall>B. \<Gamma> \<turnstile> Var x : B \<longleftrightarrow> \<Gamma>' \<turnstile> Var x : B"
  shows "\<Gamma> \<turnstile> Comp M (cap xs) : A \<longleftrightarrow> \<Gamma>' \<turnstile> Comp M (cap xs) : A"
  unfolding cap_local using assms list_all2_cong_set[of xs "\<lambda>x B. \<Gamma> \<turnstile> Var x : B" "\<lambda>x B. \<Gamma>' \<turnstile> Var x : B"]
  by metis

theorem cap_nonretain_2:
  assumes "y \<notin> set xs"
  shows "CE (Env (zip xs Bs) True) \<turnstile> Var y : A \<Longrightarrow> Om \<preceq> A \<and> \<not> ess A"
    and "CT m \<turnstile> Comp (Var y) (cap xs) : A \<Longrightarrow> \<not> ess A"
proof -
  have key: "CE (Env (zip xs Bs) True) \<turnstile> Var y : A \<Longrightarrow> Om \<preceq> A" for Bs A
  proof -
    assume h: "CE (Env (zip xs Bs) True) \<turnstile> Var y : A"
    from gen_Var[OF h] show "Om \<preceq> A"
    proof
      assume "Om \<preceq> A" then show ?thesis .
    next
      assume "\<exists>m B. provides (CE (Env (zip xs Bs) True)) m \<and> map_of m y = Some B \<and> B \<preceq> A"
      then obtain m B ob where p: "Env (zip xs Bs) True \<preceq> Env m ob" and mb: "map_of m y = Some B"
        by auto
      from sub_env_fields[OF p] mb obtain Y where "map_of (zip xs Bs) y = Some Y"
        unfolding fields_le_def by blast
      then have "y \<in> set xs" by (auto dest!: map_of_SomeD set_zip_leftD)
      with assms show ?thesis by simp
    qed
  qed
  have ne: "Om \<preceq> A \<Longrightarrow> \<not> ess A" for A
    using ess_down[of Om A] by auto
  show "CE (Env (zip xs Bs) True) \<turnstile> Var y : A \<Longrightarrow> Om \<preceq> A \<and> \<not> ess A"
    using key ne by blast
  assume "CT m \<turnstile> Comp (Var y) (cap xs) : A"
  then obtain Bs' where "CE (Env (zip xs Bs') True) \<turnstile> Var y : A" unfolding cap_local by blast
  then show "\<not> ess A" using key ne by blast
qed

lemma typ_Var_CT:
  "CT m \<turnstile> Var x : B \<longleftrightarrow> Om \<preceq> B \<or> (\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B)"
proof
  assume h: "CT m \<turnstile> Var x : B"
  from gen_Var[OF h] show "Om \<preceq> B \<or> (\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B)"
  proof
    assume "Om \<preceq> B" then show ?thesis by simp
  next
    assume "\<exists>m' B'. provides (CT m) m' \<and> map_of m' x = Some B' \<and> B' \<preceq> B"
    then obtain m' B' where "fields_le m m'" "map_of m' x = Some B'" "B' \<preceq> B" by auto
    then obtain A' where "map_of m x = Some A'" "A' \<preceq> B'" unfolding fields_le_def by blast
    then show ?thesis using \<open>B' \<preceq> B\<close> by (blast intro: s_trans)
  qed
next
  assume "Om \<preceq> B \<or> (\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B)"
  then show "CT m \<turnstile> Var x : B"
  proof
    assume "Om \<preceq> B" then show ?thesis by (rule TSub[OF TOm])
  next
    assume "\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B"
    then obtain A' where a: "map_of m x = Some A'" and s: "A' \<preceq> B" by blast
    have "provides (CT m) m" by (simp add: fields_le_refl)
    from TVar[OF this a] show ?thesis by (rule TSub[OF _ s])
  qed
qed

theorem cap_nonretain_3:
  "CT m \<turnstile> Comp M (cap xs) : A \<longleftrightarrow>
     (\<exists>Bs. list_all2 (\<lambda>x B. Om \<preceq> B \<or> (\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B)) xs Bs \<and>
           CE (Env (zip xs Bs) True) \<turnstile> M : A)"
proof -
  have "\<And>Bs. list_all2 (\<lambda>x B. CT m \<turnstile> Var x : B) xs Bs =
          list_all2 (\<lambda>x B. Om \<preceq> B \<or> (\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B)) xs Bs"
    by (rule list_all2_cong_set) (simp add: typ_Var_CT)
  then show ?thesis unfolding cap_local by simp
qed

subsection \<open>Proposition 9.7: lazy environments, evaluated arguments\<close>

theorem cap_beta:
  "fb F \<Longrightarrow> App (Comp (Lam x M) (cap xs)) F \<rightarrow>\<^sub>\<beta> Comp M (Extn F x (cap xs))"
  by (rule Beta)

theorem cap_ext_lookup:
  "Comp (Var x) (Extn F x (cap xs)) \<rightarrow>\<^sub>\<sigma> F"
  "y \<in> set xs \<Longrightarrow> y \<noteq> x \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (Extn F x (cap xs))) (Var y)"
  "y \<notin> set xs \<Longrightarrow> y \<noteq> x \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (Extn F x (cap xs))) (Comp (Var y) Nil)"
proof -
  show "Comp (Var x) (Extn F x (cap xs)) \<rightarrow>\<^sub>\<sigma> F" by (rule sig.VarRef)
next
  assume h: "y \<in> set xs" and ne: "y \<noteq> x"
  have "Comp (Var y) (Extn F x (cap xs)) \<rightarrow>\<^sub>\<sigma> Comp (Var y) (cap xs)" by (rule sig.VarSkip[OF ne[symmetric]])
  then show "sig\<^sup>*\<^sup>* (Comp (Var y) (Extn F x (cap xs))) (Var y)"
    using cap_hit[OF h] by (rule converse_rtranclp_into_rtranclp)
next
  assume h: "y \<notin> set xs" and ne: "y \<noteq> x"
  have "Comp (Var y) (Extn F x (cap xs)) \<rightarrow>\<^sub>\<sigma> Comp (Var y) (cap xs)" by (rule sig.VarSkip[OF ne[symmetric]])
  then show "sig\<^sup>*\<^sup>* (Comp (Var y) (Extn F x (cap xs))) (Comp (Var y) Nil)"
    using cap_miss[OF h] by (rule converse_rtranclp_into_rtranclp)
qed

theorem cap_lazy_env:
  assumes "x \<noteq> z"
  shows "sig\<^sup>*\<^sup>* (Comp (Var z) (Extn Omega x (cap [z]))) (Var z)"
    and "\<Gamma> \<turnstile> Omega : Om"
    and "Typ (Comp (Var z) (Extn Omega x (cap [z])))"
proof -
  show "sig\<^sup>*\<^sup>* (Comp (Var z) (Extn Omega x (cap [z]))) (Var z)"
    using cap_ext_lookup(2)[of z "[z]" x Omega] assms by simp
  then have r: "Comp (Var z) (Extn Omega x (cap [z])) \<rightarrow>\<^sub>v\<^sup>* Var z" by (rule sig_steps_cbv)
  show "\<Gamma> \<turnstile> Omega : Om" by (rule Omega_Om)
  have "CFN (Comp (Var z) (Extn Omega x (cap [z])))"
    unfolding CFN_def using r NF_Var fb_Var by blast
  then show "Typ (Comp (Var z) (Extn Omega x (cap [z])))" using main_characterization by blast
qed

theorem cap_eager_arg:
  "\<not> Typ (App (Comp (Lam x (Var z)) (cap [z])) Omega)"
  "\<not> (CT m \<turnstile> App (Comp (Lam x (Var z)) (cap [z])) Omega : A \<and> ess A)"
  "\<not> (CT m \<turnstile> Omega : A \<and> ess A)"
proof -
  have b: "App (Comp (Lam x (Var z)) (cap [z])) Omega \<rightarrow>\<^sub>\<beta>
             App (Comp (Lam x (Var z)) (cap [z])) (Comp (App (Var 0) (Var 0)) (Extn (Comp dw Nil) 0 Nil))"
    by (rule beta.AppR[OF FClo Omega_loop(1)])
  have s: "sig\<^sup>*\<^sup>* (App (Comp (Lam x (Var z)) (cap [z]))
                     (Comp (App (Var 0) (Var 0)) (Extn (Comp dw Nil) 0 Nil)))
                 (App (Comp (Lam x (Var z)) (cap [z])) Omega)"
    by (rule sig_steps_lift[OF sig.AppR Omega_loop(2)])
  show nt: "\<not> Typ (App (Comp (Lam x (Var z)) (cap [z])) Omega)"
    using loop_not_CFN[OF b s] main_characterization by blast
  show "\<not> (CT m \<turnstile> App (Comp (Lam x (Var z)) (cap [z])) Omega : A \<and> ess A)"
    using nt unfolding Typ_def by blast
  show "\<not> (CT m \<turnstile> Omega : A \<and> ess A)"
    using Omega_not_Typ unfolding Typ_def by blast
qed

end
