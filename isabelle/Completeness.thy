theory Completeness
  imports Typing Uniform
begin

section \<open>Completeness: \<open>CFN M \<Longrightarrow> Typ M\<close>\<close>

subsection \<open>Replacing a subterm by one with at least the same typings\<close>

definition at_least :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "at_least M N \<longleftrightarrow> (\<forall>\<Gamma> A. \<Gamma> \<turnstile> N : A \<longrightarrow> \<Gamma> \<turnstile> M : A)"

lemma rep_AppL_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = App N L \<Longrightarrow> (\<forall>\<Gamma> A. \<Gamma> \<turnstile> N : A \<longrightarrow> \<Gamma> \<turnstile> M : A) \<Longrightarrow>
     \<Gamma> \<turnstile> App M L : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_AppL: "at_least M N \<Longrightarrow> at_least (App M L) (App N L)"
  unfolding at_least_def by (blast intro: rep_AppL_aux)

lemma rep_AppR_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = App L N \<Longrightarrow> (\<forall>\<Gamma> A. \<Gamma> \<turnstile> N : A \<longrightarrow> \<Gamma> \<turnstile> M : A) \<Longrightarrow>
     \<Gamma> \<turnstile> App L M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_AppR: "at_least M N \<Longrightarrow> at_least (App L M) (App L N)"
  unfolding at_least_def by (blast intro: rep_AppR_aux)

lemma rep_Lam_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = Lam x N \<Longrightarrow> (\<forall>\<Gamma> A. \<Gamma> \<turnstile> N : A \<longrightarrow> \<Gamma> \<turnstile> M : A) \<Longrightarrow>
     \<Gamma> \<turnstile> Lam x M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_Lam: "at_least M N \<Longrightarrow> at_least (Lam x M) (Lam x N)"
  unfolding at_least_def by (blast intro: rep_Lam_aux)

lemma rep_CompL_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = Comp N L \<Longrightarrow> (\<forall>\<Gamma> A. \<Gamma> \<turnstile> N : A \<longrightarrow> \<Gamma> \<turnstile> M : A) \<Longrightarrow>
     \<Gamma> \<turnstile> Comp M L : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_CompL: "at_least M N \<Longrightarrow> at_least (Comp M L) (Comp N L)"
  unfolding at_least_def by (blast intro: rep_CompL_aux)

lemma rep_CompR_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = Comp L N \<Longrightarrow> (\<forall>\<Gamma> A. \<Gamma> \<turnstile> N : A \<longrightarrow> \<Gamma> \<turnstile> M : A) \<Longrightarrow>
     \<Gamma> \<turnstile> Comp L M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_CompR: "at_least M N \<Longrightarrow> at_least (Comp L M) (Comp L N)"
  unfolding at_least_def by (blast intro: rep_CompR_aux)

lemma rep_ExtnL_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = Extn N x L \<Longrightarrow> (\<forall>\<Gamma> A. \<Gamma> \<turnstile> N : A \<longrightarrow> \<Gamma> \<turnstile> M : A) \<Longrightarrow>
     \<Gamma> \<turnstile> Extn M x L : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_ExtnL: "at_least M N \<Longrightarrow> at_least (Extn M x L) (Extn N x L)"
  unfolding at_least_def by (blast intro: rep_ExtnL_aux)

lemma rep_ExtnR_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = Extn L x N \<Longrightarrow> (\<forall>\<Gamma> A. \<Gamma> \<turnstile> N : A \<longrightarrow> \<Gamma> \<turnstile> M : A) \<Longrightarrow>
     \<Gamma> \<turnstile> Extn L x M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_ExtnR: "at_least M N \<Longrightarrow> at_least (Extn L x M) (Extn L x N)"
  unfolding at_least_def by (blast intro: rep_ExtnR_aux)

subsection \<open>Root rules\<close>

lemma exp_Ass: "at_least (Comp (Comp L M) N) (Comp L (Comp M N))"
  unfolding at_least_def
proof (intro allI impI)
  fix \<Gamma> A
  assume "\<Gamma> \<turnstile> Comp L (Comp M N) : A"
  then obtain D where 1: "\<Gamma> \<turnstile> Comp M N : D" and 2: "CE D \<turnstile> L : A"
    using gen_Comp by blast
  from 1 obtain D' where 3: "\<Gamma> \<turnstile> N : D'" and 4: "CE D' \<turnstile> M : D"
    using gen_Comp by blast
  from 4 2 have "CE D' \<turnstile> Comp L M : A" by (rule TComp)
  with 3 show "\<Gamma> \<turnstile> Comp (Comp L M) N : A" by (rule TComp)
qed

lemma exp_DNil: "at_least (Comp Nil N) Nil"
  unfolding at_least_def
proof (intro allI impI)
  fix \<Gamma> A
  assume "\<Gamma> \<turnstile> Nil : A"
  then have "CE Om \<turnstile> Nil : A" using gen_Nil by (blast intro: TSub TNil)
  then show "\<Gamma> \<turnstile> Comp Nil N : A" by (rule TComp[OF TOm])
qed

lemma exp_VarRef: "at_least (Comp (Var x) (Extn M x N)) M"
  unfolding at_least_def
proof (intro allI impI)
  fix \<Gamma> A
  assume "\<Gamma> \<turnstile> M : A"
  then have "\<Gamma> \<turnstile> Extn M x N : Env [(x, A)] False"
    using TExtn[of \<Gamma> M A N "[]" False x] typ_env_om by blast
  moreover have "CE (Env [(x, A)] False) \<turnstile> Var x : A"
    by (rule TVar[of _ "[(x, A)]"]) (auto intro: s_refl)
  ultimately show "\<Gamma> \<turnstile> Comp (Var x) (Extn M x N) : A" by (rule TComp)
qed

lemma exp_VarSkip: "x \<noteq> y \<Longrightarrow> at_least (Comp (Var y) (Extn M x N)) (Comp (Var y) N)"
  unfolding at_least_def
proof (intro allI impI)
  fix \<Gamma> A
  assume xy: "x \<noteq> y" and "\<Gamma> \<turnstile> Comp (Var y) N : A"
  then obtain D where 1: "\<Gamma> \<turnstile> N : D" and 2: "CE D \<turnstile> Var y : A"
    using gen_Comp by blast
  from gen_Var[OF 2] show "\<Gamma> \<turnstile> Comp (Var y) (Extn M x N) : A"
  proof
    assume "Om \<preceq> A"
    then have "CE Om \<turnstile> Var y : A" by (blast intro: TSub TOm)
    moreover have "\<Gamma> \<turnstile> Extn M x N : Om" by (rule TOm)
    ultimately show ?thesis by (blast intro: TComp)
  next
    assume "\<exists>m B. provides (CE D) m \<and> map_of m y = Some B \<and> B \<preceq> A"
    then obtain m B ob where d: "D \<preceq> Env m ob" and l: "map_of m y = Some B" and b: "B \<preceq> A"
      by auto
    have "\<Gamma> \<turnstile> N : Env m ob" using 1 d by (rule TSub)
    then have "\<Gamma> \<turnstile> Extn M x N : Env ((x, Om) # m) ob" by (rule TExtn[OF TOm])
    moreover have "CE (Env ((x, Om) # m) ob) \<turnstile> Var y : A"
    proof -
      have "map_of ((x, Om) # m) y = Some B" using l xy by simp
      moreover have "provides (CE (Env ((x, Om) # m) ob)) ((x, Om) # m)"
        by (auto intro: s_refl)
      ultimately have "CE (Env ((x, Om) # m) ob) \<turnstile> Var y : B" by (rule TVar[rotated])
      then show ?thesis using b by (rule TSub)
    qed
    ultimately show ?thesis by (rule TComp)
  qed
qed

lemma exp_DExtn: "at_least (Comp (Extn L x M) N) (Extn (Comp L N) x (Comp M N))"
  unfolding at_least_def
proof (intro allI impI)
  fix \<Gamma> A
  assume "\<Gamma> \<turnstile> Extn (Comp L N) x (Comp M N) : A"
  then obtain B m ob where 1: "\<Gamma> \<turnstile> Comp L N : B" and 2: "\<Gamma> \<turnstile> Comp M N : Env m ob"
    and s: "Env ((x, B) # m) ob \<preceq> A"
    using gen_Extn by blast
  from 1 obtain D1 where a: "\<Gamma> \<turnstile> N : D1" "CE D1 \<turnstile> L : B" using gen_Comp by blast
  from 2 obtain D2 where b: "\<Gamma> \<turnstile> N : D2" "CE D2 \<turnstile> M : Env m ob" using gen_Comp by blast
  have "\<Gamma> \<turnstile> N : Inter D1 D2" using a(1) b(1) by (rule TInter)
  moreover have "CE (Inter D1 D2) \<turnstile> Extn L x M : Env ((x, B) # m) ob"
  proof (rule TExtn)
    show "CE (Inter D1 D2) \<turnstile> L : B" by (rule narrowing[OF a(2)]) (simp add: s_il)
    show "CE (Inter D1 D2) \<turnstile> M : Env m ob" by (rule narrowing[OF b(2)]) (simp add: s_ir)
  qed
  ultimately have "\<Gamma> \<turnstile> Comp (Extn L x M) N : Env ((x, B) # m) ob" by (rule TComp)
  from this s show "\<Gamma> \<turnstile> Comp (Extn L x M) N : A" by (rule TSub)
qed

lemma exp_DApp_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = App (Comp M1 N) (Comp M2 N) \<Longrightarrow> \<Gamma> \<turnstile> Comp (App M1 M2) N : A"
proof (induction rule: hasty.induct)
  case (TApp \<Gamma> P A B Q)
  then have p: "\<Gamma> \<turnstile> Comp M1 N : Arr A B" and q: "\<Gamma> \<turnstile> Comp M2 N : A" and e: "ess A" by auto
  from p obtain D1 where a: "\<Gamma> \<turnstile> N : D1" "CE D1 \<turnstile> M1 : Arr A B" using gen_Comp by blast
  from q obtain D2 where b: "\<Gamma> \<turnstile> N : D2" "CE D2 \<turnstile> M2 : A" using gen_Comp by blast
  have "\<Gamma> \<turnstile> N : Inter D1 D2" using a(1) b(1) by (rule TInter)
  moreover have "CE (Inter D1 D2) \<turnstile> App M1 M2 : B"
  proof (rule hasty.TApp)
    show "CE (Inter D1 D2) \<turnstile> M1 : Arr A B" by (rule narrowing[OF a(2)]) (simp add: s_il)
    show "CE (Inter D1 D2) \<turnstile> M2 : A" by (rule narrowing[OF b(2)]) (simp add: s_ir)
    show "ess A" by (rule e)
  qed
  ultimately show ?case by (rule TComp)
qed (auto intro: hasty.intros)

lemma exp_DApp: "at_least (Comp (App M1 M2) N) (App (Comp M1 N) (Comp M2 N))"
  unfolding at_least_def using exp_DApp_aux by blast

subsection \<open>Subject expansion for \<open>\<sigma>\<close>\<close>


lemma sig_expansion: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> at_least M N"
proof (induction rule: sig.induct)
  case (Ass L M N) show ?case by (rule exp_Ass)
next
  case (DNil M) show ?case by (rule exp_DNil)
next
  case (DExtn L x M N) show ?case by (rule exp_DExtn)
next
  case (VarRef x M N) show ?case by (rule exp_VarRef)
next
  case (VarSkip x y M N) then show ?case by (rule exp_VarSkip)
next
  case (DApp M1 M2 N) show ?case by (rule exp_DApp)
next
  case (AppL M N L) then show ?case by (blast intro: rep_AppL)
next
  case (AppR M N L) then show ?case by (blast intro: rep_AppR)
next
  case (Lam M N x) then show ?case by (blast intro: rep_Lam)
next
  case (CompL M N L) then show ?case by (blast intro: rep_CompL)
next
  case (CompR M N L) then show ?case by (blast intro: rep_CompR)
next
  case (ExtnL M N x L) then show ?case by (blast intro: rep_ExtnL)
next
  case (ExtnR M N L x) then show ?case by (blast intro: rep_ExtnR)
qed

lemma subject_expansion_sig: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> \<Gamma> \<turnstile> N : A \<Longrightarrow> \<Gamma> \<turnstile> M : A"
  using sig_expansion by (auto simp: at_least_def)

subsection \<open>Refining the top-level context\<close>

lemma fields_le_refl: "fields_le m m"
  by (auto simp: fields_le_def intro: s_refl)

lemma fields_le_trans: "fields_le m1 m2 \<Longrightarrow> fields_le m2 m3 \<Longrightarrow> fields_le m1 m3"
  unfolding fields_le_def by (blast intro: s_trans)

lemma emeet_le1: "fields_le (emeet m1 m2) m1"
  by (auto simp: fields_le_def map_of_emeet intro: s_il s_refl split: option.split)

lemma emeet_le2: "fields_le (emeet m1 m2) m2"
  by (auto simp: fields_le_def map_of_emeet intro: s_ir s_refl split: option.split)

lemma narrowT: "CT m \<turnstile> M : A \<Longrightarrow> fields_le m' m \<Longrightarrow> CT m' \<turnstile> M : A"
  using narrowing[of "CT m" M A "CT m'"] by simp

lemma sub_env_head: "B \<preceq> B' \<Longrightarrow> Env ((x, B) # m) ob \<preceq> Env ((x, B') # m) ob"
proof (rule s_env)
  assume "B \<preceq> B'"
  then show "\<forall>y A'. map_of ((x, B') # m) y = Some A' \<longrightarrow>
      (\<exists>A. map_of ((x, B) # m) y = Some A \<and> A \<preceq> A')"
    by (auto intro: s_refl)
qed simp

definition exp_top :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "exp_top M N \<longleftrightarrow>
     (\<forall>m A. CT m \<turnstile> N : A \<longrightarrow> (\<exists>m'. fields_le m' m \<and> CT m' \<turnstile> M : A))"

lemma exp_topI:
  "(\<And>m A. CT m \<turnstile> N : A \<Longrightarrow> \<exists>m'. fields_le m' m \<and> CT m' \<turnstile> M : A) \<Longrightarrow> exp_top M N"
  unfolding exp_top_def by blast

lemma exp_topD:
  "exp_top M N \<Longrightarrow> CT m \<turnstile> N : A \<Longrightarrow> \<exists>m'. fields_le m' m \<and> CT m' \<turnstile> M : A"
  unfolding exp_top_def by blast

lemma refine_meet:
  assumes "fields_le m1 m" "CT m1 \<turnstile> M : A" "fields_le m2 m" "CT m2 \<turnstile> M : B"
  shows "\<exists>m'. fields_le m' m \<and> CT m' \<turnstile> M : Inter A B"
proof -
  have "CT (emeet m1 m2) \<turnstile> M : Inter A B" using top_meet[OF assms(2) assms(4)] .
  moreover have "fields_le (emeet m1 m2) m" using emeet_le1 assms(1) by (rule fields_le_trans)
  ultimately show ?thesis by blast
qed

lemma rep_AppL_top_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = App N L \<Longrightarrow> \<Gamma> = CT m \<Longrightarrow> exp_top M N \<Longrightarrow>
     \<exists>m'. fields_le m' m \<and> CT m' \<turnstile> App M L : A"
proof (induction arbitrary: m rule: hasty.induct)
  case (TApp \<Gamma> P A B Q)
  then have n: "CT m \<turnstile> N : Arr A B" and l: "CT m \<turnstile> L : A" and e: "ess A" by auto
  from exp_topD[OF TApp.prems(3) n] obtain m' where s: "fields_le m' m"
    and t: "CT m' \<turnstile> M : Arr A B" by blast
  have "CT m' \<turnstile> L : A" using narrowT[OF l s] .
  then show ?case using s t e by (blast intro: hasty.TApp)
next
  case (TOm \<Gamma> P)
  then show ?case by (blast intro: hasty.TOm fields_le_refl)
next
  case (TInter \<Gamma> P A B)
  then obtain m1 m2 where "fields_le m1 m" "CT m1 \<turnstile> App M L : A"
    "fields_le m2 m" "CT m2 \<turnstile> App M L : B" by blast
  then show ?case by (rule refine_meet)
next
  case (TSub \<Gamma> P A B)
  then show ?case by (blast intro: hasty.TSub)
qed auto

lemma rep_AppL_top: "exp_top M N \<Longrightarrow> exp_top (App M L) (App N L)"
  by (rule exp_topI) (rule rep_AppL_top_aux[OF _ refl refl])

lemma rep_AppR_top_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = App L N \<Longrightarrow> \<Gamma> = CT m \<Longrightarrow> exp_top M N \<Longrightarrow>
     \<exists>m'. fields_le m' m \<and> CT m' \<turnstile> App L M : A"
proof (induction arbitrary: m rule: hasty.induct)
  case (TApp \<Gamma> P A B Q)
  then have l: "CT m \<turnstile> L : Arr A B" and n: "CT m \<turnstile> N : A" and e: "ess A" by auto
  from exp_topD[OF TApp.prems(3) n] obtain m' where s: "fields_le m' m"
    and t: "CT m' \<turnstile> M : A" by blast
  have "CT m' \<turnstile> L : Arr A B" using narrowT[OF l s] .
  then show ?case using s t e by (blast intro: hasty.TApp)
next
  case (TOm \<Gamma> P)
  then show ?case by (blast intro: hasty.TOm fields_le_refl)
next
  case (TInter \<Gamma> P A B)
  then obtain m1 m2 where "fields_le m1 m" "CT m1 \<turnstile> App L M : A"
    "fields_le m2 m" "CT m2 \<turnstile> App L M : B" by blast
  then show ?case by (rule refine_meet)
next
  case (TSub \<Gamma> P A B)
  then show ?case by (blast intro: hasty.TSub)
qed auto

lemma rep_AppR_top: "exp_top M N \<Longrightarrow> exp_top (App L M) (App L N)"
  by (rule exp_topI) (rule rep_AppR_top_aux[OF _ refl refl])

lemma rep_VarR_top_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = Comp (Var x) N \<Longrightarrow> \<Gamma> = CT m \<Longrightarrow> exp_top M N \<Longrightarrow>
     \<exists>m'. fields_le m' m \<and> CT m' \<turnstile> Comp (Var x) M : A"
proof (induction arbitrary: m rule: hasty.induct)
  case (TComp \<Gamma> Q D K A)
  then have n: "CT m \<turnstile> N : D" and v: "CE D \<turnstile> Var x : A" by auto
  from exp_topD[OF TComp.prems(3) n] obtain m' where s: "fields_le m' m"
    and t: "CT m' \<turnstile> M : D" by blast
  then show ?case using v by (blast intro: hasty.TComp)
next
  case (TOm \<Gamma> P)
  then show ?case by (blast intro: hasty.TOm fields_le_refl)
next
  case (TInter \<Gamma> P A B)
  then obtain m1 m2 where "fields_le m1 m" "CT m1 \<turnstile> Comp (Var x) M : A"
    "fields_le m2 m" "CT m2 \<turnstile> Comp (Var x) M : B" by blast
  then show ?case by (rule refine_meet)
next
  case (TSub \<Gamma> P A B)
  then show ?case by (blast intro: hasty.TSub)
qed auto

lemma rep_VarR_top: "exp_top M N \<Longrightarrow> exp_top (Comp (Var x) M) (Comp (Var x) N)"
  by (rule exp_topI) (rule rep_VarR_top_aux[OF _ refl refl])

subsection \<open>Fireballs have essential types at top level\<close>

lemma inert_fb_typable:
  "inert M \<Longrightarrow> \<forall>m A. \<exists>m'. fields_le m' m \<and> CT m' \<turnstile> M : A"
  "fb M \<Longrightarrow> \<forall>m. \<exists>m' T. fields_le m' m \<and> ess T \<and> CT m' \<turnstile> M : T"
proof (induction rule: inert_fb.inducts)
  case (IVar x)
  show ?case
  proof (intro allI)
    fix m A
    have "CT (emeet m [(x, A)]) \<turnstile> Var x : A"
      by (rule TVar[of _ "[(x, A)]"])
         (auto simp: fields_le_def map_of_emeet intro: s_ir s_refl split: option.split)
    then show "\<exists>m'. fields_le m' m \<and> CT m' \<turnstile> Var x : A" using emeet_le1 by blast
  qed
next
  case (IApp M N)
  show ?case
  proof (intro allI)
    fix m A
    from IApp.IH(2) obtain m1 T where s1: "fields_le m1 m" and e: "ess T"
      and t1: "CT m1 \<turnstile> N : T" by blast
    from IApp.IH(1) obtain m2 where s2: "fields_le m2 m1" and t2: "CT m2 \<turnstile> M : Arr T A"
      by blast
    have "CT m2 \<turnstile> N : T" using narrowT[OF t1 s2] .
    then have "CT m2 \<turnstile> App M N : A" using t2 e by (blast intro: hasty.TApp)
    moreover have "fields_le m2 m" using s2 s1 by (rule fields_le_trans)
    ultimately show "\<exists>m'. fields_le m' m \<and> CT m' \<turnstile> App M N : A" by blast
  qed
next
  case (IComp M x)
  show ?case
  proof (intro allI)
    fix m A
    from IComp.IH obtain m' where s: "fields_le m' m"
      and t: "CT m' \<turnstile> M : Env [(x, A)] True" by blast
    have "CE (Env [(x, A)] True) \<turnstile> Var x : A"
      by (rule TVar[of _ "[(x, A)]"]) (auto intro: s_refl)
    then have "CT m' \<turnstile> Comp (Var x) M : A" using t by (rule hasty.TComp[rotated])
    then show "\<exists>m'. fields_le m' m \<and> CT m' \<turnstile> Comp (Var x) M : A" using s by blast
  qed
next
  case (FInert M)
  show ?case
  proof (intro allI)
    fix m
    from FInert.IH obtain m' where "fields_le m' m" "CT m' \<turnstile> M : TV 0" by blast
    then show "\<exists>m' T. fields_le m' m \<and> ess T \<and> CT m' \<turnstile> M : T" by force
  qed
next
  case (FLam x M)
  have "\<And>m. CT m \<turnstile> Lam x M : Arr Om Om" by (rule TCode)
  then show ?case by (force intro: fields_le_refl)
next
  case (FClo x M L)
  have "\<And>m. CT m \<turnstile> L : Env [] False" by (rule typ_env_om)
  moreover have "CE (Env [] False) \<turnstile> Lam x M : Arr Om Om"
    by (rule TLam[OF s_refl]) (rule TOm)
  ultimately have "\<And>m. CT m \<turnstile> Comp (Lam x M) L : Arr Om Om" by (blast intro: hasty.TComp)
  then show ?case by (force intro: fields_le_refl)
next
  case FNil
  have "\<And>m. CT m \<turnstile> Nil : Env [] True" by (rule TNil)
  then show ?case by (force intro: fields_le_refl)
next
  case (FExtn M x L)
  have "\<And>m. CT m \<turnstile> Extn M x L : Env [(x, Om)] False"
    by (rule TExtn[OF TOm typ_env_om])
  then show ?case by (force intro: fields_le_refl)
qed

lemma fb_typable: "fb M \<Longrightarrow> \<exists>m' T. fields_le m' m \<and> ess T \<and> CT m' \<turnstile> M : T"
  using inert_fb_typable(2) by blast

subsection \<open>\<open>\<beta>\<^sub>v\<close>-expansion at top level\<close>

lemma exp_Beta_top: "fb V \<Longrightarrow> exp_top (App (Comp (Lam x B) L) V) (Comp B (Extn V x L))"
proof (rule exp_topI)
  fix m A
  assume f: "fb V" and "CT m \<turnstile> Comp B (Extn V x L) : A"
  then obtain D where 1: "CT m \<turnstile> Extn V x L : D" and 2: "CE D \<turnstile> B : A"
    using gen_Comp by blast
  from 1 obtain T m1 o1 where v: "CT m \<turnstile> V : T" and l: "CT m \<turnstile> L : Env m1 o1"
    and s: "Env ((x, T) # m1) o1 \<preceq> D"
    using gen_Extn by blast
  from fb_typable[OF f, of m] obtain m' T' where s': "fields_le m' m" and e: "ess T'"
    and v': "CT m' \<turnstile> V : T'" by blast
  have vv: "CT m' \<turnstile> V : Inter T T'" using hasty.TInter[OF narrowT[OF v s'] v'] .
  have "Env ((x, Inter T T') # m1) o1 \<preceq> D" using sub_env_head[OF s_il] s by (rule s_trans)
  then have sd: "Env ((x, Inter T T') # m1) o1 \<preceq> D" .
  have "CE (Env ((x, Inter T T') # m1) o1) \<turnstile> B : A" by (rule narrowing[OF 2]) (simp add: sd)
  then have "CE (Env m1 o1) \<turnstile> Lam x B : Arr (Inter T T') A" by (rule TLam[OF s_refl])
  then have "CT m' \<turnstile> Comp (Lam x B) L : Arr (Inter T T') A"
    using narrowT[OF l s'] by (rule hasty.TComp[rotated])
  then have "CT m' \<turnstile> App (Comp (Lam x B) L) V : A" using vv e by (auto intro: hasty.TApp)
  then show "\<exists>m'. fields_le m' m \<and> CT m' \<turnstile> App (Comp (Lam x B) L) V : A" using s' by blast
qed

lemma beta_expansion_top: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> exp_top M N"
proof (induction rule: beta.induct)
  case (Beta N x M L) show ?case using Beta.hyps by (rule exp_Beta_top)
next
  case (AppL M N L) show ?case using AppL.IH by (rule rep_AppL_top)
next
  case (AppR L M N) show ?case using AppR.IH by (rule rep_AppR_top)
next
  case (VarR M N x) show ?case using VarR.IH by (rule rep_VarR_top)
qed

subsection \<open>Subject expansion and completeness\<close>

lemma subject_expansion_top:
  "M \<rightarrow>\<^sub>v N \<Longrightarrow> CT m \<turnstile> N : A \<Longrightarrow> \<exists>m'. fields_le m' m \<and> CT m' \<turnstile> M : A"
proof -
  assume s: "M \<rightarrow>\<^sub>v N" and t: "CT m \<turnstile> N : A"
  from s consider "M \<rightarrow>\<^sub>\<sigma> N" | "M \<rightarrow>\<^sub>\<beta> N" by (auto simp: cbv_def)
  then show ?thesis
  proof cases
    case 1 then show ?thesis using subject_expansion_sig[OF 1 t] fields_le_refl by blast
  next
    case 2 then show ?thesis using exp_topD[OF beta_expansion_top[OF 2] t] by blast
  qed
qed

lemma subject_expansion_steps:
  "M \<rightarrow>\<^sub>v\<^sup>* N \<Longrightarrow> CT m \<turnstile> N : A \<Longrightarrow> \<exists>m'. CT m' \<turnstile> M : A"
proof (induction arbitrary: m rule: converse_rtranclp_induct)
  case base then show ?case by blast
next
  case (step M M')
  then obtain m1 where "CT m1 \<turnstile> M' : A" by blast
  then show ?case using subject_expansion_top[OF step.hyps(1)] by blast
qed

theorem completeness: "CFN M \<Longrightarrow> Typ M"
proof -
  assume "CFN M"
  then obtain N where r: "M \<rightarrow>\<^sub>v\<^sup>* N" and c: "fb N" by (auto simp: CFN_def)
  from fb_typable[OF c, of "[]"] obtain m T where t: "CT m \<turnstile> N : T" and e: "ess T"
    by blast
  from subject_expansion_steps[OF r t] obtain m' where "CT m' \<turnstile> M : T" by blast
  with e show "Typ M" by (auto simp: Typ_def)
qed

end
