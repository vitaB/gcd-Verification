theory ggt
imports Main
begin

fun ggt :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ggt 0 m = m"
  | "ggt n m = ggt(m mod n) n"

lemma [simp]: " n = 0 \<Longrightarrow> ggt n m = m" by simp
lemma [simp]: "n \<noteq> 0 \<Longrightarrow> ggt n m = ggt (m mod n) n"
  apply (case_tac n)
  apply (auto)
done

theorem ggt_o [simp] :  "ggt m 0 = m"
  apply(induct_tac m)
  apply (auto)
done

lemma ggt_same [simp]: "ggt n n = n"
  apply (case_tac n)
  apply (auto)
done

lemma ggt_mod : " m > 0 \<longrightarrow> ggt (n mod m) m = ggt n m"
  apply (case_tac n)
  apply (simp)
  apply safe
  apply (case_tac "m = n")
  apply (simp)
  apply (case_tac "m < n")
  apply (auto)
done

theorem ggt_kom : "ggt m n = ggt n m"
  apply (case_tac n)
  apply (simp)
  apply safe
  apply (simp add: ggt_mod)
done

theorem ggt_impl : "n \<ge> m \<longrightarrow> ggt n m = ggt(n - m) m"
  apply (case_tac m)
  apply (simp)
  apply (subst ggt_kom)
  apply (simp)
  apply (rule impI)
  apply (subst (2) ggt_kom)
  apply (simp)
  apply (cut_tac n="Suc nat" and m ="n" in  le_mod_geq)
  apply (assumption)
  apply (simp)
done

end


