theory ggt
imports Main
begin

fun ggt :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ggt 0 m = m"
  | "ggt n m = ggt(m mod n) n"

theorem ggt_o [simp] :  "ggt m 0 = m"
  apply(induct_tac m)
  apply(simp)
  apply(simp)
done

lemma ggt_same : "ggt n n = n"
  apply (case_tac n)
  apply (simp)
  apply (simp)
done

lemma ggt_mod : " m > 0 \<longrightarrow> ggt n m =  ggt (n mod m) m"
  apply (case_tac n)
  apply (simp)
  apply safe
  apply (case_tac "m = n")
  apply (simp)
  apply (case_tac "m < n")
  apply (simp)
  apply (auto)
  apply (case_tac m)
  apply (auto)
done

theorem ggt_kom : "ggt m n = ggt n m"
  apply (case_tac n)
  apply (simp)
  apply safe
  apply (simp)
  apply (simp add: ggt_mo)
  apply (insert ggt_mod)
  (*apply (rule sym)
  apply (cut_tac ggt_mod)
  apply (auto)
  apply (rule ggt_mod)
  apply (simp add: ggt_mod)
done*)
sorry

theorem ggt_impl : "n \<ge> m \<longrightarrow> ggt n m = ggt(n - m) m"
  apply (case_tac m)
  apply (simp)
end


