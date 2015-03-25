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
  apply (subgoal_tac (m = n \<and> m < n \<and> m > n))

theorem ggt_kom : "ggt m n = ggt n m"
  apply (case_tac n)
  apply (simp)
  apply (auto)

theorem ggt_impl : "n \<ge> m \<longrightarrow> ggt n m = ggt(n - m) m"

end


