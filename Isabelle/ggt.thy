theory ggt
imports Main
begin
fun ggt :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ggt 0 m = m"
  | "ggt n m = ggt(m mod n) n"

theorem ggt_o [simp] : "\<forall> n. n = 0 \<longrightarrow> ggt m n = m"
apply(simp)
apply(induct_tac m)
apply(simp)
apply(simp)
done

lemma ggt_mod : "n \<noteq>  0 \<longrightarrow> ggt m n = ggt n (m mod n)"
apply(rule_tac impI)

theorem ggt_kom : "ggt m n = ggt n m"
apply(induction m)
apply(simp)

done

end


