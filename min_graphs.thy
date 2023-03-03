theory min_graphs

imports 
"Main"

begin

text\<open>
En el desarrollo de la siguiente teoría utilizamos la representación de grafos dirigidos de la 
teoría Graph\_Theory.thy de L. Noschinski 
\cite{Graph_Theory-AFP}:
\<close>
record ('a,'b) pre_digraph =
  verts :: "'a set"
  arcs :: "'b set"
  tail :: "'b \<Rightarrow> 'a"
  head :: "'b \<Rightarrow> 'a"
  
definition tails:: "('a,'b) pre_digraph \<Rightarrow> 'a set" where
   "tails G \<equiv>  {tail G e |e. e \<in> arcs G }"

definition tails_set :: "('a,'b) pre_digraph \<Rightarrow> 'b set \<Rightarrow> 'a set" where
   "tails_set G E \<equiv>  { tail G e |e. e \<in> E \<and> E \<subseteq> arcs G }"

definition heads:: "('a,'b) pre_digraph \<Rightarrow> 'a set" where
   "heads G \<equiv>  { head G e |e.  e \<in> arcs G }"

definition heads_set:: "('a,'b) pre_digraph \<Rightarrow> 'b set \<Rightarrow> 'a set" where
   "heads_set G E \<equiv>  { head G e |e.  e \<in> E \<and> E \<subseteq> arcs G }"

definition neighbor::  "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
   "neighbor G v u  \<equiv>
   \<exists>e. e\<in> (arcs G) \<and> (( head G e = v \<and> tail G e = u) \<or>
   (head G e  = u \<and> tail G e = v))"

definition neighborhood:: "('a,'b) pre_digraph \<Rightarrow> 'a  \<Rightarrow> 'a set" where
   "neighborhood G v \<equiv> {u |u. neighbor G u v}"

definition bipartite_digraph:: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
   "bipartite_digraph G X Y  \<equiv> 
       (X \<union> Y = (verts G)) \<and>  X \<inter> Y = {} \<and>
       (\<forall>e \<in> (arcs G).(tail G e) \<in> X \<longleftrightarrow> (head G e) \<in> Y)"

definition dir_bipartite_digraph:: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" 
  where
  "dir_bipartite_digraph G X Y  \<equiv> (bipartite_digraph G X Y) \<and> 
   ((tails G = X) \<and>  (\<forall> e1 \<in> arcs G. \<forall> e2 \<in> arcs G. e1 = e2 \<longleftrightarrow> head G e1 = head G e2 \<and> tail G e1 = tail G e2))"  

definition K_E_bipartite_digraph:: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" 
  where
  "K_E_bipartite_digraph G X Y \<equiv>
  (dir_bipartite_digraph G X Y) \<and> (\<forall>x\<in>X.  finite (neighborhood G x))"

definition dirBD_matching:: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where
  "dirBD_matching G X Y E  \<equiv>  
           dir_bipartite_digraph G X Y \<and> (E  \<subseteq>  (arcs G)) \<and>
           (\<forall> e1\<in>E. (\<forall> e2\<in> E.  e1 \<noteq> e2 \<longrightarrow>
           ((head G e1) \<noteq> (head G e2)) \<and> 
           ((tail G e1) \<noteq> (tail G e2))))"

lemma tail_head:
  assumes "dir_bipartite_digraph G X Y" and "e \<in> arcs G" 
  shows "(tail G e) \<in> X \<and> (head G e) \<in> Y" using assms 
     by (unfold dir_bipartite_digraph_def, unfold bipartite_digraph_def, unfold tails_def, auto)

lemma tail_head1:
  assumes "dirBD_matching G X Y E" and "e \<in> E" 
  shows "(tail G e) \<in> X \<and> (head G e) \<in> Y" 
  using assms tail_head[of G X Y e] by(unfold dirBD_matching_def, auto) 

lemma dirBD_matching_tail_edge_unicity:
   "dirBD_matching G X Y E \<longrightarrow>  
    (\<forall>e1 \<in> E. (\<forall> e2\<in> E. (tail G e1 = tail G e2) \<longrightarrow> e1 = e2))"
proof
  assume "dirBD_matching G X Y E"
  thus "\<forall>e1\<in>E. \<forall>e2\<in>E. tail G e1 = tail G e2 \<longrightarrow> e1 = e2"
     by (unfold dirBD_matching_def, auto)
qed

lemma dirBD_matching_head_edge_unicity:
   "dirBD_matching G X Y E \<longrightarrow>  
    (\<forall>e1 \<in> E. (\<forall> e2\<in> E. (head G e1 = head G e2) \<longrightarrow> e1 = e2))"
proof
  assume "dirBD_matching G X Y E"
  thus " \<forall>e1\<in>E. \<forall>e2\<in>E. head G e1 = head G e2 \<longrightarrow> e1 = e2"
     by(unfold dirBD_matching_def, auto)
qed

definition dirBD_perfect_matching::
  "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where
  "dirBD_perfect_matching G X Y E \<equiv> 
   dirBD_matching G X Y E \<and> (tails_set G E = X)"

lemma Edge_unicity_in_dirBD_P_matching1: 
      "\<forall>x\<in>X. dirBD_perfect_matching G X Y E \<longrightarrow> (\<exists>e \<in> E. tail G e = x)"
proof
  fix x 
  assume Hip1: "x \<in> X"
  show "dirBD_perfect_matching G X Y E \<longrightarrow> (\<exists>e\<in>E. tail G e = x)"
  proof
    assume "dirBD_perfect_matching G X Y E"
    hence  "X = tails_set G E"  by(unfold dirBD_perfect_matching_def, auto)
    hence "x \<in> tails_set G E" using Hip1 by auto
    thus "\<exists>e\<in>E. tail G e = x " by(unfold tails_set_def, auto)
  qed
qed

lemma Edge_unicity_in_dirBD_P_matching: 
   "\<forall>x\<in>X. dirBD_perfect_matching G X Y E \<longrightarrow> (\<exists>!e \<in> E. tail G e = x)"
proof
  fix x 
  assume Hip1: "x \<in> X"
  show "dirBD_perfect_matching G X Y E \<longrightarrow> (\<exists>!e \<in> E. tail G e = x)" 
  proof
    assume Hip2: "dirBD_perfect_matching G X Y E" 
    then obtain "\<exists>e. e \<in> E \<and> tail G e = x"
    using Hip1  Edge_unicity_in_dirBD_P_matching1[of X G Y E] by auto
    then obtain e where e: "e \<in> E \<and>  tail G e = x" by auto
    hence a: "e \<in> E \<and>  tail G e = x" by auto
    show "\<exists>!e. e \<in> E \<and> tail G e = x"
    proof
      show  "e \<in> E \<and> tail G e = x"  using a by auto
      next      
      fix e1 
      assume Hip1: "e1 \<in> E \<and> tail G e1 = x"
      hence "tail G e = tail G e1 \<and> e \<in> E  \<and> e1 \<in> E" using a by auto
      moreover 
      have "dirBD_matching G X Y E"
        using Hip2  by(unfold dirBD_perfect_matching_def, auto)
      ultimately
      show "e1 = e" 
        using Hip2 dirBD_matching_tail_edge_unicity[of G X Y E]
        by auto 
    qed
  qed
qed

end
