theory Koenig_Egervary

imports Hall_Th_Graph_Theo

begin


subsection‹König-Egervary theorem›

text‹
\begin{teorema}[König-Egervary]\label{Konig-Egervary}
If $G$ is a bipartite graph, then the maximum size of a matching in $G$ equals the minimum size of a
vertex cover $G$.
\end{teorema}
›

text‹
\begin{definicion}
A vertex cover of a graph $G$ is a set $Q\subseteq V(G)$ that contains at least one
endpoint of every edge. The vertices in $Q$ \emph{cover} $E(G)$.
\end{definition}
›

definition  vertex_cover:: "('a,'b) pre_digraph ⇒ 'a set ⇒ bool"
  where
  "vertex_cover G Q  ≡ (Q  ⊆  (verts G)) ∧ (∀ e ∈ (arcs G). (head G e)∈ Q ∨ (tail G e) ∈ Q)"
 "('a,'b) pre_digraph ⇒ 'a set ⇒ bool"
  where
  "vertex_cover G Q  ≡ (Q  ⊆  (verts G)) ∧ (∀ e ∈ (arcs G). (head G e)∈ Q ∨ (tail G e) ∈ Q)"

lemma assumes "dirBD_matching G X Y E" and  "vertex_cover G Q"  and "finite Q"
  shows "card E ≤ card Q"
  sorry

(* Un vertice no cubre dos arcos distintos *)
lemma vertex_cover:
  assumes "dirBD_matching G X Y E" 
  shows "∀v∈(verts G). ∀e1∈E. ∀e2∈E. e1 ≠ e2 ⟶
          (((tail G e1) = v ∨ (head G e1) = v) ⟶ ((tail G e2) ≠ v ∧ (head G e2) ≠ v))"
proof
  fix v
  assume h0: "v∈(verts G)" 
  show "∀e1∈E.
            ∀e2∈E.
               e1 ≠ e2 ⟶
               (((tail G e1) = v ∨ (head G e1) = v) ⟶ ((tail G e2) ≠ v ∧ (head G e2) ≠ v))"              
  proof
    fix e1
    assume h1: "e1 ∈ E" 
    show "∀e2∈E.
           e1 ≠ e2 ⟶
           (((tail G e1) = v ∨ (head G e1) = v) ⟶ ((tail G e2) ≠ v ∧ (head G e2) ≠ v))"
    proof
      fix e2
      assume h2: "e2 ∈ E"
      show   "e1 ≠ e2 ⟶
              (((tail G e1) = v ∨ (head G e1) = v) ⟶ ((tail G e2) ≠ v ∧ (head G e2) ≠ v))"
      proof
        have 1: "tail G e1 ∈ X ∧ head G e1 ∈ Y" 
          using h1 assms tail_head1[of G X Y E e1] by auto
         have 2: "tail G e2 ∈ X ∧ head G e2 ∈ Y" 
          using h2 assms tail_head1[of G X Y E e2] by auto
        assume *: "e1 ≠ e2"
        show  "((tail G e1) = v ∨ (head G e1) = v) ⟶ ((tail G e2) ≠ v ∧ (head G e2) ≠ v)"
        proof(rule ccontr)
          assume
          hip: "¬(((tail G e1) = v ∨ (head G e1) = v) ⟶ ((tail G e2) ≠ v ∧ (head G e2) ≠ v))"                       
          show False
          proof-
            have "(tail G e1 = v ∨ head G e1 = v) ∧ (tail G e2 = v ∨ head G e2 = v)" 
              using hip by auto 
            hence "((tail G e1 = v ∨ head G e1 = v) ∧ (tail G e2 = v)) ∨
                   ((tail G e1 = v ∨ head G e1 = v) ∧ (head G e2 = v))" 
              by auto
            thus False 
            proof(rule disjE)
              assume hip1: "(tail G e1 = v ∨ head G e1 = v) ∧ tail G e2 = v"
              show  False 
              proof-
                have "(tail G e1 = v ∧ tail G e2 = v) ∨ (head G e1 = v ∧ tail G e2 = v)" 
                  using hip1 by auto
                thus False 
                proof(rule disjE)
                  assume "tail G e1 = v ∧ tail G e2 = v"
                  hence "tail G e1 =  tail G e2" by auto
                  thus False using h1 h2 * assms by(unfold dirBD_matching_def, auto) 
                next 
                  assume "head G e1 = v ∧ tail G e2 = v"
                  hence "v∈X ∧ v∈Y" using 1 2 by auto
                  thus False using assms 
                    by(unfold dirBD_matching_def, unfold dir_bipartite_digraph_def,
                       unfold _bipartite_digraph_def, auto)
                qed
              qed 
            next
              assume hip2: "(tail G e1 = v ∨ head G e1 = v) ∧ head G e2 = v"
              show  False 
              proof-
                have "(tail G e1 = v ∧ head G e2 = v) ∨ (head G e1 = v ∧ head G e2 = v)" 
                  using hip2 by auto
                thus False 
                proof(rule disjE)
                  assume "tail G e1 = v ∧ head G e2 = v"
                  hence "v∈X ∧ v∈Y" using 1 2 by auto
                  thus False using assms 
                    by(unfold dirBD_matching_def, unfold dir_bipartite_digraph_def,
                       unfold _bipartite_digraph_def, auto) 
                next 
                  assume "head G e1 = v ∧ head G e2 = v"
                  thus False using h1 h2 * assms by(unfold dirBD_matching_def, auto) 
                qed
              qed 
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma vert_cover:
  assumes "(dirBD_perfect_matching G X Y E)"  
  shows   "vertex_cover G X"
proof(unfold vertex_cover_def, rule conjI)
  show "X ⊆ verts G"  using assms
    by(unfold dirBD_perfect_matching_def, unfold dirBD_matching_def,
       unfold  dir_bipartite_digraph_def, unfold bipartite_digraph_def, auto)
next 
  show "∀e∈arcs G. head G e ∈ X ∨ tail G e ∈ X" 
  proof
    fix e
    assume hip: "e ∈ arcs G"
    show "head G e ∈ X ∨ tail G e ∈ X"
    proof-
      have "tail G e ∈ X" using assms hip
        by(unfold dirBD_perfect_matching_def, unfold dirBD_matching_def,
           unfold dir_bipartite_digraph_def, unfold tails_def, auto )
      thus ?thesis by auto
    qed
  qed
qed


definition f_matching_cover :: "('a,'b) pre_digraph ⇒ 'a set ⇒ ('b  ⇒ 'a)"
  where 
  "f_matching_cover G Q = (λe. (THE v. v ∈ Q ∧ (tail G e = v ∨ head G e = v)))"

lemma matching_cover_inj_on:
"(dirBD_matching G X Y E ∧ (vertex_cover G Q)) ⟶ inj_on (f_matching_cover G Q) E"
  sorry

lemma f_matching_subset_cover:
"(f_matching_cover G Q) ` E ⊆ Q"
  sorry

lemma assumes "dirBD_matching G X Y E" and  "vertex_cover G Q"  and "finite Q"
  shows "card E ≤ card Q" 
  using matching_cover_inj_on[of G X Y E Q] f_matching_subset_cover[of G Q E] assms card_inj_on_le 
  by auto


section‹ König-Egervary infinito for countable graphs›

text‹
In a bipartite graph $G = (X,Y,E)$  we define the demand $D(Z)$ of a set of
vertices $Z⊆Y$ by $D(Z) = \{v\in X | N(v) ⊆ Z}$, the set of vertices in $X$  all
of whose neighbors are in $Z$.
 ›
 
definition demand:: "('a,'b) pre_digraph ⇒ 'a set ⇒ 'a set"
  where
  "demand G Z ≡ {v |v. (v ∈ tails G) ∧ neighborhood G v ⊆ Z}"  

text‹
\begin{lema}
Let $G = (X,Y,E)$ be a  bipartite graph. "dirBD_matching G X Y E
$F = \{Z⊆Y | there is a matching in G of $Z$ into  D(Z) \}$
has a maximum element, ie., one containg all the others.
\end{lema}
 ›

definition  dirBD_sub_matching::
            "('a,'b) pre_digraph ⇒ 'a set ⇒ 'a set ⇒ 'a set ⇒ 'a set ⇒ 'b set ⇒ bool"
  where
  "dirBD_sub_matching G X Y W T E ≡ 
                      (dirBD_matching G X Y E) ∧ (W ⊆ tails_set G E) ∧ (T ⊆ heads_set G E)" 

definition  matchings_demands::
            "('a,'b) pre_digraph ⇒ 'a set ⇒ 'a set  ⇒ 'a set set"
  where "matchings_demands G X Y  ≡ {Z|Z. ∃E. (dirBD_sub_matching G X Y E (demand G Z) Z)}"

lemma  
  fixes  G :: "('a, 'b) pre_digraph"
  assumes  "verts G ≠ {}" and "arcs G ≠ {}" 
  shows  "∃W∈(matchings_demands G X Y).∀T∈(matchings_demands G X Y). T⊆W"

(*<*)
end
(*>*)
