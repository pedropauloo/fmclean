
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros p np,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro np,
  by_contradiction hboom,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,

  exact doubleneg_elim P,
  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pq,
  cases pq with hp hq,
    right,
    exact hp,

    left,
    exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intros hpq,
  cases hpq with hp hq,
  split,
  exact hq,
  exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro npq,
  intro p,
  cases npq with hnp hq,
  contradiction,
  exact hq
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro pq,
  intro np,
  cases pq with hp hq,
  contradiction,
  exact hq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro pq,
  intro nq,
  intro p,
  have hq : Q := pq p,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro hnqp,
  intro p,
  by_contradiction,
  have np := hnqp h,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  exact impl_as_contrapositive P Q,
  exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro n_p_or_np,
  have h : P ∨ ¬P,
  right, 
  intro np,
  have h2 : P ∨ ¬P,
  left,
  exact np,
  contradiction,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro p_q_p,
  intro np,
  by_cases h : (P → Q),

  have h2 : P := p_q_p h,
  contradiction,

  have h2 : (P → Q),
  intro p,
  contradiction,
  have h3 : P := p_q_p h2,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro p_or_q,
  intro np_or_nq,
  cases np_or_nq with hnp hnq,
  cases p_or_q with hp hq,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro p_and_q,
  intro np_or_nq,
  cases p_and_q with hp hq,
  cases np_or_nq with hnp hnq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro n_p_or_q,
  split,
  
  intro p,
  have h2 : P ∨ Q,
  left,
  exact p,
  contradiction,

  intro q,
  have h2 : P ∨ Q,
  right,
  exact q,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro np_and_nq,
  intro p_or_q,
  cases np_and_nq with hnp hnq,
  cases p_or_q with hp hq,
  contradiction, 
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro p_and_q,
  by_cases q:Q,
  right,

  intro p,
  have hpq: P∧Q,
  split,
  exact p,
  exact q,
  contradiction,

  left,
  exact q,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nq_or_np,
  intro p_and_q,
  cases p_and_q with p q,
  cases nq_or_np with hnq hnp,
  contradiction,
  contradiction,
end

-- try again withou magic
theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  exact demorgan_conj P Q,
  exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro p_and_q_or_r,
  cases p_and_q_or_r with p q_or_r,
  cases q_or_r with q r,
  
  left,
  split,
  exact p,
  exact q,

  right,
  split,
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pq_pr,
  cases pq_pr with p_and_q p_and_r,
  cases p_and_q with p q,
  split,
  exact p,
  left,
  exact q,

  cases p_and_r with p r,
  split,
  exact p,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro p_or_qr,

  cases p_or_qr with p qr,
  split,
  left,
  exact p,
  left,
  exact p,

  cases qr with q r,
  split,
  right,
  exact q,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pq_and_pr,
  cases pq_and_pr with pq pr,
  cases pq with p q,
  left,
  exact p,
  cases pr with p r,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pq_r,
  intro p,
  intro q,
  have h : P ∧ Q,
  split,
  exact p,
  exact q,
  have r : R := pq_r h,
  exact r, 
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro p_q_r,
  intro pq,
  cases pq with p q,
  have q_r : Q → R := p_q_r p,
  have r : R := q_r q,
  exact r, 
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
intro p,
exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pp,
  cases pp with p p,
  exact p,

  intro pp,
  split,
  exact pp,
  exact pp,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split, 
  intro pp,
  cases pp with p p,
  repeat {exact p},
  intro pp,
  left,
  exact pp,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro nex_px,
  intro x,
  intro n_px,
  have h : ∃x, P x,
  existsi x,
  exact n_px,
  contradiction,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro px_npx,
  intro ex_px,
  cases ex_px with x px,
  have h : ¬P x := px_npx x,
  contradiction,
end
theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro pu_px,
  by_contradiction ne,
  apply pu_px,
  intro x,
  by_contradiction npx,
  apply ne,
  existsi x,
  exact npx,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro e_npx,
  intro p_px,
  cases e_npx with x npx,
  have h : P x := p_px x,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  exact demorgan_forall U P,
  exact demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  exact demorgan_exists U P,
  exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro e_px,
  intro p_npx,
  cases e_px with x px,
  have h: ¬P x := p_npx x,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro p_px,
  intro e_npx,
  cases e_npx with x npx,
  have h: P x := p_px x,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros n_e_npx x,
  by_contradiction npx,
  apply n_e_npx,
  existsi x,
  exact npx,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  rw contrapositive_law,
  rw doubleneg_law,
  exact demorgan_exists U P,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,
  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  exact exists_as_neg_forall U P,
  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro e_pxq,
  cases e_pxq with x pxq,
  cases pxq with px qx,
  
  split,
  existsi x,
  exact px,

  existsi x,
  exact qx,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro e_px_qx,
  cases e_px_qx with x q,
  cases q with px qx,
  left,
  existsi x,
  exact px,
  right,
  existsi x,
  exact qx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro epx_eqx,
  cases epx_eqx with epx eqx,

  cases epx with x px,
  existsi x,
  left,
  exact px,

  cases eqx with x qx,
  existsi x,
  right,
  exact qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro p_px_qx,
  split,
  intro x,
  have h : P x ∧ Q x := p_px_qx x,
  cases h with px qx,
  exact px,

  intro x,
  have h: P x ∧ Q x := p_px_qx x,
  cases h with px qx,
  exact qx,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro p_px_qx,
  intro x,
  cases p_px_qx with px qx,
  
  split,
  have h : P x := px x,
  exact h,

  have h : Q x := qx x,
  exact h
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro p_px_qx,
  intro x,
  cases p_px_qx with px qx,

  have h : P x := px x,
  left,
  exact h,

  have h : Q x := qx x,
  right,
  exact h,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
