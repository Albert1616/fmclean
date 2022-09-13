
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros hhp h,
  have hh : false := h hhp,
  exact hh,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro np,
  by_contradiction p,
  have newfalse: false:= np p,
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
  intro imp_ou,
  cases imp_ou with hp hq,
  right,
  exact hp,
  left,
  exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro peq,
  split,
  cases peq with p q,
  exact q,
  cases peq with p q,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros impl p,
  cases impl with np q,
  have nnp: false := np p,
  contradiction,
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros impl np,
  cases impl with p q,
  have nnp: false:= np p,
  contradiction,
  exact q, 
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros impl nq p,
  have newq: Q:= impl p,
  have ff: false:= nq newq,
  contradiction,
end

theorem impl_as_contrapositive_converse :--*
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros impl p,
  by_contradiction q,
  have newnp:¬P:=impl q,
  have newfalse: false:=newnp p,
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
  intro impl,
  apply impl,
  right,
  intro np,
  have nporp:P∨¬P,
  left,
  exact np,
  have newfalse:false:=impl nporp,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
 intros impq np,
 have nimpl:P → Q,
 intro p,
 have newfalse:false:=np p,
 contradiction,
 have newP:P:=impq nimpl,
 have newfalse:false:=np newP,
 contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros impl nimpl,
  cases impl with p q,
  cases nimpl with np nq,
  have bool: false:= np p,
  contradiction,
  cases nimpl with np nq,
  have bool: false:= nq q,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros impl bool,
  cases bool with np nq,
  cases impl with p q,
  have newfalse: false:= np p,
  contradiction,
  cases impl with p q,
  have newfalse: false:= nq q,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro impl,
  split,
  intro p,
  apply impl,
  left,
  exact p,
  intro q,
  apply impl,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros impl disj,
  cases disj with p q,
  cases impl with np nq,
  have newfalse:false:=np p,
  contradiction,
  cases impl with np nq,
  have newfalse:false:=nq q,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro impl,
  by_cases q:Q,
  right,
  intro p,
  have pq:P∧Q,
  split,
  exact p,
  exact q,
  have newfalse:false:=impl pq,
  contradiction,
  left,
  assumption,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros impl disj,
  cases impl with nq np,
  cases disj with p q,
  have newfalse: false:= nq q,
  contradiction,
  cases disj with p q,
  have newfalse: false:= np p,
  contradiction,
end

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
  intro impl,
  cases impl with p qr,
  cases qr with q r,
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
  intro impl,
  split,
  cases impl,
  cases impl with p q,
  exact p,
  cases impl with p q,
  exact p,
  cases impl with p q,
  left,
  cases p with p_p p_q,
  exact p_q,
  right,
  cases q with q_p q_q,
  exact q_q,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro impl,
  cases impl with p qer,
  split,
  left,
  assumption, 
  left,
  assumption, 
  cases qer with q r,
  split,
  right,
  exact q,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro impl,
  cases impl with pouq pour,
  cases pouq,
  left,exact pouq,
  cases pour,
  left,
  exact pour,
  right,
  split,
  exact pouq,
  exact pour,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros impl p q,
  apply impl,
  split,
  assumption, 
  assumption,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros impl pq,
  cases pq with p q,
  apply impl,
  exact p,
  exact q,
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
  intro impl,
  cases impl with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro impl,
  cases impl with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro p,
  cases p with p p,
  assumption,
  intro p,
  split,
  assumption, 
  assumption,

end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro p,
  cases p,
  assumption, 
  assumption,
  intro p,
  left,
  assumption,
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
  intros impl x px,
  apply impl,
  existsi x,
  exact px,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros Vx Ex,
  cases Ex with x p,
  have px:¬P x:=Vx x,
  have newfalse:false:=px p,
  contradiction,
end

theorem demorgan_forall :--**
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro Vx,
  by_contradiction nE,
  apply Vx,
  intro x,
  by_contradiction px,
  apply nE,
  existsi x,
  exact px,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros Ex Vx,
  cases Ex with x p,
  have px:P x:=Vx x,
  have newfalse:false:=p px,
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
  intros impl parat,
  cases impl with p np x,
  have px: ¬P p := parat p,
  have newfalse: false:= px np,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro Vx,
  intro Ex,
  cases Ex with x Px,
  have px:P x:=Vx x,
  contradiction,
end

theorem forall_as_neg_exists_converse :--**
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros Ex x,
  by_contradiction npx,
  apply Ex,
  existsi x,
  exact npx,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  rw [ contrapositive_law , doubleneg_law],
  exact demorgan_exists U P,
end

theorem forall_as_neg_exists_law :--**
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,
  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :--**
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
  intro Ex,
  split,
  cases Ex with x px_or_qx,
  existsi x,
  cases px_or_qx with px qx,
  exact px,
  cases Ex with x px_or_qx,
  existsi x,
  cases px_or_qx with px qx,
  exact qx,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro Ex,
  cases Ex with x q,
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
  intro Ex,
  cases Ex with p q,
  cases p with x px,
  existsi x,
  left,
  exact px,
  cases q with x qx,
  existsi x,
  right,
  exact qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro Vx,
  split,
  intro x,
  have pxq:P x ∧ Q x:=Vx x,
  cases pxq with px qx,
  exact px,
  intro x,
  have pxq:P x ∧ Q x:=Vx x,
  cases pxq,
  exact pxq_right,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro Vx,
  intro x,
  split,
  cases Vx with px qx,
  have impx:P x:=px x,
  exact impx,
  cases Vx with px qx,
  have imqx:Q x:=qx x,
  exact imqx,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro Vx,
  intro x,
  cases Vx with px qx,
  left,
  have impx:P x:=px x,
  exact impx,
  right,
  have imqx:Q x:=qx x,
  exact imqx,
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
