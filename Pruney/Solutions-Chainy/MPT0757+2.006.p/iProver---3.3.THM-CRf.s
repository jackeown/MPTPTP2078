%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:11 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   63 (  97 expanded)
%              Number of clauses        :   26 (  27 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  222 ( 412 expanded)
%              Number of equality atoms :   38 (  80 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK0(X0),X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f29,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ~ ( ~ r2_xboole_0(X1,X0)
                & X0 != X1
                & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
     => ( ~ r2_xboole_0(sK2,X0)
        & sK2 != X0
        & ~ r2_xboole_0(X0,sK2)
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r2_xboole_0(X1,sK1)
          & sK1 != X1
          & ~ r2_xboole_0(sK1,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    & sK1 != sK2
    & ~ r2_xboole_0(sK1,sK2)
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f26,f25])).

fof(f40,plain,(
    ~ r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ~ r2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_275,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_348,plain,
    ( sK1 != X0
    | sK1 = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_349,plain,
    ( sK1 != sK1
    | sK1 = sK2
    | sK2 != sK1 ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_185,plain,
    ( r1_ordinal1(X0,X1)
    | r1_tarski(X2,X3)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X3)
    | X1 != X2
    | X0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_186,plain,
    ( r1_ordinal1(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_6,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_190,plain,
    ( ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | r1_tarski(X1,X0)
    | r1_ordinal1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_186,c_6])).

cnf(c_191,plain,
    ( r1_ordinal1(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_8,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_214,plain,
    ( r1_tarski(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_191,c_8])).

cnf(c_344,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK2,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_274,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_281,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,negated_conjecture,
    ( ~ r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_168,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_169,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK2 = sK1 ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_10,negated_conjecture,
    ( ~ r2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_157,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_158,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(unflattening,[status(thm)],[c_157])).

cnf(c_11,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_13,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_349,c_344,c_281,c_169,c_158,c_11,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:07:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.64/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.64/0.98  
% 0.64/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.64/0.98  
% 0.64/0.98  ------  iProver source info
% 0.64/0.98  
% 0.64/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.64/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.64/0.98  git: non_committed_changes: false
% 0.64/0.98  git: last_make_outside_of_git: false
% 0.64/0.98  
% 0.64/0.98  ------ 
% 0.64/0.98  
% 0.64/0.98  ------ Input Options
% 0.64/0.98  
% 0.64/0.98  --out_options                           all
% 0.64/0.98  --tptp_safe_out                         true
% 0.64/0.98  --problem_path                          ""
% 0.64/0.98  --include_path                          ""
% 0.64/0.98  --clausifier                            res/vclausify_rel
% 0.64/0.98  --clausifier_options                    --mode clausify
% 0.64/0.98  --stdin                                 false
% 0.64/0.98  --stats_out                             all
% 0.64/0.98  
% 0.64/0.98  ------ General Options
% 0.64/0.98  
% 0.64/0.98  --fof                                   false
% 0.64/0.98  --time_out_real                         305.
% 0.64/0.98  --time_out_virtual                      -1.
% 0.64/0.98  --symbol_type_check                     false
% 0.64/0.98  --clausify_out                          false
% 0.64/0.98  --sig_cnt_out                           false
% 0.64/0.98  --trig_cnt_out                          false
% 0.64/0.98  --trig_cnt_out_tolerance                1.
% 0.64/0.98  --trig_cnt_out_sk_spl                   false
% 0.64/0.98  --abstr_cl_out                          false
% 0.64/0.98  
% 0.64/0.98  ------ Global Options
% 0.64/0.98  
% 0.64/0.98  --schedule                              default
% 0.64/0.98  --add_important_lit                     false
% 0.64/0.98  --prop_solver_per_cl                    1000
% 0.64/0.98  --min_unsat_core                        false
% 0.64/0.98  --soft_assumptions                      false
% 0.64/0.98  --soft_lemma_size                       3
% 0.64/0.98  --prop_impl_unit_size                   0
% 0.64/0.98  --prop_impl_unit                        []
% 0.64/0.98  --share_sel_clauses                     true
% 0.64/0.98  --reset_solvers                         false
% 0.64/0.98  --bc_imp_inh                            [conj_cone]
% 0.64/0.98  --conj_cone_tolerance                   3.
% 0.64/0.98  --extra_neg_conj                        none
% 0.64/0.98  --large_theory_mode                     true
% 0.64/0.98  --prolific_symb_bound                   200
% 0.64/0.98  --lt_threshold                          2000
% 0.64/0.98  --clause_weak_htbl                      true
% 0.64/0.98  --gc_record_bc_elim                     false
% 0.64/0.98  
% 0.64/0.98  ------ Preprocessing Options
% 0.64/0.98  
% 0.64/0.98  --preprocessing_flag                    true
% 0.64/0.98  --time_out_prep_mult                    0.1
% 0.64/0.98  --splitting_mode                        input
% 0.64/0.98  --splitting_grd                         true
% 0.64/0.98  --splitting_cvd                         false
% 0.64/0.98  --splitting_cvd_svl                     false
% 0.64/0.98  --splitting_nvd                         32
% 0.64/0.98  --sub_typing                            true
% 0.64/0.98  --prep_gs_sim                           true
% 0.64/0.98  --prep_unflatten                        true
% 0.64/0.98  --prep_res_sim                          true
% 0.64/0.98  --prep_upred                            true
% 0.64/0.98  --prep_sem_filter                       exhaustive
% 0.64/0.98  --prep_sem_filter_out                   false
% 0.64/0.98  --pred_elim                             true
% 0.64/0.98  --res_sim_input                         true
% 0.64/0.98  --eq_ax_congr_red                       true
% 0.64/0.98  --pure_diseq_elim                       true
% 0.64/0.98  --brand_transform                       false
% 0.64/0.98  --non_eq_to_eq                          false
% 0.64/0.98  --prep_def_merge                        true
% 0.64/0.98  --prep_def_merge_prop_impl              false
% 0.64/0.98  --prep_def_merge_mbd                    true
% 0.64/0.98  --prep_def_merge_tr_red                 false
% 0.64/0.98  --prep_def_merge_tr_cl                  false
% 0.64/0.98  --smt_preprocessing                     true
% 0.64/0.98  --smt_ac_axioms                         fast
% 0.64/0.98  --preprocessed_out                      false
% 0.64/0.98  --preprocessed_stats                    false
% 0.64/0.98  
% 0.64/0.98  ------ Abstraction refinement Options
% 0.64/0.98  
% 0.64/0.98  --abstr_ref                             []
% 0.64/0.98  --abstr_ref_prep                        false
% 0.64/0.98  --abstr_ref_until_sat                   false
% 0.64/0.98  --abstr_ref_sig_restrict                funpre
% 0.64/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.64/0.98  --abstr_ref_under                       []
% 0.64/0.98  
% 0.64/0.98  ------ SAT Options
% 0.64/0.98  
% 0.64/0.98  --sat_mode                              false
% 0.64/0.98  --sat_fm_restart_options                ""
% 0.64/0.98  --sat_gr_def                            false
% 0.64/0.98  --sat_epr_types                         true
% 0.64/0.98  --sat_non_cyclic_types                  false
% 0.64/0.98  --sat_finite_models                     false
% 0.64/0.98  --sat_fm_lemmas                         false
% 0.64/0.98  --sat_fm_prep                           false
% 0.64/0.98  --sat_fm_uc_incr                        true
% 0.64/0.98  --sat_out_model                         small
% 0.64/0.98  --sat_out_clauses                       false
% 0.64/0.98  
% 0.64/0.98  ------ QBF Options
% 0.64/0.98  
% 0.64/0.98  --qbf_mode                              false
% 0.64/0.98  --qbf_elim_univ                         false
% 0.64/0.98  --qbf_dom_inst                          none
% 0.64/0.98  --qbf_dom_pre_inst                      false
% 0.64/0.98  --qbf_sk_in                             false
% 0.64/0.98  --qbf_pred_elim                         true
% 0.64/0.98  --qbf_split                             512
% 0.64/0.98  
% 0.64/0.98  ------ BMC1 Options
% 0.64/0.98  
% 0.64/0.98  --bmc1_incremental                      false
% 0.64/0.98  --bmc1_axioms                           reachable_all
% 0.64/0.98  --bmc1_min_bound                        0
% 0.64/0.98  --bmc1_max_bound                        -1
% 0.64/0.98  --bmc1_max_bound_default                -1
% 0.64/0.98  --bmc1_symbol_reachability              true
% 0.64/0.98  --bmc1_property_lemmas                  false
% 0.64/0.98  --bmc1_k_induction                      false
% 0.64/0.98  --bmc1_non_equiv_states                 false
% 0.64/0.98  --bmc1_deadlock                         false
% 0.64/0.98  --bmc1_ucm                              false
% 0.64/0.98  --bmc1_add_unsat_core                   none
% 0.64/0.98  --bmc1_unsat_core_children              false
% 0.64/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.64/0.98  --bmc1_out_stat                         full
% 0.64/0.98  --bmc1_ground_init                      false
% 0.64/0.98  --bmc1_pre_inst_next_state              false
% 0.64/0.98  --bmc1_pre_inst_state                   false
% 0.64/0.98  --bmc1_pre_inst_reach_state             false
% 0.64/0.98  --bmc1_out_unsat_core                   false
% 0.64/0.98  --bmc1_aig_witness_out                  false
% 0.64/0.98  --bmc1_verbose                          false
% 0.64/0.98  --bmc1_dump_clauses_tptp                false
% 0.64/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.64/0.98  --bmc1_dump_file                        -
% 0.64/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.64/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.64/0.98  --bmc1_ucm_extend_mode                  1
% 0.64/0.98  --bmc1_ucm_init_mode                    2
% 0.64/0.98  --bmc1_ucm_cone_mode                    none
% 0.64/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.64/0.98  --bmc1_ucm_relax_model                  4
% 0.64/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.64/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.64/0.98  --bmc1_ucm_layered_model                none
% 0.64/0.98  --bmc1_ucm_max_lemma_size               10
% 0.64/0.98  
% 0.64/0.98  ------ AIG Options
% 0.64/0.98  
% 0.64/0.98  --aig_mode                              false
% 0.64/0.98  
% 0.64/0.98  ------ Instantiation Options
% 0.64/0.98  
% 0.64/0.98  --instantiation_flag                    true
% 0.64/0.98  --inst_sos_flag                         false
% 0.64/0.98  --inst_sos_phase                        true
% 0.64/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.64/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.64/0.98  --inst_lit_sel_side                     num_symb
% 0.64/0.98  --inst_solver_per_active                1400
% 0.64/0.98  --inst_solver_calls_frac                1.
% 0.64/0.98  --inst_passive_queue_type               priority_queues
% 0.64/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.64/0.98  --inst_passive_queues_freq              [25;2]
% 0.64/0.98  --inst_dismatching                      true
% 0.64/0.98  --inst_eager_unprocessed_to_passive     true
% 0.64/0.98  --inst_prop_sim_given                   true
% 0.64/0.98  --inst_prop_sim_new                     false
% 0.64/0.98  --inst_subs_new                         false
% 0.64/0.98  --inst_eq_res_simp                      false
% 0.64/0.98  --inst_subs_given                       false
% 0.64/0.98  --inst_orphan_elimination               true
% 0.64/0.98  --inst_learning_loop_flag               true
% 0.64/0.98  --inst_learning_start                   3000
% 0.64/0.98  --inst_learning_factor                  2
% 0.64/0.98  --inst_start_prop_sim_after_learn       3
% 0.64/0.98  --inst_sel_renew                        solver
% 0.64/0.98  --inst_lit_activity_flag                true
% 0.64/0.98  --inst_restr_to_given                   false
% 0.64/0.98  --inst_activity_threshold               500
% 0.64/0.98  --inst_out_proof                        true
% 0.64/0.98  
% 0.64/0.98  ------ Resolution Options
% 0.64/0.98  
% 0.64/0.98  --resolution_flag                       true
% 0.64/0.98  --res_lit_sel                           adaptive
% 0.64/0.98  --res_lit_sel_side                      none
% 0.64/0.98  --res_ordering                          kbo
% 0.64/0.98  --res_to_prop_solver                    active
% 0.64/0.98  --res_prop_simpl_new                    false
% 0.64/0.98  --res_prop_simpl_given                  true
% 0.64/0.98  --res_passive_queue_type                priority_queues
% 0.64/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.64/0.98  --res_passive_queues_freq               [15;5]
% 0.64/0.98  --res_forward_subs                      full
% 0.64/0.98  --res_backward_subs                     full
% 0.64/0.98  --res_forward_subs_resolution           true
% 0.64/0.98  --res_backward_subs_resolution          true
% 0.64/0.98  --res_orphan_elimination                true
% 0.64/0.98  --res_time_limit                        2.
% 0.64/0.98  --res_out_proof                         true
% 0.64/0.98  
% 0.64/0.98  ------ Superposition Options
% 0.64/0.98  
% 0.64/0.98  --superposition_flag                    true
% 0.64/0.98  --sup_passive_queue_type                priority_queues
% 0.64/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.64/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.64/0.98  --demod_completeness_check              fast
% 0.64/0.98  --demod_use_ground                      true
% 0.64/0.98  --sup_to_prop_solver                    passive
% 0.64/0.98  --sup_prop_simpl_new                    true
% 0.64/0.98  --sup_prop_simpl_given                  true
% 0.64/0.98  --sup_fun_splitting                     false
% 0.64/0.98  --sup_smt_interval                      50000
% 0.64/0.98  
% 0.64/0.98  ------ Superposition Simplification Setup
% 0.64/0.98  
% 0.64/0.98  --sup_indices_passive                   []
% 0.64/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.64/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.98  --sup_full_bw                           [BwDemod]
% 0.64/0.98  --sup_immed_triv                        [TrivRules]
% 0.64/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.64/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.98  --sup_immed_bw_main                     []
% 0.64/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.64/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/0.98  
% 0.64/0.98  ------ Combination Options
% 0.64/0.98  
% 0.64/0.98  --comb_res_mult                         3
% 0.64/0.98  --comb_sup_mult                         2
% 0.64/0.98  --comb_inst_mult                        10
% 0.64/0.98  
% 0.64/0.98  ------ Debug Options
% 0.64/0.98  
% 0.64/0.98  --dbg_backtrace                         false
% 0.64/0.98  --dbg_dump_prop_clauses                 false
% 0.64/0.98  --dbg_dump_prop_clauses_file            -
% 0.64/0.98  --dbg_out_stat                          false
% 0.64/0.98  ------ Parsing...
% 0.64/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.64/0.98  
% 0.64/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.64/0.98  
% 0.64/0.98  ------ Preprocessing...------  preprocesses with Option_epr_non_horn_eq
% 0.64/0.98   gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e ------  preprocesses with Option_epr_non_horn_eq
% 0.64/0.98  
% 0.64/0.98  
% 0.64/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.64/0.98  ------ Proving...
% 0.64/0.98  ------ Problem Properties 
% 0.64/0.98  
% 0.64/0.98  
% 0.64/0.98  clauses                                 6
% 0.64/0.98  conjectures                             3
% 0.64/0.98  EPR                                     6
% 0.64/0.98  Horn                                    5
% 0.64/0.98  unary                                   4
% 0.64/0.98  binary                                  1
% 0.64/0.98  lits                                    10
% 0.64/0.98  lits eq                                 2
% 0.64/0.98  fd_pure                                 0
% 0.64/0.98  fd_pseudo                               0
% 0.64/0.98  fd_cond                                 0
% 0.64/0.98  fd_pseudo_cond                          0
% 0.64/0.98  AC symbols                              0
% 0.64/0.98  
% 0.64/0.98  ------ Schedule EPR non Horn eq is on
% 0.64/0.98  
% 0.64/0.98  ------ Option_epr_non_horn_eq Time Limit: Unbounded
% 0.64/0.98  
% 0.64/0.98  
% 0.64/0.98  ------ 
% 0.64/0.98  Current options:
% 0.64/0.98  ------ 
% 0.64/0.98  
% 0.64/0.98  ------ Input Options
% 0.64/0.98  
% 0.64/0.98  --out_options                           all
% 0.64/0.98  --tptp_safe_out                         true
% 0.64/0.98  --problem_path                          ""
% 0.64/0.98  --include_path                          ""
% 0.64/0.98  --clausifier                            res/vclausify_rel
% 0.64/0.98  --clausifier_options                    --mode clausify
% 0.64/0.98  --stdin                                 false
% 0.64/0.98  --stats_out                             all
% 0.64/0.98  
% 0.64/0.98  ------ General Options
% 0.64/0.98  
% 0.64/0.98  --fof                                   false
% 0.64/0.98  --time_out_real                         305.
% 0.64/0.98  --time_out_virtual                      -1.
% 0.64/0.98  --symbol_type_check                     false
% 0.64/0.98  --clausify_out                          false
% 0.64/0.98  --sig_cnt_out                           false
% 0.64/0.98  --trig_cnt_out                          false
% 0.64/0.98  --trig_cnt_out_tolerance                1.
% 0.64/0.98  --trig_cnt_out_sk_spl                   false
% 0.64/0.98  --abstr_cl_out                          false
% 0.64/0.98  
% 0.64/0.98  ------ Global Options
% 0.64/0.98  
% 0.64/0.98  --schedule                              none
% 0.64/0.98  --add_important_lit                     false
% 0.64/0.98  --prop_solver_per_cl                    1000
% 0.64/0.98  --min_unsat_core                        false
% 0.64/0.98  --soft_assumptions                      false
% 0.64/0.98  --soft_lemma_size                       3
% 0.64/0.98  --prop_impl_unit_size                   0
% 0.64/0.98  --prop_impl_unit                        []
% 0.64/0.98  --share_sel_clauses                     false
% 0.64/0.98  --reset_solvers                         false
% 0.64/0.98  --bc_imp_inh                            [conj_cone]
% 0.64/0.98  --conj_cone_tolerance                   3.
% 0.64/0.98  --extra_neg_conj                        none
% 0.64/0.98  --large_theory_mode                     true
% 0.64/0.98  --prolific_symb_bound                   500
% 0.64/0.98  --lt_threshold                          2000
% 0.64/0.98  --clause_weak_htbl                      true
% 0.64/0.98  --gc_record_bc_elim                     false
% 0.64/0.98  
% 0.64/0.98  ------ Preprocessing Options
% 0.64/0.98  
% 0.64/0.98  --preprocessing_flag                    true
% 0.64/0.98  --time_out_prep_mult                    0.2
% 0.64/0.98  --splitting_mode                        input
% 0.64/0.98  --splitting_grd                         true
% 0.64/0.98  --splitting_cvd                         false
% 0.64/0.98  --splitting_cvd_svl                     true
% 0.64/0.98  --splitting_nvd                         128
% 0.64/0.98  --sub_typing                            true
% 0.64/0.98  --prep_gs_sim                           false
% 0.64/0.98  --prep_unflatten                        true
% 0.64/0.98  --prep_res_sim                          false
% 0.64/0.98  --prep_upred                            true
% 0.64/0.98  --prep_sem_filter                       neg
% 0.64/0.98  --prep_sem_filter_out                   false
% 0.64/0.98  --pred_elim                             true
% 0.64/0.98  --res_sim_input                         false
% 0.64/0.98  --eq_ax_congr_red                       true
% 0.64/0.98  --pure_diseq_elim                       true
% 0.64/0.98  --brand_transform                       false
% 0.64/0.98  --non_eq_to_eq                          false
% 0.64/0.98  --prep_def_merge                        false
% 0.64/0.98  --prep_def_merge_prop_impl              false
% 0.64/0.98  --prep_def_merge_mbd                    false
% 0.64/0.98  --prep_def_merge_tr_red                 false
% 0.64/0.98  --prep_def_merge_tr_cl                  false
% 0.64/0.98  --smt_preprocessing                     true
% 0.64/0.98  --smt_ac_axioms                         fast
% 0.64/0.98  --preprocessed_out                      false
% 0.64/0.98  --preprocessed_stats                    false
% 0.64/0.98  
% 0.64/0.98  ------ Abstraction refinement Options
% 0.64/0.98  
% 0.64/0.98  --abstr_ref                             []
% 0.64/0.98  --abstr_ref_prep                        false
% 0.64/0.98  --abstr_ref_until_sat                   false
% 0.64/0.98  --abstr_ref_sig_restrict                funpre
% 0.64/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.64/0.98  --abstr_ref_under                       []
% 0.64/0.98  
% 0.64/0.98  ------ SAT Options
% 0.64/0.98  
% 0.64/0.98  --sat_mode                              false
% 0.64/0.98  --sat_fm_restart_options                ""
% 0.64/0.98  --sat_gr_def                            false
% 0.64/0.98  --sat_epr_types                         true
% 0.64/0.98  --sat_non_cyclic_types                  false
% 0.64/0.98  --sat_finite_models                     false
% 0.64/0.98  --sat_fm_lemmas                         false
% 0.64/0.98  --sat_fm_prep                           false
% 0.64/0.98  --sat_fm_uc_incr                        true
% 0.64/0.98  --sat_out_model                         small
% 0.64/0.98  --sat_out_clauses                       false
% 0.64/0.98  
% 0.64/0.98  ------ QBF Options
% 0.64/0.98  
% 0.64/0.98  --qbf_mode                              false
% 0.64/0.98  --qbf_elim_univ                         false
% 0.64/0.98  --qbf_dom_inst                          none
% 0.64/0.98  --qbf_dom_pre_inst                      false
% 0.64/0.98  --qbf_sk_in                             false
% 0.64/0.98  --qbf_pred_elim                         true
% 0.64/0.98  --qbf_split                             512
% 0.64/0.98  
% 0.64/0.98  ------ BMC1 Options
% 0.64/0.98  
% 0.64/0.98  --bmc1_incremental                      false
% 0.64/0.98  --bmc1_axioms                           reachable_all
% 0.64/0.98  --bmc1_min_bound                        0
% 0.64/0.98  --bmc1_max_bound                        -1
% 0.64/0.98  --bmc1_max_bound_default                -1
% 0.64/0.98  --bmc1_symbol_reachability              true
% 0.64/0.98  --bmc1_property_lemmas                  false
% 0.64/0.98  --bmc1_k_induction                      false
% 0.64/0.98  --bmc1_non_equiv_states                 false
% 0.64/0.98  --bmc1_deadlock                         false
% 0.64/0.98  --bmc1_ucm                              false
% 0.64/0.98  --bmc1_add_unsat_core                   none
% 0.64/0.98  --bmc1_unsat_core_children              false
% 0.64/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.64/0.98  --bmc1_out_stat                         full
% 0.64/0.98  --bmc1_ground_init                      false
% 0.64/0.98  --bmc1_pre_inst_next_state              false
% 0.64/0.98  --bmc1_pre_inst_state                   false
% 0.64/0.98  --bmc1_pre_inst_reach_state             false
% 0.64/0.98  --bmc1_out_unsat_core                   false
% 0.64/0.98  --bmc1_aig_witness_out                  false
% 0.64/0.98  --bmc1_verbose                          false
% 0.64/0.98  --bmc1_dump_clauses_tptp                false
% 0.64/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.64/0.98  --bmc1_dump_file                        -
% 0.64/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.64/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.64/0.98  --bmc1_ucm_extend_mode                  1
% 0.64/0.98  --bmc1_ucm_init_mode                    2
% 0.64/0.98  --bmc1_ucm_cone_mode                    none
% 0.64/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.64/0.98  --bmc1_ucm_relax_model                  4
% 0.64/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.64/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.64/0.98  --bmc1_ucm_layered_model                none
% 0.64/0.98  --bmc1_ucm_max_lemma_size               10
% 0.64/0.98  
% 0.64/0.98  ------ AIG Options
% 0.64/0.98  
% 0.64/0.98  --aig_mode                              false
% 0.64/0.98  
% 0.64/0.98  ------ Instantiation Options
% 0.64/0.98  
% 0.64/0.98  --instantiation_flag                    true
% 0.64/0.98  --inst_sos_flag                         false
% 0.64/0.98  --inst_sos_phase                        true
% 0.64/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.64/0.98  --inst_lit_sel                          [+non_prol_conj_symb;+prop]
% 0.64/0.98  --inst_lit_sel_side                     num_var
% 0.64/0.98  --inst_solver_per_active                1400
% 0.64/0.98  --inst_solver_calls_frac                1.
% 0.64/0.98  --inst_passive_queue_type               priority_queues
% 0.64/0.98  --inst_passive_queues                   [[-has_eq;+conj_symb;-num_lits];[+conj_non_prolific_symb;-num_lits;-conj_dist]]
% 0.64/0.98  --inst_passive_queues_freq              [10;2]
% 0.64/0.98  --inst_dismatching                      false
% 0.64/0.98  --inst_eager_unprocessed_to_passive     true
% 0.64/0.98  --inst_prop_sim_given                   false
% 0.64/0.98  --inst_prop_sim_new                     false
% 0.64/0.98  --inst_subs_new                         false
% 0.64/0.98  --inst_eq_res_simp                      false
% 0.64/0.98  --inst_subs_given                       false
% 0.64/0.98  --inst_orphan_elimination               true
% 0.64/0.98  --inst_learning_loop_flag               true
% 0.64/0.98  --inst_learning_start                   100
% 0.64/0.98  --inst_learning_factor                  8
% 0.64/0.98  --inst_start_prop_sim_after_learn       10
% 0.64/0.98  --inst_sel_renew                        solver
% 0.64/0.98  --inst_lit_activity_flag                false
% 0.64/0.98  --inst_restr_to_given                   false
% 0.64/0.98  --inst_activity_threshold               1000
% 0.64/0.98  --inst_out_proof                        true
% 0.64/0.98  
% 0.64/0.98  ------ Resolution Options
% 0.64/0.98  
% 0.64/0.98  --resolution_flag                       true
% 0.64/0.98  --res_lit_sel                           neg_nrc
% 0.64/0.98  --res_lit_sel_side                      cnt
% 0.64/0.98  --res_ordering                          kbo
% 0.64/0.98  --res_to_prop_solver                    none
% 0.64/0.98  --res_prop_simpl_new                    false
% 0.64/0.98  --res_prop_simpl_given                  true
% 0.64/0.98  --res_passive_queue_type                priority_queues
% 0.64/0.98  --res_passive_queues                    [[-num_lits;-num_var;+horn];[-ground;+conj_symb;+conj_dist]]
% 0.64/0.98  --res_passive_queues_freq               [15;5]
% 0.64/0.98  --res_forward_subs                      subset_subsumption
% 0.64/0.98  --res_backward_subs                     subset_subsumption
% 0.64/0.98  --res_forward_subs_resolution           true
% 0.64/0.98  --res_backward_subs_resolution          false
% 0.64/0.98  --res_orphan_elimination                false
% 0.64/0.98  --res_time_limit                        0.1
% 0.64/0.98  --res_out_proof                         true
% 0.64/0.98  
% 0.64/0.98  ------ Superposition Options
% 0.64/0.98  
% 0.64/0.98  --superposition_flag                    false
% 0.64/0.98  --sup_passive_queue_type                priority_queues
% 0.64/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.64/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.64/0.98  --demod_completeness_check              fast
% 0.64/0.98  --demod_use_ground                      true
% 0.64/0.98  --sup_to_prop_solver                    passive
% 0.64/0.98  --sup_prop_simpl_new                    true
% 0.64/0.98  --sup_prop_simpl_given                  true
% 0.64/0.98  --sup_fun_splitting                     false
% 0.64/0.98  --sup_smt_interval                      50000
% 0.64/0.98  
% 0.64/0.98  ------ Superposition Simplification Setup
% 0.64/0.98  
% 0.64/0.98  --sup_indices_passive                   []
% 0.64/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.64/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.98  --sup_full_bw                           [BwDemod]
% 0.64/0.98  --sup_immed_triv                        [TrivRules]
% 0.64/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.64/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.98  --sup_immed_bw_main                     []
% 0.64/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.64/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/0.98  
% 0.64/0.98  ------ Combination Options
% 0.64/0.98  
% 0.64/0.98  --comb_res_mult                         1
% 0.64/0.98  --comb_sup_mult                         2
% 0.64/0.98  --comb_inst_mult                        100
% 0.64/0.98  
% 0.64/0.98  ------ Debug Options
% 0.64/0.98  
% 0.64/0.98  --dbg_backtrace                         false
% 0.64/0.98  --dbg_dump_prop_clauses                 false
% 0.64/0.98  --dbg_dump_prop_clauses_file            -
% 0.64/0.98  --dbg_out_stat                          false
% 0.64/0.98  
% 0.64/0.98  
% 0.64/0.98  
% 0.64/0.98  
% 0.64/0.98  ------ Proving...
% 0.64/0.98  
% 0.64/0.98  
% 0.64/0.98  % SZS status Theorem for theBenchmark.p
% 0.64/0.98  
% 0.64/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 0.64/0.98  
% 0.64/0.98  fof(f2,axiom,(
% 0.64/0.98    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/0.98  
% 0.64/0.98  fof(f11,plain,(
% 0.64/0.98    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.64/0.98    inference(ennf_transformation,[],[f2])).
% 0.64/0.98  
% 0.64/0.98  fof(f18,plain,(
% 0.64/0.98    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 0.64/0.98    inference(nnf_transformation,[],[f11])).
% 0.64/0.98  
% 0.64/0.98  fof(f19,plain,(
% 0.64/0.98    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.64/0.98    inference(rectify,[],[f18])).
% 0.64/0.98  
% 0.64/0.98  fof(f20,plain,(
% 0.64/0.98    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK0(X0),X0) & r2_hidden(sK0(X0),X0)))),
% 0.64/0.98    introduced(choice_axiom,[])).
% 0.64/0.98  
% 0.64/0.98  fof(f21,plain,(
% 0.64/0.98    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK0(X0),X0) & r2_hidden(sK0(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.64/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 0.64/0.98  
% 0.64/0.98  fof(f29,plain,(
% 0.64/0.98    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 0.64/0.98    inference(cnf_transformation,[],[f21])).
% 0.64/0.98  
% 0.64/0.98  fof(f5,axiom,(
% 0.64/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/0.98  
% 0.64/0.98  fof(f14,plain,(
% 0.64/0.98    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.64/0.98    inference(ennf_transformation,[],[f5])).
% 0.64/0.98  
% 0.64/0.98  fof(f15,plain,(
% 0.64/0.98    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.64/0.98    inference(flattening,[],[f14])).
% 0.64/0.98  
% 0.64/0.98  fof(f37,plain,(
% 0.64/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.64/0.98    inference(cnf_transformation,[],[f15])).
% 0.64/0.98  
% 0.64/0.98  fof(f3,axiom,(
% 0.64/0.98    ! [X0] : (v3_ordinal1(X0) <=> (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/0.98  
% 0.64/0.98  fof(f22,plain,(
% 0.64/0.98    ! [X0] : ((v3_ordinal1(X0) | (~v2_ordinal1(X0) | ~v1_ordinal1(X0))) & ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0)))),
% 0.64/0.98    inference(nnf_transformation,[],[f3])).
% 0.64/0.98  
% 0.64/0.98  fof(f23,plain,(
% 0.64/0.98    ! [X0] : ((v3_ordinal1(X0) | ~v2_ordinal1(X0) | ~v1_ordinal1(X0)) & ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0)))),
% 0.64/0.98    inference(flattening,[],[f22])).
% 0.64/0.98  
% 0.64/0.98  fof(f32,plain,(
% 0.64/0.98    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.64/0.98    inference(cnf_transformation,[],[f23])).
% 0.64/0.98  
% 0.64/0.98  fof(f4,axiom,(
% 0.64/0.98    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/0.98  
% 0.64/0.98  fof(f12,plain,(
% 0.64/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.64/0.98    inference(ennf_transformation,[],[f4])).
% 0.64/0.98  
% 0.64/0.98  fof(f13,plain,(
% 0.64/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.64/0.98    inference(flattening,[],[f12])).
% 0.64/0.98  
% 0.64/0.98  fof(f24,plain,(
% 0.64/0.98    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.64/0.98    inference(nnf_transformation,[],[f13])).
% 0.64/0.98  
% 0.64/0.98  fof(f35,plain,(
% 0.64/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.64/0.98    inference(cnf_transformation,[],[f24])).
% 0.64/0.98  
% 0.64/0.98  fof(f1,axiom,(
% 0.64/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/0.98  
% 0.64/0.98  fof(f8,plain,(
% 0.64/0.98    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.64/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 0.64/0.98  
% 0.64/0.98  fof(f9,plain,(
% 0.64/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.64/0.98    inference(ennf_transformation,[],[f8])).
% 0.64/0.98  
% 0.64/0.98  fof(f10,plain,(
% 0.64/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.64/0.98    inference(flattening,[],[f9])).
% 0.64/0.98  
% 0.64/0.98  fof(f28,plain,(
% 0.64/0.98    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.64/0.98    inference(cnf_transformation,[],[f10])).
% 0.64/0.98  
% 0.64/0.98  fof(f6,conjecture,(
% 0.64/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/0.98  
% 0.64/0.98  fof(f7,negated_conjecture,(
% 0.64/0.98    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.64/0.98    inference(negated_conjecture,[],[f6])).
% 0.64/0.98  
% 0.64/0.98  fof(f16,plain,(
% 0.64/0.98    ? [X0] : (? [X1] : ((~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.64/0.98    inference(ennf_transformation,[],[f7])).
% 0.64/0.98  
% 0.64/0.98  fof(f17,plain,(
% 0.64/0.98    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.64/0.98    inference(flattening,[],[f16])).
% 0.64/0.98  
% 0.64/0.98  fof(f26,plain,(
% 0.64/0.98    ( ! [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) => (~r2_xboole_0(sK2,X0) & sK2 != X0 & ~r2_xboole_0(X0,sK2) & v3_ordinal1(sK2))) )),
% 0.64/0.98    introduced(choice_axiom,[])).
% 0.64/0.98  
% 0.64/0.98  fof(f25,plain,(
% 0.64/0.98    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (~r2_xboole_0(X1,sK1) & sK1 != X1 & ~r2_xboole_0(sK1,X1) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 0.64/0.98    introduced(choice_axiom,[])).
% 0.64/0.98  
% 0.64/0.98  fof(f27,plain,(
% 0.64/0.98    (~r2_xboole_0(sK2,sK1) & sK1 != sK2 & ~r2_xboole_0(sK1,sK2) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 0.64/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f26,f25])).
% 0.64/0.98  
% 0.64/0.98  fof(f40,plain,(
% 0.64/0.98    ~r2_xboole_0(sK1,sK2)),
% 0.64/0.98    inference(cnf_transformation,[],[f27])).
% 0.64/0.98  
% 0.64/0.98  fof(f42,plain,(
% 0.64/0.98    ~r2_xboole_0(sK2,sK1)),
% 0.64/0.98    inference(cnf_transformation,[],[f27])).
% 0.64/0.98  
% 0.64/0.98  fof(f41,plain,(
% 0.64/0.98    sK1 != sK2),
% 0.64/0.98    inference(cnf_transformation,[],[f27])).
% 0.64/0.98  
% 0.64/0.98  fof(f39,plain,(
% 0.64/0.98    v3_ordinal1(sK2)),
% 0.64/0.98    inference(cnf_transformation,[],[f27])).
% 0.64/0.98  
% 0.64/0.98  fof(f38,plain,(
% 0.64/0.98    v3_ordinal1(sK1)),
% 0.64/0.98    inference(cnf_transformation,[],[f27])).
% 0.64/0.98  
% 0.64/0.98  cnf(c_275,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_348,plain,
% 0.64/0.98      ( sK1 != X0 | sK1 = sK2 | sK2 != X0 ),
% 0.64/0.98      inference(instantiation,[status(thm)],[c_275]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_349,plain,
% 0.64/0.98      ( sK1 != sK1 | sK1 = sK2 | sK2 != sK1 ),
% 0.64/0.98      inference(instantiation,[status(thm)],[c_348]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_3,plain,
% 0.64/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,X1) | ~ v1_ordinal1(X1) ),
% 0.64/0.98      inference(cnf_transformation,[],[f29]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_9,plain,
% 0.64/0.98      ( r1_ordinal1(X0,X1)
% 0.64/0.98      | r2_hidden(X1,X0)
% 0.64/0.98      | ~ v3_ordinal1(X0)
% 0.64/0.98      | ~ v3_ordinal1(X1) ),
% 0.64/0.98      inference(cnf_transformation,[],[f37]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_185,plain,
% 0.64/0.98      ( r1_ordinal1(X0,X1)
% 0.64/0.98      | r1_tarski(X2,X3)
% 0.64/0.98      | ~ v3_ordinal1(X0)
% 0.64/0.98      | ~ v3_ordinal1(X1)
% 0.64/0.98      | ~ v1_ordinal1(X3)
% 0.64/0.98      | X1 != X2
% 0.64/0.98      | X0 != X3 ),
% 0.64/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_9]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_186,plain,
% 0.64/0.98      ( r1_ordinal1(X0,X1)
% 0.64/0.98      | r1_tarski(X1,X0)
% 0.64/0.98      | ~ v3_ordinal1(X0)
% 0.64/0.98      | ~ v3_ordinal1(X1)
% 0.64/0.98      | ~ v1_ordinal1(X0) ),
% 0.64/0.98      inference(unflattening,[status(thm)],[c_185]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_6,plain,
% 0.64/0.98      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 0.64/0.98      inference(cnf_transformation,[],[f32]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_190,plain,
% 0.64/0.98      ( ~ v3_ordinal1(X1)
% 0.64/0.98      | ~ v3_ordinal1(X0)
% 0.64/0.98      | r1_tarski(X1,X0)
% 0.64/0.98      | r1_ordinal1(X0,X1) ),
% 0.64/0.98      inference(global_propositional_subsumption,
% 0.64/0.98                [status(thm)],
% 0.64/0.98                [c_186,c_6]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_191,plain,
% 0.64/0.98      ( r1_ordinal1(X0,X1)
% 0.64/0.98      | r1_tarski(X1,X0)
% 0.64/0.98      | ~ v3_ordinal1(X0)
% 0.64/0.98      | ~ v3_ordinal1(X1) ),
% 0.64/0.98      inference(renaming,[status(thm)],[c_190]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_8,plain,
% 0.64/0.98      ( ~ r1_ordinal1(X0,X1)
% 0.64/0.98      | r1_tarski(X0,X1)
% 0.64/0.98      | ~ v3_ordinal1(X0)
% 0.64/0.98      | ~ v3_ordinal1(X1) ),
% 0.64/0.98      inference(cnf_transformation,[],[f35]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_214,plain,
% 0.64/0.98      ( r1_tarski(X0,X1)
% 0.64/0.98      | r1_tarski(X1,X0)
% 0.64/0.98      | ~ v3_ordinal1(X0)
% 0.64/0.98      | ~ v3_ordinal1(X1) ),
% 0.64/0.98      inference(resolution,[status(thm)],[c_191,c_8]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_344,plain,
% 0.64/0.98      ( r1_tarski(sK1,sK2)
% 0.64/0.98      | r1_tarski(sK2,sK1)
% 0.64/0.98      | ~ v3_ordinal1(sK1)
% 0.64/0.98      | ~ v3_ordinal1(sK2) ),
% 0.64/0.98      inference(instantiation,[status(thm)],[c_214]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_274,plain,( X0 = X0 ),theory(equality) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_281,plain,
% 0.64/0.98      ( sK1 = sK1 ),
% 0.64/0.98      inference(instantiation,[status(thm)],[c_274]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_0,plain,
% 0.64/0.98      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 0.64/0.98      inference(cnf_transformation,[],[f28]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_12,negated_conjecture,
% 0.64/0.98      ( ~ r2_xboole_0(sK1,sK2) ),
% 0.64/0.98      inference(cnf_transformation,[],[f40]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_168,plain,
% 0.64/0.98      ( ~ r1_tarski(X0,X1) | X1 = X0 | sK1 != X0 | sK2 != X1 ),
% 0.64/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_169,plain,
% 0.64/0.98      ( ~ r1_tarski(sK1,sK2) | sK2 = sK1 ),
% 0.64/0.98      inference(unflattening,[status(thm)],[c_168]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_10,negated_conjecture,
% 0.64/0.98      ( ~ r2_xboole_0(sK2,sK1) ),
% 0.64/0.98      inference(cnf_transformation,[],[f42]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_157,plain,
% 0.64/0.98      ( ~ r1_tarski(X0,X1) | X1 = X0 | sK1 != X1 | sK2 != X0 ),
% 0.64/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_158,plain,
% 0.64/0.98      ( ~ r1_tarski(sK2,sK1) | sK1 = sK2 ),
% 0.64/0.98      inference(unflattening,[status(thm)],[c_157]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_11,negated_conjecture,
% 0.64/0.98      ( sK1 != sK2 ),
% 0.64/0.98      inference(cnf_transformation,[],[f41]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_13,negated_conjecture,
% 0.64/0.98      ( v3_ordinal1(sK2) ),
% 0.64/0.98      inference(cnf_transformation,[],[f39]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(c_14,negated_conjecture,
% 0.64/0.98      ( v3_ordinal1(sK1) ),
% 0.64/0.98      inference(cnf_transformation,[],[f38]) ).
% 0.64/0.98  
% 0.64/0.98  cnf(contradiction,plain,
% 0.64/0.98      ( $false ),
% 0.64/0.98      inference(minisat,
% 0.64/0.98                [status(thm)],
% 0.64/0.98                [c_349,c_344,c_281,c_169,c_158,c_11,c_13,c_14]) ).
% 0.64/0.98  
% 0.64/0.98  
% 0.64/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 0.64/0.98  
% 0.64/0.98  ------                               Statistics
% 0.64/0.98  
% 0.64/0.98  ------ General
% 0.64/0.98  
% 0.64/0.98  abstr_ref_over_cycles:                  0
% 0.64/0.98  abstr_ref_under_cycles:                 0
% 0.64/0.98  gc_basic_clause_elim:                   0
% 0.64/0.98  forced_gc_time:                         0
% 0.64/0.98  parsing_time:                           0.011
% 0.64/0.98  unif_index_cands_time:                  0.
% 0.64/0.98  unif_index_add_time:                    0.
% 0.64/0.98  orderings_time:                         0.
% 0.64/0.98  out_proof_time:                         0.011
% 0.64/0.98  total_time:                             0.049
% 0.64/0.98  num_of_symbols:                         38
% 0.64/0.98  num_of_terms:                           229
% 0.64/0.98  
% 0.64/0.98  ------ Preprocessing
% 0.64/0.98  
% 0.64/0.98  num_of_splits:                          0
% 0.64/0.98  num_of_split_atoms:                     0
% 0.64/0.98  num_of_reused_defs:                     0
% 0.64/0.98  num_eq_ax_congr_red:                    7
% 0.64/0.98  num_of_sem_filtered_clauses:            1
% 0.64/0.98  num_of_subtypes:                        1
% 0.64/0.98  monotx_restored_types:                  0
% 0.64/0.98  sat_num_of_epr_types:                   0
% 0.64/0.98  sat_num_of_non_cyclic_types:            0
% 0.64/0.98  sat_guarded_non_collapsed_types:        0
% 0.64/0.98  num_pure_diseq_elim:                    0
% 0.64/0.98  simp_replaced_by:                       0
% 0.64/0.98  res_preprocessed:                       21
% 0.64/0.98  prep_upred:                             0
% 0.64/0.98  prep_unflattend:                        8
% 0.64/0.98  smt_new_axioms:                         0
% 0.64/0.98  pred_elim_cands:                        2
% 0.64/0.98  pred_elim:                              5
% 0.64/0.98  pred_elim_cl:                           9
% 0.64/0.98  pred_elim_cycles:                       7
% 0.64/0.98  merged_defs:                            0
% 0.64/0.98  merged_defs_ncl:                        0
% 0.64/0.98  bin_hyper_res:                          0
% 0.64/0.98  prep_cycles:                            4
% 0.64/0.98  pred_elim_time:                         0.001
% 0.64/0.98  splitting_time:                         0.
% 0.64/0.98  sem_filter_time:                        0.
% 0.64/0.98  monotx_time:                            0.
% 0.64/0.98  subtype_inf_time:                       0.
% 0.64/0.98  
% 0.64/0.98  ------ Problem properties
% 0.64/0.98  
% 0.64/0.98  clauses:                                6
% 0.64/0.98  conjectures:                            3
% 0.64/0.98  epr:                                    6
% 0.64/0.98  horn:                                   5
% 0.64/0.98  ground:                                 5
% 0.64/0.98  unary:                                  4
% 0.64/0.98  binary:                                 1
% 0.64/0.98  lits:                                   10
% 0.64/0.98  lits_eq:                                2
% 0.64/0.98  fd_pure:                                0
% 0.64/0.98  fd_pseudo:                              0
% 0.64/0.98  fd_cond:                                0
% 0.64/0.98  fd_pseudo_cond:                         0
% 0.64/0.98  ac_symbols:                             0
% 0.64/0.98  
% 0.64/0.98  ------ Propositional Solver
% 0.64/0.98  
% 0.64/0.98  prop_solver_calls:                      22
% 0.64/0.98  prop_fast_solver_calls:                 107
% 0.64/0.98  smt_solver_calls:                       0
% 0.64/0.98  smt_fast_solver_calls:                  0
% 0.64/0.98  prop_num_of_clauses:                    77
% 0.64/0.98  prop_preprocess_simplified:             696
% 0.64/0.98  prop_fo_subsumed:                       2
% 0.64/0.98  prop_solver_time:                       0.
% 0.64/0.98  smt_solver_time:                        0.
% 0.64/0.98  smt_fast_solver_time:                   0.
% 0.64/0.98  prop_fast_solver_time:                  0.
% 0.64/0.98  prop_unsat_core_time:                   0.
% 0.64/0.98  
% 0.64/0.98  ------ QBF
% 0.64/0.98  
% 0.64/0.98  qbf_q_res:                              0
% 0.64/0.98  qbf_num_tautologies:                    0
% 0.64/0.98  qbf_prep_cycles:                        0
% 0.64/0.98  
% 0.64/0.98  ------ BMC1
% 0.64/0.98  
% 0.64/0.98  bmc1_current_bound:                     -1
% 0.64/0.98  bmc1_last_solved_bound:                 -1
% 0.64/0.98  bmc1_unsat_core_size:                   -1
% 0.64/0.98  bmc1_unsat_core_parents_size:           -1
% 0.64/0.98  bmc1_merge_next_fun:                    0
% 0.64/0.98  bmc1_unsat_core_clauses_time:           0.
% 0.64/0.98  
% 0.64/0.98  ------ Instantiation
% 0.64/0.98  
% 0.64/0.98  inst_num_of_clauses:                    11
% 0.64/0.98  inst_num_in_passive:                    2
% 0.64/0.98  inst_num_in_active:                     7
% 0.64/0.98  inst_num_in_unprocessed:                1
% 0.64/0.98  inst_num_of_loops:                      8
% 0.64/0.98  inst_num_of_learning_restarts:          0
% 0.64/0.98  inst_num_moves_active_passive:          0
% 0.64/0.98  inst_lit_activity:                      0
% 0.64/0.98  inst_lit_activity_moves:                0
% 0.64/0.98  inst_num_tautologies:                   0
% 0.64/0.98  inst_num_prop_implied:                  0
% 0.64/0.98  inst_num_existing_simplified:           0
% 0.64/0.98  inst_num_eq_res_simplified:             0
% 0.64/0.98  inst_num_child_elim:                    0
% 0.64/0.98  inst_num_of_dismatching_blockings:      0
% 0.64/0.98  inst_num_of_non_proper_insts:           3
% 0.64/0.98  inst_num_of_duplicates:                 0
% 0.64/0.98  inst_inst_num_from_inst_to_res:         0
% 0.64/0.98  inst_dismatching_checking_time:         0.
% 0.64/0.98  
% 0.64/0.98  ------ Resolution
% 0.64/0.98  
% 0.64/0.98  res_num_of_clauses:                     10
% 0.64/0.98  res_num_in_passive:                     9
% 0.64/0.98  res_num_in_active:                      1
% 0.64/0.98  res_num_of_loops:                       24
% 0.64/0.98  res_forward_subset_subsumed:            0
% 0.64/0.98  res_backward_subset_subsumed:           0
% 0.64/0.98  res_forward_subsumed:                   0
% 0.64/0.98  res_backward_subsumed:                  0
% 0.64/0.98  res_forward_subsumption_resolution:     0
% 0.64/0.98  res_backward_subsumption_resolution:    0
% 0.64/0.98  res_clause_to_clause_subsumption:       8
% 0.64/0.98  res_orphan_elimination:                 0
% 0.64/0.98  res_tautology_del:                      3
% 0.64/0.98  res_num_eq_res_simplified:              0
% 0.64/0.98  res_num_sel_changes:                    0
% 0.64/0.98  res_moves_from_active_to_pass:          0
% 0.64/0.98  
% 0.64/0.98  ------ Superposition
% 0.64/0.98  
% 0.64/0.98  sup_time_total:                         0.
% 0.64/0.98  sup_time_generating:                    0.
% 0.64/0.98  sup_time_sim_full:                      0.
% 0.64/0.98  sup_time_sim_immed:                     0.
% 0.64/0.98  
% 0.64/0.98  sup_num_of_clauses:                     0
% 0.64/0.98  sup_num_in_active:                      0
% 0.64/0.98  sup_num_in_passive:                     0
% 0.64/0.98  sup_num_of_loops:                       0
% 0.64/0.98  sup_fw_superposition:                   0
% 0.64/0.98  sup_bw_superposition:                   0
% 0.64/0.98  sup_immediate_simplified:               0
% 0.64/0.98  sup_given_eliminated:                   0
% 0.64/0.98  comparisons_done:                       0
% 0.64/0.98  comparisons_avoided:                    0
% 0.64/0.98  
% 0.64/0.98  ------ Simplifications
% 0.64/0.98  
% 0.64/0.98  
% 0.64/0.98  sim_fw_subset_subsumed:                 0
% 0.64/0.98  sim_bw_subset_subsumed:                 0
% 0.64/0.98  sim_fw_subsumed:                        0
% 0.64/0.98  sim_bw_subsumed:                        0
% 0.64/0.98  sim_fw_subsumption_res:                 0
% 0.64/0.98  sim_bw_subsumption_res:                 0
% 0.64/0.98  sim_tautology_del:                      0
% 0.64/0.98  sim_eq_tautology_del:                   0
% 0.64/0.98  sim_eq_res_simp:                        0
% 0.64/0.98  sim_fw_demodulated:                     0
% 0.64/0.98  sim_bw_demodulated:                     0
% 0.64/0.98  sim_light_normalised:                   0
% 0.64/0.98  sim_joinable_taut:                      0
% 0.64/0.98  sim_joinable_simp:                      0
% 0.64/0.98  sim_ac_normalised:                      0
% 0.64/0.98  sim_smt_subsumption:                    0
% 0.64/0.98  
%------------------------------------------------------------------------------
