%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:11 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 292 expanded)
%              Number of clauses        :   21 (  62 expanded)
%              Number of leaves         :    7 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  161 (1094 expanded)
%              Number of equality atoms :  160 (1093 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) )
   => ( ( sK7 != sK11
        | sK6 != sK10
        | sK5 != sK9
        | sK4 != sK8 )
      & k4_mcart_1(sK4,sK5,sK6,sK7) = k4_mcart_1(sK8,sK9,sK10,sK11) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( sK7 != sK11
      | sK6 != sK10
      | sK5 != sK9
      | sK4 != sK8 )
    & k4_mcart_1(sK4,sK5,sK6,sK7) = k4_mcart_1(sK8,sK9,sK10,sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f10,f19])).

fof(f28,plain,(
    k4_mcart_1(sK4,sK5,sK6,sK7) = k4_mcart_1(sK8,sK9,sK10,sK11) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f30,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7) = k4_tarski(k4_tarski(k4_tarski(sK8,sK9),sK10),sK11) ),
    inference(definition_unfolding,[],[f28,f27,f27])).

fof(f1,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f8])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK0(X0,X1) != X1
        & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK0(X0,X1) != X1
              & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f21,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f21])).

fof(f34,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_mcart_1(k4_tarski(X4,X5)) = X4
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k2_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X5
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X3
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK3(X0,X1) != X1
        & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ( sK3(X0,X1) != X1
              & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).

fof(f24,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f24])).

fof(f38,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_mcart_1(k4_tarski(X4,X5)) = X5
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f37])).

fof(f29,plain,
    ( sK7 != sK11
    | sK6 != sK10
    | sK5 != sK9
    | sK4 != sK8 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7) = k4_tarski(k4_tarski(k4_tarski(sK8,sK9),sK10),sK11) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_92,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[status(thm)],[c_2])).

cnf(c_199,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7)) = k4_tarski(k4_tarski(sK8,sK9),sK10) ),
    inference(superposition,[status(thm)],[c_7,c_92])).

cnf(c_200,plain,
    ( k4_tarski(k4_tarski(sK8,sK9),sK10) = k4_tarski(k4_tarski(sK4,sK5),sK6) ),
    inference(demodulation,[status(thm)],[c_199,c_92])).

cnf(c_865,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6)) = k4_tarski(sK8,sK9) ),
    inference(superposition,[status(thm)],[c_200,c_92])).

cnf(c_892,plain,
    ( k4_tarski(sK8,sK9) = k4_tarski(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_865,c_92])).

cnf(c_5,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_117,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[status(thm)],[c_5])).

cnf(c_3707,plain,
    ( k2_mcart_1(k4_tarski(sK4,sK5)) = sK9 ),
    inference(superposition,[status(thm)],[c_892,c_117])).

cnf(c_3897,plain,
    ( sK9 = sK5 ),
    inference(demodulation,[status(thm)],[c_3707,c_117])).

cnf(c_3710,plain,
    ( k1_mcart_1(k4_tarski(sK4,sK5)) = sK8 ),
    inference(superposition,[status(thm)],[c_892,c_92])).

cnf(c_3790,plain,
    ( sK8 = sK4 ),
    inference(demodulation,[status(thm)],[c_3710,c_92])).

cnf(c_451,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7)) = sK11 ),
    inference(superposition,[status(thm)],[c_7,c_117])).

cnf(c_458,plain,
    ( sK11 = sK7 ),
    inference(demodulation,[status(thm)],[c_451,c_117])).

cnf(c_6,negated_conjecture,
    ( sK4 != sK8
    | sK5 != sK9
    | sK6 != sK10
    | sK7 != sK11 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3392,plain,
    ( sK8 != sK4
    | sK9 != sK5
    | sK10 != sK6
    | sK7 != sK7 ),
    inference(demodulation,[status(thm)],[c_458,c_6])).

cnf(c_3393,plain,
    ( sK8 != sK4
    | sK9 != sK5
    | sK10 != sK6 ),
    inference(equality_resolution_simp,[status(thm)],[c_3392])).

cnf(c_862,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6)) = sK10 ),
    inference(superposition,[status(thm)],[c_200,c_117])).

cnf(c_953,plain,
    ( sK10 = sK6 ),
    inference(demodulation,[status(thm)],[c_862,c_117])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3897,c_3790,c_3393,c_953])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:47:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.17/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/0.99  
% 3.17/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.17/0.99  
% 3.17/0.99  ------  iProver source info
% 3.17/0.99  
% 3.17/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.17/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.17/0.99  git: non_committed_changes: false
% 3.17/0.99  git: last_make_outside_of_git: false
% 3.17/0.99  
% 3.17/0.99  ------ 
% 3.17/0.99  
% 3.17/0.99  ------ Input Options
% 3.17/0.99  
% 3.17/0.99  --out_options                           all
% 3.17/0.99  --tptp_safe_out                         true
% 3.17/0.99  --problem_path                          ""
% 3.17/0.99  --include_path                          ""
% 3.17/0.99  --clausifier                            res/vclausify_rel
% 3.17/0.99  --clausifier_options                    --mode clausify
% 3.17/0.99  --stdin                                 false
% 3.17/0.99  --stats_out                             sel
% 3.17/0.99  
% 3.17/0.99  ------ General Options
% 3.17/0.99  
% 3.17/0.99  --fof                                   false
% 3.17/0.99  --time_out_real                         604.99
% 3.17/0.99  --time_out_virtual                      -1.
% 3.17/0.99  --symbol_type_check                     false
% 3.17/0.99  --clausify_out                          false
% 3.17/0.99  --sig_cnt_out                           false
% 3.17/0.99  --trig_cnt_out                          false
% 3.17/0.99  --trig_cnt_out_tolerance                1.
% 3.17/0.99  --trig_cnt_out_sk_spl                   false
% 3.17/0.99  --abstr_cl_out                          false
% 3.17/0.99  
% 3.17/0.99  ------ Global Options
% 3.17/0.99  
% 3.17/0.99  --schedule                              none
% 3.17/0.99  --add_important_lit                     false
% 3.17/0.99  --prop_solver_per_cl                    1000
% 3.17/0.99  --min_unsat_core                        false
% 3.17/0.99  --soft_assumptions                      false
% 3.17/0.99  --soft_lemma_size                       3
% 3.17/0.99  --prop_impl_unit_size                   0
% 3.17/0.99  --prop_impl_unit                        []
% 3.17/0.99  --share_sel_clauses                     true
% 3.17/0.99  --reset_solvers                         false
% 3.17/0.99  --bc_imp_inh                            [conj_cone]
% 3.17/0.99  --conj_cone_tolerance                   3.
% 3.17/0.99  --extra_neg_conj                        none
% 3.17/0.99  --large_theory_mode                     true
% 3.17/0.99  --prolific_symb_bound                   200
% 3.17/0.99  --lt_threshold                          2000
% 3.17/0.99  --clause_weak_htbl                      true
% 3.17/0.99  --gc_record_bc_elim                     false
% 3.17/0.99  
% 3.17/0.99  ------ Preprocessing Options
% 3.17/0.99  
% 3.17/0.99  --preprocessing_flag                    true
% 3.17/0.99  --time_out_prep_mult                    0.1
% 3.17/0.99  --splitting_mode                        input
% 3.17/0.99  --splitting_grd                         true
% 3.17/0.99  --splitting_cvd                         false
% 3.17/0.99  --splitting_cvd_svl                     false
% 3.17/0.99  --splitting_nvd                         32
% 3.17/0.99  --sub_typing                            true
% 3.17/0.99  --prep_gs_sim                           false
% 3.17/0.99  --prep_unflatten                        true
% 3.17/0.99  --prep_res_sim                          true
% 3.17/0.99  --prep_upred                            true
% 3.17/0.99  --prep_sem_filter                       exhaustive
% 3.17/0.99  --prep_sem_filter_out                   false
% 3.17/0.99  --pred_elim                             false
% 3.17/0.99  --res_sim_input                         true
% 3.17/0.99  --eq_ax_congr_red                       true
% 3.17/0.99  --pure_diseq_elim                       true
% 3.17/0.99  --brand_transform                       false
% 3.17/0.99  --non_eq_to_eq                          false
% 3.17/0.99  --prep_def_merge                        true
% 3.17/0.99  --prep_def_merge_prop_impl              false
% 3.17/0.99  --prep_def_merge_mbd                    true
% 3.17/0.99  --prep_def_merge_tr_red                 false
% 3.17/0.99  --prep_def_merge_tr_cl                  false
% 3.17/0.99  --smt_preprocessing                     true
% 3.17/0.99  --smt_ac_axioms                         fast
% 3.17/0.99  --preprocessed_out                      false
% 3.17/0.99  --preprocessed_stats                    false
% 3.17/0.99  
% 3.17/0.99  ------ Abstraction refinement Options
% 3.17/0.99  
% 3.17/0.99  --abstr_ref                             []
% 3.17/0.99  --abstr_ref_prep                        false
% 3.17/0.99  --abstr_ref_until_sat                   false
% 3.17/0.99  --abstr_ref_sig_restrict                funpre
% 3.17/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/0.99  --abstr_ref_under                       []
% 3.17/0.99  
% 3.17/0.99  ------ SAT Options
% 3.17/0.99  
% 3.17/0.99  --sat_mode                              false
% 3.17/0.99  --sat_fm_restart_options                ""
% 3.17/0.99  --sat_gr_def                            false
% 3.17/0.99  --sat_epr_types                         true
% 3.17/0.99  --sat_non_cyclic_types                  false
% 3.17/0.99  --sat_finite_models                     false
% 3.17/0.99  --sat_fm_lemmas                         false
% 3.17/0.99  --sat_fm_prep                           false
% 3.17/0.99  --sat_fm_uc_incr                        true
% 3.17/0.99  --sat_out_model                         small
% 3.17/0.99  --sat_out_clauses                       false
% 3.17/0.99  
% 3.17/0.99  ------ QBF Options
% 3.17/0.99  
% 3.17/0.99  --qbf_mode                              false
% 3.17/0.99  --qbf_elim_univ                         false
% 3.17/0.99  --qbf_dom_inst                          none
% 3.17/0.99  --qbf_dom_pre_inst                      false
% 3.17/0.99  --qbf_sk_in                             false
% 3.17/0.99  --qbf_pred_elim                         true
% 3.17/0.99  --qbf_split                             512
% 3.17/0.99  
% 3.17/0.99  ------ BMC1 Options
% 3.17/0.99  
% 3.17/0.99  --bmc1_incremental                      false
% 3.17/0.99  --bmc1_axioms                           reachable_all
% 3.17/0.99  --bmc1_min_bound                        0
% 3.17/0.99  --bmc1_max_bound                        -1
% 3.17/0.99  --bmc1_max_bound_default                -1
% 3.17/0.99  --bmc1_symbol_reachability              true
% 3.17/0.99  --bmc1_property_lemmas                  false
% 3.17/0.99  --bmc1_k_induction                      false
% 3.17/0.99  --bmc1_non_equiv_states                 false
% 3.17/0.99  --bmc1_deadlock                         false
% 3.17/0.99  --bmc1_ucm                              false
% 3.17/0.99  --bmc1_add_unsat_core                   none
% 3.17/0.99  --bmc1_unsat_core_children              false
% 3.17/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/0.99  --bmc1_out_stat                         full
% 3.17/0.99  --bmc1_ground_init                      false
% 3.17/0.99  --bmc1_pre_inst_next_state              false
% 3.17/0.99  --bmc1_pre_inst_state                   false
% 3.17/0.99  --bmc1_pre_inst_reach_state             false
% 3.17/0.99  --bmc1_out_unsat_core                   false
% 3.17/0.99  --bmc1_aig_witness_out                  false
% 3.17/0.99  --bmc1_verbose                          false
% 3.17/0.99  --bmc1_dump_clauses_tptp                false
% 3.17/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.17/0.99  --bmc1_dump_file                        -
% 3.17/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.17/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.17/0.99  --bmc1_ucm_extend_mode                  1
% 3.17/0.99  --bmc1_ucm_init_mode                    2
% 3.17/0.99  --bmc1_ucm_cone_mode                    none
% 3.17/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.17/0.99  --bmc1_ucm_relax_model                  4
% 3.17/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.17/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/0.99  --bmc1_ucm_layered_model                none
% 3.17/0.99  --bmc1_ucm_max_lemma_size               10
% 3.17/0.99  
% 3.17/0.99  ------ AIG Options
% 3.17/0.99  
% 3.17/0.99  --aig_mode                              false
% 3.17/0.99  
% 3.17/0.99  ------ Instantiation Options
% 3.17/0.99  
% 3.17/0.99  --instantiation_flag                    true
% 3.17/0.99  --inst_sos_flag                         false
% 3.17/0.99  --inst_sos_phase                        true
% 3.17/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/0.99  --inst_lit_sel_side                     num_symb
% 3.17/0.99  --inst_solver_per_active                1400
% 3.17/0.99  --inst_solver_calls_frac                1.
% 3.17/0.99  --inst_passive_queue_type               priority_queues
% 3.17/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/0.99  --inst_passive_queues_freq              [25;2]
% 3.17/0.99  --inst_dismatching                      true
% 3.17/0.99  --inst_eager_unprocessed_to_passive     true
% 3.17/0.99  --inst_prop_sim_given                   true
% 3.17/0.99  --inst_prop_sim_new                     false
% 3.17/0.99  --inst_subs_new                         false
% 3.17/0.99  --inst_eq_res_simp                      false
% 3.17/0.99  --inst_subs_given                       false
% 3.17/0.99  --inst_orphan_elimination               true
% 3.17/0.99  --inst_learning_loop_flag               true
% 3.17/0.99  --inst_learning_start                   3000
% 3.17/0.99  --inst_learning_factor                  2
% 3.17/0.99  --inst_start_prop_sim_after_learn       3
% 3.17/0.99  --inst_sel_renew                        solver
% 3.17/0.99  --inst_lit_activity_flag                true
% 3.17/0.99  --inst_restr_to_given                   false
% 3.17/0.99  --inst_activity_threshold               500
% 3.17/0.99  --inst_out_proof                        true
% 3.17/0.99  
% 3.17/0.99  ------ Resolution Options
% 3.17/0.99  
% 3.17/0.99  --resolution_flag                       true
% 3.17/0.99  --res_lit_sel                           adaptive
% 3.17/0.99  --res_lit_sel_side                      none
% 3.17/0.99  --res_ordering                          kbo
% 3.17/0.99  --res_to_prop_solver                    active
% 3.17/0.99  --res_prop_simpl_new                    false
% 3.17/0.99  --res_prop_simpl_given                  true
% 3.17/0.99  --res_passive_queue_type                priority_queues
% 3.17/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/0.99  --res_passive_queues_freq               [15;5]
% 3.17/0.99  --res_forward_subs                      full
% 3.17/0.99  --res_backward_subs                     full
% 3.17/0.99  --res_forward_subs_resolution           true
% 3.17/0.99  --res_backward_subs_resolution          true
% 3.17/0.99  --res_orphan_elimination                true
% 3.17/0.99  --res_time_limit                        2.
% 3.17/0.99  --res_out_proof                         true
% 3.17/0.99  
% 3.17/0.99  ------ Superposition Options
% 3.17/0.99  
% 3.17/0.99  --superposition_flag                    true
% 3.17/0.99  --sup_passive_queue_type                priority_queues
% 3.17/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/0.99  --sup_passive_queues_freq               [1;4]
% 3.17/0.99  --demod_completeness_check              fast
% 3.17/0.99  --demod_use_ground                      true
% 3.17/0.99  --sup_to_prop_solver                    passive
% 3.17/0.99  --sup_prop_simpl_new                    true
% 3.17/0.99  --sup_prop_simpl_given                  true
% 3.17/0.99  --sup_fun_splitting                     false
% 3.17/0.99  --sup_smt_interval                      50000
% 3.17/0.99  
% 3.17/0.99  ------ Superposition Simplification Setup
% 3.17/0.99  
% 3.17/0.99  --sup_indices_passive                   []
% 3.17/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.99  --sup_full_bw                           [BwDemod]
% 3.17/0.99  --sup_immed_triv                        [TrivRules]
% 3.17/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.99  --sup_immed_bw_main                     []
% 3.17/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.99  
% 3.17/0.99  ------ Combination Options
% 3.17/0.99  
% 3.17/0.99  --comb_res_mult                         3
% 3.17/0.99  --comb_sup_mult                         2
% 3.17/0.99  --comb_inst_mult                        10
% 3.17/0.99  
% 3.17/0.99  ------ Debug Options
% 3.17/0.99  
% 3.17/0.99  --dbg_backtrace                         false
% 3.17/0.99  --dbg_dump_prop_clauses                 false
% 3.17/0.99  --dbg_dump_prop_clauses_file            -
% 3.17/0.99  --dbg_out_stat                          false
% 3.17/0.99  ------ Parsing...
% 3.17/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.17/0.99  
% 3.17/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.17/0.99  
% 3.17/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.17/0.99  
% 3.17/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.17/0.99  ------ Proving...
% 3.17/0.99  ------ Problem Properties 
% 3.17/0.99  
% 3.17/0.99  
% 3.17/0.99  clauses                                 8
% 3.17/0.99  conjectures                             2
% 3.17/0.99  EPR                                     1
% 3.17/0.99  Horn                                    6
% 3.17/0.99  unary                                   1
% 3.17/0.99  binary                                  6
% 3.17/0.99  lits                                    17
% 3.17/0.99  lits eq                                 17
% 3.17/0.99  fd_pure                                 0
% 3.17/0.99  fd_pseudo                               0
% 3.17/0.99  fd_cond                                 0
% 3.17/0.99  fd_pseudo_cond                          4
% 3.17/0.99  AC symbols                              0
% 3.17/0.99  
% 3.17/0.99  ------ Input Options Time Limit: Unbounded
% 3.17/0.99  
% 3.17/0.99  
% 3.17/0.99  ------ 
% 3.17/0.99  Current options:
% 3.17/0.99  ------ 
% 3.17/0.99  
% 3.17/0.99  ------ Input Options
% 3.17/0.99  
% 3.17/0.99  --out_options                           all
% 3.17/0.99  --tptp_safe_out                         true
% 3.17/0.99  --problem_path                          ""
% 3.17/0.99  --include_path                          ""
% 3.17/0.99  --clausifier                            res/vclausify_rel
% 3.17/0.99  --clausifier_options                    --mode clausify
% 3.17/0.99  --stdin                                 false
% 3.17/0.99  --stats_out                             sel
% 3.17/0.99  
% 3.17/0.99  ------ General Options
% 3.17/0.99  
% 3.17/0.99  --fof                                   false
% 3.17/0.99  --time_out_real                         604.99
% 3.17/0.99  --time_out_virtual                      -1.
% 3.17/0.99  --symbol_type_check                     false
% 3.17/0.99  --clausify_out                          false
% 3.17/0.99  --sig_cnt_out                           false
% 3.17/0.99  --trig_cnt_out                          false
% 3.17/0.99  --trig_cnt_out_tolerance                1.
% 3.17/0.99  --trig_cnt_out_sk_spl                   false
% 3.17/0.99  --abstr_cl_out                          false
% 3.17/0.99  
% 3.17/0.99  ------ Global Options
% 3.17/0.99  
% 3.17/0.99  --schedule                              none
% 3.17/0.99  --add_important_lit                     false
% 3.17/0.99  --prop_solver_per_cl                    1000
% 3.17/0.99  --min_unsat_core                        false
% 3.17/0.99  --soft_assumptions                      false
% 3.17/0.99  --soft_lemma_size                       3
% 3.17/0.99  --prop_impl_unit_size                   0
% 3.17/0.99  --prop_impl_unit                        []
% 3.17/0.99  --share_sel_clauses                     true
% 3.17/0.99  --reset_solvers                         false
% 3.17/0.99  --bc_imp_inh                            [conj_cone]
% 3.17/0.99  --conj_cone_tolerance                   3.
% 3.17/0.99  --extra_neg_conj                        none
% 3.17/0.99  --large_theory_mode                     true
% 3.17/0.99  --prolific_symb_bound                   200
% 3.17/0.99  --lt_threshold                          2000
% 3.17/0.99  --clause_weak_htbl                      true
% 3.17/0.99  --gc_record_bc_elim                     false
% 3.17/0.99  
% 3.17/0.99  ------ Preprocessing Options
% 3.17/0.99  
% 3.17/0.99  --preprocessing_flag                    true
% 3.17/0.99  --time_out_prep_mult                    0.1
% 3.17/0.99  --splitting_mode                        input
% 3.17/0.99  --splitting_grd                         true
% 3.17/0.99  --splitting_cvd                         false
% 3.17/0.99  --splitting_cvd_svl                     false
% 3.17/0.99  --splitting_nvd                         32
% 3.17/0.99  --sub_typing                            true
% 3.17/0.99  --prep_gs_sim                           false
% 3.17/0.99  --prep_unflatten                        true
% 3.17/0.99  --prep_res_sim                          true
% 3.17/0.99  --prep_upred                            true
% 3.17/0.99  --prep_sem_filter                       exhaustive
% 3.17/0.99  --prep_sem_filter_out                   false
% 3.17/0.99  --pred_elim                             false
% 3.17/0.99  --res_sim_input                         true
% 3.17/0.99  --eq_ax_congr_red                       true
% 3.17/0.99  --pure_diseq_elim                       true
% 3.17/0.99  --brand_transform                       false
% 3.17/0.99  --non_eq_to_eq                          false
% 3.17/0.99  --prep_def_merge                        true
% 3.17/0.99  --prep_def_merge_prop_impl              false
% 3.17/0.99  --prep_def_merge_mbd                    true
% 3.17/0.99  --prep_def_merge_tr_red                 false
% 3.17/0.99  --prep_def_merge_tr_cl                  false
% 3.17/0.99  --smt_preprocessing                     true
% 3.17/0.99  --smt_ac_axioms                         fast
% 3.17/0.99  --preprocessed_out                      false
% 3.17/0.99  --preprocessed_stats                    false
% 3.17/0.99  
% 3.17/0.99  ------ Abstraction refinement Options
% 3.17/0.99  
% 3.17/0.99  --abstr_ref                             []
% 3.17/0.99  --abstr_ref_prep                        false
% 3.17/0.99  --abstr_ref_until_sat                   false
% 3.17/0.99  --abstr_ref_sig_restrict                funpre
% 3.17/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/0.99  --abstr_ref_under                       []
% 3.17/0.99  
% 3.17/0.99  ------ SAT Options
% 3.17/0.99  
% 3.17/0.99  --sat_mode                              false
% 3.17/0.99  --sat_fm_restart_options                ""
% 3.17/0.99  --sat_gr_def                            false
% 3.17/0.99  --sat_epr_types                         true
% 3.17/0.99  --sat_non_cyclic_types                  false
% 3.17/0.99  --sat_finite_models                     false
% 3.17/0.99  --sat_fm_lemmas                         false
% 3.17/0.99  --sat_fm_prep                           false
% 3.17/0.99  --sat_fm_uc_incr                        true
% 3.17/0.99  --sat_out_model                         small
% 3.17/0.99  --sat_out_clauses                       false
% 3.17/0.99  
% 3.17/0.99  ------ QBF Options
% 3.17/0.99  
% 3.17/0.99  --qbf_mode                              false
% 3.17/0.99  --qbf_elim_univ                         false
% 3.17/0.99  --qbf_dom_inst                          none
% 3.17/0.99  --qbf_dom_pre_inst                      false
% 3.17/0.99  --qbf_sk_in                             false
% 3.17/0.99  --qbf_pred_elim                         true
% 3.17/0.99  --qbf_split                             512
% 3.17/0.99  
% 3.17/0.99  ------ BMC1 Options
% 3.17/0.99  
% 3.17/0.99  --bmc1_incremental                      false
% 3.17/0.99  --bmc1_axioms                           reachable_all
% 3.17/0.99  --bmc1_min_bound                        0
% 3.17/0.99  --bmc1_max_bound                        -1
% 3.17/0.99  --bmc1_max_bound_default                -1
% 3.17/0.99  --bmc1_symbol_reachability              true
% 3.17/0.99  --bmc1_property_lemmas                  false
% 3.17/0.99  --bmc1_k_induction                      false
% 3.17/0.99  --bmc1_non_equiv_states                 false
% 3.17/0.99  --bmc1_deadlock                         false
% 3.17/0.99  --bmc1_ucm                              false
% 3.17/0.99  --bmc1_add_unsat_core                   none
% 3.17/0.99  --bmc1_unsat_core_children              false
% 3.17/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/0.99  --bmc1_out_stat                         full
% 3.17/0.99  --bmc1_ground_init                      false
% 3.17/0.99  --bmc1_pre_inst_next_state              false
% 3.17/0.99  --bmc1_pre_inst_state                   false
% 3.17/0.99  --bmc1_pre_inst_reach_state             false
% 3.17/0.99  --bmc1_out_unsat_core                   false
% 3.17/0.99  --bmc1_aig_witness_out                  false
% 3.17/0.99  --bmc1_verbose                          false
% 3.17/0.99  --bmc1_dump_clauses_tptp                false
% 3.17/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.17/0.99  --bmc1_dump_file                        -
% 3.17/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.17/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.17/0.99  --bmc1_ucm_extend_mode                  1
% 3.17/0.99  --bmc1_ucm_init_mode                    2
% 3.17/0.99  --bmc1_ucm_cone_mode                    none
% 3.17/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.17/0.99  --bmc1_ucm_relax_model                  4
% 3.17/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.17/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/0.99  --bmc1_ucm_layered_model                none
% 3.17/0.99  --bmc1_ucm_max_lemma_size               10
% 3.17/0.99  
% 3.17/0.99  ------ AIG Options
% 3.17/0.99  
% 3.17/0.99  --aig_mode                              false
% 3.17/0.99  
% 3.17/0.99  ------ Instantiation Options
% 3.17/0.99  
% 3.17/0.99  --instantiation_flag                    true
% 3.17/0.99  --inst_sos_flag                         false
% 3.17/0.99  --inst_sos_phase                        true
% 3.17/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/0.99  --inst_lit_sel_side                     num_symb
% 3.17/0.99  --inst_solver_per_active                1400
% 3.17/0.99  --inst_solver_calls_frac                1.
% 3.17/0.99  --inst_passive_queue_type               priority_queues
% 3.17/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/0.99  --inst_passive_queues_freq              [25;2]
% 3.17/0.99  --inst_dismatching                      true
% 3.17/0.99  --inst_eager_unprocessed_to_passive     true
% 3.17/0.99  --inst_prop_sim_given                   true
% 3.17/0.99  --inst_prop_sim_new                     false
% 3.17/0.99  --inst_subs_new                         false
% 3.17/0.99  --inst_eq_res_simp                      false
% 3.17/0.99  --inst_subs_given                       false
% 3.17/0.99  --inst_orphan_elimination               true
% 3.17/0.99  --inst_learning_loop_flag               true
% 3.17/0.99  --inst_learning_start                   3000
% 3.17/0.99  --inst_learning_factor                  2
% 3.17/0.99  --inst_start_prop_sim_after_learn       3
% 3.17/0.99  --inst_sel_renew                        solver
% 3.17/0.99  --inst_lit_activity_flag                true
% 3.17/0.99  --inst_restr_to_given                   false
% 3.17/0.99  --inst_activity_threshold               500
% 3.17/0.99  --inst_out_proof                        true
% 3.17/0.99  
% 3.17/0.99  ------ Resolution Options
% 3.17/0.99  
% 3.17/0.99  --resolution_flag                       true
% 3.17/0.99  --res_lit_sel                           adaptive
% 3.17/0.99  --res_lit_sel_side                      none
% 3.17/0.99  --res_ordering                          kbo
% 3.17/0.99  --res_to_prop_solver                    active
% 3.17/0.99  --res_prop_simpl_new                    false
% 3.17/0.99  --res_prop_simpl_given                  true
% 3.17/0.99  --res_passive_queue_type                priority_queues
% 3.17/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/0.99  --res_passive_queues_freq               [15;5]
% 3.17/0.99  --res_forward_subs                      full
% 3.17/0.99  --res_backward_subs                     full
% 3.17/0.99  --res_forward_subs_resolution           true
% 3.17/0.99  --res_backward_subs_resolution          true
% 3.17/0.99  --res_orphan_elimination                true
% 3.17/0.99  --res_time_limit                        2.
% 3.17/0.99  --res_out_proof                         true
% 3.17/0.99  
% 3.17/0.99  ------ Superposition Options
% 3.17/0.99  
% 3.17/0.99  --superposition_flag                    true
% 3.17/0.99  --sup_passive_queue_type                priority_queues
% 3.17/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/0.99  --sup_passive_queues_freq               [1;4]
% 3.17/0.99  --demod_completeness_check              fast
% 3.17/0.99  --demod_use_ground                      true
% 3.17/0.99  --sup_to_prop_solver                    passive
% 3.17/0.99  --sup_prop_simpl_new                    true
% 3.17/0.99  --sup_prop_simpl_given                  true
% 3.17/0.99  --sup_fun_splitting                     false
% 3.17/0.99  --sup_smt_interval                      50000
% 3.17/0.99  
% 3.17/0.99  ------ Superposition Simplification Setup
% 3.17/0.99  
% 3.17/0.99  --sup_indices_passive                   []
% 3.17/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.99  --sup_full_bw                           [BwDemod]
% 3.17/0.99  --sup_immed_triv                        [TrivRules]
% 3.17/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.99  --sup_immed_bw_main                     []
% 3.17/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.99  
% 3.17/0.99  ------ Combination Options
% 3.17/0.99  
% 3.17/0.99  --comb_res_mult                         3
% 3.17/0.99  --comb_sup_mult                         2
% 3.17/0.99  --comb_inst_mult                        10
% 3.17/0.99  
% 3.17/0.99  ------ Debug Options
% 3.17/0.99  
% 3.17/0.99  --dbg_backtrace                         false
% 3.17/0.99  --dbg_dump_prop_clauses                 false
% 3.17/0.99  --dbg_dump_prop_clauses_file            -
% 3.17/0.99  --dbg_out_stat                          false
% 3.17/0.99  
% 3.17/0.99  
% 3.17/0.99  
% 3.17/0.99  
% 3.17/0.99  ------ Proving...
% 3.17/0.99  
% 3.17/0.99  
% 3.17/0.99  % SZS status Theorem for theBenchmark.p
% 3.17/0.99  
% 3.17/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.17/0.99  
% 3.17/0.99  fof(f4,conjecture,(
% 3.17/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 3.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f5,negated_conjecture,(
% 3.17/0.99    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 3.17/0.99    inference(negated_conjecture,[],[f4])).
% 3.17/0.99  
% 3.17/0.99  fof(f10,plain,(
% 3.17/0.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7))),
% 3.17/0.99    inference(ennf_transformation,[],[f5])).
% 3.17/0.99  
% 3.17/0.99  fof(f19,plain,(
% 3.17/0.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)) => ((sK7 != sK11 | sK6 != sK10 | sK5 != sK9 | sK4 != sK8) & k4_mcart_1(sK4,sK5,sK6,sK7) = k4_mcart_1(sK8,sK9,sK10,sK11))),
% 3.17/0.99    introduced(choice_axiom,[])).
% 3.17/0.99  
% 3.17/0.99  fof(f20,plain,(
% 3.17/0.99    (sK7 != sK11 | sK6 != sK10 | sK5 != sK9 | sK4 != sK8) & k4_mcart_1(sK4,sK5,sK6,sK7) = k4_mcart_1(sK8,sK9,sK10,sK11)),
% 3.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f10,f19])).
% 3.17/0.99  
% 3.17/0.99  fof(f28,plain,(
% 3.17/0.99    k4_mcart_1(sK4,sK5,sK6,sK7) = k4_mcart_1(sK8,sK9,sK10,sK11)),
% 3.17/0.99    inference(cnf_transformation,[],[f20])).
% 3.17/0.99  
% 3.17/0.99  fof(f3,axiom,(
% 3.17/0.99    ! [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)),
% 3.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f27,plain,(
% 3.17/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 3.17/0.99    inference(cnf_transformation,[],[f3])).
% 3.17/0.99  
% 3.17/0.99  fof(f30,plain,(
% 3.17/0.99    k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7) = k4_tarski(k4_tarski(k4_tarski(sK8,sK9),sK10),sK11)),
% 3.17/0.99    inference(definition_unfolding,[],[f28,f27,f27])).
% 3.17/0.99  
% 3.17/0.99  fof(f1,axiom,(
% 3.17/0.99    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X1] : (k1_mcart_1(X0) = X1 <=> ! [X2,X3] : (k4_tarski(X2,X3) = X0 => X1 = X2)))),
% 3.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f6,plain,(
% 3.17/0.99    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (k4_tarski(X4,X5) = X0 => X3 = X4)))),
% 3.17/0.99    inference(rectify,[],[f1])).
% 3.17/0.99  
% 3.17/0.99  fof(f8,plain,(
% 3.17/0.99    ! [X0] : (! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 3.17/0.99    inference(ennf_transformation,[],[f6])).
% 3.17/0.99  
% 3.17/0.99  fof(f11,plain,(
% 3.17/0.99    ! [X0] : (! [X3] : ((k1_mcart_1(X0) = X3 | ? [X4,X5] : (X3 != X4 & k4_tarski(X4,X5) = X0)) & (! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X3)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 3.17/0.99    inference(nnf_transformation,[],[f8])).
% 3.17/0.99  
% 3.17/0.99  fof(f12,plain,(
% 3.17/0.99    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | ? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 3.17/0.99    inference(rectify,[],[f11])).
% 3.17/0.99  
% 3.17/0.99  fof(f13,plain,(
% 3.17/0.99    ! [X1,X0] : (? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0) => (sK0(X0,X1) != X1 & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0))),
% 3.17/0.99    introduced(choice_axiom,[])).
% 3.17/0.99  
% 3.17/0.99  fof(f14,plain,(
% 3.17/0.99    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | (sK0(X0,X1) != X1 & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 3.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 3.17/0.99  
% 3.17/0.99  fof(f21,plain,(
% 3.17/0.99    ( ! [X6,X4,X0,X7,X5,X1] : (X1 = X4 | k4_tarski(X4,X5) != X0 | k1_mcart_1(X0) != X1 | k4_tarski(X6,X7) != X0) )),
% 3.17/0.99    inference(cnf_transformation,[],[f14])).
% 3.17/0.99  
% 3.17/0.99  fof(f33,plain,(
% 3.17/0.99    ( ! [X6,X4,X7,X5,X1] : (X1 = X4 | k1_mcart_1(k4_tarski(X4,X5)) != X1 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 3.17/0.99    inference(equality_resolution,[],[f21])).
% 3.17/0.99  
% 3.17/0.99  fof(f34,plain,(
% 3.17/0.99    ( ! [X6,X4,X7,X5] : (k1_mcart_1(k4_tarski(X4,X5)) = X4 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 3.17/0.99    inference(equality_resolution,[],[f33])).
% 3.17/0.99  
% 3.17/0.99  fof(f2,axiom,(
% 3.17/0.99    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X1] : (k2_mcart_1(X0) = X1 <=> ! [X2,X3] : (k4_tarski(X2,X3) = X0 => X1 = X3)))),
% 3.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f7,plain,(
% 3.17/0.99    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X3] : (k2_mcart_1(X0) = X3 <=> ! [X4,X5] : (k4_tarski(X4,X5) = X0 => X3 = X5)))),
% 3.17/0.99    inference(rectify,[],[f2])).
% 3.17/0.99  
% 3.17/0.99  fof(f9,plain,(
% 3.17/0.99    ! [X0] : (! [X3] : (k2_mcart_1(X0) = X3 <=> ! [X4,X5] : (X3 = X5 | k4_tarski(X4,X5) != X0)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 3.17/0.99    inference(ennf_transformation,[],[f7])).
% 3.17/0.99  
% 3.17/0.99  fof(f15,plain,(
% 3.17/0.99    ! [X0] : (! [X3] : ((k2_mcart_1(X0) = X3 | ? [X4,X5] : (X3 != X5 & k4_tarski(X4,X5) = X0)) & (! [X4,X5] : (X3 = X5 | k4_tarski(X4,X5) != X0) | k2_mcart_1(X0) != X3)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 3.17/0.99    inference(nnf_transformation,[],[f9])).
% 3.17/0.99  
% 3.17/0.99  fof(f16,plain,(
% 3.17/0.99    ! [X0] : (! [X1] : ((k2_mcart_1(X0) = X1 | ? [X2,X3] : (X1 != X3 & k4_tarski(X2,X3) = X0)) & (! [X4,X5] : (X1 = X5 | k4_tarski(X4,X5) != X0) | k2_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 3.17/0.99    inference(rectify,[],[f15])).
% 3.17/0.99  
% 3.17/0.99  fof(f17,plain,(
% 3.17/0.99    ! [X1,X0] : (? [X2,X3] : (X1 != X3 & k4_tarski(X2,X3) = X0) => (sK3(X0,X1) != X1 & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0))),
% 3.17/0.99    introduced(choice_axiom,[])).
% 3.17/0.99  
% 3.17/0.99  fof(f18,plain,(
% 3.17/0.99    ! [X0] : (! [X1] : ((k2_mcart_1(X0) = X1 | (sK3(X0,X1) != X1 & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0)) & (! [X4,X5] : (X1 = X5 | k4_tarski(X4,X5) != X0) | k2_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 3.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).
% 3.17/0.99  
% 3.17/0.99  fof(f24,plain,(
% 3.17/0.99    ( ! [X6,X4,X0,X7,X5,X1] : (X1 = X5 | k4_tarski(X4,X5) != X0 | k2_mcart_1(X0) != X1 | k4_tarski(X6,X7) != X0) )),
% 3.17/0.99    inference(cnf_transformation,[],[f18])).
% 3.17/0.99  
% 3.17/0.99  fof(f37,plain,(
% 3.17/0.99    ( ! [X6,X4,X7,X5,X1] : (X1 = X5 | k2_mcart_1(k4_tarski(X4,X5)) != X1 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 3.17/0.99    inference(equality_resolution,[],[f24])).
% 3.17/0.99  
% 3.17/0.99  fof(f38,plain,(
% 3.17/0.99    ( ! [X6,X4,X7,X5] : (k2_mcart_1(k4_tarski(X4,X5)) = X5 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 3.17/0.99    inference(equality_resolution,[],[f37])).
% 3.17/0.99  
% 3.17/0.99  fof(f29,plain,(
% 3.17/0.99    sK7 != sK11 | sK6 != sK10 | sK5 != sK9 | sK4 != sK8),
% 3.17/0.99    inference(cnf_transformation,[],[f20])).
% 3.17/0.99  
% 3.17/0.99  cnf(c_7,negated_conjecture,
% 3.17/0.99      ( k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7) = k4_tarski(k4_tarski(k4_tarski(sK8,sK9),sK10),sK11) ),
% 3.17/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2,plain,
% 3.17/0.99      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
% 3.17/0.99      | k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.17/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_92,plain,
% 3.17/0.99      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.17/0.99      inference(equality_resolution,[status(thm)],[c_2]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_199,plain,
% 3.17/0.99      ( k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7)) = k4_tarski(k4_tarski(sK8,sK9),sK10) ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_7,c_92]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_200,plain,
% 3.17/0.99      ( k4_tarski(k4_tarski(sK8,sK9),sK10) = k4_tarski(k4_tarski(sK4,sK5),sK6) ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_199,c_92]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_865,plain,
% 3.17/0.99      ( k1_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6)) = k4_tarski(sK8,sK9) ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_200,c_92]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_892,plain,
% 3.17/0.99      ( k4_tarski(sK8,sK9) = k4_tarski(sK4,sK5) ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_865,c_92]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_5,plain,
% 3.17/0.99      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
% 3.17/0.99      | k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.17/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_117,plain,
% 3.17/0.99      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.17/0.99      inference(equality_resolution,[status(thm)],[c_5]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3707,plain,
% 3.17/0.99      ( k2_mcart_1(k4_tarski(sK4,sK5)) = sK9 ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_892,c_117]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3897,plain,
% 3.17/0.99      ( sK9 = sK5 ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_3707,c_117]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3710,plain,
% 3.17/0.99      ( k1_mcart_1(k4_tarski(sK4,sK5)) = sK8 ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_892,c_92]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3790,plain,
% 3.17/0.99      ( sK8 = sK4 ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_3710,c_92]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_451,plain,
% 3.17/0.99      ( k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7)) = sK11 ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_7,c_117]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_458,plain,
% 3.17/0.99      ( sK11 = sK7 ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_451,c_117]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6,negated_conjecture,
% 3.17/0.99      ( sK4 != sK8 | sK5 != sK9 | sK6 != sK10 | sK7 != sK11 ),
% 3.17/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3392,plain,
% 3.17/0.99      ( sK8 != sK4 | sK9 != sK5 | sK10 != sK6 | sK7 != sK7 ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_458,c_6]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3393,plain,
% 3.17/0.99      ( sK8 != sK4 | sK9 != sK5 | sK10 != sK6 ),
% 3.17/0.99      inference(equality_resolution_simp,[status(thm)],[c_3392]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_862,plain,
% 3.17/0.99      ( k2_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6)) = sK10 ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_200,c_117]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_953,plain,
% 3.17/0.99      ( sK10 = sK6 ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_862,c_117]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(contradiction,plain,
% 3.17/0.99      ( $false ),
% 3.17/0.99      inference(minisat,[status(thm)],[c_3897,c_3790,c_3393,c_953]) ).
% 3.17/0.99  
% 3.17/0.99  
% 3.17/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.17/0.99  
% 3.17/0.99  ------                               Statistics
% 3.17/0.99  
% 3.17/0.99  ------ Selected
% 3.17/0.99  
% 3.17/0.99  total_time:                             0.152
% 3.17/0.99  
%------------------------------------------------------------------------------
