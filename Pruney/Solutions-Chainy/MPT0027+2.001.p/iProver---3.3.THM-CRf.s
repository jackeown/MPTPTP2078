%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:22 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   62 (  94 expanded)
%              Number of clauses        :   39 (  46 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  152 ( 302 expanded)
%              Number of equality atoms :   76 ( 114 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( ( r1_tarski(X3,X2)
                & r1_tarski(X3,X1) )
             => r1_tarski(X3,X0) )
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X1,X2) != X0
        & ! [X3] :
            ( r1_tarski(X3,X0)
            | ~ r1_tarski(X3,X2)
            | ~ r1_tarski(X3,X1) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK1,sK2) != sK0
      & ! [X3] :
          ( r1_tarski(X3,sK0)
          | ~ r1_tarski(X3,sK2)
          | ~ r1_tarski(X3,sK1) )
      & r1_tarski(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( k3_xboole_0(sK1,sK2) != sK0
    & ! [X3] :
        ( r1_tarski(X3,sK0)
        | ~ r1_tarski(X3,sK2)
        | ~ r1_tarski(X3,sK1) )
    & r1_tarski(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f22,plain,(
    ! [X3] :
      ( r1_tarski(X3,sK0)
      | ~ r1_tarski(X3,sK2)
      | ~ r1_tarski(X3,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    k3_xboole_0(sK1,sK2) != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_75,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_859,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,sK1),X0) != X1
    | sK0 != X1
    | sK0 = k2_xboole_0(k3_xboole_0(sK2,sK1),X0) ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_860,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,sK1),sK0) != sK0
    | sK0 = k2_xboole_0(k3_xboole_0(sK2,sK1),sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_184,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_381,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_184])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(X0,sK0)
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(X0,sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_182,plain,
    ( r1_tarski(X0,sK0) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_383,plain,
    ( r1_tarski(k3_xboole_0(sK2,X0),sK0) = iProver_top
    | r1_tarski(k3_xboole_0(sK2,X0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_184,c_182])).

cnf(c_663,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_381,c_383])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_185,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_848,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,sK1),sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_663,c_185])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_591,plain,
    ( k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) = k2_xboole_0(k3_xboole_0(sK2,sK1),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_593,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) = k2_xboole_0(k3_xboole_0(sK2,sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_399,plain,
    ( k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) != X1
    | sK0 != X1
    | sK0 = k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_590,plain,
    ( k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) != k2_xboole_0(k3_xboole_0(sK2,sK1),X0)
    | sK0 = k2_xboole_0(X0,k3_xboole_0(sK2,sK1))
    | sK0 != k2_xboole_0(k3_xboole_0(sK2,sK1),X0) ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_592,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k2_xboole_0(k3_xboole_0(sK2,sK1),sK0)
    | sK0 != k2_xboole_0(k3_xboole_0(sK2,sK1),sK0)
    | sK0 = k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_414,plain,
    ( r1_tarski(X0,k3_xboole_0(sK2,sK1))
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_416,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK2,sK1))
    | ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_227,plain,
    ( k3_xboole_0(sK1,sK2) != X0
    | k3_xboole_0(sK1,sK2) = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_341,plain,
    ( k3_xboole_0(sK1,sK2) != k2_xboole_0(X0,k3_xboole_0(sK2,sK1))
    | k3_xboole_0(sK1,sK2) = sK0
    | sK0 != k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_342,plain,
    ( k3_xboole_0(sK1,sK2) != k2_xboole_0(sK0,k3_xboole_0(sK2,sK1))
    | k3_xboole_0(sK1,sK2) = sK0
    | sK0 != k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_287,plain,
    ( ~ r1_tarski(X0,k3_xboole_0(sK2,sK1))
    | k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_290,plain,
    ( ~ r1_tarski(sK0,k3_xboole_0(sK2,sK1))
    | k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_235,plain,
    ( X0 != X1
    | k3_xboole_0(sK1,sK2) != X1
    | k3_xboole_0(sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_260,plain,
    ( X0 != k3_xboole_0(sK2,sK1)
    | k3_xboole_0(sK1,sK2) = X0
    | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_286,plain,
    ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1)
    | k3_xboole_0(sK1,sK2) = k2_xboole_0(X0,k3_xboole_0(sK2,sK1))
    | k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_288,plain,
    ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1)
    | k3_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k3_xboole_0(sK2,sK1))
    | k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_232,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_74,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_80,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_5,negated_conjecture,
    ( k3_xboole_0(sK1,sK2) != sK0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_860,c_848,c_593,c_592,c_416,c_342,c_290,c_288,c_232,c_80,c_5,c_7,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:55:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 0.88/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.88/0.98  
% 0.88/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.88/0.98  
% 0.88/0.98  ------  iProver source info
% 0.88/0.98  
% 0.88/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.88/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.88/0.98  git: non_committed_changes: false
% 0.88/0.98  git: last_make_outside_of_git: false
% 0.88/0.98  
% 0.88/0.98  ------ 
% 0.88/0.98  
% 0.88/0.98  ------ Input Options
% 0.88/0.98  
% 0.88/0.98  --out_options                           all
% 0.88/0.98  --tptp_safe_out                         true
% 0.88/0.98  --problem_path                          ""
% 0.88/0.98  --include_path                          ""
% 0.88/0.98  --clausifier                            res/vclausify_rel
% 0.88/0.98  --clausifier_options                    --mode clausify
% 0.88/0.98  --stdin                                 false
% 0.88/0.98  --stats_out                             all
% 0.88/0.98  
% 0.88/0.98  ------ General Options
% 0.88/0.98  
% 0.88/0.98  --fof                                   false
% 0.88/0.98  --time_out_real                         305.
% 0.88/0.98  --time_out_virtual                      -1.
% 0.88/0.98  --symbol_type_check                     false
% 0.88/0.98  --clausify_out                          false
% 0.88/0.98  --sig_cnt_out                           false
% 0.88/0.98  --trig_cnt_out                          false
% 0.88/0.98  --trig_cnt_out_tolerance                1.
% 0.88/0.98  --trig_cnt_out_sk_spl                   false
% 0.88/0.98  --abstr_cl_out                          false
% 0.88/0.98  
% 0.88/0.98  ------ Global Options
% 0.88/0.98  
% 0.88/0.98  --schedule                              default
% 0.88/0.98  --add_important_lit                     false
% 0.88/0.98  --prop_solver_per_cl                    1000
% 0.88/0.98  --min_unsat_core                        false
% 0.88/0.98  --soft_assumptions                      false
% 0.88/0.98  --soft_lemma_size                       3
% 0.88/0.98  --prop_impl_unit_size                   0
% 0.88/0.98  --prop_impl_unit                        []
% 0.88/0.98  --share_sel_clauses                     true
% 0.88/0.98  --reset_solvers                         false
% 0.88/0.98  --bc_imp_inh                            [conj_cone]
% 0.88/0.98  --conj_cone_tolerance                   3.
% 0.88/0.98  --extra_neg_conj                        none
% 0.88/0.98  --large_theory_mode                     true
% 0.88/0.98  --prolific_symb_bound                   200
% 0.88/0.98  --lt_threshold                          2000
% 0.88/0.98  --clause_weak_htbl                      true
% 0.88/0.98  --gc_record_bc_elim                     false
% 0.88/0.98  
% 0.88/0.98  ------ Preprocessing Options
% 0.88/0.98  
% 0.88/0.98  --preprocessing_flag                    true
% 0.88/0.98  --time_out_prep_mult                    0.1
% 0.88/0.98  --splitting_mode                        input
% 0.88/0.98  --splitting_grd                         true
% 0.88/0.98  --splitting_cvd                         false
% 0.88/0.98  --splitting_cvd_svl                     false
% 0.88/0.98  --splitting_nvd                         32
% 0.88/0.98  --sub_typing                            true
% 0.88/0.98  --prep_gs_sim                           true
% 0.88/0.98  --prep_unflatten                        true
% 0.88/0.98  --prep_res_sim                          true
% 0.88/0.98  --prep_upred                            true
% 0.88/0.98  --prep_sem_filter                       exhaustive
% 0.88/0.98  --prep_sem_filter_out                   false
% 0.88/0.98  --pred_elim                             true
% 0.88/0.98  --res_sim_input                         true
% 0.88/0.98  --eq_ax_congr_red                       true
% 0.88/0.98  --pure_diseq_elim                       true
% 0.88/0.98  --brand_transform                       false
% 0.88/0.98  --non_eq_to_eq                          false
% 0.88/0.98  --prep_def_merge                        true
% 0.88/0.98  --prep_def_merge_prop_impl              false
% 0.88/0.98  --prep_def_merge_mbd                    true
% 0.88/0.98  --prep_def_merge_tr_red                 false
% 0.88/0.98  --prep_def_merge_tr_cl                  false
% 0.88/0.98  --smt_preprocessing                     true
% 0.88/0.98  --smt_ac_axioms                         fast
% 0.88/0.98  --preprocessed_out                      false
% 0.88/0.98  --preprocessed_stats                    false
% 0.88/0.98  
% 0.88/0.98  ------ Abstraction refinement Options
% 0.88/0.98  
% 0.88/0.98  --abstr_ref                             []
% 0.88/0.98  --abstr_ref_prep                        false
% 0.88/0.98  --abstr_ref_until_sat                   false
% 0.88/0.98  --abstr_ref_sig_restrict                funpre
% 0.88/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.88/0.98  --abstr_ref_under                       []
% 0.88/0.98  
% 0.88/0.98  ------ SAT Options
% 0.88/0.98  
% 0.88/0.98  --sat_mode                              false
% 0.88/0.98  --sat_fm_restart_options                ""
% 0.88/0.98  --sat_gr_def                            false
% 0.88/0.98  --sat_epr_types                         true
% 0.88/0.98  --sat_non_cyclic_types                  false
% 0.88/0.98  --sat_finite_models                     false
% 0.88/0.98  --sat_fm_lemmas                         false
% 0.88/0.98  --sat_fm_prep                           false
% 0.88/0.98  --sat_fm_uc_incr                        true
% 0.88/0.98  --sat_out_model                         small
% 0.88/0.98  --sat_out_clauses                       false
% 0.88/0.98  
% 0.88/0.98  ------ QBF Options
% 0.88/0.98  
% 0.88/0.98  --qbf_mode                              false
% 0.88/0.98  --qbf_elim_univ                         false
% 0.88/0.98  --qbf_dom_inst                          none
% 0.88/0.98  --qbf_dom_pre_inst                      false
% 0.88/0.98  --qbf_sk_in                             false
% 0.88/0.98  --qbf_pred_elim                         true
% 0.88/0.98  --qbf_split                             512
% 0.88/0.98  
% 0.88/0.98  ------ BMC1 Options
% 0.88/0.98  
% 0.88/0.98  --bmc1_incremental                      false
% 0.88/0.98  --bmc1_axioms                           reachable_all
% 0.88/0.98  --bmc1_min_bound                        0
% 0.88/0.98  --bmc1_max_bound                        -1
% 0.88/0.98  --bmc1_max_bound_default                -1
% 0.88/0.98  --bmc1_symbol_reachability              true
% 0.88/0.98  --bmc1_property_lemmas                  false
% 0.88/0.98  --bmc1_k_induction                      false
% 0.88/0.98  --bmc1_non_equiv_states                 false
% 0.88/0.98  --bmc1_deadlock                         false
% 0.88/0.98  --bmc1_ucm                              false
% 0.88/0.98  --bmc1_add_unsat_core                   none
% 0.88/0.98  --bmc1_unsat_core_children              false
% 0.88/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.88/0.98  --bmc1_out_stat                         full
% 0.88/0.98  --bmc1_ground_init                      false
% 0.88/0.98  --bmc1_pre_inst_next_state              false
% 0.88/0.98  --bmc1_pre_inst_state                   false
% 0.88/0.98  --bmc1_pre_inst_reach_state             false
% 0.88/0.98  --bmc1_out_unsat_core                   false
% 0.88/0.98  --bmc1_aig_witness_out                  false
% 0.88/0.98  --bmc1_verbose                          false
% 0.88/0.98  --bmc1_dump_clauses_tptp                false
% 0.88/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.88/0.98  --bmc1_dump_file                        -
% 0.88/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.88/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.88/0.98  --bmc1_ucm_extend_mode                  1
% 0.88/0.98  --bmc1_ucm_init_mode                    2
% 0.88/0.98  --bmc1_ucm_cone_mode                    none
% 0.88/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.88/0.98  --bmc1_ucm_relax_model                  4
% 0.88/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.88/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.88/0.98  --bmc1_ucm_layered_model                none
% 0.88/0.98  --bmc1_ucm_max_lemma_size               10
% 0.88/0.98  
% 0.88/0.98  ------ AIG Options
% 0.88/0.98  
% 0.88/0.98  --aig_mode                              false
% 0.88/0.98  
% 0.88/0.98  ------ Instantiation Options
% 0.88/0.98  
% 0.88/0.98  --instantiation_flag                    true
% 0.88/0.98  --inst_sos_flag                         false
% 0.88/0.98  --inst_sos_phase                        true
% 0.88/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.88/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.88/0.98  --inst_lit_sel_side                     num_symb
% 0.88/0.98  --inst_solver_per_active                1400
% 0.88/0.98  --inst_solver_calls_frac                1.
% 0.88/0.98  --inst_passive_queue_type               priority_queues
% 0.88/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.88/0.98  --inst_passive_queues_freq              [25;2]
% 0.88/0.98  --inst_dismatching                      true
% 0.88/0.98  --inst_eager_unprocessed_to_passive     true
% 0.88/0.98  --inst_prop_sim_given                   true
% 0.88/0.98  --inst_prop_sim_new                     false
% 0.88/0.98  --inst_subs_new                         false
% 0.88/0.98  --inst_eq_res_simp                      false
% 0.88/0.98  --inst_subs_given                       false
% 0.88/0.98  --inst_orphan_elimination               true
% 0.88/0.98  --inst_learning_loop_flag               true
% 0.88/0.98  --inst_learning_start                   3000
% 0.88/0.98  --inst_learning_factor                  2
% 0.88/0.98  --inst_start_prop_sim_after_learn       3
% 0.88/0.98  --inst_sel_renew                        solver
% 0.88/0.98  --inst_lit_activity_flag                true
% 0.88/0.98  --inst_restr_to_given                   false
% 0.88/0.98  --inst_activity_threshold               500
% 0.88/0.98  --inst_out_proof                        true
% 0.88/0.98  
% 0.88/0.98  ------ Resolution Options
% 0.88/0.98  
% 0.88/0.98  --resolution_flag                       true
% 0.88/0.98  --res_lit_sel                           adaptive
% 0.88/0.98  --res_lit_sel_side                      none
% 0.88/0.98  --res_ordering                          kbo
% 0.88/0.98  --res_to_prop_solver                    active
% 0.88/0.98  --res_prop_simpl_new                    false
% 0.88/0.98  --res_prop_simpl_given                  true
% 0.88/0.98  --res_passive_queue_type                priority_queues
% 0.88/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.88/0.98  --res_passive_queues_freq               [15;5]
% 0.88/0.98  --res_forward_subs                      full
% 0.88/0.98  --res_backward_subs                     full
% 0.88/0.98  --res_forward_subs_resolution           true
% 0.88/0.98  --res_backward_subs_resolution          true
% 0.88/0.98  --res_orphan_elimination                true
% 0.88/0.98  --res_time_limit                        2.
% 0.88/0.98  --res_out_proof                         true
% 0.88/0.98  
% 0.88/0.98  ------ Superposition Options
% 0.88/0.98  
% 0.88/0.98  --superposition_flag                    true
% 0.88/0.98  --sup_passive_queue_type                priority_queues
% 0.88/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.88/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.88/0.98  --demod_completeness_check              fast
% 0.88/0.98  --demod_use_ground                      true
% 0.88/0.98  --sup_to_prop_solver                    passive
% 0.88/0.98  --sup_prop_simpl_new                    true
% 0.88/0.98  --sup_prop_simpl_given                  true
% 0.88/0.98  --sup_fun_splitting                     false
% 0.88/0.98  --sup_smt_interval                      50000
% 0.88/0.98  
% 0.88/0.98  ------ Superposition Simplification Setup
% 0.88/0.98  
% 0.88/0.98  --sup_indices_passive                   []
% 0.88/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.88/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.98  --sup_full_bw                           [BwDemod]
% 0.88/0.98  --sup_immed_triv                        [TrivRules]
% 0.88/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.88/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.98  --sup_immed_bw_main                     []
% 0.88/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.88/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/0.98  
% 0.88/0.98  ------ Combination Options
% 0.88/0.98  
% 0.88/0.98  --comb_res_mult                         3
% 0.88/0.98  --comb_sup_mult                         2
% 0.88/0.98  --comb_inst_mult                        10
% 0.88/0.98  
% 0.88/0.98  ------ Debug Options
% 0.88/0.98  
% 0.88/0.98  --dbg_backtrace                         false
% 0.88/0.98  --dbg_dump_prop_clauses                 false
% 0.88/0.98  --dbg_dump_prop_clauses_file            -
% 0.88/0.98  --dbg_out_stat                          false
% 0.88/0.98  ------ Parsing...
% 0.88/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.88/0.98  
% 0.88/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.88/0.98  
% 0.88/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.88/0.98  
% 0.88/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.88/0.98  ------ Proving...
% 0.88/0.98  ------ Problem Properties 
% 0.88/0.98  
% 0.88/0.98  
% 0.88/0.98  clauses                                 9
% 0.88/0.98  conjectures                             4
% 0.88/0.98  EPR                                     3
% 0.88/0.98  Horn                                    9
% 0.88/0.98  unary                                   6
% 0.88/0.98  binary                                  1
% 0.88/0.98  lits                                    14
% 0.88/0.98  lits eq                                 4
% 0.88/0.98  fd_pure                                 0
% 0.88/0.98  fd_pseudo                               0
% 0.88/0.98  fd_cond                                 0
% 0.88/0.98  fd_pseudo_cond                          0
% 0.88/0.98  AC symbols                              0
% 0.88/0.98  
% 0.88/0.98  ------ Schedule dynamic 5 is on 
% 0.88/0.98  
% 0.88/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.88/0.98  
% 0.88/0.98  
% 0.88/0.98  ------ 
% 0.88/0.98  Current options:
% 0.88/0.98  ------ 
% 0.88/0.98  
% 0.88/0.98  ------ Input Options
% 0.88/0.98  
% 0.88/0.98  --out_options                           all
% 0.88/0.98  --tptp_safe_out                         true
% 0.88/0.98  --problem_path                          ""
% 0.88/0.98  --include_path                          ""
% 0.88/0.98  --clausifier                            res/vclausify_rel
% 0.88/0.98  --clausifier_options                    --mode clausify
% 0.88/0.98  --stdin                                 false
% 0.88/0.98  --stats_out                             all
% 0.88/0.98  
% 0.88/0.98  ------ General Options
% 0.88/0.98  
% 0.88/0.98  --fof                                   false
% 0.88/0.98  --time_out_real                         305.
% 0.88/0.98  --time_out_virtual                      -1.
% 0.88/0.98  --symbol_type_check                     false
% 0.88/0.98  --clausify_out                          false
% 0.88/0.98  --sig_cnt_out                           false
% 0.88/0.98  --trig_cnt_out                          false
% 0.88/0.98  --trig_cnt_out_tolerance                1.
% 0.88/0.98  --trig_cnt_out_sk_spl                   false
% 0.88/0.98  --abstr_cl_out                          false
% 0.88/0.98  
% 0.88/0.98  ------ Global Options
% 0.88/0.98  
% 0.88/0.98  --schedule                              default
% 0.88/0.98  --add_important_lit                     false
% 0.88/0.98  --prop_solver_per_cl                    1000
% 0.88/0.98  --min_unsat_core                        false
% 0.88/0.98  --soft_assumptions                      false
% 0.88/0.98  --soft_lemma_size                       3
% 0.88/0.98  --prop_impl_unit_size                   0
% 0.88/0.98  --prop_impl_unit                        []
% 0.88/0.98  --share_sel_clauses                     true
% 0.88/0.98  --reset_solvers                         false
% 0.88/0.98  --bc_imp_inh                            [conj_cone]
% 0.88/0.98  --conj_cone_tolerance                   3.
% 0.88/0.98  --extra_neg_conj                        none
% 0.88/0.98  --large_theory_mode                     true
% 0.88/0.98  --prolific_symb_bound                   200
% 0.88/0.98  --lt_threshold                          2000
% 0.88/0.98  --clause_weak_htbl                      true
% 0.88/0.98  --gc_record_bc_elim                     false
% 0.88/0.98  
% 0.88/0.98  ------ Preprocessing Options
% 0.88/0.98  
% 0.88/0.98  --preprocessing_flag                    true
% 0.88/0.98  --time_out_prep_mult                    0.1
% 0.88/0.98  --splitting_mode                        input
% 0.88/0.98  --splitting_grd                         true
% 0.88/0.98  --splitting_cvd                         false
% 0.88/0.98  --splitting_cvd_svl                     false
% 0.88/0.98  --splitting_nvd                         32
% 0.88/0.98  --sub_typing                            true
% 0.88/0.98  --prep_gs_sim                           true
% 0.88/0.98  --prep_unflatten                        true
% 0.88/0.98  --prep_res_sim                          true
% 0.88/0.98  --prep_upred                            true
% 0.88/0.98  --prep_sem_filter                       exhaustive
% 0.88/0.98  --prep_sem_filter_out                   false
% 0.88/0.98  --pred_elim                             true
% 0.88/0.98  --res_sim_input                         true
% 0.88/0.98  --eq_ax_congr_red                       true
% 0.88/0.98  --pure_diseq_elim                       true
% 0.88/0.98  --brand_transform                       false
% 0.88/0.98  --non_eq_to_eq                          false
% 0.88/0.98  --prep_def_merge                        true
% 0.88/0.98  --prep_def_merge_prop_impl              false
% 0.88/0.98  --prep_def_merge_mbd                    true
% 0.88/0.98  --prep_def_merge_tr_red                 false
% 0.88/0.98  --prep_def_merge_tr_cl                  false
% 0.88/0.98  --smt_preprocessing                     true
% 0.88/0.98  --smt_ac_axioms                         fast
% 0.88/0.98  --preprocessed_out                      false
% 0.88/0.98  --preprocessed_stats                    false
% 0.88/0.98  
% 0.88/0.98  ------ Abstraction refinement Options
% 0.88/0.98  
% 0.88/0.98  --abstr_ref                             []
% 0.88/0.98  --abstr_ref_prep                        false
% 0.88/0.98  --abstr_ref_until_sat                   false
% 0.88/0.98  --abstr_ref_sig_restrict                funpre
% 0.88/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.88/0.98  --abstr_ref_under                       []
% 0.88/0.98  
% 0.88/0.98  ------ SAT Options
% 0.88/0.98  
% 0.88/0.98  --sat_mode                              false
% 0.88/0.98  --sat_fm_restart_options                ""
% 0.88/0.98  --sat_gr_def                            false
% 0.88/0.98  --sat_epr_types                         true
% 0.88/0.98  --sat_non_cyclic_types                  false
% 0.88/0.98  --sat_finite_models                     false
% 0.88/0.98  --sat_fm_lemmas                         false
% 0.88/0.98  --sat_fm_prep                           false
% 0.88/0.98  --sat_fm_uc_incr                        true
% 0.88/0.98  --sat_out_model                         small
% 0.88/0.98  --sat_out_clauses                       false
% 0.88/0.98  
% 0.88/0.98  ------ QBF Options
% 0.88/0.98  
% 0.88/0.98  --qbf_mode                              false
% 0.88/0.98  --qbf_elim_univ                         false
% 0.88/0.98  --qbf_dom_inst                          none
% 0.88/0.98  --qbf_dom_pre_inst                      false
% 0.88/0.98  --qbf_sk_in                             false
% 0.88/0.98  --qbf_pred_elim                         true
% 0.88/0.98  --qbf_split                             512
% 0.88/0.98  
% 0.88/0.98  ------ BMC1 Options
% 0.88/0.98  
% 0.88/0.98  --bmc1_incremental                      false
% 0.88/0.98  --bmc1_axioms                           reachable_all
% 0.88/0.98  --bmc1_min_bound                        0
% 0.88/0.98  --bmc1_max_bound                        -1
% 0.88/0.98  --bmc1_max_bound_default                -1
% 0.88/0.98  --bmc1_symbol_reachability              true
% 0.88/0.98  --bmc1_property_lemmas                  false
% 0.88/0.98  --bmc1_k_induction                      false
% 0.88/0.98  --bmc1_non_equiv_states                 false
% 0.88/0.98  --bmc1_deadlock                         false
% 0.88/0.98  --bmc1_ucm                              false
% 0.88/0.98  --bmc1_add_unsat_core                   none
% 0.88/0.98  --bmc1_unsat_core_children              false
% 0.88/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.88/0.98  --bmc1_out_stat                         full
% 0.88/0.98  --bmc1_ground_init                      false
% 0.88/0.98  --bmc1_pre_inst_next_state              false
% 0.88/0.98  --bmc1_pre_inst_state                   false
% 0.88/0.98  --bmc1_pre_inst_reach_state             false
% 0.88/0.98  --bmc1_out_unsat_core                   false
% 0.88/0.98  --bmc1_aig_witness_out                  false
% 0.88/0.98  --bmc1_verbose                          false
% 0.88/0.98  --bmc1_dump_clauses_tptp                false
% 0.88/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.88/0.98  --bmc1_dump_file                        -
% 0.88/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.88/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.88/0.98  --bmc1_ucm_extend_mode                  1
% 0.88/0.98  --bmc1_ucm_init_mode                    2
% 0.88/0.98  --bmc1_ucm_cone_mode                    none
% 0.88/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.88/0.98  --bmc1_ucm_relax_model                  4
% 0.88/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.88/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.88/0.98  --bmc1_ucm_layered_model                none
% 0.88/0.98  --bmc1_ucm_max_lemma_size               10
% 0.88/0.98  
% 0.88/0.98  ------ AIG Options
% 0.88/0.98  
% 0.88/0.98  --aig_mode                              false
% 0.88/0.98  
% 0.88/0.98  ------ Instantiation Options
% 0.88/0.98  
% 0.88/0.98  --instantiation_flag                    true
% 0.88/0.98  --inst_sos_flag                         false
% 0.88/0.98  --inst_sos_phase                        true
% 0.88/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.88/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.88/0.98  --inst_lit_sel_side                     none
% 0.88/0.98  --inst_solver_per_active                1400
% 0.88/0.98  --inst_solver_calls_frac                1.
% 0.88/0.98  --inst_passive_queue_type               priority_queues
% 0.88/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.88/0.98  --inst_passive_queues_freq              [25;2]
% 0.88/0.98  --inst_dismatching                      true
% 0.88/0.98  --inst_eager_unprocessed_to_passive     true
% 0.88/0.98  --inst_prop_sim_given                   true
% 0.88/0.98  --inst_prop_sim_new                     false
% 0.88/0.98  --inst_subs_new                         false
% 0.88/0.98  --inst_eq_res_simp                      false
% 0.88/0.98  --inst_subs_given                       false
% 0.88/0.98  --inst_orphan_elimination               true
% 0.88/0.98  --inst_learning_loop_flag               true
% 0.88/0.98  --inst_learning_start                   3000
% 0.88/0.98  --inst_learning_factor                  2
% 0.88/0.98  --inst_start_prop_sim_after_learn       3
% 0.88/0.98  --inst_sel_renew                        solver
% 0.88/0.98  --inst_lit_activity_flag                true
% 0.88/0.98  --inst_restr_to_given                   false
% 0.88/0.98  --inst_activity_threshold               500
% 0.88/0.98  --inst_out_proof                        true
% 0.88/0.98  
% 0.88/0.98  ------ Resolution Options
% 0.88/0.98  
% 0.88/0.98  --resolution_flag                       false
% 0.88/0.98  --res_lit_sel                           adaptive
% 0.88/0.98  --res_lit_sel_side                      none
% 0.88/0.98  --res_ordering                          kbo
% 0.88/0.98  --res_to_prop_solver                    active
% 0.88/0.98  --res_prop_simpl_new                    false
% 0.88/0.98  --res_prop_simpl_given                  true
% 0.88/0.98  --res_passive_queue_type                priority_queues
% 0.88/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.88/0.98  --res_passive_queues_freq               [15;5]
% 0.88/0.98  --res_forward_subs                      full
% 0.88/0.98  --res_backward_subs                     full
% 0.88/0.98  --res_forward_subs_resolution           true
% 0.88/0.98  --res_backward_subs_resolution          true
% 0.88/0.98  --res_orphan_elimination                true
% 0.88/0.98  --res_time_limit                        2.
% 0.88/0.98  --res_out_proof                         true
% 0.88/0.98  
% 0.88/0.98  ------ Superposition Options
% 0.88/0.98  
% 0.88/0.98  --superposition_flag                    true
% 0.88/0.98  --sup_passive_queue_type                priority_queues
% 0.88/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.88/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.88/0.98  --demod_completeness_check              fast
% 0.88/0.98  --demod_use_ground                      true
% 0.88/0.98  --sup_to_prop_solver                    passive
% 0.88/0.98  --sup_prop_simpl_new                    true
% 0.88/0.98  --sup_prop_simpl_given                  true
% 0.88/0.98  --sup_fun_splitting                     false
% 0.88/0.98  --sup_smt_interval                      50000
% 0.88/0.98  
% 0.88/0.98  ------ Superposition Simplification Setup
% 0.88/0.98  
% 0.88/0.98  --sup_indices_passive                   []
% 0.88/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.88/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.98  --sup_full_bw                           [BwDemod]
% 0.88/0.98  --sup_immed_triv                        [TrivRules]
% 0.88/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.88/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.98  --sup_immed_bw_main                     []
% 0.88/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.88/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/0.98  
% 0.88/0.98  ------ Combination Options
% 0.88/0.98  
% 0.88/0.98  --comb_res_mult                         3
% 0.88/0.98  --comb_sup_mult                         2
% 0.88/0.98  --comb_inst_mult                        10
% 0.88/0.98  
% 0.88/0.98  ------ Debug Options
% 0.88/0.98  
% 0.88/0.98  --dbg_backtrace                         false
% 0.88/0.98  --dbg_dump_prop_clauses                 false
% 0.88/0.98  --dbg_dump_prop_clauses_file            -
% 0.88/0.98  --dbg_out_stat                          false
% 0.88/0.98  
% 0.88/0.98  
% 0.88/0.98  
% 0.88/0.98  
% 0.88/0.98  ------ Proving...
% 0.88/0.98  
% 0.88/0.98  
% 0.88/0.98  % SZS status Theorem for theBenchmark.p
% 0.88/0.98  
% 0.88/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 0.88/0.98  
% 0.88/0.98  fof(f2,axiom,(
% 0.88/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.98  
% 0.88/0.98  fof(f16,plain,(
% 0.88/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.88/0.98    inference(cnf_transformation,[],[f2])).
% 0.88/0.98  
% 0.88/0.98  fof(f4,axiom,(
% 0.88/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.98  
% 0.88/0.98  fof(f18,plain,(
% 0.88/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.88/0.98    inference(cnf_transformation,[],[f4])).
% 0.88/0.98  
% 0.88/0.98  fof(f6,conjecture,(
% 0.88/0.98    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.98  
% 0.88/0.98  fof(f7,negated_conjecture,(
% 0.88/0.98    ~! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.88/0.98    inference(negated_conjecture,[],[f6])).
% 0.88/0.98  
% 0.88/0.98  fof(f11,plain,(
% 0.88/0.98    ? [X0,X1,X2] : (k3_xboole_0(X1,X2) != X0 & (! [X3] : (r1_tarski(X3,X0) | (~r1_tarski(X3,X2) | ~r1_tarski(X3,X1))) & r1_tarski(X0,X2) & r1_tarski(X0,X1)))),
% 0.88/0.98    inference(ennf_transformation,[],[f7])).
% 0.88/0.98  
% 0.88/0.98  fof(f12,plain,(
% 0.88/0.98    ? [X0,X1,X2] : (k3_xboole_0(X1,X2) != X0 & ! [X3] : (r1_tarski(X3,X0) | ~r1_tarski(X3,X2) | ~r1_tarski(X3,X1)) & r1_tarski(X0,X2) & r1_tarski(X0,X1))),
% 0.88/0.98    inference(flattening,[],[f11])).
% 0.88/0.98  
% 0.88/0.98  fof(f13,plain,(
% 0.88/0.98    ? [X0,X1,X2] : (k3_xboole_0(X1,X2) != X0 & ! [X3] : (r1_tarski(X3,X0) | ~r1_tarski(X3,X2) | ~r1_tarski(X3,X1)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => (k3_xboole_0(sK1,sK2) != sK0 & ! [X3] : (r1_tarski(X3,sK0) | ~r1_tarski(X3,sK2) | ~r1_tarski(X3,sK1)) & r1_tarski(sK0,sK2) & r1_tarski(sK0,sK1))),
% 0.88/0.98    introduced(choice_axiom,[])).
% 0.88/0.98  
% 0.88/0.98  fof(f14,plain,(
% 0.88/0.98    k3_xboole_0(sK1,sK2) != sK0 & ! [X3] : (r1_tarski(X3,sK0) | ~r1_tarski(X3,sK2) | ~r1_tarski(X3,sK1)) & r1_tarski(sK0,sK2) & r1_tarski(sK0,sK1)),
% 0.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.88/0.98  
% 0.88/0.98  fof(f22,plain,(
% 0.88/0.98    ( ! [X3] : (r1_tarski(X3,sK0) | ~r1_tarski(X3,sK2) | ~r1_tarski(X3,sK1)) )),
% 0.88/0.98    inference(cnf_transformation,[],[f14])).
% 0.88/0.98  
% 0.88/0.98  fof(f3,axiom,(
% 0.88/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.98  
% 0.88/0.98  fof(f8,plain,(
% 0.88/0.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.88/0.98    inference(ennf_transformation,[],[f3])).
% 0.88/0.98  
% 0.88/0.98  fof(f17,plain,(
% 0.88/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.88/0.98    inference(cnf_transformation,[],[f8])).
% 0.88/0.98  
% 0.88/0.98  fof(f1,axiom,(
% 0.88/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.98  
% 0.88/0.98  fof(f15,plain,(
% 0.88/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.88/0.98    inference(cnf_transformation,[],[f1])).
% 0.88/0.98  
% 0.88/0.98  fof(f5,axiom,(
% 0.88/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.98  
% 0.88/0.98  fof(f9,plain,(
% 0.88/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.88/0.98    inference(ennf_transformation,[],[f5])).
% 0.88/0.98  
% 0.88/0.98  fof(f10,plain,(
% 0.88/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.88/0.98    inference(flattening,[],[f9])).
% 0.88/0.98  
% 0.88/0.98  fof(f19,plain,(
% 0.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.88/0.98    inference(cnf_transformation,[],[f10])).
% 0.88/0.98  
% 0.88/0.98  fof(f23,plain,(
% 0.88/0.98    k3_xboole_0(sK1,sK2) != sK0),
% 0.88/0.98    inference(cnf_transformation,[],[f14])).
% 0.88/0.98  
% 0.88/0.98  fof(f21,plain,(
% 0.88/0.98    r1_tarski(sK0,sK2)),
% 0.88/0.98    inference(cnf_transformation,[],[f14])).
% 0.88/0.98  
% 0.88/0.98  fof(f20,plain,(
% 0.88/0.98    r1_tarski(sK0,sK1)),
% 0.88/0.98    inference(cnf_transformation,[],[f14])).
% 0.88/0.98  
% 0.88/0.98  cnf(c_75,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_859,plain,
% 0.88/0.98      ( k2_xboole_0(k3_xboole_0(sK2,sK1),X0) != X1
% 0.88/0.98      | sK0 != X1
% 0.88/0.98      | sK0 = k2_xboole_0(k3_xboole_0(sK2,sK1),X0) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_75]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_860,plain,
% 0.88/0.98      ( k2_xboole_0(k3_xboole_0(sK2,sK1),sK0) != sK0
% 0.88/0.98      | sK0 = k2_xboole_0(k3_xboole_0(sK2,sK1),sK0)
% 0.88/0.98      | sK0 != sK0 ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_859]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_1,plain,
% 0.88/0.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 0.88/0.98      inference(cnf_transformation,[],[f16]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_3,plain,
% 0.88/0.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 0.88/0.98      inference(cnf_transformation,[],[f18]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_184,plain,
% 0.88/0.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 0.88/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_381,plain,
% 0.88/0.98      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 0.88/0.98      inference(superposition,[status(thm)],[c_1,c_184]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_6,negated_conjecture,
% 0.88/0.98      ( r1_tarski(X0,sK0) | ~ r1_tarski(X0,sK2) | ~ r1_tarski(X0,sK1) ),
% 0.88/0.98      inference(cnf_transformation,[],[f22]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_182,plain,
% 0.88/0.98      ( r1_tarski(X0,sK0) = iProver_top
% 0.88/0.98      | r1_tarski(X0,sK2) != iProver_top
% 0.88/0.98      | r1_tarski(X0,sK1) != iProver_top ),
% 0.88/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_383,plain,
% 0.88/0.98      ( r1_tarski(k3_xboole_0(sK2,X0),sK0) = iProver_top
% 0.88/0.98      | r1_tarski(k3_xboole_0(sK2,X0),sK1) != iProver_top ),
% 0.88/0.98      inference(superposition,[status(thm)],[c_184,c_182]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_663,plain,
% 0.88/0.98      ( r1_tarski(k3_xboole_0(sK2,sK1),sK0) = iProver_top ),
% 0.88/0.98      inference(superposition,[status(thm)],[c_381,c_383]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_2,plain,
% 0.88/0.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 0.88/0.98      inference(cnf_transformation,[],[f17]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_185,plain,
% 0.88/0.98      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 0.88/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_848,plain,
% 0.88/0.98      ( k2_xboole_0(k3_xboole_0(sK2,sK1),sK0) = sK0 ),
% 0.88/0.98      inference(superposition,[status(thm)],[c_663,c_185]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_0,plain,
% 0.88/0.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 0.88/0.98      inference(cnf_transformation,[],[f15]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_591,plain,
% 0.88/0.98      ( k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) = k2_xboole_0(k3_xboole_0(sK2,sK1),X0) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_593,plain,
% 0.88/0.98      ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) = k2_xboole_0(k3_xboole_0(sK2,sK1),sK0) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_591]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_399,plain,
% 0.88/0.98      ( k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) != X1
% 0.88/0.98      | sK0 != X1
% 0.88/0.98      | sK0 = k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_75]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_590,plain,
% 0.88/0.98      ( k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) != k2_xboole_0(k3_xboole_0(sK2,sK1),X0)
% 0.88/0.98      | sK0 = k2_xboole_0(X0,k3_xboole_0(sK2,sK1))
% 0.88/0.98      | sK0 != k2_xboole_0(k3_xboole_0(sK2,sK1),X0) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_399]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_592,plain,
% 0.88/0.98      ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k2_xboole_0(k3_xboole_0(sK2,sK1),sK0)
% 0.88/0.98      | sK0 != k2_xboole_0(k3_xboole_0(sK2,sK1),sK0)
% 0.88/0.98      | sK0 = k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_590]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_4,plain,
% 0.88/0.98      ( ~ r1_tarski(X0,X1)
% 0.88/0.98      | ~ r1_tarski(X0,X2)
% 0.88/0.98      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 0.88/0.98      inference(cnf_transformation,[],[f19]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_414,plain,
% 0.88/0.98      ( r1_tarski(X0,k3_xboole_0(sK2,sK1))
% 0.88/0.98      | ~ r1_tarski(X0,sK2)
% 0.88/0.98      | ~ r1_tarski(X0,sK1) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_416,plain,
% 0.88/0.98      ( r1_tarski(sK0,k3_xboole_0(sK2,sK1))
% 0.88/0.98      | ~ r1_tarski(sK0,sK2)
% 0.88/0.98      | ~ r1_tarski(sK0,sK1) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_414]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_227,plain,
% 0.88/0.98      ( k3_xboole_0(sK1,sK2) != X0
% 0.88/0.98      | k3_xboole_0(sK1,sK2) = sK0
% 0.88/0.98      | sK0 != X0 ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_75]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_341,plain,
% 0.88/0.98      ( k3_xboole_0(sK1,sK2) != k2_xboole_0(X0,k3_xboole_0(sK2,sK1))
% 0.88/0.98      | k3_xboole_0(sK1,sK2) = sK0
% 0.88/0.98      | sK0 != k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_227]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_342,plain,
% 0.88/0.98      ( k3_xboole_0(sK1,sK2) != k2_xboole_0(sK0,k3_xboole_0(sK2,sK1))
% 0.88/0.98      | k3_xboole_0(sK1,sK2) = sK0
% 0.88/0.98      | sK0 != k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_341]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_287,plain,
% 0.88/0.98      ( ~ r1_tarski(X0,k3_xboole_0(sK2,sK1))
% 0.88/0.98      | k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK2,sK1) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_290,plain,
% 0.88/0.98      ( ~ r1_tarski(sK0,k3_xboole_0(sK2,sK1))
% 0.88/0.98      | k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK2,sK1) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_287]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_235,plain,
% 0.88/0.98      ( X0 != X1
% 0.88/0.98      | k3_xboole_0(sK1,sK2) != X1
% 0.88/0.98      | k3_xboole_0(sK1,sK2) = X0 ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_75]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_260,plain,
% 0.88/0.98      ( X0 != k3_xboole_0(sK2,sK1)
% 0.88/0.98      | k3_xboole_0(sK1,sK2) = X0
% 0.88/0.98      | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_235]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_286,plain,
% 0.88/0.98      ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1)
% 0.88/0.98      | k3_xboole_0(sK1,sK2) = k2_xboole_0(X0,k3_xboole_0(sK2,sK1))
% 0.88/0.98      | k2_xboole_0(X0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(sK2,sK1) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_260]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_288,plain,
% 0.88/0.98      ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1)
% 0.88/0.98      | k3_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k3_xboole_0(sK2,sK1))
% 0.88/0.98      | k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(sK2,sK1) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_286]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_232,plain,
% 0.88/0.98      ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_74,plain,( X0 = X0 ),theory(equality) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_80,plain,
% 0.88/0.98      ( sK0 = sK0 ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_74]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_5,negated_conjecture,
% 0.88/0.98      ( k3_xboole_0(sK1,sK2) != sK0 ),
% 0.88/0.98      inference(cnf_transformation,[],[f23]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_7,negated_conjecture,
% 0.88/0.98      ( r1_tarski(sK0,sK2) ),
% 0.88/0.98      inference(cnf_transformation,[],[f21]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_8,negated_conjecture,
% 0.88/0.98      ( r1_tarski(sK0,sK1) ),
% 0.88/0.98      inference(cnf_transformation,[],[f20]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(contradiction,plain,
% 0.88/0.98      ( $false ),
% 0.88/0.98      inference(minisat,
% 0.88/0.98                [status(thm)],
% 0.88/0.98                [c_860,c_848,c_593,c_592,c_416,c_342,c_290,c_288,c_232,
% 0.88/0.98                 c_80,c_5,c_7,c_8]) ).
% 0.88/0.98  
% 0.88/0.98  
% 0.88/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 0.88/0.98  
% 0.88/0.98  ------                               Statistics
% 0.88/0.98  
% 0.88/0.98  ------ General
% 0.88/0.98  
% 0.88/0.98  abstr_ref_over_cycles:                  0
% 0.88/0.98  abstr_ref_under_cycles:                 0
% 0.88/0.98  gc_basic_clause_elim:                   0
% 0.88/0.98  forced_gc_time:                         0
% 0.88/0.98  parsing_time:                           0.008
% 0.88/0.98  unif_index_cands_time:                  0.
% 0.88/0.98  unif_index_add_time:                    0.
% 0.88/0.98  orderings_time:                         0.
% 0.88/0.98  out_proof_time:                         0.008
% 0.88/0.98  total_time:                             0.061
% 0.88/0.98  num_of_symbols:                         37
% 0.88/0.98  num_of_terms:                           764
% 0.88/0.98  
% 0.88/0.98  ------ Preprocessing
% 0.88/0.98  
% 0.88/0.98  num_of_splits:                          0
% 0.88/0.98  num_of_split_atoms:                     0
% 0.88/0.98  num_of_reused_defs:                     0
% 0.88/0.98  num_eq_ax_congr_red:                    4
% 0.88/0.98  num_of_sem_filtered_clauses:            1
% 0.88/0.98  num_of_subtypes:                        0
% 0.88/0.98  monotx_restored_types:                  0
% 0.88/0.98  sat_num_of_epr_types:                   0
% 0.88/0.98  sat_num_of_non_cyclic_types:            0
% 0.88/0.98  sat_guarded_non_collapsed_types:        0
% 0.88/0.98  num_pure_diseq_elim:                    0
% 0.88/0.98  simp_replaced_by:                       0
% 0.88/0.98  res_preprocessed:                       36
% 0.88/0.98  prep_upred:                             0
% 0.88/0.98  prep_unflattend:                        0
% 0.88/0.98  smt_new_axioms:                         0
% 0.88/0.98  pred_elim_cands:                        1
% 0.88/0.98  pred_elim:                              0
% 0.88/0.98  pred_elim_cl:                           0
% 0.88/0.98  pred_elim_cycles:                       1
% 0.88/0.98  merged_defs:                            0
% 0.88/0.98  merged_defs_ncl:                        0
% 0.88/0.98  bin_hyper_res:                          0
% 0.88/0.98  prep_cycles:                            3
% 0.88/0.98  pred_elim_time:                         0.
% 0.88/0.98  splitting_time:                         0.
% 0.88/0.98  sem_filter_time:                        0.
% 0.88/0.98  monotx_time:                            0.001
% 0.88/0.98  subtype_inf_time:                       0.
% 0.88/0.98  
% 0.88/0.98  ------ Problem properties
% 0.88/0.98  
% 0.88/0.98  clauses:                                9
% 0.88/0.98  conjectures:                            4
% 0.88/0.98  epr:                                    3
% 0.88/0.98  horn:                                   9
% 0.88/0.98  ground:                                 3
% 0.88/0.98  unary:                                  6
% 0.88/0.98  binary:                                 1
% 0.88/0.98  lits:                                   14
% 0.88/0.98  lits_eq:                                4
% 0.88/0.98  fd_pure:                                0
% 0.88/0.98  fd_pseudo:                              0
% 0.88/0.98  fd_cond:                                0
% 0.88/0.98  fd_pseudo_cond:                         0
% 0.88/0.98  ac_symbols:                             0
% 0.88/0.98  
% 0.88/0.98  ------ Propositional Solver
% 0.88/0.98  
% 0.88/0.98  prop_solver_calls:                      24
% 0.88/0.98  prop_fast_solver_calls:                 159
% 0.88/0.98  smt_solver_calls:                       0
% 0.88/0.98  smt_fast_solver_calls:                  0
% 0.88/0.98  prop_num_of_clauses:                    307
% 0.88/0.98  prop_preprocess_simplified:             1208
% 0.88/0.98  prop_fo_subsumed:                       1
% 0.88/0.98  prop_solver_time:                       0.
% 0.88/0.98  smt_solver_time:                        0.
% 0.88/0.98  smt_fast_solver_time:                   0.
% 0.88/0.98  prop_fast_solver_time:                  0.
% 0.88/0.98  prop_unsat_core_time:                   0.
% 0.88/0.98  
% 0.88/0.98  ------ QBF
% 0.88/0.98  
% 0.88/0.98  qbf_q_res:                              0
% 0.88/0.98  qbf_num_tautologies:                    0
% 0.88/0.98  qbf_prep_cycles:                        0
% 0.88/0.98  
% 0.88/0.98  ------ BMC1
% 0.88/0.98  
% 0.88/0.98  bmc1_current_bound:                     -1
% 0.88/0.98  bmc1_last_solved_bound:                 -1
% 0.88/0.98  bmc1_unsat_core_size:                   -1
% 0.88/0.98  bmc1_unsat_core_parents_size:           -1
% 0.88/0.98  bmc1_merge_next_fun:                    0
% 0.88/0.98  bmc1_unsat_core_clauses_time:           0.
% 0.88/0.98  
% 0.88/0.98  ------ Instantiation
% 0.88/0.98  
% 0.88/0.98  inst_num_of_clauses:                    136
% 0.88/0.98  inst_num_in_passive:                    31
% 0.88/0.98  inst_num_in_active:                     90
% 0.88/0.98  inst_num_in_unprocessed:                14
% 0.88/0.98  inst_num_of_loops:                      102
% 0.88/0.98  inst_num_of_learning_restarts:          0
% 0.88/0.98  inst_num_moves_active_passive:          7
% 0.88/0.98  inst_lit_activity:                      0
% 0.88/0.98  inst_lit_activity_moves:                0
% 0.88/0.98  inst_num_tautologies:                   0
% 0.88/0.98  inst_num_prop_implied:                  0
% 0.88/0.98  inst_num_existing_simplified:           0
% 0.88/0.98  inst_num_eq_res_simplified:             0
% 0.88/0.98  inst_num_child_elim:                    0
% 0.88/0.98  inst_num_of_dismatching_blockings:      17
% 0.88/0.98  inst_num_of_non_proper_insts:           133
% 0.88/0.98  inst_num_of_duplicates:                 0
% 0.88/0.98  inst_inst_num_from_inst_to_res:         0
% 0.88/0.98  inst_dismatching_checking_time:         0.
% 0.88/0.98  
% 0.88/0.98  ------ Resolution
% 0.88/0.98  
% 0.88/0.98  res_num_of_clauses:                     0
% 0.88/0.98  res_num_in_passive:                     0
% 0.88/0.98  res_num_in_active:                      0
% 0.88/0.98  res_num_of_loops:                       39
% 0.88/0.98  res_forward_subset_subsumed:            51
% 0.88/0.98  res_backward_subset_subsumed:           0
% 0.88/0.98  res_forward_subsumed:                   0
% 0.88/0.98  res_backward_subsumed:                  0
% 0.88/0.98  res_forward_subsumption_resolution:     0
% 0.88/0.98  res_backward_subsumption_resolution:    0
% 0.88/0.98  res_clause_to_clause_subsumption:       91
% 0.88/0.98  res_orphan_elimination:                 0
% 0.88/0.98  res_tautology_del:                      22
% 0.88/0.98  res_num_eq_res_simplified:              0
% 0.88/0.98  res_num_sel_changes:                    0
% 0.88/0.98  res_moves_from_active_to_pass:          0
% 0.88/0.98  
% 0.88/0.98  ------ Superposition
% 0.88/0.98  
% 0.88/0.98  sup_time_total:                         0.
% 0.88/0.98  sup_time_generating:                    0.
% 0.88/0.98  sup_time_sim_full:                      0.
% 0.88/0.98  sup_time_sim_immed:                     0.
% 0.88/0.98  
% 0.88/0.98  sup_num_of_clauses:                     27
% 0.88/0.98  sup_num_in_active:                      20
% 0.88/0.98  sup_num_in_passive:                     7
% 0.88/0.98  sup_num_of_loops:                       20
% 0.88/0.98  sup_fw_superposition:                   25
% 0.88/0.98  sup_bw_superposition:                   8
% 0.88/0.98  sup_immediate_simplified:               0
% 0.88/0.98  sup_given_eliminated:                   0
% 0.88/0.98  comparisons_done:                       0
% 0.88/0.98  comparisons_avoided:                    0
% 0.88/0.98  
% 0.88/0.98  ------ Simplifications
% 0.88/0.98  
% 0.88/0.98  
% 0.88/0.98  sim_fw_subset_subsumed:                 0
% 0.88/0.98  sim_bw_subset_subsumed:                 0
% 0.88/0.98  sim_fw_subsumed:                        0
% 0.88/0.98  sim_bw_subsumed:                        0
% 0.88/0.98  sim_fw_subsumption_res:                 0
% 0.88/0.98  sim_bw_subsumption_res:                 0
% 0.88/0.98  sim_tautology_del:                      0
% 0.88/0.98  sim_eq_tautology_del:                   0
% 0.88/0.98  sim_eq_res_simp:                        0
% 0.88/0.98  sim_fw_demodulated:                     0
% 0.88/0.98  sim_bw_demodulated:                     0
% 0.88/0.98  sim_light_normalised:                   0
% 0.88/0.98  sim_joinable_taut:                      0
% 0.88/0.98  sim_joinable_simp:                      0
% 0.88/0.98  sim_ac_normalised:                      0
% 0.88/0.98  sim_smt_subsumption:                    0
% 0.88/0.98  
%------------------------------------------------------------------------------
