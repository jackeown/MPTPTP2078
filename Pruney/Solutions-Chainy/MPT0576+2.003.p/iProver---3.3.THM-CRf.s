%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:51 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 122 expanded)
%              Number of clauses        :   33 (  39 expanded)
%              Number of leaves         :    9 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  142 ( 442 expanded)
%              Number of equality atoms :   44 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(sK3,X1))
        & r1_tarski(X0,X1)
        & r1_tarski(X2,sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f22,f21])).

fof(f36,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_355,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_362,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1190,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_355,c_362])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_352,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_358,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1508,plain,
    ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_352,c_358])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_359,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1931,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_359])).

cnf(c_6575,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1931])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_354,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_357,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1189,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X2,X1)) = k10_relat_1(X2,X1)
    | r1_tarski(X0,X2) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_357,c_362])).

cnf(c_4663,plain,
    ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0)) = k10_relat_1(sK3,X0)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_354,c_1189])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_481,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0))
    | ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_528,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0))
    | k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0)) = k10_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5985,plain,
    ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0)) = k10_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4663,c_13,c_12,c_11,c_481,c_528])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_363,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3004,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_363])).

cnf(c_6012,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
    | r1_tarski(X0,k10_relat_1(sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5985,c_3004])).

cnf(c_28883,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6575,c_6012])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28883,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.66/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/1.51  
% 7.66/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.66/1.51  
% 7.66/1.51  ------  iProver source info
% 7.66/1.51  
% 7.66/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.66/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.66/1.51  git: non_committed_changes: false
% 7.66/1.51  git: last_make_outside_of_git: false
% 7.66/1.51  
% 7.66/1.51  ------ 
% 7.66/1.51  
% 7.66/1.51  ------ Input Options
% 7.66/1.51  
% 7.66/1.51  --out_options                           all
% 7.66/1.51  --tptp_safe_out                         true
% 7.66/1.51  --problem_path                          ""
% 7.66/1.51  --include_path                          ""
% 7.66/1.51  --clausifier                            res/vclausify_rel
% 7.66/1.51  --clausifier_options                    --mode clausify
% 7.66/1.51  --stdin                                 false
% 7.66/1.51  --stats_out                             all
% 7.66/1.51  
% 7.66/1.51  ------ General Options
% 7.66/1.51  
% 7.66/1.51  --fof                                   false
% 7.66/1.51  --time_out_real                         305.
% 7.66/1.51  --time_out_virtual                      -1.
% 7.66/1.51  --symbol_type_check                     false
% 7.66/1.51  --clausify_out                          false
% 7.66/1.51  --sig_cnt_out                           false
% 7.66/1.51  --trig_cnt_out                          false
% 7.66/1.51  --trig_cnt_out_tolerance                1.
% 7.66/1.51  --trig_cnt_out_sk_spl                   false
% 7.66/1.51  --abstr_cl_out                          false
% 7.66/1.51  
% 7.66/1.51  ------ Global Options
% 7.66/1.51  
% 7.66/1.51  --schedule                              default
% 7.66/1.51  --add_important_lit                     false
% 7.66/1.51  --prop_solver_per_cl                    1000
% 7.66/1.51  --min_unsat_core                        false
% 7.66/1.51  --soft_assumptions                      false
% 7.66/1.51  --soft_lemma_size                       3
% 7.66/1.51  --prop_impl_unit_size                   0
% 7.66/1.51  --prop_impl_unit                        []
% 7.66/1.51  --share_sel_clauses                     true
% 7.66/1.51  --reset_solvers                         false
% 7.66/1.51  --bc_imp_inh                            [conj_cone]
% 7.66/1.51  --conj_cone_tolerance                   3.
% 7.66/1.51  --extra_neg_conj                        none
% 7.66/1.51  --large_theory_mode                     true
% 7.66/1.51  --prolific_symb_bound                   200
% 7.66/1.51  --lt_threshold                          2000
% 7.66/1.51  --clause_weak_htbl                      true
% 7.66/1.51  --gc_record_bc_elim                     false
% 7.66/1.51  
% 7.66/1.51  ------ Preprocessing Options
% 7.66/1.51  
% 7.66/1.51  --preprocessing_flag                    true
% 7.66/1.51  --time_out_prep_mult                    0.1
% 7.66/1.51  --splitting_mode                        input
% 7.66/1.51  --splitting_grd                         true
% 7.66/1.51  --splitting_cvd                         false
% 7.66/1.51  --splitting_cvd_svl                     false
% 7.66/1.51  --splitting_nvd                         32
% 7.66/1.51  --sub_typing                            true
% 7.66/1.51  --prep_gs_sim                           true
% 7.66/1.51  --prep_unflatten                        true
% 7.66/1.51  --prep_res_sim                          true
% 7.66/1.51  --prep_upred                            true
% 7.66/1.51  --prep_sem_filter                       exhaustive
% 7.66/1.51  --prep_sem_filter_out                   false
% 7.66/1.51  --pred_elim                             true
% 7.66/1.51  --res_sim_input                         true
% 7.66/1.51  --eq_ax_congr_red                       true
% 7.66/1.51  --pure_diseq_elim                       true
% 7.66/1.51  --brand_transform                       false
% 7.66/1.51  --non_eq_to_eq                          false
% 7.66/1.51  --prep_def_merge                        true
% 7.66/1.51  --prep_def_merge_prop_impl              false
% 7.66/1.51  --prep_def_merge_mbd                    true
% 7.66/1.51  --prep_def_merge_tr_red                 false
% 7.66/1.51  --prep_def_merge_tr_cl                  false
% 7.66/1.51  --smt_preprocessing                     true
% 7.66/1.51  --smt_ac_axioms                         fast
% 7.66/1.51  --preprocessed_out                      false
% 7.66/1.51  --preprocessed_stats                    false
% 7.66/1.51  
% 7.66/1.51  ------ Abstraction refinement Options
% 7.66/1.51  
% 7.66/1.51  --abstr_ref                             []
% 7.66/1.51  --abstr_ref_prep                        false
% 7.66/1.51  --abstr_ref_until_sat                   false
% 7.66/1.51  --abstr_ref_sig_restrict                funpre
% 7.66/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.51  --abstr_ref_under                       []
% 7.66/1.51  
% 7.66/1.51  ------ SAT Options
% 7.66/1.51  
% 7.66/1.51  --sat_mode                              false
% 7.66/1.51  --sat_fm_restart_options                ""
% 7.66/1.51  --sat_gr_def                            false
% 7.66/1.51  --sat_epr_types                         true
% 7.66/1.51  --sat_non_cyclic_types                  false
% 7.66/1.51  --sat_finite_models                     false
% 7.66/1.51  --sat_fm_lemmas                         false
% 7.66/1.51  --sat_fm_prep                           false
% 7.66/1.51  --sat_fm_uc_incr                        true
% 7.66/1.51  --sat_out_model                         small
% 7.66/1.51  --sat_out_clauses                       false
% 7.66/1.51  
% 7.66/1.51  ------ QBF Options
% 7.66/1.51  
% 7.66/1.51  --qbf_mode                              false
% 7.66/1.51  --qbf_elim_univ                         false
% 7.66/1.51  --qbf_dom_inst                          none
% 7.66/1.51  --qbf_dom_pre_inst                      false
% 7.66/1.51  --qbf_sk_in                             false
% 7.66/1.51  --qbf_pred_elim                         true
% 7.66/1.51  --qbf_split                             512
% 7.66/1.51  
% 7.66/1.51  ------ BMC1 Options
% 7.66/1.51  
% 7.66/1.51  --bmc1_incremental                      false
% 7.66/1.51  --bmc1_axioms                           reachable_all
% 7.66/1.51  --bmc1_min_bound                        0
% 7.66/1.51  --bmc1_max_bound                        -1
% 7.66/1.51  --bmc1_max_bound_default                -1
% 7.66/1.51  --bmc1_symbol_reachability              true
% 7.66/1.51  --bmc1_property_lemmas                  false
% 7.66/1.51  --bmc1_k_induction                      false
% 7.66/1.51  --bmc1_non_equiv_states                 false
% 7.66/1.51  --bmc1_deadlock                         false
% 7.66/1.51  --bmc1_ucm                              false
% 7.66/1.51  --bmc1_add_unsat_core                   none
% 7.66/1.51  --bmc1_unsat_core_children              false
% 7.66/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.51  --bmc1_out_stat                         full
% 7.66/1.51  --bmc1_ground_init                      false
% 7.66/1.51  --bmc1_pre_inst_next_state              false
% 7.66/1.51  --bmc1_pre_inst_state                   false
% 7.66/1.51  --bmc1_pre_inst_reach_state             false
% 7.66/1.51  --bmc1_out_unsat_core                   false
% 7.66/1.51  --bmc1_aig_witness_out                  false
% 7.66/1.51  --bmc1_verbose                          false
% 7.66/1.51  --bmc1_dump_clauses_tptp                false
% 7.66/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.51  --bmc1_dump_file                        -
% 7.66/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.51  --bmc1_ucm_extend_mode                  1
% 7.66/1.51  --bmc1_ucm_init_mode                    2
% 7.66/1.51  --bmc1_ucm_cone_mode                    none
% 7.66/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.51  --bmc1_ucm_relax_model                  4
% 7.66/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.51  --bmc1_ucm_layered_model                none
% 7.66/1.51  --bmc1_ucm_max_lemma_size               10
% 7.66/1.51  
% 7.66/1.51  ------ AIG Options
% 7.66/1.51  
% 7.66/1.51  --aig_mode                              false
% 7.66/1.51  
% 7.66/1.51  ------ Instantiation Options
% 7.66/1.51  
% 7.66/1.51  --instantiation_flag                    true
% 7.66/1.51  --inst_sos_flag                         false
% 7.66/1.51  --inst_sos_phase                        true
% 7.66/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.51  --inst_lit_sel_side                     num_symb
% 7.66/1.51  --inst_solver_per_active                1400
% 7.66/1.51  --inst_solver_calls_frac                1.
% 7.66/1.51  --inst_passive_queue_type               priority_queues
% 7.66/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.51  --inst_passive_queues_freq              [25;2]
% 7.66/1.51  --inst_dismatching                      true
% 7.66/1.51  --inst_eager_unprocessed_to_passive     true
% 7.66/1.51  --inst_prop_sim_given                   true
% 7.66/1.51  --inst_prop_sim_new                     false
% 7.66/1.51  --inst_subs_new                         false
% 7.66/1.51  --inst_eq_res_simp                      false
% 7.66/1.51  --inst_subs_given                       false
% 7.66/1.51  --inst_orphan_elimination               true
% 7.66/1.51  --inst_learning_loop_flag               true
% 7.66/1.51  --inst_learning_start                   3000
% 7.66/1.51  --inst_learning_factor                  2
% 7.66/1.51  --inst_start_prop_sim_after_learn       3
% 7.66/1.51  --inst_sel_renew                        solver
% 7.66/1.51  --inst_lit_activity_flag                true
% 7.66/1.51  --inst_restr_to_given                   false
% 7.66/1.51  --inst_activity_threshold               500
% 7.66/1.51  --inst_out_proof                        true
% 7.66/1.51  
% 7.66/1.51  ------ Resolution Options
% 7.66/1.51  
% 7.66/1.51  --resolution_flag                       true
% 7.66/1.51  --res_lit_sel                           adaptive
% 7.66/1.51  --res_lit_sel_side                      none
% 7.66/1.51  --res_ordering                          kbo
% 7.66/1.51  --res_to_prop_solver                    active
% 7.66/1.51  --res_prop_simpl_new                    false
% 7.66/1.51  --res_prop_simpl_given                  true
% 7.66/1.51  --res_passive_queue_type                priority_queues
% 7.66/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.51  --res_passive_queues_freq               [15;5]
% 7.66/1.51  --res_forward_subs                      full
% 7.66/1.51  --res_backward_subs                     full
% 7.66/1.51  --res_forward_subs_resolution           true
% 7.66/1.51  --res_backward_subs_resolution          true
% 7.66/1.51  --res_orphan_elimination                true
% 7.66/1.51  --res_time_limit                        2.
% 7.66/1.51  --res_out_proof                         true
% 7.66/1.51  
% 7.66/1.51  ------ Superposition Options
% 7.66/1.51  
% 7.66/1.51  --superposition_flag                    true
% 7.66/1.51  --sup_passive_queue_type                priority_queues
% 7.66/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.51  --demod_completeness_check              fast
% 7.66/1.51  --demod_use_ground                      true
% 7.66/1.51  --sup_to_prop_solver                    passive
% 7.66/1.51  --sup_prop_simpl_new                    true
% 7.66/1.51  --sup_prop_simpl_given                  true
% 7.66/1.51  --sup_fun_splitting                     false
% 7.66/1.51  --sup_smt_interval                      50000
% 7.66/1.51  
% 7.66/1.51  ------ Superposition Simplification Setup
% 7.66/1.51  
% 7.66/1.51  --sup_indices_passive                   []
% 7.66/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.51  --sup_full_bw                           [BwDemod]
% 7.66/1.51  --sup_immed_triv                        [TrivRules]
% 7.66/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.51  --sup_immed_bw_main                     []
% 7.66/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.51  
% 7.66/1.51  ------ Combination Options
% 7.66/1.51  
% 7.66/1.51  --comb_res_mult                         3
% 7.66/1.51  --comb_sup_mult                         2
% 7.66/1.51  --comb_inst_mult                        10
% 7.66/1.51  
% 7.66/1.51  ------ Debug Options
% 7.66/1.51  
% 7.66/1.51  --dbg_backtrace                         false
% 7.66/1.51  --dbg_dump_prop_clauses                 false
% 7.66/1.51  --dbg_dump_prop_clauses_file            -
% 7.66/1.51  --dbg_out_stat                          false
% 7.66/1.51  ------ Parsing...
% 7.66/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.66/1.51  
% 7.66/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.66/1.51  
% 7.66/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.66/1.51  
% 7.66/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.66/1.51  ------ Proving...
% 7.66/1.51  ------ Problem Properties 
% 7.66/1.51  
% 7.66/1.51  
% 7.66/1.51  clauses                                 14
% 7.66/1.51  conjectures                             5
% 7.66/1.51  EPR                                     4
% 7.66/1.51  Horn                                    14
% 7.66/1.51  unary                                   8
% 7.66/1.51  binary                                  5
% 7.66/1.51  lits                                    22
% 7.66/1.51  lits eq                                 5
% 7.66/1.51  fd_pure                                 0
% 7.66/1.51  fd_pseudo                               0
% 7.66/1.51  fd_cond                                 1
% 7.66/1.51  fd_pseudo_cond                          0
% 7.66/1.51  AC symbols                              0
% 7.66/1.51  
% 7.66/1.51  ------ Schedule dynamic 5 is on 
% 7.66/1.51  
% 7.66/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.66/1.51  
% 7.66/1.51  
% 7.66/1.51  ------ 
% 7.66/1.51  Current options:
% 7.66/1.51  ------ 
% 7.66/1.51  
% 7.66/1.51  ------ Input Options
% 7.66/1.51  
% 7.66/1.51  --out_options                           all
% 7.66/1.51  --tptp_safe_out                         true
% 7.66/1.51  --problem_path                          ""
% 7.66/1.51  --include_path                          ""
% 7.66/1.51  --clausifier                            res/vclausify_rel
% 7.66/1.51  --clausifier_options                    --mode clausify
% 7.66/1.51  --stdin                                 false
% 7.66/1.51  --stats_out                             all
% 7.66/1.51  
% 7.66/1.51  ------ General Options
% 7.66/1.51  
% 7.66/1.51  --fof                                   false
% 7.66/1.51  --time_out_real                         305.
% 7.66/1.51  --time_out_virtual                      -1.
% 7.66/1.51  --symbol_type_check                     false
% 7.66/1.51  --clausify_out                          false
% 7.66/1.51  --sig_cnt_out                           false
% 7.66/1.51  --trig_cnt_out                          false
% 7.66/1.51  --trig_cnt_out_tolerance                1.
% 7.66/1.51  --trig_cnt_out_sk_spl                   false
% 7.66/1.51  --abstr_cl_out                          false
% 7.66/1.51  
% 7.66/1.51  ------ Global Options
% 7.66/1.51  
% 7.66/1.51  --schedule                              default
% 7.66/1.51  --add_important_lit                     false
% 7.66/1.51  --prop_solver_per_cl                    1000
% 7.66/1.51  --min_unsat_core                        false
% 7.66/1.51  --soft_assumptions                      false
% 7.66/1.51  --soft_lemma_size                       3
% 7.66/1.51  --prop_impl_unit_size                   0
% 7.66/1.51  --prop_impl_unit                        []
% 7.66/1.51  --share_sel_clauses                     true
% 7.66/1.51  --reset_solvers                         false
% 7.66/1.51  --bc_imp_inh                            [conj_cone]
% 7.66/1.51  --conj_cone_tolerance                   3.
% 7.66/1.51  --extra_neg_conj                        none
% 7.66/1.51  --large_theory_mode                     true
% 7.66/1.51  --prolific_symb_bound                   200
% 7.66/1.51  --lt_threshold                          2000
% 7.66/1.51  --clause_weak_htbl                      true
% 7.66/1.51  --gc_record_bc_elim                     false
% 7.66/1.51  
% 7.66/1.51  ------ Preprocessing Options
% 7.66/1.51  
% 7.66/1.51  --preprocessing_flag                    true
% 7.66/1.51  --time_out_prep_mult                    0.1
% 7.66/1.51  --splitting_mode                        input
% 7.66/1.51  --splitting_grd                         true
% 7.66/1.51  --splitting_cvd                         false
% 7.66/1.51  --splitting_cvd_svl                     false
% 7.66/1.51  --splitting_nvd                         32
% 7.66/1.51  --sub_typing                            true
% 7.66/1.51  --prep_gs_sim                           true
% 7.66/1.51  --prep_unflatten                        true
% 7.66/1.51  --prep_res_sim                          true
% 7.66/1.51  --prep_upred                            true
% 7.66/1.51  --prep_sem_filter                       exhaustive
% 7.66/1.51  --prep_sem_filter_out                   false
% 7.66/1.51  --pred_elim                             true
% 7.66/1.51  --res_sim_input                         true
% 7.66/1.51  --eq_ax_congr_red                       true
% 7.66/1.51  --pure_diseq_elim                       true
% 7.66/1.51  --brand_transform                       false
% 7.66/1.51  --non_eq_to_eq                          false
% 7.66/1.51  --prep_def_merge                        true
% 7.66/1.51  --prep_def_merge_prop_impl              false
% 7.66/1.51  --prep_def_merge_mbd                    true
% 7.66/1.51  --prep_def_merge_tr_red                 false
% 7.66/1.51  --prep_def_merge_tr_cl                  false
% 7.66/1.51  --smt_preprocessing                     true
% 7.66/1.51  --smt_ac_axioms                         fast
% 7.66/1.51  --preprocessed_out                      false
% 7.66/1.51  --preprocessed_stats                    false
% 7.66/1.51  
% 7.66/1.51  ------ Abstraction refinement Options
% 7.66/1.51  
% 7.66/1.51  --abstr_ref                             []
% 7.66/1.51  --abstr_ref_prep                        false
% 7.66/1.51  --abstr_ref_until_sat                   false
% 7.66/1.51  --abstr_ref_sig_restrict                funpre
% 7.66/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.51  --abstr_ref_under                       []
% 7.66/1.51  
% 7.66/1.51  ------ SAT Options
% 7.66/1.51  
% 7.66/1.51  --sat_mode                              false
% 7.66/1.51  --sat_fm_restart_options                ""
% 7.66/1.51  --sat_gr_def                            false
% 7.66/1.51  --sat_epr_types                         true
% 7.66/1.51  --sat_non_cyclic_types                  false
% 7.66/1.51  --sat_finite_models                     false
% 7.66/1.51  --sat_fm_lemmas                         false
% 7.66/1.51  --sat_fm_prep                           false
% 7.66/1.51  --sat_fm_uc_incr                        true
% 7.66/1.51  --sat_out_model                         small
% 7.66/1.51  --sat_out_clauses                       false
% 7.66/1.51  
% 7.66/1.51  ------ QBF Options
% 7.66/1.51  
% 7.66/1.51  --qbf_mode                              false
% 7.66/1.51  --qbf_elim_univ                         false
% 7.66/1.51  --qbf_dom_inst                          none
% 7.66/1.51  --qbf_dom_pre_inst                      false
% 7.66/1.51  --qbf_sk_in                             false
% 7.66/1.51  --qbf_pred_elim                         true
% 7.66/1.51  --qbf_split                             512
% 7.66/1.51  
% 7.66/1.51  ------ BMC1 Options
% 7.66/1.51  
% 7.66/1.51  --bmc1_incremental                      false
% 7.66/1.51  --bmc1_axioms                           reachable_all
% 7.66/1.51  --bmc1_min_bound                        0
% 7.66/1.51  --bmc1_max_bound                        -1
% 7.66/1.51  --bmc1_max_bound_default                -1
% 7.66/1.51  --bmc1_symbol_reachability              true
% 7.66/1.51  --bmc1_property_lemmas                  false
% 7.66/1.51  --bmc1_k_induction                      false
% 7.66/1.51  --bmc1_non_equiv_states                 false
% 7.66/1.51  --bmc1_deadlock                         false
% 7.66/1.51  --bmc1_ucm                              false
% 7.66/1.51  --bmc1_add_unsat_core                   none
% 7.66/1.51  --bmc1_unsat_core_children              false
% 7.66/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.51  --bmc1_out_stat                         full
% 7.66/1.51  --bmc1_ground_init                      false
% 7.66/1.51  --bmc1_pre_inst_next_state              false
% 7.66/1.51  --bmc1_pre_inst_state                   false
% 7.66/1.51  --bmc1_pre_inst_reach_state             false
% 7.66/1.51  --bmc1_out_unsat_core                   false
% 7.66/1.51  --bmc1_aig_witness_out                  false
% 7.66/1.51  --bmc1_verbose                          false
% 7.66/1.51  --bmc1_dump_clauses_tptp                false
% 7.66/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.51  --bmc1_dump_file                        -
% 7.66/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.51  --bmc1_ucm_extend_mode                  1
% 7.66/1.51  --bmc1_ucm_init_mode                    2
% 7.66/1.51  --bmc1_ucm_cone_mode                    none
% 7.66/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.51  --bmc1_ucm_relax_model                  4
% 7.66/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.51  --bmc1_ucm_layered_model                none
% 7.66/1.51  --bmc1_ucm_max_lemma_size               10
% 7.66/1.51  
% 7.66/1.51  ------ AIG Options
% 7.66/1.51  
% 7.66/1.51  --aig_mode                              false
% 7.66/1.51  
% 7.66/1.51  ------ Instantiation Options
% 7.66/1.51  
% 7.66/1.51  --instantiation_flag                    true
% 7.66/1.51  --inst_sos_flag                         false
% 7.66/1.51  --inst_sos_phase                        true
% 7.66/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.51  --inst_lit_sel_side                     none
% 7.66/1.51  --inst_solver_per_active                1400
% 7.66/1.51  --inst_solver_calls_frac                1.
% 7.66/1.51  --inst_passive_queue_type               priority_queues
% 7.66/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.51  --inst_passive_queues_freq              [25;2]
% 7.66/1.51  --inst_dismatching                      true
% 7.66/1.51  --inst_eager_unprocessed_to_passive     true
% 7.66/1.51  --inst_prop_sim_given                   true
% 7.66/1.51  --inst_prop_sim_new                     false
% 7.66/1.51  --inst_subs_new                         false
% 7.66/1.51  --inst_eq_res_simp                      false
% 7.66/1.51  --inst_subs_given                       false
% 7.66/1.51  --inst_orphan_elimination               true
% 7.66/1.51  --inst_learning_loop_flag               true
% 7.66/1.51  --inst_learning_start                   3000
% 7.66/1.51  --inst_learning_factor                  2
% 7.66/1.51  --inst_start_prop_sim_after_learn       3
% 7.66/1.51  --inst_sel_renew                        solver
% 7.66/1.51  --inst_lit_activity_flag                true
% 7.66/1.51  --inst_restr_to_given                   false
% 7.66/1.51  --inst_activity_threshold               500
% 7.66/1.51  --inst_out_proof                        true
% 7.66/1.51  
% 7.66/1.51  ------ Resolution Options
% 7.66/1.51  
% 7.66/1.51  --resolution_flag                       false
% 7.66/1.51  --res_lit_sel                           adaptive
% 7.66/1.51  --res_lit_sel_side                      none
% 7.66/1.51  --res_ordering                          kbo
% 7.66/1.51  --res_to_prop_solver                    active
% 7.66/1.51  --res_prop_simpl_new                    false
% 7.66/1.51  --res_prop_simpl_given                  true
% 7.66/1.51  --res_passive_queue_type                priority_queues
% 7.66/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.51  --res_passive_queues_freq               [15;5]
% 7.66/1.51  --res_forward_subs                      full
% 7.66/1.51  --res_backward_subs                     full
% 7.66/1.51  --res_forward_subs_resolution           true
% 7.66/1.51  --res_backward_subs_resolution          true
% 7.66/1.51  --res_orphan_elimination                true
% 7.66/1.51  --res_time_limit                        2.
% 7.66/1.51  --res_out_proof                         true
% 7.66/1.51  
% 7.66/1.51  ------ Superposition Options
% 7.66/1.51  
% 7.66/1.51  --superposition_flag                    true
% 7.66/1.51  --sup_passive_queue_type                priority_queues
% 7.66/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.51  --demod_completeness_check              fast
% 7.66/1.51  --demod_use_ground                      true
% 7.66/1.51  --sup_to_prop_solver                    passive
% 7.66/1.51  --sup_prop_simpl_new                    true
% 7.66/1.51  --sup_prop_simpl_given                  true
% 7.66/1.51  --sup_fun_splitting                     false
% 7.66/1.51  --sup_smt_interval                      50000
% 7.66/1.51  
% 7.66/1.51  ------ Superposition Simplification Setup
% 7.66/1.51  
% 7.66/1.51  --sup_indices_passive                   []
% 7.66/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.51  --sup_full_bw                           [BwDemod]
% 7.66/1.51  --sup_immed_triv                        [TrivRules]
% 7.66/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.51  --sup_immed_bw_main                     []
% 7.66/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.51  
% 7.66/1.51  ------ Combination Options
% 7.66/1.51  
% 7.66/1.51  --comb_res_mult                         3
% 7.66/1.51  --comb_sup_mult                         2
% 7.66/1.51  --comb_inst_mult                        10
% 7.66/1.51  
% 7.66/1.51  ------ Debug Options
% 7.66/1.51  
% 7.66/1.51  --dbg_backtrace                         false
% 7.66/1.51  --dbg_dump_prop_clauses                 false
% 7.66/1.51  --dbg_dump_prop_clauses_file            -
% 7.66/1.51  --dbg_out_stat                          false
% 7.66/1.51  
% 7.66/1.51  
% 7.66/1.51  
% 7.66/1.51  
% 7.66/1.51  ------ Proving...
% 7.66/1.51  
% 7.66/1.51  
% 7.66/1.51  % SZS status Theorem for theBenchmark.p
% 7.66/1.51  
% 7.66/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.66/1.51  
% 7.66/1.51  fof(f10,conjecture,(
% 7.66/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)))))),
% 7.66/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.51  
% 7.66/1.51  fof(f11,negated_conjecture,(
% 7.66/1.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)))))),
% 7.66/1.51    inference(negated_conjecture,[],[f10])).
% 7.66/1.51  
% 7.66/1.51  fof(f19,plain,(
% 7.66/1.51    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 7.66/1.51    inference(ennf_transformation,[],[f11])).
% 7.66/1.51  
% 7.66/1.51  fof(f20,plain,(
% 7.66/1.51    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 7.66/1.51    inference(flattening,[],[f19])).
% 7.66/1.51  
% 7.66/1.51  fof(f22,plain,(
% 7.66/1.51    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) => (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(sK3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,sK3) & v1_relat_1(sK3))) )),
% 7.66/1.51    introduced(choice_axiom,[])).
% 7.66/1.51  
% 7.66/1.51  fof(f21,plain,(
% 7.66/1.51    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 7.66/1.51    introduced(choice_axiom,[])).
% 7.66/1.51  
% 7.66/1.51  fof(f23,plain,(
% 7.66/1.51    (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 7.66/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f22,f21])).
% 7.66/1.51  
% 7.66/1.51  fof(f36,plain,(
% 7.66/1.51    r1_tarski(sK0,sK1)),
% 7.66/1.51    inference(cnf_transformation,[],[f23])).
% 7.66/1.51  
% 7.66/1.51  fof(f3,axiom,(
% 7.66/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.66/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.51  
% 7.66/1.51  fof(f13,plain,(
% 7.66/1.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.66/1.51    inference(ennf_transformation,[],[f3])).
% 7.66/1.51  
% 7.66/1.51  fof(f26,plain,(
% 7.66/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.66/1.51    inference(cnf_transformation,[],[f13])).
% 7.66/1.51  
% 7.66/1.51  fof(f33,plain,(
% 7.66/1.51    v1_relat_1(sK2)),
% 7.66/1.51    inference(cnf_transformation,[],[f23])).
% 7.66/1.51  
% 7.66/1.51  fof(f8,axiom,(
% 7.66/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 7.66/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.51  
% 7.66/1.51  fof(f16,plain,(
% 7.66/1.51    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.66/1.51    inference(ennf_transformation,[],[f8])).
% 7.66/1.51  
% 7.66/1.51  fof(f31,plain,(
% 7.66/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 7.66/1.51    inference(cnf_transformation,[],[f16])).
% 7.66/1.51  
% 7.66/1.51  fof(f7,axiom,(
% 7.66/1.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.66/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.51  
% 7.66/1.51  fof(f30,plain,(
% 7.66/1.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.66/1.51    inference(cnf_transformation,[],[f7])).
% 7.66/1.51  
% 7.66/1.51  fof(f35,plain,(
% 7.66/1.51    r1_tarski(sK2,sK3)),
% 7.66/1.51    inference(cnf_transformation,[],[f23])).
% 7.66/1.51  
% 7.66/1.51  fof(f9,axiom,(
% 7.66/1.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 7.66/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.51  
% 7.66/1.51  fof(f17,plain,(
% 7.66/1.51    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 7.66/1.51    inference(ennf_transformation,[],[f9])).
% 7.66/1.51  
% 7.66/1.51  fof(f18,plain,(
% 7.66/1.51    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 7.66/1.51    inference(flattening,[],[f17])).
% 7.66/1.51  
% 7.66/1.51  fof(f32,plain,(
% 7.66/1.51    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 7.66/1.51    inference(cnf_transformation,[],[f18])).
% 7.66/1.51  
% 7.66/1.51  fof(f34,plain,(
% 7.66/1.51    v1_relat_1(sK3)),
% 7.66/1.51    inference(cnf_transformation,[],[f23])).
% 7.66/1.51  
% 7.66/1.51  fof(f1,axiom,(
% 7.66/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.66/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.51  
% 7.66/1.51  fof(f24,plain,(
% 7.66/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.66/1.51    inference(cnf_transformation,[],[f1])).
% 7.66/1.51  
% 7.66/1.51  fof(f2,axiom,(
% 7.66/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.66/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.51  
% 7.66/1.51  fof(f12,plain,(
% 7.66/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.66/1.51    inference(ennf_transformation,[],[f2])).
% 7.66/1.51  
% 7.66/1.51  fof(f25,plain,(
% 7.66/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.66/1.51    inference(cnf_transformation,[],[f12])).
% 7.66/1.51  
% 7.66/1.51  fof(f37,plain,(
% 7.66/1.51    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))),
% 7.66/1.51    inference(cnf_transformation,[],[f23])).
% 7.66/1.51  
% 7.66/1.51  cnf(c_10,negated_conjecture,
% 7.66/1.51      ( r1_tarski(sK0,sK1) ),
% 7.66/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_355,plain,
% 7.66/1.51      ( r1_tarski(sK0,sK1) = iProver_top ),
% 7.66/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_2,plain,
% 7.66/1.51      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.66/1.51      inference(cnf_transformation,[],[f26]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_362,plain,
% 7.66/1.51      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.66/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_1190,plain,
% 7.66/1.51      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 7.66/1.51      inference(superposition,[status(thm)],[c_355,c_362]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_13,negated_conjecture,
% 7.66/1.51      ( v1_relat_1(sK2) ),
% 7.66/1.51      inference(cnf_transformation,[],[f33]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_352,plain,
% 7.66/1.51      ( v1_relat_1(sK2) = iProver_top ),
% 7.66/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_7,plain,
% 7.66/1.51      ( ~ v1_relat_1(X0)
% 7.66/1.51      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 7.66/1.51      inference(cnf_transformation,[],[f31]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_358,plain,
% 7.66/1.51      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 7.66/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_1508,plain,
% 7.66/1.51      ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
% 7.66/1.51      inference(superposition,[status(thm)],[c_352,c_358]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_6,plain,
% 7.66/1.51      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.66/1.51      inference(cnf_transformation,[],[f30]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_359,plain,
% 7.66/1.51      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.66/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_1931,plain,
% 7.66/1.51      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X0,X1))) = iProver_top ),
% 7.66/1.51      inference(superposition,[status(thm)],[c_1508,c_359]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_6575,plain,
% 7.66/1.51      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 7.66/1.51      inference(superposition,[status(thm)],[c_1190,c_1931]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_11,negated_conjecture,
% 7.66/1.51      ( r1_tarski(sK2,sK3) ),
% 7.66/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_354,plain,
% 7.66/1.51      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.66/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_8,plain,
% 7.66/1.51      ( ~ r1_tarski(X0,X1)
% 7.66/1.51      | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2))
% 7.66/1.51      | ~ v1_relat_1(X1)
% 7.66/1.51      | ~ v1_relat_1(X0) ),
% 7.66/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_357,plain,
% 7.66/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.66/1.51      | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2)) = iProver_top
% 7.66/1.51      | v1_relat_1(X1) != iProver_top
% 7.66/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_1189,plain,
% 7.66/1.51      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X2,X1)) = k10_relat_1(X2,X1)
% 7.66/1.51      | r1_tarski(X0,X2) != iProver_top
% 7.66/1.51      | v1_relat_1(X2) != iProver_top
% 7.66/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.51      inference(superposition,[status(thm)],[c_357,c_362]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_4663,plain,
% 7.66/1.51      ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0)) = k10_relat_1(sK3,X0)
% 7.66/1.51      | v1_relat_1(sK3) != iProver_top
% 7.66/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.51      inference(superposition,[status(thm)],[c_354,c_1189]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_12,negated_conjecture,
% 7.66/1.51      ( v1_relat_1(sK3) ),
% 7.66/1.51      inference(cnf_transformation,[],[f34]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_481,plain,
% 7.66/1.51      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0))
% 7.66/1.51      | ~ r1_tarski(sK2,sK3)
% 7.66/1.51      | ~ v1_relat_1(sK3)
% 7.66/1.51      | ~ v1_relat_1(sK2) ),
% 7.66/1.51      inference(instantiation,[status(thm)],[c_8]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_528,plain,
% 7.66/1.51      ( ~ r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0))
% 7.66/1.51      | k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0)) = k10_relat_1(sK3,X0) ),
% 7.66/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_5985,plain,
% 7.66/1.51      ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0)) = k10_relat_1(sK3,X0) ),
% 7.66/1.51      inference(global_propositional_subsumption,
% 7.66/1.51                [status(thm)],
% 7.66/1.51                [c_4663,c_13,c_12,c_11,c_481,c_528]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_0,plain,
% 7.66/1.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.66/1.51      inference(cnf_transformation,[],[f24]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_1,plain,
% 7.66/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 7.66/1.51      inference(cnf_transformation,[],[f25]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_363,plain,
% 7.66/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.66/1.51      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 7.66/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.66/1.51  
% 7.66/1.51  cnf(c_3004,plain,
% 7.66/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.66/1.52      | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_0,c_363]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_6012,plain,
% 7.66/1.52      ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
% 7.66/1.52      | r1_tarski(X0,k10_relat_1(sK2,X1)) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_5985,c_3004]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_28883,plain,
% 7.66/1.52      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) = iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_6575,c_6012]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_9,negated_conjecture,
% 7.66/1.52      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) ),
% 7.66/1.52      inference(cnf_transformation,[],[f37]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_18,plain,
% 7.66/1.52      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(contradiction,plain,
% 7.66/1.52      ( $false ),
% 7.66/1.52      inference(minisat,[status(thm)],[c_28883,c_18]) ).
% 7.66/1.52  
% 7.66/1.52  
% 7.66/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.66/1.52  
% 7.66/1.52  ------                               Statistics
% 7.66/1.52  
% 7.66/1.52  ------ General
% 7.66/1.52  
% 7.66/1.52  abstr_ref_over_cycles:                  0
% 7.66/1.52  abstr_ref_under_cycles:                 0
% 7.66/1.52  gc_basic_clause_elim:                   0
% 7.66/1.52  forced_gc_time:                         0
% 7.66/1.52  parsing_time:                           0.006
% 7.66/1.52  unif_index_cands_time:                  0.
% 7.66/1.52  unif_index_add_time:                    0.
% 7.66/1.52  orderings_time:                         0.
% 7.66/1.52  out_proof_time:                         0.008
% 7.66/1.52  total_time:                             0.919
% 7.66/1.52  num_of_symbols:                         41
% 7.66/1.52  num_of_terms:                           39111
% 7.66/1.52  
% 7.66/1.52  ------ Preprocessing
% 7.66/1.52  
% 7.66/1.52  num_of_splits:                          0
% 7.66/1.52  num_of_split_atoms:                     0
% 7.66/1.52  num_of_reused_defs:                     0
% 7.66/1.52  num_eq_ax_congr_red:                    4
% 7.66/1.52  num_of_sem_filtered_clauses:            1
% 7.66/1.52  num_of_subtypes:                        0
% 7.66/1.52  monotx_restored_types:                  0
% 7.66/1.52  sat_num_of_epr_types:                   0
% 7.66/1.52  sat_num_of_non_cyclic_types:            0
% 7.66/1.52  sat_guarded_non_collapsed_types:        0
% 7.66/1.52  num_pure_diseq_elim:                    0
% 7.66/1.52  simp_replaced_by:                       0
% 7.66/1.52  res_preprocessed:                       55
% 7.66/1.52  prep_upred:                             0
% 7.66/1.52  prep_unflattend:                        0
% 7.66/1.52  smt_new_axioms:                         0
% 7.66/1.52  pred_elim_cands:                        2
% 7.66/1.52  pred_elim:                              0
% 7.66/1.52  pred_elim_cl:                           0
% 7.66/1.52  pred_elim_cycles:                       1
% 7.66/1.52  merged_defs:                            0
% 7.66/1.52  merged_defs_ncl:                        0
% 7.66/1.52  bin_hyper_res:                          0
% 7.66/1.52  prep_cycles:                            3
% 7.66/1.52  pred_elim_time:                         0.
% 7.66/1.52  splitting_time:                         0.
% 7.66/1.52  sem_filter_time:                        0.
% 7.66/1.52  monotx_time:                            0.
% 7.66/1.52  subtype_inf_time:                       0.
% 7.66/1.52  
% 7.66/1.52  ------ Problem properties
% 7.66/1.52  
% 7.66/1.52  clauses:                                14
% 7.66/1.52  conjectures:                            5
% 7.66/1.52  epr:                                    4
% 7.66/1.52  horn:                                   14
% 7.66/1.52  ground:                                 5
% 7.66/1.52  unary:                                  8
% 7.66/1.52  binary:                                 5
% 7.66/1.52  lits:                                   22
% 7.66/1.52  lits_eq:                                5
% 7.66/1.52  fd_pure:                                0
% 7.66/1.52  fd_pseudo:                              0
% 7.66/1.52  fd_cond:                                1
% 7.66/1.52  fd_pseudo_cond:                         0
% 7.66/1.52  ac_symbols:                             0
% 7.66/1.52  
% 7.66/1.52  ------ Propositional Solver
% 7.66/1.52  
% 7.66/1.52  prop_solver_calls:                      26
% 7.66/1.52  prop_fast_solver_calls:                 459
% 7.66/1.52  smt_solver_calls:                       0
% 7.66/1.52  smt_fast_solver_calls:                  0
% 7.66/1.52  prop_num_of_clauses:                    11218
% 7.66/1.52  prop_preprocess_simplified:             20455
% 7.66/1.52  prop_fo_subsumed:                       2
% 7.66/1.52  prop_solver_time:                       0.
% 7.66/1.52  smt_solver_time:                        0.
% 7.66/1.52  smt_fast_solver_time:                   0.
% 7.66/1.52  prop_fast_solver_time:                  0.
% 7.66/1.52  prop_unsat_core_time:                   0.001
% 7.66/1.52  
% 7.66/1.52  ------ QBF
% 7.66/1.52  
% 7.66/1.52  qbf_q_res:                              0
% 7.66/1.52  qbf_num_tautologies:                    0
% 7.66/1.52  qbf_prep_cycles:                        0
% 7.66/1.52  
% 7.66/1.52  ------ BMC1
% 7.66/1.52  
% 7.66/1.52  bmc1_current_bound:                     -1
% 7.66/1.52  bmc1_last_solved_bound:                 -1
% 7.66/1.52  bmc1_unsat_core_size:                   -1
% 7.66/1.52  bmc1_unsat_core_parents_size:           -1
% 7.66/1.52  bmc1_merge_next_fun:                    0
% 7.66/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.66/1.52  
% 7.66/1.52  ------ Instantiation
% 7.66/1.52  
% 7.66/1.52  inst_num_of_clauses:                    3244
% 7.66/1.52  inst_num_in_passive:                    1886
% 7.66/1.52  inst_num_in_active:                     1091
% 7.66/1.52  inst_num_in_unprocessed:                267
% 7.66/1.52  inst_num_of_loops:                      1150
% 7.66/1.52  inst_num_of_learning_restarts:          0
% 7.66/1.52  inst_num_moves_active_passive:          55
% 7.66/1.52  inst_lit_activity:                      0
% 7.66/1.52  inst_lit_activity_moves:                0
% 7.66/1.52  inst_num_tautologies:                   0
% 7.66/1.52  inst_num_prop_implied:                  0
% 7.66/1.52  inst_num_existing_simplified:           0
% 7.66/1.52  inst_num_eq_res_simplified:             0
% 7.66/1.52  inst_num_child_elim:                    0
% 7.66/1.52  inst_num_of_dismatching_blockings:      5709
% 7.66/1.52  inst_num_of_non_proper_insts:           4458
% 7.66/1.52  inst_num_of_duplicates:                 0
% 7.66/1.52  inst_inst_num_from_inst_to_res:         0
% 7.66/1.52  inst_dismatching_checking_time:         0.
% 7.66/1.52  
% 7.66/1.52  ------ Resolution
% 7.66/1.52  
% 7.66/1.52  res_num_of_clauses:                     0
% 7.66/1.52  res_num_in_passive:                     0
% 7.66/1.52  res_num_in_active:                      0
% 7.66/1.52  res_num_of_loops:                       58
% 7.66/1.52  res_forward_subset_subsumed:            183
% 7.66/1.52  res_backward_subset_subsumed:           10
% 7.66/1.52  res_forward_subsumed:                   0
% 7.66/1.52  res_backward_subsumed:                  0
% 7.66/1.52  res_forward_subsumption_resolution:     0
% 7.66/1.52  res_backward_subsumption_resolution:    0
% 7.66/1.52  res_clause_to_clause_subsumption:       5419
% 7.66/1.52  res_orphan_elimination:                 0
% 7.66/1.52  res_tautology_del:                      316
% 7.66/1.52  res_num_eq_res_simplified:              0
% 7.66/1.52  res_num_sel_changes:                    0
% 7.66/1.52  res_moves_from_active_to_pass:          0
% 7.66/1.52  
% 7.66/1.52  ------ Superposition
% 7.66/1.52  
% 7.66/1.52  sup_time_total:                         0.
% 7.66/1.52  sup_time_generating:                    0.
% 7.66/1.52  sup_time_sim_full:                      0.
% 7.66/1.52  sup_time_sim_immed:                     0.
% 7.66/1.52  
% 7.66/1.52  sup_num_of_clauses:                     1250
% 7.66/1.52  sup_num_in_active:                      229
% 7.66/1.52  sup_num_in_passive:                     1021
% 7.66/1.52  sup_num_of_loops:                       228
% 7.66/1.52  sup_fw_superposition:                   1264
% 7.66/1.52  sup_bw_superposition:                   598
% 7.66/1.52  sup_immediate_simplified:               17
% 7.66/1.52  sup_given_eliminated:                   0
% 7.66/1.52  comparisons_done:                       0
% 7.66/1.52  comparisons_avoided:                    0
% 7.66/1.52  
% 7.66/1.52  ------ Simplifications
% 7.66/1.52  
% 7.66/1.52  
% 7.66/1.52  sim_fw_subset_subsumed:                 0
% 7.66/1.52  sim_bw_subset_subsumed:                 0
% 7.66/1.52  sim_fw_subsumed:                        10
% 7.66/1.52  sim_bw_subsumed:                        0
% 7.66/1.52  sim_fw_subsumption_res:                 0
% 7.66/1.52  sim_bw_subsumption_res:                 0
% 7.66/1.52  sim_tautology_del:                      5
% 7.66/1.52  sim_eq_tautology_del:                   4
% 7.66/1.52  sim_eq_res_simp:                        0
% 7.66/1.52  sim_fw_demodulated:                     1
% 7.66/1.52  sim_bw_demodulated:                     0
% 7.66/1.52  sim_light_normalised:                   8
% 7.66/1.52  sim_joinable_taut:                      0
% 7.66/1.52  sim_joinable_simp:                      0
% 7.66/1.52  sim_ac_normalised:                      0
% 7.66/1.52  sim_smt_subsumption:                    0
% 7.66/1.52  
%------------------------------------------------------------------------------
