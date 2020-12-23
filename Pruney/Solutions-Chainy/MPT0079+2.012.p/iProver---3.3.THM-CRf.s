%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:47 EST 2020

% Result     : Theorem 6.97s
% Output     : CNFRefutation 6.97s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 154 expanded)
%              Number of clauses        :   42 (  58 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :  127 ( 309 expanded)
%              Number of equality atoms :   87 ( 192 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f20])).

fof(f33,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f31,f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f35,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_191,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_13,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_210,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_13])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_192,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_505,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_192])).

cnf(c_2290,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_210,c_505])).

cnf(c_2912,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_191,c_2290])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_84,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_85,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_84])).

cnf(c_607,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_85])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_679,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_607,c_8])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_681,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_679,c_5])).

cnf(c_2924,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2912,c_681])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_193,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7327,plain,
    ( k2_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_2924,c_193])).

cnf(c_403,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_210,c_191])).

cnf(c_2286,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_403,c_505])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_89,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_90,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_89])).

cnf(c_621,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_90,c_8])).

cnf(c_645,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_621,c_5])).

cnf(c_2310,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2286,c_645])).

cnf(c_4462,plain,
    ( k2_xboole_0(sK2,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2310,c_193])).

cnf(c_27899,plain,
    ( k2_xboole_0(sK1,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_4462,c_0])).

cnf(c_30291,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_7327,c_27899])).

cnf(c_124,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_247,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_29421,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_123,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1802,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_10,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30291,c_29421,c_1802,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:52:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 6.97/1.43  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.97/1.43  
% 6.97/1.43  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.97/1.43  
% 6.97/1.43  ------  iProver source info
% 6.97/1.43  
% 6.97/1.43  git: date: 2020-06-30 10:37:57 +0100
% 6.97/1.43  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.97/1.43  git: non_committed_changes: false
% 6.97/1.43  git: last_make_outside_of_git: false
% 6.97/1.43  
% 6.97/1.43  ------ 
% 6.97/1.43  
% 6.97/1.43  ------ Input Options
% 6.97/1.43  
% 6.97/1.43  --out_options                           all
% 6.97/1.43  --tptp_safe_out                         true
% 6.97/1.43  --problem_path                          ""
% 6.97/1.43  --include_path                          ""
% 6.97/1.43  --clausifier                            res/vclausify_rel
% 6.97/1.43  --clausifier_options                    --mode clausify
% 6.97/1.43  --stdin                                 false
% 6.97/1.43  --stats_out                             all
% 6.97/1.43  
% 6.97/1.43  ------ General Options
% 6.97/1.43  
% 6.97/1.43  --fof                                   false
% 6.97/1.43  --time_out_real                         305.
% 6.97/1.43  --time_out_virtual                      -1.
% 6.97/1.43  --symbol_type_check                     false
% 6.97/1.43  --clausify_out                          false
% 6.97/1.43  --sig_cnt_out                           false
% 6.97/1.43  --trig_cnt_out                          false
% 6.97/1.43  --trig_cnt_out_tolerance                1.
% 6.97/1.43  --trig_cnt_out_sk_spl                   false
% 6.97/1.43  --abstr_cl_out                          false
% 6.97/1.43  
% 6.97/1.43  ------ Global Options
% 6.97/1.43  
% 6.97/1.43  --schedule                              default
% 6.97/1.43  --add_important_lit                     false
% 6.97/1.43  --prop_solver_per_cl                    1000
% 6.97/1.43  --min_unsat_core                        false
% 6.97/1.43  --soft_assumptions                      false
% 6.97/1.43  --soft_lemma_size                       3
% 6.97/1.43  --prop_impl_unit_size                   0
% 6.97/1.43  --prop_impl_unit                        []
% 6.97/1.43  --share_sel_clauses                     true
% 6.97/1.43  --reset_solvers                         false
% 6.97/1.43  --bc_imp_inh                            [conj_cone]
% 6.97/1.43  --conj_cone_tolerance                   3.
% 6.97/1.43  --extra_neg_conj                        none
% 6.97/1.43  --large_theory_mode                     true
% 6.97/1.43  --prolific_symb_bound                   200
% 6.97/1.43  --lt_threshold                          2000
% 6.97/1.43  --clause_weak_htbl                      true
% 6.97/1.43  --gc_record_bc_elim                     false
% 6.97/1.43  
% 6.97/1.43  ------ Preprocessing Options
% 6.97/1.43  
% 6.97/1.43  --preprocessing_flag                    true
% 6.97/1.43  --time_out_prep_mult                    0.1
% 6.97/1.43  --splitting_mode                        input
% 6.97/1.43  --splitting_grd                         true
% 6.97/1.43  --splitting_cvd                         false
% 6.97/1.43  --splitting_cvd_svl                     false
% 6.97/1.43  --splitting_nvd                         32
% 6.97/1.43  --sub_typing                            true
% 6.97/1.43  --prep_gs_sim                           true
% 6.97/1.43  --prep_unflatten                        true
% 6.97/1.43  --prep_res_sim                          true
% 6.97/1.43  --prep_upred                            true
% 6.97/1.43  --prep_sem_filter                       exhaustive
% 6.97/1.43  --prep_sem_filter_out                   false
% 6.97/1.43  --pred_elim                             true
% 6.97/1.43  --res_sim_input                         true
% 6.97/1.43  --eq_ax_congr_red                       true
% 6.97/1.43  --pure_diseq_elim                       true
% 6.97/1.43  --brand_transform                       false
% 6.97/1.43  --non_eq_to_eq                          false
% 6.97/1.43  --prep_def_merge                        true
% 6.97/1.43  --prep_def_merge_prop_impl              false
% 6.97/1.43  --prep_def_merge_mbd                    true
% 6.97/1.43  --prep_def_merge_tr_red                 false
% 6.97/1.43  --prep_def_merge_tr_cl                  false
% 6.97/1.43  --smt_preprocessing                     true
% 6.97/1.43  --smt_ac_axioms                         fast
% 6.97/1.43  --preprocessed_out                      false
% 6.97/1.43  --preprocessed_stats                    false
% 6.97/1.43  
% 6.97/1.43  ------ Abstraction refinement Options
% 6.97/1.43  
% 6.97/1.43  --abstr_ref                             []
% 6.97/1.43  --abstr_ref_prep                        false
% 6.97/1.43  --abstr_ref_until_sat                   false
% 6.97/1.43  --abstr_ref_sig_restrict                funpre
% 6.97/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 6.97/1.43  --abstr_ref_under                       []
% 6.97/1.43  
% 6.97/1.43  ------ SAT Options
% 6.97/1.43  
% 6.97/1.43  --sat_mode                              false
% 6.97/1.43  --sat_fm_restart_options                ""
% 6.97/1.43  --sat_gr_def                            false
% 6.97/1.43  --sat_epr_types                         true
% 6.97/1.43  --sat_non_cyclic_types                  false
% 6.97/1.43  --sat_finite_models                     false
% 6.97/1.43  --sat_fm_lemmas                         false
% 6.97/1.43  --sat_fm_prep                           false
% 6.97/1.43  --sat_fm_uc_incr                        true
% 6.97/1.43  --sat_out_model                         small
% 6.97/1.43  --sat_out_clauses                       false
% 6.97/1.43  
% 6.97/1.43  ------ QBF Options
% 6.97/1.43  
% 6.97/1.43  --qbf_mode                              false
% 6.97/1.43  --qbf_elim_univ                         false
% 6.97/1.43  --qbf_dom_inst                          none
% 6.97/1.43  --qbf_dom_pre_inst                      false
% 6.97/1.43  --qbf_sk_in                             false
% 6.97/1.43  --qbf_pred_elim                         true
% 6.97/1.43  --qbf_split                             512
% 6.97/1.43  
% 6.97/1.43  ------ BMC1 Options
% 6.97/1.43  
% 6.97/1.43  --bmc1_incremental                      false
% 6.97/1.43  --bmc1_axioms                           reachable_all
% 6.97/1.43  --bmc1_min_bound                        0
% 6.97/1.43  --bmc1_max_bound                        -1
% 6.97/1.43  --bmc1_max_bound_default                -1
% 6.97/1.43  --bmc1_symbol_reachability              true
% 6.97/1.43  --bmc1_property_lemmas                  false
% 6.97/1.43  --bmc1_k_induction                      false
% 6.97/1.43  --bmc1_non_equiv_states                 false
% 6.97/1.43  --bmc1_deadlock                         false
% 6.97/1.43  --bmc1_ucm                              false
% 6.97/1.43  --bmc1_add_unsat_core                   none
% 6.97/1.43  --bmc1_unsat_core_children              false
% 6.97/1.43  --bmc1_unsat_core_extrapolate_axioms    false
% 6.97/1.43  --bmc1_out_stat                         full
% 6.97/1.43  --bmc1_ground_init                      false
% 6.97/1.43  --bmc1_pre_inst_next_state              false
% 6.97/1.43  --bmc1_pre_inst_state                   false
% 6.97/1.43  --bmc1_pre_inst_reach_state             false
% 6.97/1.43  --bmc1_out_unsat_core                   false
% 6.97/1.43  --bmc1_aig_witness_out                  false
% 6.97/1.43  --bmc1_verbose                          false
% 6.97/1.43  --bmc1_dump_clauses_tptp                false
% 6.97/1.43  --bmc1_dump_unsat_core_tptp             false
% 6.97/1.43  --bmc1_dump_file                        -
% 6.97/1.43  --bmc1_ucm_expand_uc_limit              128
% 6.97/1.43  --bmc1_ucm_n_expand_iterations          6
% 6.97/1.43  --bmc1_ucm_extend_mode                  1
% 6.97/1.43  --bmc1_ucm_init_mode                    2
% 6.97/1.43  --bmc1_ucm_cone_mode                    none
% 6.97/1.43  --bmc1_ucm_reduced_relation_type        0
% 6.97/1.43  --bmc1_ucm_relax_model                  4
% 6.97/1.43  --bmc1_ucm_full_tr_after_sat            true
% 6.97/1.43  --bmc1_ucm_expand_neg_assumptions       false
% 6.97/1.43  --bmc1_ucm_layered_model                none
% 6.97/1.43  --bmc1_ucm_max_lemma_size               10
% 6.97/1.43  
% 6.97/1.43  ------ AIG Options
% 6.97/1.43  
% 6.97/1.43  --aig_mode                              false
% 6.97/1.43  
% 6.97/1.43  ------ Instantiation Options
% 6.97/1.43  
% 6.97/1.43  --instantiation_flag                    true
% 6.97/1.43  --inst_sos_flag                         false
% 6.97/1.43  --inst_sos_phase                        true
% 6.97/1.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.97/1.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.97/1.43  --inst_lit_sel_side                     num_symb
% 6.97/1.43  --inst_solver_per_active                1400
% 6.97/1.43  --inst_solver_calls_frac                1.
% 6.97/1.43  --inst_passive_queue_type               priority_queues
% 6.97/1.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.97/1.43  --inst_passive_queues_freq              [25;2]
% 6.97/1.43  --inst_dismatching                      true
% 6.97/1.43  --inst_eager_unprocessed_to_passive     true
% 6.97/1.43  --inst_prop_sim_given                   true
% 6.97/1.43  --inst_prop_sim_new                     false
% 6.97/1.43  --inst_subs_new                         false
% 6.97/1.43  --inst_eq_res_simp                      false
% 6.97/1.43  --inst_subs_given                       false
% 6.97/1.43  --inst_orphan_elimination               true
% 6.97/1.43  --inst_learning_loop_flag               true
% 6.97/1.43  --inst_learning_start                   3000
% 6.97/1.43  --inst_learning_factor                  2
% 6.97/1.43  --inst_start_prop_sim_after_learn       3
% 6.97/1.43  --inst_sel_renew                        solver
% 6.97/1.43  --inst_lit_activity_flag                true
% 6.97/1.43  --inst_restr_to_given                   false
% 6.97/1.43  --inst_activity_threshold               500
% 6.97/1.43  --inst_out_proof                        true
% 6.97/1.43  
% 6.97/1.43  ------ Resolution Options
% 6.97/1.43  
% 6.97/1.43  --resolution_flag                       true
% 6.97/1.43  --res_lit_sel                           adaptive
% 6.97/1.43  --res_lit_sel_side                      none
% 6.97/1.43  --res_ordering                          kbo
% 6.97/1.43  --res_to_prop_solver                    active
% 6.97/1.43  --res_prop_simpl_new                    false
% 6.97/1.43  --res_prop_simpl_given                  true
% 6.97/1.43  --res_passive_queue_type                priority_queues
% 6.97/1.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.97/1.43  --res_passive_queues_freq               [15;5]
% 6.97/1.43  --res_forward_subs                      full
% 6.97/1.43  --res_backward_subs                     full
% 6.97/1.43  --res_forward_subs_resolution           true
% 6.97/1.43  --res_backward_subs_resolution          true
% 6.97/1.43  --res_orphan_elimination                true
% 6.97/1.43  --res_time_limit                        2.
% 6.97/1.43  --res_out_proof                         true
% 6.97/1.43  
% 6.97/1.43  ------ Superposition Options
% 6.97/1.43  
% 6.97/1.43  --superposition_flag                    true
% 6.97/1.43  --sup_passive_queue_type                priority_queues
% 6.97/1.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.97/1.43  --sup_passive_queues_freq               [8;1;4]
% 6.97/1.43  --demod_completeness_check              fast
% 6.97/1.43  --demod_use_ground                      true
% 6.97/1.43  --sup_to_prop_solver                    passive
% 6.97/1.43  --sup_prop_simpl_new                    true
% 6.97/1.43  --sup_prop_simpl_given                  true
% 6.97/1.43  --sup_fun_splitting                     false
% 6.97/1.43  --sup_smt_interval                      50000
% 6.97/1.43  
% 6.97/1.43  ------ Superposition Simplification Setup
% 6.97/1.43  
% 6.97/1.43  --sup_indices_passive                   []
% 6.97/1.43  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.97/1.43  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.97/1.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.97/1.43  --sup_full_triv                         [TrivRules;PropSubs]
% 6.97/1.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.97/1.43  --sup_full_bw                           [BwDemod]
% 6.97/1.43  --sup_immed_triv                        [TrivRules]
% 6.97/1.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.97/1.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.97/1.43  --sup_immed_bw_main                     []
% 6.97/1.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.97/1.43  --sup_input_triv                        [Unflattening;TrivRules]
% 6.97/1.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.97/1.43  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.97/1.43  
% 6.97/1.43  ------ Combination Options
% 6.97/1.43  
% 6.97/1.43  --comb_res_mult                         3
% 6.97/1.43  --comb_sup_mult                         2
% 6.97/1.43  --comb_inst_mult                        10
% 6.97/1.43  
% 6.97/1.43  ------ Debug Options
% 6.97/1.43  
% 6.97/1.43  --dbg_backtrace                         false
% 6.97/1.43  --dbg_dump_prop_clauses                 false
% 6.97/1.43  --dbg_dump_prop_clauses_file            -
% 6.97/1.43  --dbg_out_stat                          false
% 6.97/1.43  ------ Parsing...
% 6.97/1.43  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.97/1.43  
% 6.97/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.97/1.43  
% 6.97/1.43  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.97/1.43  
% 6.97/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.97/1.43  ------ Proving...
% 6.97/1.43  ------ Problem Properties 
% 6.97/1.43  
% 6.97/1.43  
% 6.97/1.43  clauses                                 13
% 6.97/1.43  conjectures                             2
% 6.97/1.43  EPR                                     1
% 6.97/1.43  Horn                                    13
% 6.97/1.43  unary                                   11
% 6.97/1.43  binary                                  2
% 6.97/1.43  lits                                    15
% 6.97/1.43  lits eq                                 11
% 6.97/1.43  fd_pure                                 0
% 6.97/1.43  fd_pseudo                               0
% 6.97/1.43  fd_cond                                 0
% 6.97/1.43  fd_pseudo_cond                          0
% 6.97/1.43  AC symbols                              0
% 6.97/1.43  
% 6.97/1.43  ------ Schedule dynamic 5 is on 
% 6.97/1.43  
% 6.97/1.43  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.97/1.43  
% 6.97/1.43  
% 6.97/1.43  ------ 
% 6.97/1.43  Current options:
% 6.97/1.43  ------ 
% 6.97/1.43  
% 6.97/1.43  ------ Input Options
% 6.97/1.43  
% 6.97/1.43  --out_options                           all
% 6.97/1.43  --tptp_safe_out                         true
% 6.97/1.43  --problem_path                          ""
% 6.97/1.43  --include_path                          ""
% 6.97/1.43  --clausifier                            res/vclausify_rel
% 6.97/1.43  --clausifier_options                    --mode clausify
% 6.97/1.43  --stdin                                 false
% 6.97/1.43  --stats_out                             all
% 6.97/1.43  
% 6.97/1.43  ------ General Options
% 6.97/1.43  
% 6.97/1.43  --fof                                   false
% 6.97/1.43  --time_out_real                         305.
% 6.97/1.43  --time_out_virtual                      -1.
% 6.97/1.43  --symbol_type_check                     false
% 6.97/1.43  --clausify_out                          false
% 6.97/1.43  --sig_cnt_out                           false
% 6.97/1.43  --trig_cnt_out                          false
% 6.97/1.43  --trig_cnt_out_tolerance                1.
% 6.97/1.43  --trig_cnt_out_sk_spl                   false
% 6.97/1.43  --abstr_cl_out                          false
% 6.97/1.43  
% 6.97/1.43  ------ Global Options
% 6.97/1.43  
% 6.97/1.43  --schedule                              default
% 6.97/1.43  --add_important_lit                     false
% 6.97/1.43  --prop_solver_per_cl                    1000
% 6.97/1.43  --min_unsat_core                        false
% 6.97/1.43  --soft_assumptions                      false
% 6.97/1.43  --soft_lemma_size                       3
% 6.97/1.43  --prop_impl_unit_size                   0
% 6.97/1.43  --prop_impl_unit                        []
% 6.97/1.43  --share_sel_clauses                     true
% 6.97/1.43  --reset_solvers                         false
% 6.97/1.43  --bc_imp_inh                            [conj_cone]
% 6.97/1.43  --conj_cone_tolerance                   3.
% 6.97/1.43  --extra_neg_conj                        none
% 6.97/1.43  --large_theory_mode                     true
% 6.97/1.43  --prolific_symb_bound                   200
% 6.97/1.43  --lt_threshold                          2000
% 6.97/1.43  --clause_weak_htbl                      true
% 6.97/1.43  --gc_record_bc_elim                     false
% 6.97/1.43  
% 6.97/1.43  ------ Preprocessing Options
% 6.97/1.43  
% 6.97/1.43  --preprocessing_flag                    true
% 6.97/1.43  --time_out_prep_mult                    0.1
% 6.97/1.43  --splitting_mode                        input
% 6.97/1.43  --splitting_grd                         true
% 6.97/1.43  --splitting_cvd                         false
% 6.97/1.43  --splitting_cvd_svl                     false
% 6.97/1.43  --splitting_nvd                         32
% 6.97/1.43  --sub_typing                            true
% 6.97/1.43  --prep_gs_sim                           true
% 6.97/1.43  --prep_unflatten                        true
% 6.97/1.43  --prep_res_sim                          true
% 6.97/1.43  --prep_upred                            true
% 6.97/1.43  --prep_sem_filter                       exhaustive
% 6.97/1.43  --prep_sem_filter_out                   false
% 6.97/1.43  --pred_elim                             true
% 6.97/1.43  --res_sim_input                         true
% 6.97/1.44  --eq_ax_congr_red                       true
% 6.97/1.44  --pure_diseq_elim                       true
% 6.97/1.44  --brand_transform                       false
% 6.97/1.44  --non_eq_to_eq                          false
% 6.97/1.44  --prep_def_merge                        true
% 6.97/1.44  --prep_def_merge_prop_impl              false
% 6.97/1.44  --prep_def_merge_mbd                    true
% 6.97/1.44  --prep_def_merge_tr_red                 false
% 6.97/1.44  --prep_def_merge_tr_cl                  false
% 6.97/1.44  --smt_preprocessing                     true
% 6.97/1.44  --smt_ac_axioms                         fast
% 6.97/1.44  --preprocessed_out                      false
% 6.97/1.44  --preprocessed_stats                    false
% 6.97/1.44  
% 6.97/1.44  ------ Abstraction refinement Options
% 6.97/1.44  
% 6.97/1.44  --abstr_ref                             []
% 6.97/1.44  --abstr_ref_prep                        false
% 6.97/1.44  --abstr_ref_until_sat                   false
% 6.97/1.44  --abstr_ref_sig_restrict                funpre
% 6.97/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 6.97/1.44  --abstr_ref_under                       []
% 6.97/1.44  
% 6.97/1.44  ------ SAT Options
% 6.97/1.44  
% 6.97/1.44  --sat_mode                              false
% 6.97/1.44  --sat_fm_restart_options                ""
% 6.97/1.44  --sat_gr_def                            false
% 6.97/1.44  --sat_epr_types                         true
% 6.97/1.44  --sat_non_cyclic_types                  false
% 6.97/1.44  --sat_finite_models                     false
% 6.97/1.44  --sat_fm_lemmas                         false
% 6.97/1.44  --sat_fm_prep                           false
% 6.97/1.44  --sat_fm_uc_incr                        true
% 6.97/1.44  --sat_out_model                         small
% 6.97/1.44  --sat_out_clauses                       false
% 6.97/1.44  
% 6.97/1.44  ------ QBF Options
% 6.97/1.44  
% 6.97/1.44  --qbf_mode                              false
% 6.97/1.44  --qbf_elim_univ                         false
% 6.97/1.44  --qbf_dom_inst                          none
% 6.97/1.44  --qbf_dom_pre_inst                      false
% 6.97/1.44  --qbf_sk_in                             false
% 6.97/1.44  --qbf_pred_elim                         true
% 6.97/1.44  --qbf_split                             512
% 6.97/1.44  
% 6.97/1.44  ------ BMC1 Options
% 6.97/1.44  
% 6.97/1.44  --bmc1_incremental                      false
% 6.97/1.44  --bmc1_axioms                           reachable_all
% 6.97/1.44  --bmc1_min_bound                        0
% 6.97/1.44  --bmc1_max_bound                        -1
% 6.97/1.44  --bmc1_max_bound_default                -1
% 6.97/1.44  --bmc1_symbol_reachability              true
% 6.97/1.44  --bmc1_property_lemmas                  false
% 6.97/1.44  --bmc1_k_induction                      false
% 6.97/1.44  --bmc1_non_equiv_states                 false
% 6.97/1.44  --bmc1_deadlock                         false
% 6.97/1.44  --bmc1_ucm                              false
% 6.97/1.44  --bmc1_add_unsat_core                   none
% 6.97/1.44  --bmc1_unsat_core_children              false
% 6.97/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 6.97/1.44  --bmc1_out_stat                         full
% 6.97/1.44  --bmc1_ground_init                      false
% 6.97/1.44  --bmc1_pre_inst_next_state              false
% 6.97/1.44  --bmc1_pre_inst_state                   false
% 6.97/1.44  --bmc1_pre_inst_reach_state             false
% 6.97/1.44  --bmc1_out_unsat_core                   false
% 6.97/1.44  --bmc1_aig_witness_out                  false
% 6.97/1.44  --bmc1_verbose                          false
% 6.97/1.44  --bmc1_dump_clauses_tptp                false
% 6.97/1.44  --bmc1_dump_unsat_core_tptp             false
% 6.97/1.44  --bmc1_dump_file                        -
% 6.97/1.44  --bmc1_ucm_expand_uc_limit              128
% 6.97/1.44  --bmc1_ucm_n_expand_iterations          6
% 6.97/1.44  --bmc1_ucm_extend_mode                  1
% 6.97/1.44  --bmc1_ucm_init_mode                    2
% 6.97/1.44  --bmc1_ucm_cone_mode                    none
% 6.97/1.44  --bmc1_ucm_reduced_relation_type        0
% 6.97/1.44  --bmc1_ucm_relax_model                  4
% 6.97/1.44  --bmc1_ucm_full_tr_after_sat            true
% 6.97/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 6.97/1.44  --bmc1_ucm_layered_model                none
% 6.97/1.44  --bmc1_ucm_max_lemma_size               10
% 6.97/1.44  
% 6.97/1.44  ------ AIG Options
% 6.97/1.44  
% 6.97/1.44  --aig_mode                              false
% 6.97/1.44  
% 6.97/1.44  ------ Instantiation Options
% 6.97/1.44  
% 6.97/1.44  --instantiation_flag                    true
% 6.97/1.44  --inst_sos_flag                         false
% 6.97/1.44  --inst_sos_phase                        true
% 6.97/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.97/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.97/1.44  --inst_lit_sel_side                     none
% 6.97/1.44  --inst_solver_per_active                1400
% 6.97/1.44  --inst_solver_calls_frac                1.
% 6.97/1.44  --inst_passive_queue_type               priority_queues
% 6.97/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.97/1.44  --inst_passive_queues_freq              [25;2]
% 6.97/1.44  --inst_dismatching                      true
% 6.97/1.44  --inst_eager_unprocessed_to_passive     true
% 6.97/1.44  --inst_prop_sim_given                   true
% 6.97/1.44  --inst_prop_sim_new                     false
% 6.97/1.44  --inst_subs_new                         false
% 6.97/1.44  --inst_eq_res_simp                      false
% 6.97/1.44  --inst_subs_given                       false
% 6.97/1.44  --inst_orphan_elimination               true
% 6.97/1.44  --inst_learning_loop_flag               true
% 6.97/1.44  --inst_learning_start                   3000
% 6.97/1.44  --inst_learning_factor                  2
% 6.97/1.44  --inst_start_prop_sim_after_learn       3
% 6.97/1.44  --inst_sel_renew                        solver
% 6.97/1.44  --inst_lit_activity_flag                true
% 6.97/1.44  --inst_restr_to_given                   false
% 6.97/1.44  --inst_activity_threshold               500
% 6.97/1.44  --inst_out_proof                        true
% 6.97/1.44  
% 6.97/1.44  ------ Resolution Options
% 6.97/1.44  
% 6.97/1.44  --resolution_flag                       false
% 6.97/1.44  --res_lit_sel                           adaptive
% 6.97/1.44  --res_lit_sel_side                      none
% 6.97/1.44  --res_ordering                          kbo
% 6.97/1.44  --res_to_prop_solver                    active
% 6.97/1.44  --res_prop_simpl_new                    false
% 6.97/1.44  --res_prop_simpl_given                  true
% 6.97/1.44  --res_passive_queue_type                priority_queues
% 6.97/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.97/1.44  --res_passive_queues_freq               [15;5]
% 6.97/1.44  --res_forward_subs                      full
% 6.97/1.44  --res_backward_subs                     full
% 6.97/1.44  --res_forward_subs_resolution           true
% 6.97/1.44  --res_backward_subs_resolution          true
% 6.97/1.44  --res_orphan_elimination                true
% 6.97/1.44  --res_time_limit                        2.
% 6.97/1.44  --res_out_proof                         true
% 6.97/1.44  
% 6.97/1.44  ------ Superposition Options
% 6.97/1.44  
% 6.97/1.44  --superposition_flag                    true
% 6.97/1.44  --sup_passive_queue_type                priority_queues
% 6.97/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.97/1.44  --sup_passive_queues_freq               [8;1;4]
% 6.97/1.44  --demod_completeness_check              fast
% 6.97/1.44  --demod_use_ground                      true
% 6.97/1.44  --sup_to_prop_solver                    passive
% 6.97/1.44  --sup_prop_simpl_new                    true
% 6.97/1.44  --sup_prop_simpl_given                  true
% 6.97/1.44  --sup_fun_splitting                     false
% 6.97/1.44  --sup_smt_interval                      50000
% 6.97/1.44  
% 6.97/1.44  ------ Superposition Simplification Setup
% 6.97/1.44  
% 6.97/1.44  --sup_indices_passive                   []
% 6.97/1.44  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.97/1.44  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.97/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.97/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 6.97/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.97/1.44  --sup_full_bw                           [BwDemod]
% 6.97/1.44  --sup_immed_triv                        [TrivRules]
% 6.97/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.97/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.97/1.44  --sup_immed_bw_main                     []
% 6.97/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.97/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 6.97/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.97/1.44  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.97/1.44  
% 6.97/1.44  ------ Combination Options
% 6.97/1.44  
% 6.97/1.44  --comb_res_mult                         3
% 6.97/1.44  --comb_sup_mult                         2
% 6.97/1.44  --comb_inst_mult                        10
% 6.97/1.44  
% 6.97/1.44  ------ Debug Options
% 6.97/1.44  
% 6.97/1.44  --dbg_backtrace                         false
% 6.97/1.44  --dbg_dump_prop_clauses                 false
% 6.97/1.44  --dbg_dump_prop_clauses_file            -
% 6.97/1.44  --dbg_out_stat                          false
% 6.97/1.44  
% 6.97/1.44  
% 6.97/1.44  
% 6.97/1.44  
% 6.97/1.44  ------ Proving...
% 6.97/1.44  
% 6.97/1.44  
% 6.97/1.44  % SZS status Theorem for theBenchmark.p
% 6.97/1.44  
% 6.97/1.44  % SZS output start CNFRefutation for theBenchmark.p
% 6.97/1.44  
% 6.97/1.44  fof(f11,axiom,(
% 6.97/1.44    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.97/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.44  
% 6.97/1.44  fof(f32,plain,(
% 6.97/1.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.97/1.44    inference(cnf_transformation,[],[f11])).
% 6.97/1.44  
% 6.97/1.44  fof(f1,axiom,(
% 6.97/1.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 6.97/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.44  
% 6.97/1.44  fof(f22,plain,(
% 6.97/1.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 6.97/1.44    inference(cnf_transformation,[],[f1])).
% 6.97/1.44  
% 6.97/1.44  fof(f12,conjecture,(
% 6.97/1.44    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 6.97/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.44  
% 6.97/1.44  fof(f13,negated_conjecture,(
% 6.97/1.44    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 6.97/1.44    inference(negated_conjecture,[],[f12])).
% 6.97/1.44  
% 6.97/1.44  fof(f18,plain,(
% 6.97/1.44    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 6.97/1.44    inference(ennf_transformation,[],[f13])).
% 6.97/1.44  
% 6.97/1.44  fof(f19,plain,(
% 6.97/1.44    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 6.97/1.44    inference(flattening,[],[f18])).
% 6.97/1.44  
% 6.97/1.44  fof(f20,plain,(
% 6.97/1.44    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 6.97/1.44    introduced(choice_axiom,[])).
% 6.97/1.44  
% 6.97/1.44  fof(f21,plain,(
% 6.97/1.44    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 6.97/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f20])).
% 6.97/1.44  
% 6.97/1.44  fof(f33,plain,(
% 6.97/1.44    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 6.97/1.44    inference(cnf_transformation,[],[f21])).
% 6.97/1.44  
% 6.97/1.44  fof(f8,axiom,(
% 6.97/1.44    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 6.97/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.44  
% 6.97/1.44  fof(f17,plain,(
% 6.97/1.44    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.97/1.44    inference(ennf_transformation,[],[f8])).
% 6.97/1.44  
% 6.97/1.44  fof(f29,plain,(
% 6.97/1.44    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 6.97/1.44    inference(cnf_transformation,[],[f17])).
% 6.97/1.44  
% 6.97/1.44  fof(f2,axiom,(
% 6.97/1.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.97/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.44  
% 6.97/1.44  fof(f23,plain,(
% 6.97/1.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.97/1.44    inference(cnf_transformation,[],[f2])).
% 6.97/1.44  
% 6.97/1.44  fof(f10,axiom,(
% 6.97/1.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.97/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.44  
% 6.97/1.44  fof(f31,plain,(
% 6.97/1.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.97/1.44    inference(cnf_transformation,[],[f10])).
% 6.97/1.44  
% 6.97/1.44  fof(f37,plain,(
% 6.97/1.44    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 6.97/1.44    inference(definition_unfolding,[],[f23,f31,f31])).
% 6.97/1.44  
% 6.97/1.44  fof(f3,axiom,(
% 6.97/1.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.97/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.44  
% 6.97/1.44  fof(f14,plain,(
% 6.97/1.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.97/1.44    inference(unused_predicate_definition_removal,[],[f3])).
% 6.97/1.44  
% 6.97/1.44  fof(f15,plain,(
% 6.97/1.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 6.97/1.44    inference(ennf_transformation,[],[f14])).
% 6.97/1.44  
% 6.97/1.44  fof(f24,plain,(
% 6.97/1.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.97/1.44    inference(cnf_transformation,[],[f15])).
% 6.97/1.44  
% 6.97/1.44  fof(f38,plain,(
% 6.97/1.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 6.97/1.44    inference(definition_unfolding,[],[f24,f31])).
% 6.97/1.44  
% 6.97/1.44  fof(f35,plain,(
% 6.97/1.44    r1_xboole_0(sK3,sK1)),
% 6.97/1.44    inference(cnf_transformation,[],[f21])).
% 6.97/1.44  
% 6.97/1.44  fof(f9,axiom,(
% 6.97/1.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.97/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.44  
% 6.97/1.44  fof(f30,plain,(
% 6.97/1.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.97/1.44    inference(cnf_transformation,[],[f9])).
% 6.97/1.44  
% 6.97/1.44  fof(f40,plain,(
% 6.97/1.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 6.97/1.44    inference(definition_unfolding,[],[f30,f31])).
% 6.97/1.44  
% 6.97/1.44  fof(f6,axiom,(
% 6.97/1.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.97/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.44  
% 6.97/1.44  fof(f27,plain,(
% 6.97/1.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.97/1.44    inference(cnf_transformation,[],[f6])).
% 6.97/1.44  
% 6.97/1.44  fof(f4,axiom,(
% 6.97/1.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 6.97/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.44  
% 6.97/1.44  fof(f16,plain,(
% 6.97/1.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 6.97/1.44    inference(ennf_transformation,[],[f4])).
% 6.97/1.44  
% 6.97/1.44  fof(f25,plain,(
% 6.97/1.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 6.97/1.44    inference(cnf_transformation,[],[f16])).
% 6.97/1.44  
% 6.97/1.44  fof(f34,plain,(
% 6.97/1.44    r1_xboole_0(sK2,sK0)),
% 6.97/1.44    inference(cnf_transformation,[],[f21])).
% 6.97/1.44  
% 6.97/1.44  fof(f36,plain,(
% 6.97/1.44    sK1 != sK2),
% 6.97/1.44    inference(cnf_transformation,[],[f21])).
% 6.97/1.44  
% 6.97/1.44  cnf(c_9,plain,
% 6.97/1.44      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 6.97/1.44      inference(cnf_transformation,[],[f32]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_191,plain,
% 6.97/1.44      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 6.97/1.44      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_0,plain,
% 6.97/1.44      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 6.97/1.44      inference(cnf_transformation,[],[f22]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_13,negated_conjecture,
% 6.97/1.44      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 6.97/1.44      inference(cnf_transformation,[],[f33]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_210,plain,
% 6.97/1.44      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 6.97/1.44      inference(demodulation,[status(thm)],[c_0,c_13]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_7,plain,
% 6.97/1.44      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 6.97/1.44      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 6.97/1.44      inference(cnf_transformation,[],[f29]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_192,plain,
% 6.97/1.44      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 6.97/1.44      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 6.97/1.44      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_505,plain,
% 6.97/1.44      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 6.97/1.44      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 6.97/1.44      inference(superposition,[status(thm)],[c_0,c_192]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_2290,plain,
% 6.97/1.44      ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
% 6.97/1.44      | r1_tarski(k4_xboole_0(X0,sK3),sK2) = iProver_top ),
% 6.97/1.44      inference(superposition,[status(thm)],[c_210,c_505]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_2912,plain,
% 6.97/1.44      ( r1_tarski(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
% 6.97/1.44      inference(superposition,[status(thm)],[c_191,c_2290]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_1,plain,
% 6.97/1.44      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 6.97/1.44      inference(cnf_transformation,[],[f37]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_2,plain,
% 6.97/1.44      ( ~ r1_xboole_0(X0,X1)
% 6.97/1.44      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 6.97/1.44      inference(cnf_transformation,[],[f38]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_11,negated_conjecture,
% 6.97/1.44      ( r1_xboole_0(sK3,sK1) ),
% 6.97/1.44      inference(cnf_transformation,[],[f35]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_84,plain,
% 6.97/1.44      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 6.97/1.44      | sK3 != X0
% 6.97/1.44      | sK1 != X1 ),
% 6.97/1.44      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_85,plain,
% 6.97/1.44      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 6.97/1.44      inference(unflattening,[status(thm)],[c_84]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_607,plain,
% 6.97/1.44      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 6.97/1.44      inference(superposition,[status(thm)],[c_1,c_85]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_8,plain,
% 6.97/1.44      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 6.97/1.44      inference(cnf_transformation,[],[f40]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_679,plain,
% 6.97/1.44      ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK3) ),
% 6.97/1.44      inference(superposition,[status(thm)],[c_607,c_8]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_5,plain,
% 6.97/1.44      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.97/1.44      inference(cnf_transformation,[],[f27]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_681,plain,
% 6.97/1.44      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 6.97/1.44      inference(demodulation,[status(thm)],[c_679,c_5]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_2924,plain,
% 6.97/1.44      ( r1_tarski(sK1,sK2) = iProver_top ),
% 6.97/1.44      inference(light_normalisation,[status(thm)],[c_2912,c_681]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_3,plain,
% 6.97/1.44      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 6.97/1.44      inference(cnf_transformation,[],[f25]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_193,plain,
% 6.97/1.44      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 6.97/1.44      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_7327,plain,
% 6.97/1.44      ( k2_xboole_0(sK1,sK2) = sK2 ),
% 6.97/1.44      inference(superposition,[status(thm)],[c_2924,c_193]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_403,plain,
% 6.97/1.44      ( r1_tarski(sK2,k2_xboole_0(sK1,sK0)) = iProver_top ),
% 6.97/1.44      inference(superposition,[status(thm)],[c_210,c_191]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_2286,plain,
% 6.97/1.44      ( r1_tarski(k4_xboole_0(sK2,sK0),sK1) = iProver_top ),
% 6.97/1.44      inference(superposition,[status(thm)],[c_403,c_505]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_12,negated_conjecture,
% 6.97/1.44      ( r1_xboole_0(sK2,sK0) ),
% 6.97/1.44      inference(cnf_transformation,[],[f34]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_89,plain,
% 6.97/1.44      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 6.97/1.44      | sK0 != X1
% 6.97/1.44      | sK2 != X0 ),
% 6.97/1.44      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_90,plain,
% 6.97/1.44      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 6.97/1.44      inference(unflattening,[status(thm)],[c_89]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_621,plain,
% 6.97/1.44      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
% 6.97/1.44      inference(superposition,[status(thm)],[c_90,c_8]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_645,plain,
% 6.97/1.44      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 6.97/1.44      inference(demodulation,[status(thm)],[c_621,c_5]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_2310,plain,
% 6.97/1.44      ( r1_tarski(sK2,sK1) = iProver_top ),
% 6.97/1.44      inference(light_normalisation,[status(thm)],[c_2286,c_645]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_4462,plain,
% 6.97/1.44      ( k2_xboole_0(sK2,sK1) = sK1 ),
% 6.97/1.44      inference(superposition,[status(thm)],[c_2310,c_193]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_27899,plain,
% 6.97/1.44      ( k2_xboole_0(sK1,sK2) = sK1 ),
% 6.97/1.44      inference(superposition,[status(thm)],[c_4462,c_0]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_30291,plain,
% 6.97/1.44      ( sK2 = sK1 ),
% 6.97/1.44      inference(light_normalisation,[status(thm)],[c_7327,c_27899]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_124,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_247,plain,
% 6.97/1.44      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 6.97/1.44      inference(instantiation,[status(thm)],[c_124]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_29421,plain,
% 6.97/1.44      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 6.97/1.44      inference(instantiation,[status(thm)],[c_247]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_123,plain,( X0 = X0 ),theory(equality) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_1802,plain,
% 6.97/1.44      ( sK1 = sK1 ),
% 6.97/1.44      inference(instantiation,[status(thm)],[c_123]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(c_10,negated_conjecture,
% 6.97/1.44      ( sK1 != sK2 ),
% 6.97/1.44      inference(cnf_transformation,[],[f36]) ).
% 6.97/1.44  
% 6.97/1.44  cnf(contradiction,plain,
% 6.97/1.44      ( $false ),
% 6.97/1.44      inference(minisat,[status(thm)],[c_30291,c_29421,c_1802,c_10]) ).
% 6.97/1.44  
% 6.97/1.44  
% 6.97/1.44  % SZS output end CNFRefutation for theBenchmark.p
% 6.97/1.44  
% 6.97/1.44  ------                               Statistics
% 6.97/1.44  
% 6.97/1.44  ------ General
% 6.97/1.44  
% 6.97/1.44  abstr_ref_over_cycles:                  0
% 6.97/1.44  abstr_ref_under_cycles:                 0
% 6.97/1.44  gc_basic_clause_elim:                   0
% 6.97/1.44  forced_gc_time:                         0
% 6.97/1.44  parsing_time:                           0.007
% 6.97/1.44  unif_index_cands_time:                  0.
% 6.97/1.44  unif_index_add_time:                    0.
% 6.97/1.44  orderings_time:                         0.
% 6.97/1.44  out_proof_time:                         0.007
% 6.97/1.44  total_time:                             0.781
% 6.97/1.44  num_of_symbols:                         40
% 6.97/1.44  num_of_terms:                           29110
% 6.97/1.44  
% 6.97/1.44  ------ Preprocessing
% 6.97/1.44  
% 6.97/1.44  num_of_splits:                          0
% 6.97/1.44  num_of_split_atoms:                     0
% 6.97/1.44  num_of_reused_defs:                     0
% 6.97/1.44  num_eq_ax_congr_red:                    0
% 6.97/1.44  num_of_sem_filtered_clauses:            1
% 6.97/1.44  num_of_subtypes:                        0
% 6.97/1.44  monotx_restored_types:                  0
% 6.97/1.44  sat_num_of_epr_types:                   0
% 6.97/1.44  sat_num_of_non_cyclic_types:            0
% 6.97/1.44  sat_guarded_non_collapsed_types:        0
% 6.97/1.44  num_pure_diseq_elim:                    0
% 6.97/1.44  simp_replaced_by:                       0
% 6.97/1.44  res_preprocessed:                       64
% 6.97/1.44  prep_upred:                             0
% 6.97/1.44  prep_unflattend:                        4
% 6.97/1.44  smt_new_axioms:                         0
% 6.97/1.44  pred_elim_cands:                        1
% 6.97/1.44  pred_elim:                              1
% 6.97/1.44  pred_elim_cl:                           1
% 6.97/1.44  pred_elim_cycles:                       3
% 6.97/1.44  merged_defs:                            0
% 6.97/1.44  merged_defs_ncl:                        0
% 6.97/1.44  bin_hyper_res:                          0
% 6.97/1.44  prep_cycles:                            4
% 6.97/1.44  pred_elim_time:                         0.
% 6.97/1.44  splitting_time:                         0.
% 6.97/1.44  sem_filter_time:                        0.
% 6.97/1.44  monotx_time:                            0.
% 6.97/1.44  subtype_inf_time:                       0.
% 6.97/1.44  
% 6.97/1.44  ------ Problem properties
% 6.97/1.44  
% 6.97/1.44  clauses:                                13
% 6.97/1.44  conjectures:                            2
% 6.97/1.44  epr:                                    1
% 6.97/1.44  horn:                                   13
% 6.97/1.44  ground:                                 4
% 6.97/1.44  unary:                                  11
% 6.97/1.44  binary:                                 2
% 6.97/1.44  lits:                                   15
% 6.97/1.44  lits_eq:                                11
% 6.97/1.44  fd_pure:                                0
% 6.97/1.44  fd_pseudo:                              0
% 6.97/1.44  fd_cond:                                0
% 6.97/1.44  fd_pseudo_cond:                         0
% 6.97/1.44  ac_symbols:                             0
% 6.97/1.44  
% 6.97/1.44  ------ Propositional Solver
% 6.97/1.44  
% 6.97/1.44  prop_solver_calls:                      34
% 6.97/1.44  prop_fast_solver_calls:                 470
% 6.97/1.44  smt_solver_calls:                       0
% 6.97/1.44  smt_fast_solver_calls:                  0
% 6.97/1.44  prop_num_of_clauses:                    10059
% 6.97/1.44  prop_preprocess_simplified:             20975
% 6.97/1.44  prop_fo_subsumed:                       4
% 6.97/1.44  prop_solver_time:                       0.
% 6.97/1.44  smt_solver_time:                        0.
% 6.97/1.44  smt_fast_solver_time:                   0.
% 6.97/1.44  prop_fast_solver_time:                  0.
% 6.97/1.44  prop_unsat_core_time:                   0.001
% 6.97/1.44  
% 6.97/1.44  ------ QBF
% 6.97/1.44  
% 6.97/1.44  qbf_q_res:                              0
% 6.97/1.44  qbf_num_tautologies:                    0
% 6.97/1.44  qbf_prep_cycles:                        0
% 6.97/1.44  
% 6.97/1.44  ------ BMC1
% 6.97/1.44  
% 6.97/1.44  bmc1_current_bound:                     -1
% 6.97/1.44  bmc1_last_solved_bound:                 -1
% 6.97/1.44  bmc1_unsat_core_size:                   -1
% 6.97/1.44  bmc1_unsat_core_parents_size:           -1
% 6.97/1.44  bmc1_merge_next_fun:                    0
% 6.97/1.44  bmc1_unsat_core_clauses_time:           0.
% 6.97/1.44  
% 6.97/1.44  ------ Instantiation
% 6.97/1.44  
% 6.97/1.44  inst_num_of_clauses:                    3502
% 6.97/1.44  inst_num_in_passive:                    2199
% 6.97/1.44  inst_num_in_active:                     859
% 6.97/1.44  inst_num_in_unprocessed:                445
% 6.97/1.44  inst_num_of_loops:                      1060
% 6.97/1.44  inst_num_of_learning_restarts:          0
% 6.97/1.44  inst_num_moves_active_passive:          196
% 6.97/1.44  inst_lit_activity:                      0
% 6.97/1.44  inst_lit_activity_moves:                1
% 6.97/1.44  inst_num_tautologies:                   0
% 6.97/1.44  inst_num_prop_implied:                  0
% 6.97/1.44  inst_num_existing_simplified:           0
% 6.97/1.44  inst_num_eq_res_simplified:             0
% 6.97/1.44  inst_num_child_elim:                    0
% 6.97/1.44  inst_num_of_dismatching_blockings:      3714
% 6.97/1.44  inst_num_of_non_proper_insts:           3491
% 6.97/1.44  inst_num_of_duplicates:                 0
% 6.97/1.44  inst_inst_num_from_inst_to_res:         0
% 6.97/1.44  inst_dismatching_checking_time:         0.
% 6.97/1.44  
% 6.97/1.44  ------ Resolution
% 6.97/1.44  
% 6.97/1.44  res_num_of_clauses:                     0
% 6.97/1.44  res_num_in_passive:                     0
% 6.97/1.44  res_num_in_active:                      0
% 6.97/1.44  res_num_of_loops:                       68
% 6.97/1.44  res_forward_subset_subsumed:            556
% 6.97/1.44  res_backward_subset_subsumed:           2
% 6.97/1.44  res_forward_subsumed:                   0
% 6.97/1.44  res_backward_subsumed:                  0
% 6.97/1.44  res_forward_subsumption_resolution:     0
% 6.97/1.44  res_backward_subsumption_resolution:    0
% 6.97/1.44  res_clause_to_clause_subsumption:       7482
% 6.97/1.44  res_orphan_elimination:                 0
% 6.97/1.44  res_tautology_del:                      253
% 6.97/1.44  res_num_eq_res_simplified:              0
% 6.97/1.44  res_num_sel_changes:                    0
% 6.97/1.44  res_moves_from_active_to_pass:          0
% 6.97/1.44  
% 6.97/1.44  ------ Superposition
% 6.97/1.44  
% 6.97/1.44  sup_time_total:                         0.
% 6.97/1.44  sup_time_generating:                    0.
% 6.97/1.44  sup_time_sim_full:                      0.
% 6.97/1.44  sup_time_sim_immed:                     0.
% 6.97/1.44  
% 6.97/1.44  sup_num_of_clauses:                     882
% 6.97/1.44  sup_num_in_active:                      177
% 6.97/1.44  sup_num_in_passive:                     705
% 6.97/1.44  sup_num_of_loops:                       211
% 6.97/1.44  sup_fw_superposition:                   1267
% 6.97/1.44  sup_bw_superposition:                   1405
% 6.97/1.44  sup_immediate_simplified:               1570
% 6.97/1.44  sup_given_eliminated:                   15
% 6.97/1.44  comparisons_done:                       0
% 6.97/1.44  comparisons_avoided:                    0
% 6.97/1.44  
% 6.97/1.44  ------ Simplifications
% 6.97/1.44  
% 6.97/1.44  
% 6.97/1.44  sim_fw_subset_subsumed:                 23
% 6.97/1.44  sim_bw_subset_subsumed:                 4
% 6.97/1.44  sim_fw_subsumed:                        129
% 6.97/1.44  sim_bw_subsumed:                        2
% 6.97/1.44  sim_fw_subsumption_res:                 0
% 6.97/1.44  sim_bw_subsumption_res:                 0
% 6.97/1.44  sim_tautology_del:                      8
% 6.97/1.44  sim_eq_tautology_del:                   401
% 6.97/1.44  sim_eq_res_simp:                        0
% 6.97/1.44  sim_fw_demodulated:                     716
% 6.97/1.44  sim_bw_demodulated:                     150
% 6.97/1.44  sim_light_normalised:                   1070
% 6.97/1.44  sim_joinable_taut:                      0
% 6.97/1.44  sim_joinable_simp:                      0
% 6.97/1.44  sim_ac_normalised:                      0
% 6.97/1.44  sim_smt_subsumption:                    0
% 6.97/1.44  
%------------------------------------------------------------------------------
