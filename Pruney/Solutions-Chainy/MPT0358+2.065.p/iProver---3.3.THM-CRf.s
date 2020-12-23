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
% DateTime   : Thu Dec  3 11:40:00 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 134 expanded)
%              Number of clauses        :   42 (  54 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   21
%              Number of atoms          :  154 ( 383 expanded)
%              Number of equality atoms :  102 ( 205 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK0) != sK1
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( k1_subset_1(sK0) = sK1
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ( k1_subset_1(sK0) != sK1
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( k1_subset_1(sK0) = sK1
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f23,plain,
    ( k1_subset_1(sK0) = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f26,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,
    ( k1_subset_1(sK0) != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_58,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_62,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_141,plain,
    ( k3_subset_1(sK0,sK1) != X0
    | k4_xboole_0(X1,X0) = k1_xboole_0
    | sK1 != X1
    | sK1 = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_58,c_62])).

cnf(c_142,plain,
    ( k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_141])).

cnf(c_172,plain,
    ( sK1 = k1_xboole_0
    | k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_142])).

cnf(c_173,plain,
    ( k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_172])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_149,plain,
    ( k4_xboole_0(X0,X1) != k3_subset_1(sK0,sK1)
    | sK1 != X1
    | sK1 = k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_62])).

cnf(c_150,plain,
    ( k4_xboole_0(X0,sK1) != k3_subset_1(sK0,sK1)
    | sK1 = k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_149])).

cnf(c_193,plain,
    ( sP0_iProver_split
    | sK1 = k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_150])).

cnf(c_195,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_291,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_303,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_194,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_304,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_192,plain,
    ( k4_xboole_0(X0,sK1) != k3_subset_1(sK0,sK1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_150])).

cnf(c_252,plain,
    ( k4_xboole_0(X0,sK1) != k3_subset_1(sK0,sK1)
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_111,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_7])).

cnf(c_112,plain,
    ( k3_subset_1(X0,sK1) = k4_xboole_0(X0,sK1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK0) ),
    inference(unflattening,[status(thm)],[c_111])).

cnf(c_294,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(equality_resolution,[status(thm)],[c_112])).

cnf(c_389,plain,
    ( k4_xboole_0(X0,sK1) != k4_xboole_0(sK0,sK1)
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_252,c_294])).

cnf(c_395,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_389])).

cnf(c_396,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_395])).

cnf(c_397,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_173,c_193,c_303,c_304,c_396])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_56,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_60,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 != sK1 ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_133,plain,
    ( k3_subset_1(sK0,sK1) != X0
    | k4_xboole_0(X1,X0) != k1_xboole_0
    | sK1 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_56,c_60])).

cnf(c_134,plain,
    ( k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_170,plain,
    ( sK1 != k1_xboole_0
    | k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_134])).

cnf(c_171,plain,
    ( k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_347,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_171,c_294])).

cnf(c_401,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_397,c_347])).

cnf(c_410,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_401])).

cnf(c_3,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_412,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_410,c_3])).

cnf(c_413,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_412])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:38:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 0.76/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.76/0.96  
% 0.76/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.76/0.96  
% 0.76/0.96  ------  iProver source info
% 0.76/0.96  
% 0.76/0.96  git: date: 2020-06-30 10:37:57 +0100
% 0.76/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.76/0.96  git: non_committed_changes: false
% 0.76/0.96  git: last_make_outside_of_git: false
% 0.76/0.96  
% 0.76/0.96  ------ 
% 0.76/0.96  
% 0.76/0.96  ------ Input Options
% 0.76/0.96  
% 0.76/0.96  --out_options                           all
% 0.76/0.96  --tptp_safe_out                         true
% 0.76/0.96  --problem_path                          ""
% 0.76/0.96  --include_path                          ""
% 0.76/0.96  --clausifier                            res/vclausify_rel
% 0.76/0.96  --clausifier_options                    --mode clausify
% 0.76/0.96  --stdin                                 false
% 0.76/0.96  --stats_out                             all
% 0.76/0.96  
% 0.76/0.96  ------ General Options
% 0.76/0.96  
% 0.76/0.96  --fof                                   false
% 0.76/0.96  --time_out_real                         305.
% 0.76/0.96  --time_out_virtual                      -1.
% 0.76/0.96  --symbol_type_check                     false
% 0.76/0.96  --clausify_out                          false
% 0.76/0.96  --sig_cnt_out                           false
% 0.76/0.96  --trig_cnt_out                          false
% 0.76/0.96  --trig_cnt_out_tolerance                1.
% 0.76/0.96  --trig_cnt_out_sk_spl                   false
% 0.76/0.96  --abstr_cl_out                          false
% 0.76/0.96  
% 0.76/0.96  ------ Global Options
% 0.76/0.96  
% 0.76/0.96  --schedule                              default
% 0.76/0.96  --add_important_lit                     false
% 0.76/0.96  --prop_solver_per_cl                    1000
% 0.76/0.96  --min_unsat_core                        false
% 0.76/0.96  --soft_assumptions                      false
% 0.76/0.96  --soft_lemma_size                       3
% 0.76/0.96  --prop_impl_unit_size                   0
% 0.76/0.96  --prop_impl_unit                        []
% 0.76/0.96  --share_sel_clauses                     true
% 0.76/0.96  --reset_solvers                         false
% 0.76/0.96  --bc_imp_inh                            [conj_cone]
% 0.76/0.96  --conj_cone_tolerance                   3.
% 0.76/0.96  --extra_neg_conj                        none
% 0.76/0.96  --large_theory_mode                     true
% 0.76/0.96  --prolific_symb_bound                   200
% 0.76/0.96  --lt_threshold                          2000
% 0.76/0.96  --clause_weak_htbl                      true
% 0.76/0.96  --gc_record_bc_elim                     false
% 0.76/0.96  
% 0.76/0.96  ------ Preprocessing Options
% 0.76/0.96  
% 0.76/0.96  --preprocessing_flag                    true
% 0.76/0.96  --time_out_prep_mult                    0.1
% 0.76/0.96  --splitting_mode                        input
% 0.76/0.96  --splitting_grd                         true
% 0.76/0.96  --splitting_cvd                         false
% 0.76/0.96  --splitting_cvd_svl                     false
% 0.76/0.96  --splitting_nvd                         32
% 0.76/0.96  --sub_typing                            true
% 0.76/0.96  --prep_gs_sim                           true
% 0.76/0.96  --prep_unflatten                        true
% 0.76/0.96  --prep_res_sim                          true
% 0.76/0.96  --prep_upred                            true
% 0.76/0.96  --prep_sem_filter                       exhaustive
% 0.76/0.96  --prep_sem_filter_out                   false
% 0.76/0.96  --pred_elim                             true
% 0.76/0.96  --res_sim_input                         true
% 0.76/0.96  --eq_ax_congr_red                       true
% 0.76/0.96  --pure_diseq_elim                       true
% 0.76/0.96  --brand_transform                       false
% 0.76/0.96  --non_eq_to_eq                          false
% 0.76/0.96  --prep_def_merge                        true
% 0.76/0.96  --prep_def_merge_prop_impl              false
% 0.76/0.96  --prep_def_merge_mbd                    true
% 0.76/0.96  --prep_def_merge_tr_red                 false
% 0.76/0.96  --prep_def_merge_tr_cl                  false
% 0.76/0.96  --smt_preprocessing                     true
% 0.76/0.96  --smt_ac_axioms                         fast
% 0.76/0.96  --preprocessed_out                      false
% 0.76/0.96  --preprocessed_stats                    false
% 0.76/0.96  
% 0.76/0.96  ------ Abstraction refinement Options
% 0.76/0.96  
% 0.76/0.96  --abstr_ref                             []
% 0.76/0.96  --abstr_ref_prep                        false
% 0.76/0.96  --abstr_ref_until_sat                   false
% 0.76/0.96  --abstr_ref_sig_restrict                funpre
% 0.76/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 0.76/0.96  --abstr_ref_under                       []
% 0.76/0.96  
% 0.76/0.96  ------ SAT Options
% 0.76/0.96  
% 0.76/0.96  --sat_mode                              false
% 0.76/0.96  --sat_fm_restart_options                ""
% 0.76/0.96  --sat_gr_def                            false
% 0.76/0.96  --sat_epr_types                         true
% 0.76/0.96  --sat_non_cyclic_types                  false
% 0.76/0.96  --sat_finite_models                     false
% 0.76/0.96  --sat_fm_lemmas                         false
% 0.76/0.96  --sat_fm_prep                           false
% 0.76/0.96  --sat_fm_uc_incr                        true
% 0.76/0.96  --sat_out_model                         small
% 0.76/0.96  --sat_out_clauses                       false
% 0.76/0.96  
% 0.76/0.96  ------ QBF Options
% 0.76/0.96  
% 0.76/0.96  --qbf_mode                              false
% 0.76/0.96  --qbf_elim_univ                         false
% 0.76/0.96  --qbf_dom_inst                          none
% 0.76/0.96  --qbf_dom_pre_inst                      false
% 0.76/0.96  --qbf_sk_in                             false
% 0.76/0.96  --qbf_pred_elim                         true
% 0.76/0.96  --qbf_split                             512
% 0.76/0.96  
% 0.76/0.96  ------ BMC1 Options
% 0.76/0.96  
% 0.76/0.96  --bmc1_incremental                      false
% 0.76/0.96  --bmc1_axioms                           reachable_all
% 0.76/0.96  --bmc1_min_bound                        0
% 0.76/0.96  --bmc1_max_bound                        -1
% 0.76/0.96  --bmc1_max_bound_default                -1
% 0.76/0.96  --bmc1_symbol_reachability              true
% 0.76/0.96  --bmc1_property_lemmas                  false
% 0.76/0.96  --bmc1_k_induction                      false
% 0.76/0.96  --bmc1_non_equiv_states                 false
% 0.76/0.96  --bmc1_deadlock                         false
% 0.76/0.96  --bmc1_ucm                              false
% 0.76/0.96  --bmc1_add_unsat_core                   none
% 0.76/0.96  --bmc1_unsat_core_children              false
% 0.76/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 0.76/0.96  --bmc1_out_stat                         full
% 0.76/0.96  --bmc1_ground_init                      false
% 0.76/0.96  --bmc1_pre_inst_next_state              false
% 0.76/0.96  --bmc1_pre_inst_state                   false
% 0.76/0.96  --bmc1_pre_inst_reach_state             false
% 0.76/0.96  --bmc1_out_unsat_core                   false
% 0.76/0.96  --bmc1_aig_witness_out                  false
% 0.76/0.96  --bmc1_verbose                          false
% 0.76/0.96  --bmc1_dump_clauses_tptp                false
% 0.76/0.96  --bmc1_dump_unsat_core_tptp             false
% 0.76/0.96  --bmc1_dump_file                        -
% 0.76/0.96  --bmc1_ucm_expand_uc_limit              128
% 0.76/0.96  --bmc1_ucm_n_expand_iterations          6
% 0.76/0.96  --bmc1_ucm_extend_mode                  1
% 0.76/0.96  --bmc1_ucm_init_mode                    2
% 0.76/0.96  --bmc1_ucm_cone_mode                    none
% 0.76/0.96  --bmc1_ucm_reduced_relation_type        0
% 0.76/0.96  --bmc1_ucm_relax_model                  4
% 0.76/0.96  --bmc1_ucm_full_tr_after_sat            true
% 0.76/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 0.76/0.96  --bmc1_ucm_layered_model                none
% 0.76/0.96  --bmc1_ucm_max_lemma_size               10
% 0.76/0.96  
% 0.76/0.96  ------ AIG Options
% 0.76/0.96  
% 0.76/0.96  --aig_mode                              false
% 0.76/0.96  
% 0.76/0.96  ------ Instantiation Options
% 0.76/0.96  
% 0.76/0.96  --instantiation_flag                    true
% 0.76/0.96  --inst_sos_flag                         false
% 0.76/0.96  --inst_sos_phase                        true
% 0.76/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.76/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.76/0.96  --inst_lit_sel_side                     num_symb
% 0.76/0.96  --inst_solver_per_active                1400
% 0.76/0.96  --inst_solver_calls_frac                1.
% 0.76/0.96  --inst_passive_queue_type               priority_queues
% 0.76/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.76/0.96  --inst_passive_queues_freq              [25;2]
% 0.76/0.96  --inst_dismatching                      true
% 0.76/0.96  --inst_eager_unprocessed_to_passive     true
% 0.76/0.96  --inst_prop_sim_given                   true
% 0.76/0.96  --inst_prop_sim_new                     false
% 0.76/0.96  --inst_subs_new                         false
% 0.76/0.96  --inst_eq_res_simp                      false
% 0.76/0.96  --inst_subs_given                       false
% 0.76/0.96  --inst_orphan_elimination               true
% 0.76/0.96  --inst_learning_loop_flag               true
% 0.76/0.96  --inst_learning_start                   3000
% 0.76/0.96  --inst_learning_factor                  2
% 0.76/0.96  --inst_start_prop_sim_after_learn       3
% 0.76/0.96  --inst_sel_renew                        solver
% 0.76/0.96  --inst_lit_activity_flag                true
% 0.76/0.96  --inst_restr_to_given                   false
% 0.76/0.96  --inst_activity_threshold               500
% 0.76/0.96  --inst_out_proof                        true
% 0.76/0.96  
% 0.76/0.96  ------ Resolution Options
% 0.76/0.96  
% 0.76/0.96  --resolution_flag                       true
% 0.76/0.96  --res_lit_sel                           adaptive
% 0.76/0.96  --res_lit_sel_side                      none
% 0.76/0.96  --res_ordering                          kbo
% 0.76/0.96  --res_to_prop_solver                    active
% 0.76/0.96  --res_prop_simpl_new                    false
% 0.76/0.96  --res_prop_simpl_given                  true
% 0.76/0.96  --res_passive_queue_type                priority_queues
% 0.76/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.76/0.96  --res_passive_queues_freq               [15;5]
% 0.76/0.96  --res_forward_subs                      full
% 0.76/0.96  --res_backward_subs                     full
% 0.76/0.96  --res_forward_subs_resolution           true
% 0.76/0.96  --res_backward_subs_resolution          true
% 0.76/0.96  --res_orphan_elimination                true
% 0.76/0.96  --res_time_limit                        2.
% 0.76/0.96  --res_out_proof                         true
% 0.76/0.96  
% 0.76/0.96  ------ Superposition Options
% 0.76/0.96  
% 0.76/0.96  --superposition_flag                    true
% 0.76/0.96  --sup_passive_queue_type                priority_queues
% 0.76/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.76/0.96  --sup_passive_queues_freq               [8;1;4]
% 0.76/0.96  --demod_completeness_check              fast
% 0.76/0.96  --demod_use_ground                      true
% 0.76/0.96  --sup_to_prop_solver                    passive
% 0.76/0.96  --sup_prop_simpl_new                    true
% 0.76/0.96  --sup_prop_simpl_given                  true
% 0.76/0.96  --sup_fun_splitting                     false
% 0.76/0.96  --sup_smt_interval                      50000
% 0.76/0.96  
% 0.76/0.96  ------ Superposition Simplification Setup
% 0.76/0.96  
% 0.76/0.96  --sup_indices_passive                   []
% 0.76/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 0.76/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.96  --sup_full_bw                           [BwDemod]
% 0.76/0.96  --sup_immed_triv                        [TrivRules]
% 0.76/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.76/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.96  --sup_immed_bw_main                     []
% 0.76/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.76/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 0.76/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.76/0.96  
% 0.76/0.96  ------ Combination Options
% 0.76/0.96  
% 0.76/0.96  --comb_res_mult                         3
% 0.76/0.96  --comb_sup_mult                         2
% 0.76/0.96  --comb_inst_mult                        10
% 0.76/0.96  
% 0.76/0.96  ------ Debug Options
% 0.76/0.96  
% 0.76/0.96  --dbg_backtrace                         false
% 0.76/0.96  --dbg_dump_prop_clauses                 false
% 0.76/0.96  --dbg_dump_prop_clauses_file            -
% 0.76/0.96  --dbg_out_stat                          false
% 0.76/0.96  ------ Parsing...
% 0.76/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.76/0.96  
% 0.76/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.76/0.96  
% 0.76/0.96  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.76/0.96  
% 0.76/0.96  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.76/0.96  ------ Proving...
% 0.76/0.96  ------ Problem Properties 
% 0.76/0.96  
% 0.76/0.96  
% 0.76/0.96  clauses                                 7
% 0.76/0.96  conjectures                             0
% 0.76/0.96  EPR                                     1
% 0.76/0.96  Horn                                    5
% 0.76/0.96  unary                                   1
% 0.76/0.96  binary                                  5
% 0.76/0.96  lits                                    14
% 0.76/0.96  lits eq                                 12
% 0.76/0.96  fd_pure                                 0
% 0.76/0.96  fd_pseudo                               0
% 0.76/0.96  fd_cond                                 1
% 0.76/0.96  fd_pseudo_cond                          0
% 0.76/0.96  AC symbols                              0
% 0.76/0.96  
% 0.76/0.96  ------ Schedule dynamic 5 is on 
% 0.76/0.96  
% 0.76/0.96  ------ no conjectures: strip conj schedule 
% 0.76/0.96  
% 0.76/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 0.76/0.96  
% 0.76/0.96  
% 0.76/0.96  ------ 
% 0.76/0.96  Current options:
% 0.76/0.96  ------ 
% 0.76/0.96  
% 0.76/0.96  ------ Input Options
% 0.76/0.96  
% 0.76/0.96  --out_options                           all
% 0.76/0.96  --tptp_safe_out                         true
% 0.76/0.96  --problem_path                          ""
% 0.76/0.96  --include_path                          ""
% 0.76/0.96  --clausifier                            res/vclausify_rel
% 0.76/0.96  --clausifier_options                    --mode clausify
% 0.76/0.96  --stdin                                 false
% 0.76/0.96  --stats_out                             all
% 0.76/0.96  
% 0.76/0.96  ------ General Options
% 0.76/0.96  
% 0.76/0.96  --fof                                   false
% 0.76/0.96  --time_out_real                         305.
% 0.76/0.96  --time_out_virtual                      -1.
% 0.76/0.96  --symbol_type_check                     false
% 0.76/0.96  --clausify_out                          false
% 0.76/0.96  --sig_cnt_out                           false
% 0.76/0.96  --trig_cnt_out                          false
% 0.76/0.96  --trig_cnt_out_tolerance                1.
% 0.76/0.96  --trig_cnt_out_sk_spl                   false
% 0.76/0.96  --abstr_cl_out                          false
% 0.76/0.96  
% 0.76/0.96  ------ Global Options
% 0.76/0.96  
% 0.76/0.96  --schedule                              default
% 0.76/0.96  --add_important_lit                     false
% 0.76/0.96  --prop_solver_per_cl                    1000
% 0.76/0.96  --min_unsat_core                        false
% 0.76/0.96  --soft_assumptions                      false
% 0.76/0.96  --soft_lemma_size                       3
% 0.76/0.96  --prop_impl_unit_size                   0
% 0.76/0.96  --prop_impl_unit                        []
% 0.76/0.96  --share_sel_clauses                     true
% 0.76/0.96  --reset_solvers                         false
% 0.76/0.96  --bc_imp_inh                            [conj_cone]
% 0.76/0.96  --conj_cone_tolerance                   3.
% 0.76/0.96  --extra_neg_conj                        none
% 0.76/0.96  --large_theory_mode                     true
% 0.76/0.96  --prolific_symb_bound                   200
% 0.76/0.96  --lt_threshold                          2000
% 0.76/0.96  --clause_weak_htbl                      true
% 0.76/0.96  --gc_record_bc_elim                     false
% 0.76/0.96  
% 0.76/0.96  ------ Preprocessing Options
% 0.76/0.96  
% 0.76/0.96  --preprocessing_flag                    true
% 0.76/0.96  --time_out_prep_mult                    0.1
% 0.76/0.96  --splitting_mode                        input
% 0.76/0.96  --splitting_grd                         true
% 0.76/0.96  --splitting_cvd                         false
% 0.76/0.96  --splitting_cvd_svl                     false
% 0.76/0.96  --splitting_nvd                         32
% 0.76/0.96  --sub_typing                            true
% 0.76/0.96  --prep_gs_sim                           true
% 0.76/0.96  --prep_unflatten                        true
% 0.76/0.96  --prep_res_sim                          true
% 0.76/0.96  --prep_upred                            true
% 0.76/0.96  --prep_sem_filter                       exhaustive
% 0.76/0.96  --prep_sem_filter_out                   false
% 0.76/0.96  --pred_elim                             true
% 0.76/0.96  --res_sim_input                         true
% 0.76/0.96  --eq_ax_congr_red                       true
% 0.76/0.96  --pure_diseq_elim                       true
% 0.76/0.96  --brand_transform                       false
% 0.76/0.96  --non_eq_to_eq                          false
% 0.76/0.96  --prep_def_merge                        true
% 0.76/0.96  --prep_def_merge_prop_impl              false
% 0.76/0.96  --prep_def_merge_mbd                    true
% 0.76/0.96  --prep_def_merge_tr_red                 false
% 0.76/0.96  --prep_def_merge_tr_cl                  false
% 0.76/0.96  --smt_preprocessing                     true
% 0.76/0.96  --smt_ac_axioms                         fast
% 0.76/0.96  --preprocessed_out                      false
% 0.76/0.96  --preprocessed_stats                    false
% 0.76/0.96  
% 0.76/0.96  ------ Abstraction refinement Options
% 0.76/0.96  
% 0.76/0.96  --abstr_ref                             []
% 0.76/0.96  --abstr_ref_prep                        false
% 0.76/0.96  --abstr_ref_until_sat                   false
% 0.76/0.96  --abstr_ref_sig_restrict                funpre
% 0.76/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 0.76/0.96  --abstr_ref_under                       []
% 0.76/0.96  
% 0.76/0.96  ------ SAT Options
% 0.76/0.96  
% 0.76/0.96  --sat_mode                              false
% 0.76/0.97  --sat_fm_restart_options                ""
% 0.76/0.97  --sat_gr_def                            false
% 0.76/0.97  --sat_epr_types                         true
% 0.76/0.97  --sat_non_cyclic_types                  false
% 0.76/0.97  --sat_finite_models                     false
% 0.76/0.97  --sat_fm_lemmas                         false
% 0.76/0.97  --sat_fm_prep                           false
% 0.76/0.97  --sat_fm_uc_incr                        true
% 0.76/0.97  --sat_out_model                         small
% 0.76/0.97  --sat_out_clauses                       false
% 0.76/0.97  
% 0.76/0.97  ------ QBF Options
% 0.76/0.97  
% 0.76/0.97  --qbf_mode                              false
% 0.76/0.97  --qbf_elim_univ                         false
% 0.76/0.97  --qbf_dom_inst                          none
% 0.76/0.97  --qbf_dom_pre_inst                      false
% 0.76/0.97  --qbf_sk_in                             false
% 0.76/0.97  --qbf_pred_elim                         true
% 0.76/0.97  --qbf_split                             512
% 0.76/0.97  
% 0.76/0.97  ------ BMC1 Options
% 0.76/0.97  
% 0.76/0.97  --bmc1_incremental                      false
% 0.76/0.97  --bmc1_axioms                           reachable_all
% 0.76/0.97  --bmc1_min_bound                        0
% 0.76/0.97  --bmc1_max_bound                        -1
% 0.76/0.97  --bmc1_max_bound_default                -1
% 0.76/0.97  --bmc1_symbol_reachability              true
% 0.76/0.97  --bmc1_property_lemmas                  false
% 0.76/0.97  --bmc1_k_induction                      false
% 0.76/0.97  --bmc1_non_equiv_states                 false
% 0.76/0.97  --bmc1_deadlock                         false
% 0.76/0.97  --bmc1_ucm                              false
% 0.76/0.97  --bmc1_add_unsat_core                   none
% 0.76/0.97  --bmc1_unsat_core_children              false
% 0.76/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.76/0.97  --bmc1_out_stat                         full
% 0.76/0.97  --bmc1_ground_init                      false
% 0.76/0.97  --bmc1_pre_inst_next_state              false
% 0.76/0.97  --bmc1_pre_inst_state                   false
% 0.76/0.97  --bmc1_pre_inst_reach_state             false
% 0.76/0.97  --bmc1_out_unsat_core                   false
% 0.76/0.97  --bmc1_aig_witness_out                  false
% 0.76/0.97  --bmc1_verbose                          false
% 0.76/0.97  --bmc1_dump_clauses_tptp                false
% 0.76/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.76/0.97  --bmc1_dump_file                        -
% 0.76/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.76/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.76/0.97  --bmc1_ucm_extend_mode                  1
% 0.76/0.97  --bmc1_ucm_init_mode                    2
% 0.76/0.97  --bmc1_ucm_cone_mode                    none
% 0.76/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.76/0.97  --bmc1_ucm_relax_model                  4
% 0.76/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.76/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.76/0.97  --bmc1_ucm_layered_model                none
% 0.76/0.97  --bmc1_ucm_max_lemma_size               10
% 0.76/0.97  
% 0.76/0.97  ------ AIG Options
% 0.76/0.97  
% 0.76/0.97  --aig_mode                              false
% 0.76/0.97  
% 0.76/0.97  ------ Instantiation Options
% 0.76/0.97  
% 0.76/0.97  --instantiation_flag                    true
% 0.76/0.97  --inst_sos_flag                         false
% 0.76/0.97  --inst_sos_phase                        true
% 0.76/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.76/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.76/0.97  --inst_lit_sel_side                     none
% 0.76/0.97  --inst_solver_per_active                1400
% 0.76/0.97  --inst_solver_calls_frac                1.
% 0.76/0.97  --inst_passive_queue_type               priority_queues
% 0.76/0.97  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 0.76/0.97  --inst_passive_queues_freq              [25;2]
% 0.76/0.97  --inst_dismatching                      true
% 0.76/0.97  --inst_eager_unprocessed_to_passive     true
% 0.76/0.97  --inst_prop_sim_given                   true
% 0.76/0.97  --inst_prop_sim_new                     false
% 0.76/0.97  --inst_subs_new                         false
% 0.76/0.97  --inst_eq_res_simp                      false
% 0.76/0.97  --inst_subs_given                       false
% 0.76/0.97  --inst_orphan_elimination               true
% 0.76/0.97  --inst_learning_loop_flag               true
% 0.76/0.97  --inst_learning_start                   3000
% 0.76/0.97  --inst_learning_factor                  2
% 0.76/0.97  --inst_start_prop_sim_after_learn       3
% 0.76/0.97  --inst_sel_renew                        solver
% 0.76/0.97  --inst_lit_activity_flag                true
% 0.76/0.97  --inst_restr_to_given                   false
% 0.76/0.97  --inst_activity_threshold               500
% 0.76/0.97  --inst_out_proof                        true
% 0.76/0.97  
% 0.76/0.97  ------ Resolution Options
% 0.76/0.97  
% 0.76/0.97  --resolution_flag                       false
% 0.76/0.97  --res_lit_sel                           adaptive
% 0.76/0.97  --res_lit_sel_side                      none
% 0.76/0.97  --res_ordering                          kbo
% 0.76/0.97  --res_to_prop_solver                    active
% 0.76/0.97  --res_prop_simpl_new                    false
% 0.76/0.97  --res_prop_simpl_given                  true
% 0.76/0.97  --res_passive_queue_type                priority_queues
% 0.76/0.97  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 0.76/0.97  --res_passive_queues_freq               [15;5]
% 0.76/0.97  --res_forward_subs                      full
% 0.76/0.97  --res_backward_subs                     full
% 0.76/0.97  --res_forward_subs_resolution           true
% 0.76/0.97  --res_backward_subs_resolution          true
% 0.76/0.97  --res_orphan_elimination                true
% 0.76/0.97  --res_time_limit                        2.
% 0.76/0.97  --res_out_proof                         true
% 0.76/0.97  
% 0.76/0.97  ------ Superposition Options
% 0.76/0.97  
% 0.76/0.97  --superposition_flag                    true
% 0.76/0.97  --sup_passive_queue_type                priority_queues
% 0.76/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.76/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.76/0.97  --demod_completeness_check              fast
% 0.76/0.97  --demod_use_ground                      true
% 0.76/0.97  --sup_to_prop_solver                    passive
% 0.76/0.97  --sup_prop_simpl_new                    true
% 0.76/0.97  --sup_prop_simpl_given                  true
% 0.76/0.97  --sup_fun_splitting                     false
% 0.76/0.97  --sup_smt_interval                      50000
% 0.76/0.97  
% 0.76/0.97  ------ Superposition Simplification Setup
% 0.76/0.97  
% 0.76/0.97  --sup_indices_passive                   []
% 0.76/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.76/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.97  --sup_full_bw                           [BwDemod]
% 0.76/0.97  --sup_immed_triv                        [TrivRules]
% 0.76/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.76/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.97  --sup_immed_bw_main                     []
% 0.76/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.76/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.76/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.76/0.97  
% 0.76/0.97  ------ Combination Options
% 0.76/0.97  
% 0.76/0.97  --comb_res_mult                         3
% 0.76/0.97  --comb_sup_mult                         2
% 0.76/0.97  --comb_inst_mult                        10
% 0.76/0.97  
% 0.76/0.97  ------ Debug Options
% 0.76/0.97  
% 0.76/0.97  --dbg_backtrace                         false
% 0.76/0.97  --dbg_dump_prop_clauses                 false
% 0.76/0.97  --dbg_dump_prop_clauses_file            -
% 0.76/0.97  --dbg_out_stat                          false
% 0.76/0.97  
% 0.76/0.97  
% 0.76/0.97  
% 0.76/0.97  
% 0.76/0.97  ------ Proving...
% 0.76/0.97  
% 0.76/0.97  
% 0.76/0.97  % SZS status Theorem for theBenchmark.p
% 0.76/0.97  
% 0.76/0.97   Resolution empty clause
% 0.76/0.97  
% 0.76/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 0.76/0.97  
% 0.76/0.97  fof(f1,axiom,(
% 0.76/0.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.97  
% 0.76/0.97  fof(f11,plain,(
% 0.76/0.97    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.76/0.97    inference(nnf_transformation,[],[f1])).
% 0.76/0.97  
% 0.76/0.97  fof(f17,plain,(
% 0.76/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.76/0.97    inference(cnf_transformation,[],[f11])).
% 0.76/0.97  
% 0.76/0.97  fof(f6,conjecture,(
% 0.76/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.97  
% 0.76/0.97  fof(f7,negated_conjecture,(
% 0.76/0.97    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.76/0.97    inference(negated_conjecture,[],[f6])).
% 0.76/0.97  
% 0.76/0.97  fof(f10,plain,(
% 0.76/0.97    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.76/0.97    inference(ennf_transformation,[],[f7])).
% 0.76/0.97  
% 0.76/0.97  fof(f12,plain,(
% 0.76/0.97    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.76/0.97    inference(nnf_transformation,[],[f10])).
% 0.76/0.97  
% 0.76/0.97  fof(f13,plain,(
% 0.76/0.97    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.76/0.97    inference(flattening,[],[f12])).
% 0.76/0.97  
% 0.76/0.97  fof(f14,plain,(
% 0.76/0.97    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK0) != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (k1_subset_1(sK0) = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.76/0.97    introduced(choice_axiom,[])).
% 0.76/0.97  
% 0.76/0.97  fof(f15,plain,(
% 0.76/0.97    (k1_subset_1(sK0) != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (k1_subset_1(sK0) = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.76/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.76/0.97  
% 0.76/0.97  fof(f23,plain,(
% 0.76/0.97    k1_subset_1(sK0) = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.76/0.97    inference(cnf_transformation,[],[f15])).
% 0.76/0.97  
% 0.76/0.97  fof(f4,axiom,(
% 0.76/0.97    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.97  
% 0.76/0.97  fof(f20,plain,(
% 0.76/0.97    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.76/0.97    inference(cnf_transformation,[],[f4])).
% 0.76/0.97  
% 0.76/0.97  fof(f26,plain,(
% 0.76/0.97    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.76/0.97    inference(definition_unfolding,[],[f23,f20])).
% 0.76/0.97  
% 0.76/0.97  fof(f2,axiom,(
% 0.76/0.97    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.97  
% 0.76/0.97  fof(f8,plain,(
% 0.76/0.97    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.76/0.97    inference(ennf_transformation,[],[f2])).
% 0.76/0.97  
% 0.76/0.97  fof(f18,plain,(
% 0.76/0.97    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 0.76/0.97    inference(cnf_transformation,[],[f8])).
% 0.76/0.97  
% 0.76/0.97  fof(f5,axiom,(
% 0.76/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.97  
% 0.76/0.97  fof(f9,plain,(
% 0.76/0.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.76/0.97    inference(ennf_transformation,[],[f5])).
% 0.76/0.97  
% 0.76/0.97  fof(f21,plain,(
% 0.76/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.76/0.97    inference(cnf_transformation,[],[f9])).
% 0.76/0.97  
% 0.76/0.97  fof(f22,plain,(
% 0.76/0.97    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.76/0.97    inference(cnf_transformation,[],[f15])).
% 0.76/0.97  
% 0.76/0.97  fof(f16,plain,(
% 0.76/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.76/0.97    inference(cnf_transformation,[],[f11])).
% 0.76/0.97  
% 0.76/0.97  fof(f24,plain,(
% 0.76/0.97    k1_subset_1(sK0) != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.76/0.97    inference(cnf_transformation,[],[f15])).
% 0.76/0.97  
% 0.76/0.97  fof(f25,plain,(
% 0.76/0.97    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.76/0.97    inference(definition_unfolding,[],[f24,f20])).
% 0.76/0.97  
% 0.76/0.97  fof(f3,axiom,(
% 0.76/0.97    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 0.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.97  
% 0.76/0.97  fof(f19,plain,(
% 0.76/0.97    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 0.76/0.97    inference(cnf_transformation,[],[f3])).
% 0.76/0.97  
% 0.76/0.97  cnf(c_0,plain,
% 0.76/0.97      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 0.76/0.97      inference(cnf_transformation,[],[f17]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_58,plain,
% 0.76/0.97      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 0.76/0.97      inference(prop_impl,[status(thm)],[c_0]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_6,negated_conjecture,
% 0.76/0.97      ( r1_tarski(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 = sK1 ),
% 0.76/0.97      inference(cnf_transformation,[],[f26]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_62,plain,
% 0.76/0.97      ( r1_tarski(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 = sK1 ),
% 0.76/0.97      inference(prop_impl,[status(thm)],[c_6]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_141,plain,
% 0.76/0.97      ( k3_subset_1(sK0,sK1) != X0
% 0.76/0.97      | k4_xboole_0(X1,X0) = k1_xboole_0
% 0.76/0.97      | sK1 != X1
% 0.76/0.97      | sK1 = k1_xboole_0 ),
% 0.76/0.97      inference(resolution_lifted,[status(thm)],[c_58,c_62]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_142,plain,
% 0.76/0.97      ( k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k1_xboole_0
% 0.76/0.97      | sK1 = k1_xboole_0 ),
% 0.76/0.97      inference(unflattening,[status(thm)],[c_141]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_172,plain,
% 0.76/0.97      ( sK1 = k1_xboole_0
% 0.76/0.97      | k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 0.76/0.97      inference(prop_impl,[status(thm)],[c_142]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_173,plain,
% 0.76/0.97      ( k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k1_xboole_0
% 0.76/0.97      | sK1 = k1_xboole_0 ),
% 0.76/0.97      inference(renaming,[status(thm)],[c_172]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_2,plain,
% 0.76/0.97      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 0.76/0.97      inference(cnf_transformation,[],[f18]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_149,plain,
% 0.76/0.97      ( k4_xboole_0(X0,X1) != k3_subset_1(sK0,sK1)
% 0.76/0.97      | sK1 != X1
% 0.76/0.97      | sK1 = k1_xboole_0
% 0.76/0.97      | k1_xboole_0 = X1 ),
% 0.76/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_62]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_150,plain,
% 0.76/0.97      ( k4_xboole_0(X0,sK1) != k3_subset_1(sK0,sK1)
% 0.76/0.97      | sK1 = k1_xboole_0
% 0.76/0.97      | k1_xboole_0 = sK1 ),
% 0.76/0.97      inference(unflattening,[status(thm)],[c_149]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_193,plain,
% 0.76/0.97      ( sP0_iProver_split | sK1 = k1_xboole_0 | k1_xboole_0 = sK1 ),
% 0.76/0.97      inference(splitting,
% 0.76/0.97                [splitting(split),new_symbols(definition,[])],
% 0.76/0.97                [c_150]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_195,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_291,plain,
% 0.76/0.97      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 0.76/0.97      inference(instantiation,[status(thm)],[c_195]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_303,plain,
% 0.76/0.97      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 0.76/0.97      inference(instantiation,[status(thm)],[c_291]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_194,plain,( X0 = X0 ),theory(equality) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_304,plain,
% 0.76/0.97      ( sK1 = sK1 ),
% 0.76/0.97      inference(instantiation,[status(thm)],[c_194]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_192,plain,
% 0.76/0.97      ( k4_xboole_0(X0,sK1) != k3_subset_1(sK0,sK1) | ~ sP0_iProver_split ),
% 0.76/0.97      inference(splitting,
% 0.76/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.76/0.97                [c_150]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_252,plain,
% 0.76/0.97      ( k4_xboole_0(X0,sK1) != k3_subset_1(sK0,sK1)
% 0.76/0.97      | sP0_iProver_split != iProver_top ),
% 0.76/0.97      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_4,plain,
% 0.76/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.76/0.97      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 0.76/0.97      inference(cnf_transformation,[],[f21]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_7,negated_conjecture,
% 0.76/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 0.76/0.97      inference(cnf_transformation,[],[f22]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_111,plain,
% 0.76/0.97      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 0.76/0.97      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK0)
% 0.76/0.97      | sK1 != X1 ),
% 0.76/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_7]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_112,plain,
% 0.76/0.97      ( k3_subset_1(X0,sK1) = k4_xboole_0(X0,sK1)
% 0.76/0.97      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK0) ),
% 0.76/0.97      inference(unflattening,[status(thm)],[c_111]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_294,plain,
% 0.76/0.97      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 0.76/0.97      inference(equality_resolution,[status(thm)],[c_112]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_389,plain,
% 0.76/0.97      ( k4_xboole_0(X0,sK1) != k4_xboole_0(sK0,sK1)
% 0.76/0.97      | sP0_iProver_split != iProver_top ),
% 0.76/0.97      inference(light_normalisation,[status(thm)],[c_252,c_294]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_395,plain,
% 0.76/0.97      ( sP0_iProver_split != iProver_top ),
% 0.76/0.97      inference(equality_resolution,[status(thm)],[c_389]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_396,plain,
% 0.76/0.97      ( ~ sP0_iProver_split ),
% 0.76/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_395]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_397,plain,
% 0.76/0.97      ( sK1 = k1_xboole_0 ),
% 0.76/0.97      inference(global_propositional_subsumption,
% 0.76/0.97                [status(thm)],
% 0.76/0.97                [c_173,c_193,c_303,c_304,c_396]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_1,plain,
% 0.76/0.97      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 0.76/0.97      inference(cnf_transformation,[],[f16]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_56,plain,
% 0.76/0.97      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 0.76/0.97      inference(prop_impl,[status(thm)],[c_1]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_5,negated_conjecture,
% 0.76/0.97      ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 != sK1 ),
% 0.76/0.97      inference(cnf_transformation,[],[f25]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_60,plain,
% 0.76/0.97      ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 != sK1 ),
% 0.76/0.97      inference(prop_impl,[status(thm)],[c_5]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_133,plain,
% 0.76/0.97      ( k3_subset_1(sK0,sK1) != X0
% 0.76/0.97      | k4_xboole_0(X1,X0) != k1_xboole_0
% 0.76/0.97      | sK1 != X1
% 0.76/0.97      | sK1 != k1_xboole_0 ),
% 0.76/0.97      inference(resolution_lifted,[status(thm)],[c_56,c_60]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_134,plain,
% 0.76/0.97      ( k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) != k1_xboole_0
% 0.76/0.97      | sK1 != k1_xboole_0 ),
% 0.76/0.97      inference(unflattening,[status(thm)],[c_133]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_170,plain,
% 0.76/0.97      ( sK1 != k1_xboole_0
% 0.76/0.97      | k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) != k1_xboole_0 ),
% 0.76/0.97      inference(prop_impl,[status(thm)],[c_134]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_171,plain,
% 0.76/0.97      ( k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) != k1_xboole_0
% 0.76/0.97      | sK1 != k1_xboole_0 ),
% 0.76/0.97      inference(renaming,[status(thm)],[c_170]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_347,plain,
% 0.76/0.97      ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) != k1_xboole_0
% 0.76/0.97      | sK1 != k1_xboole_0 ),
% 0.76/0.97      inference(light_normalisation,[status(thm)],[c_171,c_294]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_401,plain,
% 0.76/0.97      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) != k1_xboole_0
% 0.76/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 0.76/0.97      inference(demodulation,[status(thm)],[c_397,c_347]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_410,plain,
% 0.76/0.97      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) != k1_xboole_0 ),
% 0.76/0.97      inference(equality_resolution_simp,[status(thm)],[c_401]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_3,plain,
% 0.76/0.97      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.76/0.97      inference(cnf_transformation,[],[f19]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_412,plain,
% 0.76/0.97      ( k1_xboole_0 != k1_xboole_0 ),
% 0.76/0.97      inference(demodulation,[status(thm)],[c_410,c_3]) ).
% 0.76/0.97  
% 0.76/0.97  cnf(c_413,plain,
% 0.76/0.97      ( $false ),
% 0.76/0.97      inference(equality_resolution_simp,[status(thm)],[c_412]) ).
% 0.76/0.97  
% 0.76/0.97  
% 0.76/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 0.76/0.97  
% 0.76/0.97  ------                               Statistics
% 0.76/0.97  
% 0.76/0.97  ------ General
% 0.76/0.97  
% 0.76/0.97  abstr_ref_over_cycles:                  0
% 0.76/0.97  abstr_ref_under_cycles:                 0
% 0.76/0.97  gc_basic_clause_elim:                   0
% 0.76/0.97  forced_gc_time:                         0
% 0.76/0.97  parsing_time:                           0.008
% 0.76/0.97  unif_index_cands_time:                  0.
% 0.76/0.97  unif_index_add_time:                    0.
% 0.76/0.97  orderings_time:                         0.
% 0.76/0.97  out_proof_time:                         0.008
% 0.76/0.97  total_time:                             0.045
% 0.76/0.97  num_of_symbols:                         40
% 0.76/0.97  num_of_terms:                           389
% 0.76/0.97  
% 0.76/0.97  ------ Preprocessing
% 0.76/0.97  
% 0.76/0.97  num_of_splits:                          1
% 0.76/0.97  num_of_split_atoms:                     1
% 0.76/0.97  num_of_reused_defs:                     0
% 0.76/0.97  num_eq_ax_congr_red:                    1
% 0.76/0.97  num_of_sem_filtered_clauses:            0
% 0.76/0.97  num_of_subtypes:                        0
% 0.76/0.97  monotx_restored_types:                  0
% 0.76/0.97  sat_num_of_epr_types:                   0
% 0.76/0.97  sat_num_of_non_cyclic_types:            0
% 0.76/0.97  sat_guarded_non_collapsed_types:        0
% 0.76/0.97  num_pure_diseq_elim:                    0
% 0.76/0.97  simp_replaced_by:                       0
% 0.76/0.97  res_preprocessed:                       26
% 0.76/0.97  prep_upred:                             0
% 0.76/0.97  prep_unflattend:                        8
% 0.76/0.97  smt_new_axioms:                         0
% 0.76/0.97  pred_elim_cands:                        0
% 0.76/0.97  pred_elim:                              2
% 0.76/0.97  pred_elim_cl:                           2
% 0.76/0.97  pred_elim_cycles:                       3
% 0.76/0.97  merged_defs:                            8
% 0.76/0.97  merged_defs_ncl:                        0
% 0.76/0.97  bin_hyper_res:                          8
% 0.76/0.97  prep_cycles:                            3
% 0.76/0.97  pred_elim_time:                         0.001
% 0.76/0.97  splitting_time:                         0.
% 0.76/0.97  sem_filter_time:                        0.
% 0.76/0.97  monotx_time:                            0.
% 0.76/0.97  subtype_inf_time:                       0.
% 0.76/0.97  
% 0.76/0.97  ------ Problem properties
% 0.76/0.97  
% 0.76/0.97  clauses:                                7
% 0.76/0.97  conjectures:                            0
% 0.76/0.97  epr:                                    1
% 0.76/0.97  horn:                                   5
% 0.76/0.97  ground:                                 3
% 0.76/0.97  unary:                                  1
% 0.76/0.97  binary:                                 5
% 0.76/0.97  lits:                                   14
% 0.76/0.97  lits_eq:                                12
% 0.76/0.97  fd_pure:                                0
% 0.76/0.97  fd_pseudo:                              0
% 0.76/0.97  fd_cond:                                1
% 0.76/0.97  fd_pseudo_cond:                         0
% 0.76/0.97  ac_symbols:                             0
% 0.76/0.97  
% 0.76/0.97  ------ Propositional Solver
% 0.76/0.97  
% 0.76/0.97  prop_solver_calls:                      21
% 0.76/0.97  prop_fast_solver_calls:                 134
% 0.76/0.97  smt_solver_calls:                       0
% 0.76/0.97  smt_fast_solver_calls:                  0
% 0.76/0.97  prop_num_of_clauses:                    109
% 0.76/0.97  prop_preprocess_simplified:             630
% 0.76/0.97  prop_fo_subsumed:                       1
% 0.76/0.97  prop_solver_time:                       0.
% 0.76/0.97  smt_solver_time:                        0.
% 0.76/0.97  smt_fast_solver_time:                   0.
% 0.76/0.97  prop_fast_solver_time:                  0.
% 0.76/0.97  prop_unsat_core_time:                   0.
% 0.76/0.97  
% 0.76/0.97  ------ QBF
% 0.76/0.97  
% 0.76/0.97  qbf_q_res:                              0
% 0.76/0.97  qbf_num_tautologies:                    0
% 0.76/0.97  qbf_prep_cycles:                        0
% 0.76/0.97  
% 0.76/0.97  ------ BMC1
% 0.76/0.97  
% 0.76/0.97  bmc1_current_bound:                     -1
% 0.76/0.97  bmc1_last_solved_bound:                 -1
% 0.76/0.97  bmc1_unsat_core_size:                   -1
% 0.76/0.97  bmc1_unsat_core_parents_size:           -1
% 0.76/0.97  bmc1_merge_next_fun:                    0
% 0.76/0.97  bmc1_unsat_core_clauses_time:           0.
% 0.76/0.97  
% 0.76/0.97  ------ Instantiation
% 0.76/0.97  
% 0.76/0.97  inst_num_of_clauses:                    50
% 0.76/0.97  inst_num_in_passive:                    18
% 0.76/0.97  inst_num_in_active:                     32
% 0.76/0.97  inst_num_in_unprocessed:                0
% 0.76/0.97  inst_num_of_loops:                      40
% 0.76/0.97  inst_num_of_learning_restarts:          0
% 0.76/0.97  inst_num_moves_active_passive:          5
% 0.76/0.97  inst_lit_activity:                      0
% 0.76/0.97  inst_lit_activity_moves:                0
% 0.76/0.97  inst_num_tautologies:                   0
% 0.76/0.97  inst_num_prop_implied:                  0
% 0.76/0.97  inst_num_existing_simplified:           0
% 0.76/0.97  inst_num_eq_res_simplified:             0
% 0.76/0.97  inst_num_child_elim:                    0
% 0.76/0.97  inst_num_of_dismatching_blockings:      2
% 0.76/0.97  inst_num_of_non_proper_insts:           26
% 0.76/0.97  inst_num_of_duplicates:                 0
% 0.76/0.97  inst_inst_num_from_inst_to_res:         0
% 0.76/0.97  inst_dismatching_checking_time:         0.
% 0.76/0.97  
% 0.76/0.97  ------ Resolution
% 0.76/0.97  
% 0.76/0.97  res_num_of_clauses:                     0
% 0.76/0.97  res_num_in_passive:                     0
% 0.76/0.97  res_num_in_active:                      0
% 0.76/0.97  res_num_of_loops:                       29
% 0.76/0.97  res_forward_subset_subsumed:            4
% 0.76/0.97  res_backward_subset_subsumed:           0
% 0.76/0.97  res_forward_subsumed:                   0
% 0.76/0.97  res_backward_subsumed:                  0
% 0.76/0.97  res_forward_subsumption_resolution:     0
% 0.76/0.97  res_backward_subsumption_resolution:    0
% 0.76/0.97  res_clause_to_clause_subsumption:       13
% 0.76/0.97  res_orphan_elimination:                 0
% 0.76/0.97  res_tautology_del:                      24
% 0.76/0.97  res_num_eq_res_simplified:              0
% 0.76/0.97  res_num_sel_changes:                    0
% 0.76/0.97  res_moves_from_active_to_pass:          0
% 0.76/0.97  
% 0.76/0.97  ------ Superposition
% 0.76/0.97  
% 0.76/0.97  sup_time_total:                         0.
% 0.76/0.97  sup_time_generating:                    0.
% 0.76/0.97  sup_time_sim_full:                      0.
% 0.76/0.97  sup_time_sim_immed:                     0.
% 0.76/0.97  
% 0.76/0.97  sup_num_of_clauses:                     6
% 0.76/0.97  sup_num_in_active:                      3
% 0.76/0.97  sup_num_in_passive:                     3
% 0.76/0.97  sup_num_of_loops:                       7
% 0.76/0.97  sup_fw_superposition:                   3
% 0.76/0.97  sup_bw_superposition:                   0
% 0.76/0.97  sup_immediate_simplified:               0
% 0.76/0.97  sup_given_eliminated:                   0
% 0.76/0.97  comparisons_done:                       0
% 0.76/0.97  comparisons_avoided:                    0
% 0.76/0.97  
% 0.76/0.97  ------ Simplifications
% 0.76/0.97  
% 0.76/0.97  
% 0.76/0.97  sim_fw_subset_subsumed:                 0
% 0.76/0.97  sim_bw_subset_subsumed:                 1
% 0.76/0.97  sim_fw_subsumed:                        0
% 0.76/0.97  sim_bw_subsumed:                        0
% 0.76/0.97  sim_fw_subsumption_res:                 0
% 0.76/0.97  sim_bw_subsumption_res:                 0
% 0.76/0.97  sim_tautology_del:                      0
% 0.76/0.97  sim_eq_tautology_del:                   2
% 0.76/0.97  sim_eq_res_simp:                        1
% 0.76/0.97  sim_fw_demodulated:                     1
% 0.76/0.97  sim_bw_demodulated:                     4
% 0.76/0.97  sim_light_normalised:                   2
% 0.76/0.97  sim_joinable_taut:                      0
% 0.76/0.97  sim_joinable_simp:                      0
% 0.76/0.97  sim_ac_normalised:                      0
% 0.76/0.97  sim_smt_subsumption:                    0
% 0.76/0.97  
%------------------------------------------------------------------------------
