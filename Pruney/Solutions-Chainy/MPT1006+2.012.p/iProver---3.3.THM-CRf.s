%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:32 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   67 (  92 expanded)
%              Number of clauses        :   32 (  35 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :   15
%              Number of atoms          :  134 ( 207 expanded)
%              Number of equality atoms :   77 ( 123 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f20,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f29])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0(X0))
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f27])).

fof(f46,plain,(
    ! [X0] : v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_316,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_312,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_914,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_316,c_312])).

cnf(c_9,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_926,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_914,c_9])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_311,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_330,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_311,c_2])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_313,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_639,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_330,c_313])).

cnf(c_6,plain,
    ( v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,plain,
    ( v1_xboole_0(sK0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_167,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_422,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(X1))
    | X0 != sK0(X1) ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_540,plain,
    ( ~ v1_xboole_0(sK0(X0))
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK0(X0) ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_545,plain,
    ( k1_xboole_0 != sK0(X0)
    | v1_xboole_0(sK0(X0)) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_544,plain,
    ( ~ v1_xboole_0(sK0(X0))
    | k1_xboole_0 = sK0(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_710,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_639,c_6,c_22,c_545,c_544])).

cnf(c_317,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_715,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_710,c_317])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_719,plain,
    ( k8_relset_1(k1_xboole_0,sK1,k1_xboole_0,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_715,c_11])).

cnf(c_1068,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_926,c_719])).

cnf(c_29,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_28,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1068,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.99/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.99/1.00  
% 0.99/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.99/1.00  
% 0.99/1.00  ------  iProver source info
% 0.99/1.00  
% 0.99/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.99/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.99/1.00  git: non_committed_changes: false
% 0.99/1.00  git: last_make_outside_of_git: false
% 0.99/1.00  
% 0.99/1.00  ------ 
% 0.99/1.00  
% 0.99/1.00  ------ Input Options
% 0.99/1.00  
% 0.99/1.00  --out_options                           all
% 0.99/1.00  --tptp_safe_out                         true
% 0.99/1.00  --problem_path                          ""
% 0.99/1.00  --include_path                          ""
% 0.99/1.00  --clausifier                            res/vclausify_rel
% 0.99/1.00  --clausifier_options                    --mode clausify
% 0.99/1.00  --stdin                                 false
% 0.99/1.00  --stats_out                             all
% 0.99/1.00  
% 0.99/1.00  ------ General Options
% 0.99/1.00  
% 0.99/1.00  --fof                                   false
% 0.99/1.00  --time_out_real                         305.
% 0.99/1.00  --time_out_virtual                      -1.
% 0.99/1.00  --symbol_type_check                     false
% 0.99/1.00  --clausify_out                          false
% 0.99/1.00  --sig_cnt_out                           false
% 0.99/1.00  --trig_cnt_out                          false
% 0.99/1.00  --trig_cnt_out_tolerance                1.
% 0.99/1.00  --trig_cnt_out_sk_spl                   false
% 0.99/1.00  --abstr_cl_out                          false
% 0.99/1.00  
% 0.99/1.00  ------ Global Options
% 0.99/1.00  
% 0.99/1.00  --schedule                              default
% 0.99/1.00  --add_important_lit                     false
% 0.99/1.00  --prop_solver_per_cl                    1000
% 0.99/1.00  --min_unsat_core                        false
% 0.99/1.00  --soft_assumptions                      false
% 0.99/1.00  --soft_lemma_size                       3
% 0.99/1.00  --prop_impl_unit_size                   0
% 0.99/1.00  --prop_impl_unit                        []
% 0.99/1.00  --share_sel_clauses                     true
% 0.99/1.00  --reset_solvers                         false
% 0.99/1.00  --bc_imp_inh                            [conj_cone]
% 0.99/1.00  --conj_cone_tolerance                   3.
% 0.99/1.00  --extra_neg_conj                        none
% 0.99/1.00  --large_theory_mode                     true
% 0.99/1.00  --prolific_symb_bound                   200
% 0.99/1.00  --lt_threshold                          2000
% 0.99/1.00  --clause_weak_htbl                      true
% 0.99/1.00  --gc_record_bc_elim                     false
% 0.99/1.00  
% 0.99/1.00  ------ Preprocessing Options
% 0.99/1.00  
% 0.99/1.00  --preprocessing_flag                    true
% 0.99/1.00  --time_out_prep_mult                    0.1
% 0.99/1.00  --splitting_mode                        input
% 0.99/1.00  --splitting_grd                         true
% 0.99/1.00  --splitting_cvd                         false
% 0.99/1.00  --splitting_cvd_svl                     false
% 0.99/1.00  --splitting_nvd                         32
% 0.99/1.00  --sub_typing                            true
% 0.99/1.00  --prep_gs_sim                           true
% 0.99/1.00  --prep_unflatten                        true
% 0.99/1.00  --prep_res_sim                          true
% 0.99/1.00  --prep_upred                            true
% 0.99/1.00  --prep_sem_filter                       exhaustive
% 0.99/1.00  --prep_sem_filter_out                   false
% 0.99/1.00  --pred_elim                             true
% 0.99/1.00  --res_sim_input                         true
% 0.99/1.00  --eq_ax_congr_red                       true
% 0.99/1.00  --pure_diseq_elim                       true
% 0.99/1.00  --brand_transform                       false
% 0.99/1.00  --non_eq_to_eq                          false
% 0.99/1.00  --prep_def_merge                        true
% 0.99/1.00  --prep_def_merge_prop_impl              false
% 0.99/1.00  --prep_def_merge_mbd                    true
% 0.99/1.00  --prep_def_merge_tr_red                 false
% 0.99/1.00  --prep_def_merge_tr_cl                  false
% 0.99/1.00  --smt_preprocessing                     true
% 0.99/1.00  --smt_ac_axioms                         fast
% 0.99/1.00  --preprocessed_out                      false
% 0.99/1.00  --preprocessed_stats                    false
% 0.99/1.00  
% 0.99/1.00  ------ Abstraction refinement Options
% 0.99/1.00  
% 0.99/1.00  --abstr_ref                             []
% 0.99/1.00  --abstr_ref_prep                        false
% 0.99/1.00  --abstr_ref_until_sat                   false
% 0.99/1.00  --abstr_ref_sig_restrict                funpre
% 0.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/1.00  --abstr_ref_under                       []
% 0.99/1.00  
% 0.99/1.00  ------ SAT Options
% 0.99/1.00  
% 0.99/1.00  --sat_mode                              false
% 0.99/1.00  --sat_fm_restart_options                ""
% 0.99/1.00  --sat_gr_def                            false
% 0.99/1.00  --sat_epr_types                         true
% 0.99/1.00  --sat_non_cyclic_types                  false
% 0.99/1.00  --sat_finite_models                     false
% 0.99/1.00  --sat_fm_lemmas                         false
% 0.99/1.00  --sat_fm_prep                           false
% 0.99/1.00  --sat_fm_uc_incr                        true
% 0.99/1.00  --sat_out_model                         small
% 0.99/1.00  --sat_out_clauses                       false
% 0.99/1.00  
% 0.99/1.00  ------ QBF Options
% 0.99/1.00  
% 0.99/1.00  --qbf_mode                              false
% 0.99/1.00  --qbf_elim_univ                         false
% 0.99/1.00  --qbf_dom_inst                          none
% 0.99/1.00  --qbf_dom_pre_inst                      false
% 0.99/1.00  --qbf_sk_in                             false
% 0.99/1.00  --qbf_pred_elim                         true
% 0.99/1.00  --qbf_split                             512
% 0.99/1.00  
% 0.99/1.00  ------ BMC1 Options
% 0.99/1.00  
% 0.99/1.00  --bmc1_incremental                      false
% 0.99/1.00  --bmc1_axioms                           reachable_all
% 0.99/1.00  --bmc1_min_bound                        0
% 0.99/1.00  --bmc1_max_bound                        -1
% 0.99/1.00  --bmc1_max_bound_default                -1
% 0.99/1.00  --bmc1_symbol_reachability              true
% 0.99/1.00  --bmc1_property_lemmas                  false
% 0.99/1.00  --bmc1_k_induction                      false
% 0.99/1.00  --bmc1_non_equiv_states                 false
% 0.99/1.00  --bmc1_deadlock                         false
% 0.99/1.00  --bmc1_ucm                              false
% 0.99/1.00  --bmc1_add_unsat_core                   none
% 0.99/1.00  --bmc1_unsat_core_children              false
% 0.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/1.00  --bmc1_out_stat                         full
% 0.99/1.00  --bmc1_ground_init                      false
% 0.99/1.00  --bmc1_pre_inst_next_state              false
% 0.99/1.00  --bmc1_pre_inst_state                   false
% 0.99/1.00  --bmc1_pre_inst_reach_state             false
% 0.99/1.00  --bmc1_out_unsat_core                   false
% 0.99/1.00  --bmc1_aig_witness_out                  false
% 0.99/1.00  --bmc1_verbose                          false
% 0.99/1.00  --bmc1_dump_clauses_tptp                false
% 0.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.99/1.00  --bmc1_dump_file                        -
% 0.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.99/1.00  --bmc1_ucm_extend_mode                  1
% 0.99/1.00  --bmc1_ucm_init_mode                    2
% 0.99/1.00  --bmc1_ucm_cone_mode                    none
% 0.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.99/1.00  --bmc1_ucm_relax_model                  4
% 0.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/1.00  --bmc1_ucm_layered_model                none
% 0.99/1.00  --bmc1_ucm_max_lemma_size               10
% 0.99/1.00  
% 0.99/1.00  ------ AIG Options
% 0.99/1.00  
% 0.99/1.00  --aig_mode                              false
% 0.99/1.00  
% 0.99/1.00  ------ Instantiation Options
% 0.99/1.00  
% 0.99/1.00  --instantiation_flag                    true
% 0.99/1.00  --inst_sos_flag                         false
% 0.99/1.00  --inst_sos_phase                        true
% 0.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/1.00  --inst_lit_sel_side                     num_symb
% 0.99/1.00  --inst_solver_per_active                1400
% 0.99/1.00  --inst_solver_calls_frac                1.
% 0.99/1.00  --inst_passive_queue_type               priority_queues
% 0.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/1.00  --inst_passive_queues_freq              [25;2]
% 0.99/1.00  --inst_dismatching                      true
% 0.99/1.00  --inst_eager_unprocessed_to_passive     true
% 0.99/1.00  --inst_prop_sim_given                   true
% 0.99/1.00  --inst_prop_sim_new                     false
% 0.99/1.00  --inst_subs_new                         false
% 0.99/1.00  --inst_eq_res_simp                      false
% 0.99/1.00  --inst_subs_given                       false
% 0.99/1.00  --inst_orphan_elimination               true
% 0.99/1.00  --inst_learning_loop_flag               true
% 0.99/1.00  --inst_learning_start                   3000
% 0.99/1.00  --inst_learning_factor                  2
% 0.99/1.00  --inst_start_prop_sim_after_learn       3
% 0.99/1.00  --inst_sel_renew                        solver
% 0.99/1.00  --inst_lit_activity_flag                true
% 0.99/1.00  --inst_restr_to_given                   false
% 0.99/1.00  --inst_activity_threshold               500
% 0.99/1.00  --inst_out_proof                        true
% 0.99/1.00  
% 0.99/1.00  ------ Resolution Options
% 0.99/1.00  
% 0.99/1.00  --resolution_flag                       true
% 0.99/1.00  --res_lit_sel                           adaptive
% 0.99/1.00  --res_lit_sel_side                      none
% 0.99/1.00  --res_ordering                          kbo
% 0.99/1.00  --res_to_prop_solver                    active
% 0.99/1.00  --res_prop_simpl_new                    false
% 0.99/1.00  --res_prop_simpl_given                  true
% 0.99/1.00  --res_passive_queue_type                priority_queues
% 0.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/1.00  --res_passive_queues_freq               [15;5]
% 0.99/1.00  --res_forward_subs                      full
% 0.99/1.00  --res_backward_subs                     full
% 0.99/1.00  --res_forward_subs_resolution           true
% 0.99/1.00  --res_backward_subs_resolution          true
% 0.99/1.00  --res_orphan_elimination                true
% 0.99/1.00  --res_time_limit                        2.
% 0.99/1.00  --res_out_proof                         true
% 0.99/1.00  
% 0.99/1.00  ------ Superposition Options
% 0.99/1.00  
% 0.99/1.00  --superposition_flag                    true
% 0.99/1.00  --sup_passive_queue_type                priority_queues
% 0.99/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.99/1.00  --demod_completeness_check              fast
% 0.99/1.00  --demod_use_ground                      true
% 0.99/1.00  --sup_to_prop_solver                    passive
% 0.99/1.00  --sup_prop_simpl_new                    true
% 0.99/1.00  --sup_prop_simpl_given                  true
% 0.99/1.00  --sup_fun_splitting                     false
% 0.99/1.00  --sup_smt_interval                      50000
% 0.99/1.00  
% 0.99/1.00  ------ Superposition Simplification Setup
% 0.99/1.00  
% 0.99/1.00  --sup_indices_passive                   []
% 0.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_full_bw                           [BwDemod]
% 0.99/1.00  --sup_immed_triv                        [TrivRules]
% 0.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_immed_bw_main                     []
% 0.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.00  
% 0.99/1.00  ------ Combination Options
% 0.99/1.00  
% 0.99/1.00  --comb_res_mult                         3
% 0.99/1.00  --comb_sup_mult                         2
% 0.99/1.00  --comb_inst_mult                        10
% 0.99/1.00  
% 0.99/1.00  ------ Debug Options
% 0.99/1.00  
% 0.99/1.00  --dbg_backtrace                         false
% 0.99/1.00  --dbg_dump_prop_clauses                 false
% 0.99/1.00  --dbg_dump_prop_clauses_file            -
% 0.99/1.00  --dbg_out_stat                          false
% 0.99/1.00  ------ Parsing...
% 0.99/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.99/1.00  
% 0.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.99/1.00  
% 0.99/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.99/1.00  
% 0.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.99/1.00  ------ Proving...
% 0.99/1.00  ------ Problem Properties 
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  clauses                                 13
% 0.99/1.00  conjectures                             2
% 0.99/1.00  EPR                                     1
% 0.99/1.00  Horn                                    12
% 0.99/1.00  unary                                   9
% 0.99/1.00  binary                                  2
% 0.99/1.00  lits                                    19
% 0.99/1.00  lits eq                                 10
% 0.99/1.00  fd_pure                                 0
% 0.99/1.00  fd_pseudo                               0
% 0.99/1.00  fd_cond                                 2
% 0.99/1.00  fd_pseudo_cond                          0
% 0.99/1.00  AC symbols                              0
% 0.99/1.00  
% 0.99/1.00  ------ Schedule dynamic 5 is on 
% 0.99/1.00  
% 0.99/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  ------ 
% 0.99/1.00  Current options:
% 0.99/1.00  ------ 
% 0.99/1.00  
% 0.99/1.00  ------ Input Options
% 0.99/1.00  
% 0.99/1.00  --out_options                           all
% 0.99/1.00  --tptp_safe_out                         true
% 0.99/1.00  --problem_path                          ""
% 0.99/1.00  --include_path                          ""
% 0.99/1.00  --clausifier                            res/vclausify_rel
% 0.99/1.00  --clausifier_options                    --mode clausify
% 0.99/1.00  --stdin                                 false
% 0.99/1.00  --stats_out                             all
% 0.99/1.00  
% 0.99/1.00  ------ General Options
% 0.99/1.00  
% 0.99/1.00  --fof                                   false
% 0.99/1.00  --time_out_real                         305.
% 0.99/1.00  --time_out_virtual                      -1.
% 0.99/1.00  --symbol_type_check                     false
% 0.99/1.00  --clausify_out                          false
% 0.99/1.00  --sig_cnt_out                           false
% 0.99/1.00  --trig_cnt_out                          false
% 0.99/1.00  --trig_cnt_out_tolerance                1.
% 0.99/1.00  --trig_cnt_out_sk_spl                   false
% 0.99/1.00  --abstr_cl_out                          false
% 0.99/1.00  
% 0.99/1.00  ------ Global Options
% 0.99/1.00  
% 0.99/1.00  --schedule                              default
% 0.99/1.00  --add_important_lit                     false
% 0.99/1.00  --prop_solver_per_cl                    1000
% 0.99/1.00  --min_unsat_core                        false
% 0.99/1.00  --soft_assumptions                      false
% 0.99/1.00  --soft_lemma_size                       3
% 0.99/1.00  --prop_impl_unit_size                   0
% 0.99/1.00  --prop_impl_unit                        []
% 0.99/1.00  --share_sel_clauses                     true
% 0.99/1.00  --reset_solvers                         false
% 0.99/1.00  --bc_imp_inh                            [conj_cone]
% 0.99/1.00  --conj_cone_tolerance                   3.
% 0.99/1.00  --extra_neg_conj                        none
% 0.99/1.00  --large_theory_mode                     true
% 0.99/1.00  --prolific_symb_bound                   200
% 0.99/1.00  --lt_threshold                          2000
% 0.99/1.00  --clause_weak_htbl                      true
% 0.99/1.00  --gc_record_bc_elim                     false
% 0.99/1.00  
% 0.99/1.00  ------ Preprocessing Options
% 0.99/1.00  
% 0.99/1.00  --preprocessing_flag                    true
% 0.99/1.00  --time_out_prep_mult                    0.1
% 0.99/1.00  --splitting_mode                        input
% 0.99/1.00  --splitting_grd                         true
% 0.99/1.00  --splitting_cvd                         false
% 0.99/1.00  --splitting_cvd_svl                     false
% 0.99/1.00  --splitting_nvd                         32
% 0.99/1.00  --sub_typing                            true
% 0.99/1.00  --prep_gs_sim                           true
% 0.99/1.00  --prep_unflatten                        true
% 0.99/1.00  --prep_res_sim                          true
% 0.99/1.00  --prep_upred                            true
% 0.99/1.00  --prep_sem_filter                       exhaustive
% 0.99/1.00  --prep_sem_filter_out                   false
% 0.99/1.00  --pred_elim                             true
% 0.99/1.00  --res_sim_input                         true
% 0.99/1.00  --eq_ax_congr_red                       true
% 0.99/1.00  --pure_diseq_elim                       true
% 0.99/1.00  --brand_transform                       false
% 0.99/1.00  --non_eq_to_eq                          false
% 0.99/1.00  --prep_def_merge                        true
% 0.99/1.00  --prep_def_merge_prop_impl              false
% 0.99/1.00  --prep_def_merge_mbd                    true
% 0.99/1.00  --prep_def_merge_tr_red                 false
% 0.99/1.00  --prep_def_merge_tr_cl                  false
% 0.99/1.00  --smt_preprocessing                     true
% 0.99/1.00  --smt_ac_axioms                         fast
% 0.99/1.00  --preprocessed_out                      false
% 0.99/1.00  --preprocessed_stats                    false
% 0.99/1.00  
% 0.99/1.00  ------ Abstraction refinement Options
% 0.99/1.00  
% 0.99/1.00  --abstr_ref                             []
% 0.99/1.00  --abstr_ref_prep                        false
% 0.99/1.00  --abstr_ref_until_sat                   false
% 0.99/1.00  --abstr_ref_sig_restrict                funpre
% 0.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/1.00  --abstr_ref_under                       []
% 0.99/1.00  
% 0.99/1.00  ------ SAT Options
% 0.99/1.00  
% 0.99/1.00  --sat_mode                              false
% 0.99/1.00  --sat_fm_restart_options                ""
% 0.99/1.00  --sat_gr_def                            false
% 0.99/1.00  --sat_epr_types                         true
% 0.99/1.00  --sat_non_cyclic_types                  false
% 0.99/1.00  --sat_finite_models                     false
% 0.99/1.00  --sat_fm_lemmas                         false
% 0.99/1.00  --sat_fm_prep                           false
% 0.99/1.00  --sat_fm_uc_incr                        true
% 0.99/1.00  --sat_out_model                         small
% 0.99/1.00  --sat_out_clauses                       false
% 0.99/1.00  
% 0.99/1.00  ------ QBF Options
% 0.99/1.00  
% 0.99/1.00  --qbf_mode                              false
% 0.99/1.00  --qbf_elim_univ                         false
% 0.99/1.00  --qbf_dom_inst                          none
% 0.99/1.00  --qbf_dom_pre_inst                      false
% 0.99/1.00  --qbf_sk_in                             false
% 0.99/1.00  --qbf_pred_elim                         true
% 0.99/1.00  --qbf_split                             512
% 0.99/1.00  
% 0.99/1.00  ------ BMC1 Options
% 0.99/1.00  
% 0.99/1.00  --bmc1_incremental                      false
% 0.99/1.00  --bmc1_axioms                           reachable_all
% 0.99/1.00  --bmc1_min_bound                        0
% 0.99/1.00  --bmc1_max_bound                        -1
% 0.99/1.00  --bmc1_max_bound_default                -1
% 0.99/1.00  --bmc1_symbol_reachability              true
% 0.99/1.00  --bmc1_property_lemmas                  false
% 0.99/1.00  --bmc1_k_induction                      false
% 0.99/1.00  --bmc1_non_equiv_states                 false
% 0.99/1.00  --bmc1_deadlock                         false
% 0.99/1.00  --bmc1_ucm                              false
% 0.99/1.00  --bmc1_add_unsat_core                   none
% 0.99/1.00  --bmc1_unsat_core_children              false
% 0.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/1.00  --bmc1_out_stat                         full
% 0.99/1.00  --bmc1_ground_init                      false
% 0.99/1.00  --bmc1_pre_inst_next_state              false
% 0.99/1.00  --bmc1_pre_inst_state                   false
% 0.99/1.00  --bmc1_pre_inst_reach_state             false
% 0.99/1.00  --bmc1_out_unsat_core                   false
% 0.99/1.00  --bmc1_aig_witness_out                  false
% 0.99/1.00  --bmc1_verbose                          false
% 0.99/1.00  --bmc1_dump_clauses_tptp                false
% 0.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.99/1.00  --bmc1_dump_file                        -
% 0.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.99/1.00  --bmc1_ucm_extend_mode                  1
% 0.99/1.00  --bmc1_ucm_init_mode                    2
% 0.99/1.00  --bmc1_ucm_cone_mode                    none
% 0.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.99/1.00  --bmc1_ucm_relax_model                  4
% 0.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/1.00  --bmc1_ucm_layered_model                none
% 0.99/1.00  --bmc1_ucm_max_lemma_size               10
% 0.99/1.00  
% 0.99/1.00  ------ AIG Options
% 0.99/1.00  
% 0.99/1.00  --aig_mode                              false
% 0.99/1.00  
% 0.99/1.00  ------ Instantiation Options
% 0.99/1.00  
% 0.99/1.00  --instantiation_flag                    true
% 0.99/1.00  --inst_sos_flag                         false
% 0.99/1.00  --inst_sos_phase                        true
% 0.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/1.00  --inst_lit_sel_side                     none
% 0.99/1.00  --inst_solver_per_active                1400
% 0.99/1.00  --inst_solver_calls_frac                1.
% 0.99/1.00  --inst_passive_queue_type               priority_queues
% 0.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/1.00  --inst_passive_queues_freq              [25;2]
% 0.99/1.00  --inst_dismatching                      true
% 0.99/1.00  --inst_eager_unprocessed_to_passive     true
% 0.99/1.00  --inst_prop_sim_given                   true
% 0.99/1.00  --inst_prop_sim_new                     false
% 0.99/1.00  --inst_subs_new                         false
% 0.99/1.00  --inst_eq_res_simp                      false
% 0.99/1.00  --inst_subs_given                       false
% 0.99/1.00  --inst_orphan_elimination               true
% 0.99/1.00  --inst_learning_loop_flag               true
% 0.99/1.00  --inst_learning_start                   3000
% 0.99/1.00  --inst_learning_factor                  2
% 0.99/1.00  --inst_start_prop_sim_after_learn       3
% 0.99/1.00  --inst_sel_renew                        solver
% 0.99/1.00  --inst_lit_activity_flag                true
% 0.99/1.00  --inst_restr_to_given                   false
% 0.99/1.00  --inst_activity_threshold               500
% 0.99/1.00  --inst_out_proof                        true
% 0.99/1.00  
% 0.99/1.00  ------ Resolution Options
% 0.99/1.00  
% 0.99/1.00  --resolution_flag                       false
% 0.99/1.00  --res_lit_sel                           adaptive
% 0.99/1.00  --res_lit_sel_side                      none
% 0.99/1.00  --res_ordering                          kbo
% 0.99/1.00  --res_to_prop_solver                    active
% 0.99/1.00  --res_prop_simpl_new                    false
% 0.99/1.00  --res_prop_simpl_given                  true
% 0.99/1.00  --res_passive_queue_type                priority_queues
% 0.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/1.00  --res_passive_queues_freq               [15;5]
% 0.99/1.00  --res_forward_subs                      full
% 0.99/1.00  --res_backward_subs                     full
% 0.99/1.00  --res_forward_subs_resolution           true
% 0.99/1.00  --res_backward_subs_resolution          true
% 0.99/1.00  --res_orphan_elimination                true
% 0.99/1.00  --res_time_limit                        2.
% 0.99/1.00  --res_out_proof                         true
% 0.99/1.00  
% 0.99/1.00  ------ Superposition Options
% 0.99/1.00  
% 0.99/1.00  --superposition_flag                    true
% 0.99/1.00  --sup_passive_queue_type                priority_queues
% 0.99/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.99/1.00  --demod_completeness_check              fast
% 0.99/1.00  --demod_use_ground                      true
% 0.99/1.00  --sup_to_prop_solver                    passive
% 0.99/1.00  --sup_prop_simpl_new                    true
% 0.99/1.00  --sup_prop_simpl_given                  true
% 0.99/1.00  --sup_fun_splitting                     false
% 0.99/1.00  --sup_smt_interval                      50000
% 0.99/1.00  
% 0.99/1.00  ------ Superposition Simplification Setup
% 0.99/1.00  
% 0.99/1.00  --sup_indices_passive                   []
% 0.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_full_bw                           [BwDemod]
% 0.99/1.00  --sup_immed_triv                        [TrivRules]
% 0.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_immed_bw_main                     []
% 0.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.00  
% 0.99/1.00  ------ Combination Options
% 0.99/1.00  
% 0.99/1.00  --comb_res_mult                         3
% 0.99/1.00  --comb_sup_mult                         2
% 0.99/1.00  --comb_inst_mult                        10
% 0.99/1.00  
% 0.99/1.00  ------ Debug Options
% 0.99/1.00  
% 0.99/1.00  --dbg_backtrace                         false
% 0.99/1.00  --dbg_dump_prop_clauses                 false
% 0.99/1.00  --dbg_dump_prop_clauses_file            -
% 0.99/1.00  --dbg_out_stat                          false
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  ------ Proving...
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  % SZS status Theorem for theBenchmark.p
% 0.99/1.00  
% 0.99/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.99/1.00  
% 0.99/1.00  fof(f12,axiom,(
% 0.99/1.00    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f44,plain,(
% 0.99/1.00    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.99/1.00    inference(cnf_transformation,[],[f12])).
% 0.99/1.00  
% 0.99/1.00  fof(f11,axiom,(
% 0.99/1.00    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f43,plain,(
% 0.99/1.00    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.99/1.00    inference(cnf_transformation,[],[f11])).
% 0.99/1.00  
% 0.99/1.00  fof(f59,plain,(
% 0.99/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.99/1.00    inference(definition_unfolding,[],[f44,f43])).
% 0.99/1.00  
% 0.99/1.00  fof(f16,axiom,(
% 0.99/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f23,plain,(
% 0.99/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.99/1.00    inference(ennf_transformation,[],[f16])).
% 0.99/1.00  
% 0.99/1.00  fof(f49,plain,(
% 0.99/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.99/1.00    inference(cnf_transformation,[],[f23])).
% 0.99/1.00  
% 0.99/1.00  fof(f15,axiom,(
% 0.99/1.00    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f48,plain,(
% 0.99/1.00    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 0.99/1.00    inference(cnf_transformation,[],[f15])).
% 0.99/1.00  
% 0.99/1.00  fof(f17,conjecture,(
% 0.99/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f18,negated_conjecture,(
% 0.99/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.99/1.00    inference(negated_conjecture,[],[f17])).
% 0.99/1.00  
% 0.99/1.00  fof(f19,plain,(
% 0.99/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.99/1.00    inference(pure_predicate_removal,[],[f18])).
% 0.99/1.00  
% 0.99/1.00  fof(f20,plain,(
% 0.99/1.00    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.99/1.00    inference(pure_predicate_removal,[],[f19])).
% 0.99/1.00  
% 0.99/1.00  fof(f24,plain,(
% 0.99/1.00    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.99/1.00    inference(ennf_transformation,[],[f20])).
% 0.99/1.00  
% 0.99/1.00  fof(f29,plain,(
% 0.99/1.00    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))))),
% 0.99/1.00    introduced(choice_axiom,[])).
% 0.99/1.00  
% 0.99/1.00  fof(f30,plain,(
% 0.99/1.00    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f29])).
% 0.99/1.00  
% 0.99/1.00  fof(f50,plain,(
% 0.99/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.99/1.00    inference(cnf_transformation,[],[f30])).
% 0.99/1.00  
% 0.99/1.00  fof(f9,axiom,(
% 0.99/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f25,plain,(
% 0.99/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.99/1.00    inference(nnf_transformation,[],[f9])).
% 0.99/1.00  
% 0.99/1.00  fof(f26,plain,(
% 0.99/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.99/1.00    inference(flattening,[],[f25])).
% 0.99/1.00  
% 0.99/1.00  fof(f40,plain,(
% 0.99/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.99/1.00    inference(cnf_transformation,[],[f26])).
% 0.99/1.00  
% 0.99/1.00  fof(f61,plain,(
% 0.99/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.99/1.00    inference(equality_resolution,[],[f40])).
% 0.99/1.00  
% 0.99/1.00  fof(f14,axiom,(
% 0.99/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.01  
% 0.99/1.01  fof(f22,plain,(
% 0.99/1.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.99/1.01    inference(ennf_transformation,[],[f14])).
% 0.99/1.01  
% 0.99/1.01  fof(f47,plain,(
% 0.99/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.99/1.01    inference(cnf_transformation,[],[f22])).
% 0.99/1.01  
% 0.99/1.01  fof(f13,axiom,(
% 0.99/1.01    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.01  
% 0.99/1.01  fof(f27,plain,(
% 0.99/1.01    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 0.99/1.01    introduced(choice_axiom,[])).
% 0.99/1.01  
% 0.99/1.01  fof(f28,plain,(
% 0.99/1.01    ! [X0] : (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 0.99/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f27])).
% 0.99/1.01  
% 0.99/1.01  fof(f46,plain,(
% 0.99/1.01    ( ! [X0] : (v1_xboole_0(sK0(X0))) )),
% 0.99/1.01    inference(cnf_transformation,[],[f28])).
% 0.99/1.01  
% 0.99/1.01  fof(f1,axiom,(
% 0.99/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.01  
% 0.99/1.01  fof(f21,plain,(
% 0.99/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.99/1.01    inference(ennf_transformation,[],[f1])).
% 0.99/1.01  
% 0.99/1.01  fof(f31,plain,(
% 0.99/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.99/1.01    inference(cnf_transformation,[],[f21])).
% 0.99/1.01  
% 0.99/1.01  fof(f51,plain,(
% 0.99/1.01    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2)),
% 0.99/1.01    inference(cnf_transformation,[],[f30])).
% 0.99/1.01  
% 0.99/1.01  fof(f39,plain,(
% 0.99/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.99/1.01    inference(cnf_transformation,[],[f26])).
% 0.99/1.01  
% 0.99/1.01  cnf(c_5,plain,
% 0.99/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 0.99/1.01      inference(cnf_transformation,[],[f59]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_316,plain,
% 0.99/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 0.99/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_10,plain,
% 0.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.99/1.01      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 0.99/1.01      inference(cnf_transformation,[],[f49]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_312,plain,
% 0.99/1.01      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 0.99/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.99/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_914,plain,
% 0.99/1.01      ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
% 0.99/1.01      inference(superposition,[status(thm)],[c_316,c_312]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_9,plain,
% 0.99/1.01      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.99/1.01      inference(cnf_transformation,[],[f48]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_926,plain,
% 0.99/1.01      ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k1_xboole_0 ),
% 0.99/1.01      inference(demodulation,[status(thm)],[c_914,c_9]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_12,negated_conjecture,
% 0.99/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
% 0.99/1.01      inference(cnf_transformation,[],[f50]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_311,plain,
% 0.99/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 0.99/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_2,plain,
% 0.99/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.99/1.01      inference(cnf_transformation,[],[f61]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_330,plain,
% 0.99/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 0.99/1.01      inference(demodulation,[status(thm)],[c_311,c_2]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_8,plain,
% 0.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.99/1.01      | ~ v1_xboole_0(X1)
% 0.99/1.01      | v1_xboole_0(X0) ),
% 0.99/1.01      inference(cnf_transformation,[],[f47]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_313,plain,
% 0.99/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 0.99/1.01      | v1_xboole_0(X1) != iProver_top
% 0.99/1.01      | v1_xboole_0(X0) = iProver_top ),
% 0.99/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_639,plain,
% 0.99/1.01      ( v1_xboole_0(sK3) = iProver_top
% 0.99/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 0.99/1.01      inference(superposition,[status(thm)],[c_330,c_313]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_6,plain,
% 0.99/1.01      ( v1_xboole_0(sK0(X0)) ),
% 0.99/1.01      inference(cnf_transformation,[],[f46]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_22,plain,
% 0.99/1.01      ( v1_xboole_0(sK0(X0)) = iProver_top ),
% 0.99/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_167,plain,
% 0.99/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 0.99/1.01      theory(equality) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_422,plain,
% 0.99/1.01      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK0(X1)) | X0 != sK0(X1) ),
% 0.99/1.01      inference(instantiation,[status(thm)],[c_167]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_540,plain,
% 0.99/1.01      ( ~ v1_xboole_0(sK0(X0))
% 0.99/1.01      | v1_xboole_0(k1_xboole_0)
% 0.99/1.01      | k1_xboole_0 != sK0(X0) ),
% 0.99/1.01      inference(instantiation,[status(thm)],[c_422]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_545,plain,
% 0.99/1.01      ( k1_xboole_0 != sK0(X0)
% 0.99/1.01      | v1_xboole_0(sK0(X0)) != iProver_top
% 0.99/1.01      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 0.99/1.01      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_0,plain,
% 0.99/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 0.99/1.01      inference(cnf_transformation,[],[f31]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_544,plain,
% 0.99/1.01      ( ~ v1_xboole_0(sK0(X0)) | k1_xboole_0 = sK0(X0) ),
% 0.99/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_710,plain,
% 0.99/1.01      ( v1_xboole_0(sK3) = iProver_top ),
% 0.99/1.01      inference(global_propositional_subsumption,
% 0.99/1.01                [status(thm)],
% 0.99/1.01                [c_639,c_6,c_22,c_545,c_544]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_317,plain,
% 0.99/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 0.99/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_715,plain,
% 0.99/1.01      ( sK3 = k1_xboole_0 ),
% 0.99/1.01      inference(superposition,[status(thm)],[c_710,c_317]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_11,negated_conjecture,
% 0.99/1.01      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2) ),
% 0.99/1.01      inference(cnf_transformation,[],[f51]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_719,plain,
% 0.99/1.01      ( k8_relset_1(k1_xboole_0,sK1,k1_xboole_0,sK2) != k1_xboole_0 ),
% 0.99/1.01      inference(demodulation,[status(thm)],[c_715,c_11]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_1068,plain,
% 0.99/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 0.99/1.01      inference(demodulation,[status(thm)],[c_926,c_719]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_29,plain,
% 0.99/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 0.99/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_3,plain,
% 0.99/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 0.99/1.01      | k1_xboole_0 = X0
% 0.99/1.01      | k1_xboole_0 = X1 ),
% 0.99/1.01      inference(cnf_transformation,[],[f39]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(c_28,plain,
% 0.99/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 0.99/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 0.99/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 0.99/1.01  
% 0.99/1.01  cnf(contradiction,plain,
% 0.99/1.01      ( $false ),
% 0.99/1.01      inference(minisat,[status(thm)],[c_1068,c_29,c_28]) ).
% 0.99/1.01  
% 0.99/1.01  
% 0.99/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 0.99/1.01  
% 0.99/1.01  ------                               Statistics
% 0.99/1.01  
% 0.99/1.01  ------ General
% 0.99/1.01  
% 0.99/1.01  abstr_ref_over_cycles:                  0
% 0.99/1.01  abstr_ref_under_cycles:                 0
% 0.99/1.01  gc_basic_clause_elim:                   0
% 0.99/1.01  forced_gc_time:                         0
% 0.99/1.01  parsing_time:                           0.008
% 0.99/1.01  unif_index_cands_time:                  0.
% 0.99/1.01  unif_index_add_time:                    0.
% 0.99/1.01  orderings_time:                         0.
% 0.99/1.01  out_proof_time:                         0.007
% 0.99/1.01  total_time:                             0.062
% 0.99/1.01  num_of_symbols:                         43
% 0.99/1.01  num_of_terms:                           1296
% 0.99/1.01  
% 0.99/1.01  ------ Preprocessing
% 0.99/1.01  
% 0.99/1.01  num_of_splits:                          0
% 0.99/1.01  num_of_split_atoms:                     0
% 0.99/1.01  num_of_reused_defs:                     0
% 0.99/1.01  num_eq_ax_congr_red:                    4
% 0.99/1.01  num_of_sem_filtered_clauses:            1
% 0.99/1.01  num_of_subtypes:                        0
% 0.99/1.01  monotx_restored_types:                  0
% 0.99/1.01  sat_num_of_epr_types:                   0
% 0.99/1.01  sat_num_of_non_cyclic_types:            0
% 0.99/1.01  sat_guarded_non_collapsed_types:        0
% 0.99/1.01  num_pure_diseq_elim:                    0
% 0.99/1.01  simp_replaced_by:                       0
% 0.99/1.01  res_preprocessed:                       58
% 0.99/1.01  prep_upred:                             0
% 0.99/1.01  prep_unflattend:                        6
% 0.99/1.01  smt_new_axioms:                         0
% 0.99/1.01  pred_elim_cands:                        2
% 0.99/1.01  pred_elim:                              0
% 0.99/1.01  pred_elim_cl:                           0
% 0.99/1.01  pred_elim_cycles:                       1
% 0.99/1.01  merged_defs:                            0
% 0.99/1.01  merged_defs_ncl:                        0
% 0.99/1.01  bin_hyper_res:                          0
% 0.99/1.01  prep_cycles:                            3
% 0.99/1.01  pred_elim_time:                         0.
% 0.99/1.01  splitting_time:                         0.
% 0.99/1.01  sem_filter_time:                        0.
% 0.99/1.01  monotx_time:                            0.
% 0.99/1.01  subtype_inf_time:                       0.
% 0.99/1.01  
% 0.99/1.01  ------ Problem properties
% 0.99/1.01  
% 0.99/1.01  clauses:                                13
% 0.99/1.01  conjectures:                            2
% 0.99/1.01  epr:                                    1
% 0.99/1.01  horn:                                   12
% 0.99/1.01  ground:                                 3
% 0.99/1.01  unary:                                  9
% 0.99/1.01  binary:                                 2
% 0.99/1.01  lits:                                   19
% 0.99/1.01  lits_eq:                                10
% 0.99/1.01  fd_pure:                                0
% 0.99/1.01  fd_pseudo:                              0
% 0.99/1.01  fd_cond:                                2
% 0.99/1.01  fd_pseudo_cond:                         0
% 0.99/1.01  ac_symbols:                             0
% 0.99/1.01  
% 0.99/1.01  ------ Propositional Solver
% 0.99/1.01  
% 0.99/1.01  prop_solver_calls:                      22
% 0.99/1.01  prop_fast_solver_calls:                 291
% 0.99/1.01  smt_solver_calls:                       0
% 0.99/1.01  smt_fast_solver_calls:                  0
% 0.99/1.01  prop_num_of_clauses:                    456
% 0.99/1.01  prop_preprocess_simplified:             2164
% 0.99/1.01  prop_fo_subsumed:                       2
% 0.99/1.01  prop_solver_time:                       0.
% 0.99/1.01  smt_solver_time:                        0.
% 0.99/1.01  smt_fast_solver_time:                   0.
% 0.99/1.01  prop_fast_solver_time:                  0.
% 0.99/1.01  prop_unsat_core_time:                   0.
% 0.99/1.01  
% 0.99/1.01  ------ QBF
% 0.99/1.01  
% 0.99/1.01  qbf_q_res:                              0
% 0.99/1.01  qbf_num_tautologies:                    0
% 0.99/1.01  qbf_prep_cycles:                        0
% 0.99/1.01  
% 0.99/1.01  ------ BMC1
% 0.99/1.01  
% 0.99/1.01  bmc1_current_bound:                     -1
% 0.99/1.01  bmc1_last_solved_bound:                 -1
% 0.99/1.01  bmc1_unsat_core_size:                   -1
% 0.99/1.01  bmc1_unsat_core_parents_size:           -1
% 0.99/1.01  bmc1_merge_next_fun:                    0
% 0.99/1.01  bmc1_unsat_core_clauses_time:           0.
% 0.99/1.01  
% 0.99/1.01  ------ Instantiation
% 0.99/1.01  
% 0.99/1.01  inst_num_of_clauses:                    203
% 0.99/1.01  inst_num_in_passive:                    108
% 0.99/1.01  inst_num_in_active:                     93
% 0.99/1.01  inst_num_in_unprocessed:                2
% 0.99/1.01  inst_num_of_loops:                      100
% 0.99/1.01  inst_num_of_learning_restarts:          0
% 0.99/1.01  inst_num_moves_active_passive:          6
% 0.99/1.01  inst_lit_activity:                      0
% 0.99/1.01  inst_lit_activity_moves:                0
% 0.99/1.01  inst_num_tautologies:                   0
% 0.99/1.01  inst_num_prop_implied:                  0
% 0.99/1.01  inst_num_existing_simplified:           0
% 0.99/1.01  inst_num_eq_res_simplified:             0
% 0.99/1.01  inst_num_child_elim:                    0
% 0.99/1.01  inst_num_of_dismatching_blockings:      11
% 0.99/1.01  inst_num_of_non_proper_insts:           125
% 0.99/1.01  inst_num_of_duplicates:                 0
% 0.99/1.01  inst_inst_num_from_inst_to_res:         0
% 0.99/1.01  inst_dismatching_checking_time:         0.
% 0.99/1.01  
% 0.99/1.01  ------ Resolution
% 0.99/1.01  
% 0.99/1.01  res_num_of_clauses:                     0
% 0.99/1.01  res_num_in_passive:                     0
% 0.99/1.01  res_num_in_active:                      0
% 0.99/1.01  res_num_of_loops:                       61
% 0.99/1.01  res_forward_subset_subsumed:            11
% 0.99/1.01  res_backward_subset_subsumed:           0
% 0.99/1.01  res_forward_subsumed:                   1
% 0.99/1.01  res_backward_subsumed:                  0
% 0.99/1.01  res_forward_subsumption_resolution:     0
% 0.99/1.01  res_backward_subsumption_resolution:    0
% 0.99/1.01  res_clause_to_clause_subsumption:       29
% 0.99/1.01  res_orphan_elimination:                 0
% 0.99/1.01  res_tautology_del:                      7
% 0.99/1.01  res_num_eq_res_simplified:              0
% 0.99/1.01  res_num_sel_changes:                    0
% 0.99/1.01  res_moves_from_active_to_pass:          0
% 0.99/1.01  
% 0.99/1.01  ------ Superposition
% 0.99/1.01  
% 0.99/1.01  sup_time_total:                         0.
% 0.99/1.01  sup_time_generating:                    0.
% 0.99/1.01  sup_time_sim_full:                      0.
% 0.99/1.01  sup_time_sim_immed:                     0.
% 0.99/1.01  
% 0.99/1.01  sup_num_of_clauses:                     19
% 0.99/1.01  sup_num_in_active:                      13
% 0.99/1.01  sup_num_in_passive:                     6
% 0.99/1.01  sup_num_of_loops:                       19
% 0.99/1.01  sup_fw_superposition:                   10
% 0.99/1.01  sup_bw_superposition:                   2
% 0.99/1.01  sup_immediate_simplified:               4
% 0.99/1.01  sup_given_eliminated:                   0
% 0.99/1.01  comparisons_done:                       0
% 0.99/1.01  comparisons_avoided:                    0
% 0.99/1.01  
% 0.99/1.01  ------ Simplifications
% 0.99/1.01  
% 0.99/1.01  
% 0.99/1.01  sim_fw_subset_subsumed:                 1
% 0.99/1.01  sim_bw_subset_subsumed:                 0
% 0.99/1.01  sim_fw_subsumed:                        1
% 0.99/1.01  sim_bw_subsumed:                        0
% 0.99/1.01  sim_fw_subsumption_res:                 0
% 0.99/1.01  sim_bw_subsumption_res:                 0
% 0.99/1.01  sim_tautology_del:                      0
% 0.99/1.01  sim_eq_tautology_del:                   2
% 0.99/1.01  sim_eq_res_simp:                        0
% 0.99/1.01  sim_fw_demodulated:                     3
% 0.99/1.01  sim_bw_demodulated:                     6
% 0.99/1.01  sim_light_normalised:                   0
% 0.99/1.01  sim_joinable_taut:                      0
% 0.99/1.01  sim_joinable_simp:                      0
% 0.99/1.01  sim_ac_normalised:                      0
% 0.99/1.01  sim_smt_subsumption:                    0
% 0.99/1.01  
%------------------------------------------------------------------------------
