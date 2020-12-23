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

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 174 expanded)
%              Number of clauses        :   41 (  72 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   17
%              Number of atoms          :  147 ( 399 expanded)
%              Number of equality atoms :   99 ( 257 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f10,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_199,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_198,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_409,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_199,c_198])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_68,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_69,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_68])).

cnf(c_197,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_220,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_197,c_3])).

cnf(c_550,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(o_0_0_xboole_0)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_409,c_220])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_16,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_17,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_21,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_130,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_135,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_233,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_128,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_258,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_262,plain,
    ( X0 != o_0_0_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_264,plain,
    ( k1_xboole_0 != o_0_0_xboole_0
    | v1_xboole_0(k1_xboole_0) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_298,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_810,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_16,c_17,c_0,c_21,c_135,c_233,c_264,c_298])).

cnf(c_545,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_409,c_198])).

cnf(c_947,plain,
    ( sK2 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_810,c_545])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_83,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_84,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
    inference(unflattening,[status(thm)],[c_83])).

cnf(c_227,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_84,c_3])).

cnf(c_382,plain,
    ( k8_relset_1(k1_xboole_0,X0,sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(superposition,[status(thm)],[c_3,c_227])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_485,plain,
    ( k10_relat_1(sK2,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_382,c_8])).

cnf(c_541,plain,
    ( k10_relat_1(sK2,sK1) != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_409,c_485])).

cnf(c_1017,plain,
    ( k10_relat_1(o_0_0_xboole_0,sK1) != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_947,c_541])).

cnf(c_6,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_544,plain,
    ( k10_relat_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_409,c_6])).

cnf(c_1019,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1017,c_544])).

cnf(c_1020,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1019])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:17:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 0.98/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.98/1.01  
% 0.98/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.98/1.01  
% 0.98/1.01  ------  iProver source info
% 0.98/1.01  
% 0.98/1.01  git: date: 2020-06-30 10:37:57 +0100
% 0.98/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.98/1.01  git: non_committed_changes: false
% 0.98/1.01  git: last_make_outside_of_git: false
% 0.98/1.01  
% 0.98/1.01  ------ 
% 0.98/1.01  
% 0.98/1.01  ------ Input Options
% 0.98/1.01  
% 0.98/1.01  --out_options                           all
% 0.98/1.01  --tptp_safe_out                         true
% 0.98/1.01  --problem_path                          ""
% 0.98/1.01  --include_path                          ""
% 0.98/1.01  --clausifier                            res/vclausify_rel
% 0.98/1.01  --clausifier_options                    --mode clausify
% 0.98/1.01  --stdin                                 false
% 0.98/1.01  --stats_out                             all
% 0.98/1.01  
% 0.98/1.01  ------ General Options
% 0.98/1.01  
% 0.98/1.01  --fof                                   false
% 0.98/1.01  --time_out_real                         305.
% 0.98/1.01  --time_out_virtual                      -1.
% 0.98/1.01  --symbol_type_check                     false
% 0.98/1.01  --clausify_out                          false
% 0.98/1.01  --sig_cnt_out                           false
% 0.98/1.01  --trig_cnt_out                          false
% 0.98/1.01  --trig_cnt_out_tolerance                1.
% 0.98/1.01  --trig_cnt_out_sk_spl                   false
% 0.98/1.01  --abstr_cl_out                          false
% 0.98/1.01  
% 0.98/1.01  ------ Global Options
% 0.98/1.01  
% 0.98/1.01  --schedule                              default
% 0.98/1.01  --add_important_lit                     false
% 0.98/1.01  --prop_solver_per_cl                    1000
% 0.98/1.01  --min_unsat_core                        false
% 0.98/1.01  --soft_assumptions                      false
% 0.98/1.01  --soft_lemma_size                       3
% 0.98/1.01  --prop_impl_unit_size                   0
% 0.98/1.01  --prop_impl_unit                        []
% 0.98/1.01  --share_sel_clauses                     true
% 0.98/1.01  --reset_solvers                         false
% 0.98/1.01  --bc_imp_inh                            [conj_cone]
% 0.98/1.01  --conj_cone_tolerance                   3.
% 0.98/1.01  --extra_neg_conj                        none
% 0.98/1.01  --large_theory_mode                     true
% 0.98/1.01  --prolific_symb_bound                   200
% 0.98/1.01  --lt_threshold                          2000
% 0.98/1.01  --clause_weak_htbl                      true
% 0.98/1.01  --gc_record_bc_elim                     false
% 0.98/1.01  
% 0.98/1.01  ------ Preprocessing Options
% 0.98/1.01  
% 0.98/1.01  --preprocessing_flag                    true
% 0.98/1.01  --time_out_prep_mult                    0.1
% 0.98/1.01  --splitting_mode                        input
% 0.98/1.01  --splitting_grd                         true
% 0.98/1.01  --splitting_cvd                         false
% 0.98/1.01  --splitting_cvd_svl                     false
% 0.98/1.01  --splitting_nvd                         32
% 0.98/1.01  --sub_typing                            true
% 0.98/1.01  --prep_gs_sim                           true
% 0.98/1.01  --prep_unflatten                        true
% 0.98/1.01  --prep_res_sim                          true
% 0.98/1.01  --prep_upred                            true
% 0.98/1.01  --prep_sem_filter                       exhaustive
% 0.98/1.01  --prep_sem_filter_out                   false
% 0.98/1.01  --pred_elim                             true
% 0.98/1.01  --res_sim_input                         true
% 0.98/1.01  --eq_ax_congr_red                       true
% 0.98/1.01  --pure_diseq_elim                       true
% 0.98/1.01  --brand_transform                       false
% 0.98/1.01  --non_eq_to_eq                          false
% 0.98/1.01  --prep_def_merge                        true
% 0.98/1.01  --prep_def_merge_prop_impl              false
% 0.98/1.01  --prep_def_merge_mbd                    true
% 0.98/1.01  --prep_def_merge_tr_red                 false
% 0.98/1.01  --prep_def_merge_tr_cl                  false
% 0.98/1.01  --smt_preprocessing                     true
% 0.98/1.01  --smt_ac_axioms                         fast
% 0.98/1.01  --preprocessed_out                      false
% 0.98/1.01  --preprocessed_stats                    false
% 0.98/1.01  
% 0.98/1.01  ------ Abstraction refinement Options
% 0.98/1.01  
% 0.98/1.01  --abstr_ref                             []
% 0.98/1.01  --abstr_ref_prep                        false
% 0.98/1.01  --abstr_ref_until_sat                   false
% 0.98/1.01  --abstr_ref_sig_restrict                funpre
% 0.98/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.98/1.01  --abstr_ref_under                       []
% 0.98/1.01  
% 0.98/1.01  ------ SAT Options
% 0.98/1.01  
% 0.98/1.01  --sat_mode                              false
% 0.98/1.01  --sat_fm_restart_options                ""
% 0.98/1.01  --sat_gr_def                            false
% 0.98/1.01  --sat_epr_types                         true
% 0.98/1.01  --sat_non_cyclic_types                  false
% 0.98/1.01  --sat_finite_models                     false
% 0.98/1.01  --sat_fm_lemmas                         false
% 0.98/1.01  --sat_fm_prep                           false
% 0.98/1.01  --sat_fm_uc_incr                        true
% 0.98/1.01  --sat_out_model                         small
% 0.98/1.01  --sat_out_clauses                       false
% 0.98/1.01  
% 0.98/1.01  ------ QBF Options
% 0.98/1.01  
% 0.98/1.01  --qbf_mode                              false
% 0.98/1.01  --qbf_elim_univ                         false
% 0.98/1.01  --qbf_dom_inst                          none
% 0.98/1.01  --qbf_dom_pre_inst                      false
% 0.98/1.01  --qbf_sk_in                             false
% 0.98/1.01  --qbf_pred_elim                         true
% 0.98/1.01  --qbf_split                             512
% 0.98/1.01  
% 0.98/1.01  ------ BMC1 Options
% 0.98/1.01  
% 0.98/1.01  --bmc1_incremental                      false
% 0.98/1.01  --bmc1_axioms                           reachable_all
% 0.98/1.01  --bmc1_min_bound                        0
% 0.98/1.01  --bmc1_max_bound                        -1
% 0.98/1.01  --bmc1_max_bound_default                -1
% 0.98/1.01  --bmc1_symbol_reachability              true
% 0.98/1.01  --bmc1_property_lemmas                  false
% 0.98/1.01  --bmc1_k_induction                      false
% 0.98/1.01  --bmc1_non_equiv_states                 false
% 0.98/1.01  --bmc1_deadlock                         false
% 0.98/1.01  --bmc1_ucm                              false
% 0.98/1.01  --bmc1_add_unsat_core                   none
% 0.98/1.01  --bmc1_unsat_core_children              false
% 0.98/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.98/1.01  --bmc1_out_stat                         full
% 0.98/1.01  --bmc1_ground_init                      false
% 0.98/1.01  --bmc1_pre_inst_next_state              false
% 0.98/1.01  --bmc1_pre_inst_state                   false
% 0.98/1.01  --bmc1_pre_inst_reach_state             false
% 0.98/1.01  --bmc1_out_unsat_core                   false
% 0.98/1.01  --bmc1_aig_witness_out                  false
% 0.98/1.01  --bmc1_verbose                          false
% 0.98/1.01  --bmc1_dump_clauses_tptp                false
% 0.98/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.98/1.01  --bmc1_dump_file                        -
% 0.98/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.98/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.98/1.01  --bmc1_ucm_extend_mode                  1
% 0.98/1.01  --bmc1_ucm_init_mode                    2
% 0.98/1.01  --bmc1_ucm_cone_mode                    none
% 0.98/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.98/1.01  --bmc1_ucm_relax_model                  4
% 0.98/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.98/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.98/1.01  --bmc1_ucm_layered_model                none
% 0.98/1.01  --bmc1_ucm_max_lemma_size               10
% 0.98/1.01  
% 0.98/1.01  ------ AIG Options
% 0.98/1.01  
% 0.98/1.01  --aig_mode                              false
% 0.98/1.01  
% 0.98/1.01  ------ Instantiation Options
% 0.98/1.01  
% 0.98/1.01  --instantiation_flag                    true
% 0.98/1.01  --inst_sos_flag                         false
% 0.98/1.01  --inst_sos_phase                        true
% 0.98/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.98/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.98/1.01  --inst_lit_sel_side                     num_symb
% 0.98/1.01  --inst_solver_per_active                1400
% 0.98/1.01  --inst_solver_calls_frac                1.
% 0.98/1.01  --inst_passive_queue_type               priority_queues
% 0.98/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.98/1.01  --inst_passive_queues_freq              [25;2]
% 0.98/1.01  --inst_dismatching                      true
% 0.98/1.01  --inst_eager_unprocessed_to_passive     true
% 0.98/1.01  --inst_prop_sim_given                   true
% 0.98/1.01  --inst_prop_sim_new                     false
% 0.98/1.01  --inst_subs_new                         false
% 0.98/1.01  --inst_eq_res_simp                      false
% 0.98/1.01  --inst_subs_given                       false
% 0.98/1.01  --inst_orphan_elimination               true
% 0.98/1.01  --inst_learning_loop_flag               true
% 0.98/1.01  --inst_learning_start                   3000
% 0.98/1.01  --inst_learning_factor                  2
% 0.98/1.01  --inst_start_prop_sim_after_learn       3
% 0.98/1.01  --inst_sel_renew                        solver
% 0.98/1.01  --inst_lit_activity_flag                true
% 0.98/1.01  --inst_restr_to_given                   false
% 0.98/1.01  --inst_activity_threshold               500
% 0.98/1.01  --inst_out_proof                        true
% 0.98/1.01  
% 0.98/1.01  ------ Resolution Options
% 0.98/1.01  
% 0.98/1.01  --resolution_flag                       true
% 0.98/1.01  --res_lit_sel                           adaptive
% 0.98/1.01  --res_lit_sel_side                      none
% 0.98/1.01  --res_ordering                          kbo
% 0.98/1.01  --res_to_prop_solver                    active
% 0.98/1.01  --res_prop_simpl_new                    false
% 0.98/1.01  --res_prop_simpl_given                  true
% 0.98/1.01  --res_passive_queue_type                priority_queues
% 0.98/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.98/1.01  --res_passive_queues_freq               [15;5]
% 0.98/1.01  --res_forward_subs                      full
% 0.98/1.01  --res_backward_subs                     full
% 0.98/1.01  --res_forward_subs_resolution           true
% 0.98/1.01  --res_backward_subs_resolution          true
% 0.98/1.01  --res_orphan_elimination                true
% 0.98/1.01  --res_time_limit                        2.
% 0.98/1.01  --res_out_proof                         true
% 0.98/1.01  
% 0.98/1.01  ------ Superposition Options
% 0.98/1.01  
% 0.98/1.01  --superposition_flag                    true
% 0.98/1.01  --sup_passive_queue_type                priority_queues
% 0.98/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.98/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.98/1.01  --demod_completeness_check              fast
% 0.98/1.01  --demod_use_ground                      true
% 0.98/1.01  --sup_to_prop_solver                    passive
% 0.98/1.01  --sup_prop_simpl_new                    true
% 0.98/1.01  --sup_prop_simpl_given                  true
% 0.98/1.01  --sup_fun_splitting                     false
% 0.98/1.01  --sup_smt_interval                      50000
% 0.98/1.01  
% 0.98/1.01  ------ Superposition Simplification Setup
% 0.98/1.01  
% 0.98/1.01  --sup_indices_passive                   []
% 0.98/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.98/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.01  --sup_full_bw                           [BwDemod]
% 0.98/1.01  --sup_immed_triv                        [TrivRules]
% 0.98/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.98/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.01  --sup_immed_bw_main                     []
% 0.98/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.98/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/1.01  
% 0.98/1.01  ------ Combination Options
% 0.98/1.01  
% 0.98/1.01  --comb_res_mult                         3
% 0.98/1.01  --comb_sup_mult                         2
% 0.98/1.01  --comb_inst_mult                        10
% 0.98/1.01  
% 0.98/1.01  ------ Debug Options
% 0.98/1.01  
% 0.98/1.01  --dbg_backtrace                         false
% 0.98/1.01  --dbg_dump_prop_clauses                 false
% 0.98/1.01  --dbg_dump_prop_clauses_file            -
% 0.98/1.01  --dbg_out_stat                          false
% 0.98/1.01  ------ Parsing...
% 0.98/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.98/1.01  
% 0.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.98/1.01  
% 0.98/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.98/1.01  
% 0.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.98/1.01  ------ Proving...
% 0.98/1.01  ------ Problem Properties 
% 0.98/1.01  
% 0.98/1.01  
% 0.98/1.01  clauses                                 9
% 0.98/1.01  conjectures                             1
% 0.98/1.01  EPR                                     2
% 0.98/1.01  Horn                                    8
% 0.98/1.01  unary                                   5
% 0.98/1.01  binary                                  2
% 0.98/1.01  lits                                    15
% 0.98/1.01  lits eq                                 11
% 0.98/1.01  fd_pure                                 0
% 0.98/1.01  fd_pseudo                               0
% 0.98/1.01  fd_cond                                 2
% 0.98/1.01  fd_pseudo_cond                          0
% 0.98/1.01  AC symbols                              0
% 0.98/1.01  
% 0.98/1.01  ------ Schedule dynamic 5 is on 
% 0.98/1.01  
% 0.98/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.98/1.01  
% 0.98/1.01  
% 0.98/1.01  ------ 
% 0.98/1.01  Current options:
% 0.98/1.01  ------ 
% 0.98/1.01  
% 0.98/1.01  ------ Input Options
% 0.98/1.01  
% 0.98/1.01  --out_options                           all
% 0.98/1.01  --tptp_safe_out                         true
% 0.98/1.01  --problem_path                          ""
% 0.98/1.01  --include_path                          ""
% 0.98/1.01  --clausifier                            res/vclausify_rel
% 0.98/1.01  --clausifier_options                    --mode clausify
% 0.98/1.01  --stdin                                 false
% 0.98/1.01  --stats_out                             all
% 0.98/1.01  
% 0.98/1.01  ------ General Options
% 0.98/1.01  
% 0.98/1.01  --fof                                   false
% 0.98/1.01  --time_out_real                         305.
% 0.98/1.01  --time_out_virtual                      -1.
% 0.98/1.01  --symbol_type_check                     false
% 0.98/1.01  --clausify_out                          false
% 0.98/1.01  --sig_cnt_out                           false
% 0.98/1.01  --trig_cnt_out                          false
% 0.98/1.01  --trig_cnt_out_tolerance                1.
% 0.98/1.01  --trig_cnt_out_sk_spl                   false
% 0.98/1.01  --abstr_cl_out                          false
% 0.98/1.01  
% 0.98/1.01  ------ Global Options
% 0.98/1.01  
% 0.98/1.01  --schedule                              default
% 0.98/1.01  --add_important_lit                     false
% 0.98/1.01  --prop_solver_per_cl                    1000
% 0.98/1.01  --min_unsat_core                        false
% 0.98/1.01  --soft_assumptions                      false
% 0.98/1.01  --soft_lemma_size                       3
% 0.98/1.01  --prop_impl_unit_size                   0
% 0.98/1.01  --prop_impl_unit                        []
% 0.98/1.01  --share_sel_clauses                     true
% 0.98/1.01  --reset_solvers                         false
% 0.98/1.01  --bc_imp_inh                            [conj_cone]
% 0.98/1.01  --conj_cone_tolerance                   3.
% 0.98/1.01  --extra_neg_conj                        none
% 0.98/1.01  --large_theory_mode                     true
% 0.98/1.01  --prolific_symb_bound                   200
% 0.98/1.01  --lt_threshold                          2000
% 0.98/1.01  --clause_weak_htbl                      true
% 0.98/1.01  --gc_record_bc_elim                     false
% 0.98/1.01  
% 0.98/1.01  ------ Preprocessing Options
% 0.98/1.01  
% 0.98/1.01  --preprocessing_flag                    true
% 0.98/1.01  --time_out_prep_mult                    0.1
% 0.98/1.01  --splitting_mode                        input
% 0.98/1.01  --splitting_grd                         true
% 0.98/1.01  --splitting_cvd                         false
% 0.98/1.01  --splitting_cvd_svl                     false
% 0.98/1.01  --splitting_nvd                         32
% 0.98/1.01  --sub_typing                            true
% 0.98/1.01  --prep_gs_sim                           true
% 0.98/1.01  --prep_unflatten                        true
% 0.98/1.01  --prep_res_sim                          true
% 0.98/1.01  --prep_upred                            true
% 0.98/1.01  --prep_sem_filter                       exhaustive
% 0.98/1.01  --prep_sem_filter_out                   false
% 0.98/1.01  --pred_elim                             true
% 0.98/1.01  --res_sim_input                         true
% 0.98/1.01  --eq_ax_congr_red                       true
% 0.98/1.01  --pure_diseq_elim                       true
% 0.98/1.01  --brand_transform                       false
% 0.98/1.01  --non_eq_to_eq                          false
% 0.98/1.01  --prep_def_merge                        true
% 0.98/1.01  --prep_def_merge_prop_impl              false
% 0.98/1.01  --prep_def_merge_mbd                    true
% 0.98/1.01  --prep_def_merge_tr_red                 false
% 0.98/1.01  --prep_def_merge_tr_cl                  false
% 0.98/1.01  --smt_preprocessing                     true
% 0.98/1.01  --smt_ac_axioms                         fast
% 0.98/1.01  --preprocessed_out                      false
% 0.98/1.01  --preprocessed_stats                    false
% 0.98/1.01  
% 0.98/1.01  ------ Abstraction refinement Options
% 0.98/1.01  
% 0.98/1.01  --abstr_ref                             []
% 0.98/1.01  --abstr_ref_prep                        false
% 0.98/1.01  --abstr_ref_until_sat                   false
% 0.98/1.01  --abstr_ref_sig_restrict                funpre
% 0.98/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.98/1.01  --abstr_ref_under                       []
% 0.98/1.01  
% 0.98/1.01  ------ SAT Options
% 0.98/1.01  
% 0.98/1.01  --sat_mode                              false
% 0.98/1.01  --sat_fm_restart_options                ""
% 0.98/1.01  --sat_gr_def                            false
% 0.98/1.01  --sat_epr_types                         true
% 0.98/1.01  --sat_non_cyclic_types                  false
% 0.98/1.01  --sat_finite_models                     false
% 0.98/1.01  --sat_fm_lemmas                         false
% 0.98/1.01  --sat_fm_prep                           false
% 0.98/1.01  --sat_fm_uc_incr                        true
% 0.98/1.01  --sat_out_model                         small
% 0.98/1.01  --sat_out_clauses                       false
% 0.98/1.01  
% 0.98/1.01  ------ QBF Options
% 0.98/1.01  
% 0.98/1.01  --qbf_mode                              false
% 0.98/1.01  --qbf_elim_univ                         false
% 0.98/1.01  --qbf_dom_inst                          none
% 0.98/1.01  --qbf_dom_pre_inst                      false
% 0.98/1.01  --qbf_sk_in                             false
% 0.98/1.01  --qbf_pred_elim                         true
% 0.98/1.01  --qbf_split                             512
% 0.98/1.01  
% 0.98/1.01  ------ BMC1 Options
% 0.98/1.01  
% 0.98/1.01  --bmc1_incremental                      false
% 0.98/1.01  --bmc1_axioms                           reachable_all
% 0.98/1.01  --bmc1_min_bound                        0
% 0.98/1.01  --bmc1_max_bound                        -1
% 0.98/1.01  --bmc1_max_bound_default                -1
% 0.98/1.01  --bmc1_symbol_reachability              true
% 0.98/1.01  --bmc1_property_lemmas                  false
% 0.98/1.01  --bmc1_k_induction                      false
% 0.98/1.01  --bmc1_non_equiv_states                 false
% 0.98/1.01  --bmc1_deadlock                         false
% 0.98/1.01  --bmc1_ucm                              false
% 0.98/1.01  --bmc1_add_unsat_core                   none
% 0.98/1.01  --bmc1_unsat_core_children              false
% 0.98/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.98/1.01  --bmc1_out_stat                         full
% 0.98/1.01  --bmc1_ground_init                      false
% 0.98/1.01  --bmc1_pre_inst_next_state              false
% 0.98/1.01  --bmc1_pre_inst_state                   false
% 0.98/1.01  --bmc1_pre_inst_reach_state             false
% 0.98/1.01  --bmc1_out_unsat_core                   false
% 0.98/1.01  --bmc1_aig_witness_out                  false
% 0.98/1.01  --bmc1_verbose                          false
% 0.98/1.01  --bmc1_dump_clauses_tptp                false
% 0.98/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.98/1.01  --bmc1_dump_file                        -
% 0.98/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.98/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.98/1.01  --bmc1_ucm_extend_mode                  1
% 0.98/1.01  --bmc1_ucm_init_mode                    2
% 0.98/1.01  --bmc1_ucm_cone_mode                    none
% 0.98/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.98/1.01  --bmc1_ucm_relax_model                  4
% 0.98/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.98/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.98/1.01  --bmc1_ucm_layered_model                none
% 0.98/1.01  --bmc1_ucm_max_lemma_size               10
% 0.98/1.01  
% 0.98/1.01  ------ AIG Options
% 0.98/1.01  
% 0.98/1.01  --aig_mode                              false
% 0.98/1.01  
% 0.98/1.01  ------ Instantiation Options
% 0.98/1.01  
% 0.98/1.01  --instantiation_flag                    true
% 0.98/1.01  --inst_sos_flag                         false
% 0.98/1.01  --inst_sos_phase                        true
% 0.98/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.98/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.98/1.01  --inst_lit_sel_side                     none
% 0.98/1.01  --inst_solver_per_active                1400
% 0.98/1.01  --inst_solver_calls_frac                1.
% 0.98/1.01  --inst_passive_queue_type               priority_queues
% 0.98/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.98/1.01  --inst_passive_queues_freq              [25;2]
% 0.98/1.01  --inst_dismatching                      true
% 0.98/1.01  --inst_eager_unprocessed_to_passive     true
% 0.98/1.01  --inst_prop_sim_given                   true
% 0.98/1.01  --inst_prop_sim_new                     false
% 0.98/1.01  --inst_subs_new                         false
% 0.98/1.01  --inst_eq_res_simp                      false
% 0.98/1.01  --inst_subs_given                       false
% 0.98/1.01  --inst_orphan_elimination               true
% 0.98/1.01  --inst_learning_loop_flag               true
% 0.98/1.01  --inst_learning_start                   3000
% 0.98/1.01  --inst_learning_factor                  2
% 0.98/1.01  --inst_start_prop_sim_after_learn       3
% 0.98/1.01  --inst_sel_renew                        solver
% 0.98/1.01  --inst_lit_activity_flag                true
% 0.98/1.01  --inst_restr_to_given                   false
% 0.98/1.01  --inst_activity_threshold               500
% 0.98/1.01  --inst_out_proof                        true
% 0.98/1.01  
% 0.98/1.01  ------ Resolution Options
% 0.98/1.01  
% 0.98/1.01  --resolution_flag                       false
% 0.98/1.01  --res_lit_sel                           adaptive
% 0.98/1.01  --res_lit_sel_side                      none
% 0.98/1.01  --res_ordering                          kbo
% 0.98/1.01  --res_to_prop_solver                    active
% 0.98/1.01  --res_prop_simpl_new                    false
% 0.98/1.01  --res_prop_simpl_given                  true
% 0.98/1.01  --res_passive_queue_type                priority_queues
% 0.98/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.98/1.01  --res_passive_queues_freq               [15;5]
% 0.98/1.01  --res_forward_subs                      full
% 0.98/1.01  --res_backward_subs                     full
% 0.98/1.01  --res_forward_subs_resolution           true
% 0.98/1.01  --res_backward_subs_resolution          true
% 0.98/1.01  --res_orphan_elimination                true
% 0.98/1.01  --res_time_limit                        2.
% 0.98/1.01  --res_out_proof                         true
% 0.98/1.01  
% 0.98/1.01  ------ Superposition Options
% 0.98/1.01  
% 0.98/1.01  --superposition_flag                    true
% 0.98/1.01  --sup_passive_queue_type                priority_queues
% 0.98/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.98/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.98/1.01  --demod_completeness_check              fast
% 0.98/1.01  --demod_use_ground                      true
% 0.98/1.01  --sup_to_prop_solver                    passive
% 0.98/1.01  --sup_prop_simpl_new                    true
% 0.98/1.01  --sup_prop_simpl_given                  true
% 0.98/1.01  --sup_fun_splitting                     false
% 0.98/1.01  --sup_smt_interval                      50000
% 0.98/1.01  
% 0.98/1.01  ------ Superposition Simplification Setup
% 0.98/1.01  
% 0.98/1.01  --sup_indices_passive                   []
% 0.98/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.98/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.01  --sup_full_bw                           [BwDemod]
% 0.98/1.01  --sup_immed_triv                        [TrivRules]
% 0.98/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.98/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.01  --sup_immed_bw_main                     []
% 0.98/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.98/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/1.01  
% 0.98/1.01  ------ Combination Options
% 0.98/1.01  
% 0.98/1.01  --comb_res_mult                         3
% 0.98/1.01  --comb_sup_mult                         2
% 0.98/1.01  --comb_inst_mult                        10
% 0.98/1.01  
% 0.98/1.01  ------ Debug Options
% 0.98/1.01  
% 0.98/1.01  --dbg_backtrace                         false
% 0.98/1.01  --dbg_dump_prop_clauses                 false
% 0.98/1.01  --dbg_dump_prop_clauses_file            -
% 0.98/1.01  --dbg_out_stat                          false
% 0.98/1.01  
% 0.98/1.01  
% 0.98/1.01  
% 0.98/1.01  
% 0.98/1.01  ------ Proving...
% 0.98/1.01  
% 0.98/1.01  
% 0.98/1.01  % SZS status Theorem for theBenchmark.p
% 0.98/1.01  
% 0.98/1.01   Resolution empty clause
% 0.98/1.01  
% 0.98/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 0.98/1.01  
% 0.98/1.01  fof(f1,axiom,(
% 0.98/1.01    v1_xboole_0(o_0_0_xboole_0)),
% 0.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.01  
% 0.98/1.01  fof(f19,plain,(
% 0.98/1.01    v1_xboole_0(o_0_0_xboole_0)),
% 0.98/1.01    inference(cnf_transformation,[],[f1])).
% 0.98/1.01  
% 0.98/1.01  fof(f2,axiom,(
% 0.98/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.01  
% 0.98/1.01  fof(f11,plain,(
% 0.98/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.98/1.01    inference(ennf_transformation,[],[f2])).
% 0.98/1.01  
% 0.98/1.01  fof(f20,plain,(
% 0.98/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.98/1.01    inference(cnf_transformation,[],[f11])).
% 0.98/1.01  
% 0.98/1.01  fof(f4,axiom,(
% 0.98/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.01  
% 0.98/1.01  fof(f12,plain,(
% 0.98/1.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.98/1.01    inference(ennf_transformation,[],[f4])).
% 0.98/1.01  
% 0.98/1.01  fof(f24,plain,(
% 0.98/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.98/1.01    inference(cnf_transformation,[],[f12])).
% 0.98/1.01  
% 0.98/1.01  fof(f7,conjecture,(
% 0.98/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.01  
% 0.98/1.01  fof(f8,negated_conjecture,(
% 0.98/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.98/1.01    inference(negated_conjecture,[],[f7])).
% 0.98/1.01  
% 0.98/1.01  fof(f9,plain,(
% 0.98/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.98/1.01    inference(pure_predicate_removal,[],[f8])).
% 0.98/1.01  
% 0.98/1.01  fof(f10,plain,(
% 0.98/1.01    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.98/1.01    inference(pure_predicate_removal,[],[f9])).
% 0.98/1.01  
% 0.98/1.01  fof(f14,plain,(
% 0.98/1.01    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.98/1.01    inference(ennf_transformation,[],[f10])).
% 0.98/1.01  
% 0.98/1.01  fof(f17,plain,(
% 0.98/1.01    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.98/1.01    introduced(choice_axiom,[])).
% 0.98/1.01  
% 0.98/1.01  fof(f18,plain,(
% 0.98/1.01    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).
% 0.98/1.01  
% 0.98/1.01  fof(f27,plain,(
% 0.98/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.98/1.01    inference(cnf_transformation,[],[f18])).
% 0.98/1.01  
% 0.98/1.01  fof(f3,axiom,(
% 0.98/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.01  
% 0.98/1.01  fof(f15,plain,(
% 0.98/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.98/1.01    inference(nnf_transformation,[],[f3])).
% 0.98/1.01  
% 0.98/1.01  fof(f16,plain,(
% 0.98/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.98/1.01    inference(flattening,[],[f15])).
% 0.98/1.01  
% 0.98/1.01  fof(f22,plain,(
% 0.98/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.98/1.01    inference(cnf_transformation,[],[f16])).
% 0.98/1.01  
% 0.98/1.01  fof(f30,plain,(
% 0.98/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.98/1.01    inference(equality_resolution,[],[f22])).
% 0.98/1.01  
% 0.98/1.01  fof(f21,plain,(
% 0.98/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.98/1.01    inference(cnf_transformation,[],[f16])).
% 0.98/1.01  
% 0.98/1.01  fof(f6,axiom,(
% 0.98/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 0.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.01  
% 0.98/1.01  fof(f13,plain,(
% 0.98/1.01    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.98/1.01    inference(ennf_transformation,[],[f6])).
% 0.98/1.01  
% 0.98/1.01  fof(f26,plain,(
% 0.98/1.01    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.98/1.01    inference(cnf_transformation,[],[f13])).
% 0.98/1.01  
% 0.98/1.01  fof(f28,plain,(
% 0.98/1.01    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.98/1.01    inference(cnf_transformation,[],[f18])).
% 0.98/1.01  
% 0.98/1.01  fof(f5,axiom,(
% 0.98/1.01    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.01  
% 0.98/1.01  fof(f25,plain,(
% 0.98/1.01    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 0.98/1.01    inference(cnf_transformation,[],[f5])).
% 0.98/1.01  
% 0.98/1.01  cnf(c_0,plain,
% 0.98/1.01      ( v1_xboole_0(o_0_0_xboole_0) ),
% 0.98/1.01      inference(cnf_transformation,[],[f19]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_199,plain,
% 0.98/1.01      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 0.98/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_1,plain,
% 0.98/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 0.98/1.01      inference(cnf_transformation,[],[f20]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_198,plain,
% 0.98/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 0.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_409,plain,
% 0.98/1.01      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 0.98/1.01      inference(superposition,[status(thm)],[c_199,c_198]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_5,plain,
% 0.98/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.98/1.01      | ~ v1_xboole_0(X1)
% 0.98/1.01      | v1_xboole_0(X0) ),
% 0.98/1.01      inference(cnf_transformation,[],[f24]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_9,negated_conjecture,
% 0.98/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
% 0.98/1.01      inference(cnf_transformation,[],[f27]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_68,plain,
% 0.98/1.01      ( ~ v1_xboole_0(X0)
% 0.98/1.01      | v1_xboole_0(X1)
% 0.98/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0)
% 0.98/1.01      | sK2 != X1 ),
% 0.98/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_69,plain,
% 0.98/1.01      ( ~ v1_xboole_0(X0)
% 0.98/1.01      | v1_xboole_0(sK2)
% 0.98/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0) ),
% 0.98/1.01      inference(unflattening,[status(thm)],[c_68]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_197,plain,
% 0.98/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0)
% 0.98/1.01      | v1_xboole_0(X0) != iProver_top
% 0.98/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 0.98/1.01      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_3,plain,
% 0.98/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.98/1.01      inference(cnf_transformation,[],[f30]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_220,plain,
% 0.98/1.01      ( k1_zfmisc_1(X0) != k1_zfmisc_1(k1_xboole_0)
% 0.98/1.01      | v1_xboole_0(X0) != iProver_top
% 0.98/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 0.98/1.01      inference(demodulation,[status(thm)],[c_197,c_3]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_550,plain,
% 0.98/1.01      ( k1_zfmisc_1(X0) != k1_zfmisc_1(o_0_0_xboole_0)
% 0.98/1.01      | v1_xboole_0(X0) != iProver_top
% 0.98/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 0.98/1.01      inference(demodulation,[status(thm)],[c_409,c_220]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_4,plain,
% 0.98/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 0.98/1.01      | k1_xboole_0 = X0
% 0.98/1.01      | k1_xboole_0 = X1 ),
% 0.98/1.01      inference(cnf_transformation,[],[f21]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_16,plain,
% 0.98/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 0.98/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 0.98/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_17,plain,
% 0.98/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 0.98/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_21,plain,
% 0.98/1.01      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 0.98/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_130,plain,
% 0.98/1.01      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 0.98/1.01      theory(equality) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_135,plain,
% 0.98/1.01      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 0.98/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 0.98/1.01      inference(instantiation,[status(thm)],[c_130]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_233,plain,
% 0.98/1.01      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 0.98/1.01      | v1_xboole_0(sK2) = iProver_top
% 0.98/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 0.98/1.01      inference(instantiation,[status(thm)],[c_220]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_128,plain,
% 0.98/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 0.98/1.01      theory(equality) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_258,plain,
% 0.98/1.01      ( v1_xboole_0(X0)
% 0.98/1.01      | ~ v1_xboole_0(o_0_0_xboole_0)
% 0.98/1.01      | X0 != o_0_0_xboole_0 ),
% 0.98/1.01      inference(instantiation,[status(thm)],[c_128]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_262,plain,
% 0.98/1.01      ( X0 != o_0_0_xboole_0
% 0.98/1.01      | v1_xboole_0(X0) = iProver_top
% 0.98/1.01      | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
% 0.98/1.01      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_264,plain,
% 0.98/1.01      ( k1_xboole_0 != o_0_0_xboole_0
% 0.98/1.01      | v1_xboole_0(k1_xboole_0) = iProver_top
% 0.98/1.01      | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
% 0.98/1.01      inference(instantiation,[status(thm)],[c_262]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_298,plain,
% 0.98/1.01      ( ~ v1_xboole_0(o_0_0_xboole_0) | k1_xboole_0 = o_0_0_xboole_0 ),
% 0.98/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_810,plain,
% 0.98/1.01      ( v1_xboole_0(sK2) = iProver_top ),
% 0.98/1.01      inference(global_propositional_subsumption,
% 0.98/1.01                [status(thm)],
% 0.98/1.01                [c_550,c_16,c_17,c_0,c_21,c_135,c_233,c_264,c_298]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_545,plain,
% 0.98/1.01      ( o_0_0_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 0.98/1.01      inference(demodulation,[status(thm)],[c_409,c_198]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_947,plain,
% 0.98/1.01      ( sK2 = o_0_0_xboole_0 ),
% 0.98/1.01      inference(superposition,[status(thm)],[c_810,c_545]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_7,plain,
% 0.98/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.98/1.01      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 0.98/1.01      inference(cnf_transformation,[],[f26]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_83,plain,
% 0.98/1.01      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 0.98/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
% 0.98/1.01      | sK2 != X2 ),
% 0.98/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_9]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_84,plain,
% 0.98/1.01      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 0.98/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
% 0.98/1.01      inference(unflattening,[status(thm)],[c_83]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_227,plain,
% 0.98/1.01      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 0.98/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k1_xboole_0) ),
% 0.98/1.01      inference(demodulation,[status(thm)],[c_84,c_3]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_382,plain,
% 0.98/1.01      ( k8_relset_1(k1_xboole_0,X0,sK2,X1) = k10_relat_1(sK2,X1) ),
% 0.98/1.01      inference(superposition,[status(thm)],[c_3,c_227]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_8,negated_conjecture,
% 0.98/1.01      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
% 0.98/1.01      inference(cnf_transformation,[],[f28]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_485,plain,
% 0.98/1.01      ( k10_relat_1(sK2,sK1) != k1_xboole_0 ),
% 0.98/1.01      inference(demodulation,[status(thm)],[c_382,c_8]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_541,plain,
% 0.98/1.01      ( k10_relat_1(sK2,sK1) != o_0_0_xboole_0 ),
% 0.98/1.01      inference(demodulation,[status(thm)],[c_409,c_485]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_1017,plain,
% 0.98/1.01      ( k10_relat_1(o_0_0_xboole_0,sK1) != o_0_0_xboole_0 ),
% 0.98/1.01      inference(demodulation,[status(thm)],[c_947,c_541]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_6,plain,
% 0.98/1.01      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.98/1.01      inference(cnf_transformation,[],[f25]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_544,plain,
% 0.98/1.01      ( k10_relat_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
% 0.98/1.01      inference(demodulation,[status(thm)],[c_409,c_6]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_1019,plain,
% 0.98/1.01      ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 0.98/1.01      inference(demodulation,[status(thm)],[c_1017,c_544]) ).
% 0.98/1.01  
% 0.98/1.01  cnf(c_1020,plain,
% 0.98/1.01      ( $false ),
% 0.98/1.01      inference(equality_resolution_simp,[status(thm)],[c_1019]) ).
% 0.98/1.01  
% 0.98/1.01  
% 0.98/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 0.98/1.01  
% 0.98/1.01  ------                               Statistics
% 0.98/1.01  
% 0.98/1.01  ------ General
% 0.98/1.01  
% 0.98/1.01  abstr_ref_over_cycles:                  0
% 0.98/1.01  abstr_ref_under_cycles:                 0
% 0.98/1.01  gc_basic_clause_elim:                   0
% 0.98/1.01  forced_gc_time:                         0
% 0.98/1.01  parsing_time:                           0.012
% 0.98/1.01  unif_index_cands_time:                  0.
% 0.98/1.01  unif_index_add_time:                    0.
% 0.98/1.01  orderings_time:                         0.
% 0.98/1.01  out_proof_time:                         0.008
% 0.98/1.01  total_time:                             0.072
% 0.98/1.01  num_of_symbols:                         42
% 0.98/1.01  num_of_terms:                           1173
% 0.98/1.01  
% 0.98/1.01  ------ Preprocessing
% 0.98/1.01  
% 0.98/1.01  num_of_splits:                          0
% 0.98/1.01  num_of_split_atoms:                     0
% 0.98/1.01  num_of_reused_defs:                     0
% 0.98/1.01  num_eq_ax_congr_red:                    3
% 0.98/1.01  num_of_sem_filtered_clauses:            1
% 0.98/1.01  num_of_subtypes:                        0
% 0.98/1.01  monotx_restored_types:                  0
% 0.98/1.01  sat_num_of_epr_types:                   0
% 0.98/1.01  sat_num_of_non_cyclic_types:            0
% 0.98/1.01  sat_guarded_non_collapsed_types:        0
% 0.98/1.01  num_pure_diseq_elim:                    0
% 0.98/1.01  simp_replaced_by:                       0
% 0.98/1.01  res_preprocessed:                       52
% 0.98/1.01  prep_upred:                             0
% 0.98/1.01  prep_unflattend:                        2
% 0.98/1.01  smt_new_axioms:                         0
% 0.98/1.01  pred_elim_cands:                        1
% 0.98/1.01  pred_elim:                              1
% 0.98/1.01  pred_elim_cl:                           1
% 0.98/1.01  pred_elim_cycles:                       3
% 0.98/1.01  merged_defs:                            0
% 0.98/1.01  merged_defs_ncl:                        0
% 0.98/1.01  bin_hyper_res:                          0
% 0.98/1.01  prep_cycles:                            4
% 0.98/1.01  pred_elim_time:                         0.001
% 0.98/1.01  splitting_time:                         0.
% 0.98/1.01  sem_filter_time:                        0.
% 0.98/1.01  monotx_time:                            0.
% 0.98/1.01  subtype_inf_time:                       0.
% 0.98/1.01  
% 0.98/1.01  ------ Problem properties
% 0.98/1.01  
% 0.98/1.01  clauses:                                9
% 0.98/1.01  conjectures:                            1
% 0.98/1.01  epr:                                    2
% 0.98/1.01  horn:                                   8
% 0.98/1.01  ground:                                 2
% 0.98/1.01  unary:                                  5
% 0.98/1.01  binary:                                 2
% 0.98/1.01  lits:                                   15
% 0.98/1.01  lits_eq:                                11
% 0.98/1.01  fd_pure:                                0
% 0.98/1.01  fd_pseudo:                              0
% 0.98/1.01  fd_cond:                                2
% 0.98/1.01  fd_pseudo_cond:                         0
% 0.98/1.01  ac_symbols:                             0
% 0.98/1.01  
% 0.98/1.01  ------ Propositional Solver
% 0.98/1.01  
% 0.98/1.01  prop_solver_calls:                      26
% 0.98/1.01  prop_fast_solver_calls:                 244
% 0.98/1.01  smt_solver_calls:                       0
% 0.98/1.01  smt_fast_solver_calls:                  0
% 0.98/1.01  prop_num_of_clauses:                    453
% 0.98/1.01  prop_preprocess_simplified:             1697
% 0.98/1.01  prop_fo_subsumed:                       2
% 0.98/1.01  prop_solver_time:                       0.
% 0.98/1.01  smt_solver_time:                        0.
% 0.98/1.01  smt_fast_solver_time:                   0.
% 0.98/1.01  prop_fast_solver_time:                  0.
% 0.98/1.01  prop_unsat_core_time:                   0.
% 0.98/1.01  
% 0.98/1.01  ------ QBF
% 0.98/1.01  
% 0.98/1.01  qbf_q_res:                              0
% 0.98/1.01  qbf_num_tautologies:                    0
% 0.98/1.01  qbf_prep_cycles:                        0
% 0.98/1.01  
% 0.98/1.01  ------ BMC1
% 0.98/1.01  
% 0.98/1.01  bmc1_current_bound:                     -1
% 0.98/1.01  bmc1_last_solved_bound:                 -1
% 0.98/1.01  bmc1_unsat_core_size:                   -1
% 0.98/1.01  bmc1_unsat_core_parents_size:           -1
% 0.98/1.01  bmc1_merge_next_fun:                    0
% 0.98/1.01  bmc1_unsat_core_clauses_time:           0.
% 0.98/1.01  
% 0.98/1.01  ------ Instantiation
% 0.98/1.01  
% 0.98/1.01  inst_num_of_clauses:                    246
% 0.98/1.01  inst_num_in_passive:                    29
% 0.98/1.01  inst_num_in_active:                     121
% 0.98/1.01  inst_num_in_unprocessed:                97
% 0.98/1.01  inst_num_of_loops:                      130
% 0.98/1.01  inst_num_of_learning_restarts:          0
% 0.98/1.01  inst_num_moves_active_passive:          8
% 0.98/1.01  inst_lit_activity:                      0
% 0.98/1.01  inst_lit_activity_moves:                0
% 0.98/1.01  inst_num_tautologies:                   0
% 0.98/1.01  inst_num_prop_implied:                  0
% 0.98/1.01  inst_num_existing_simplified:           0
% 0.98/1.01  inst_num_eq_res_simplified:             0
% 0.98/1.01  inst_num_child_elim:                    0
% 0.98/1.01  inst_num_of_dismatching_blockings:      24
% 0.98/1.01  inst_num_of_non_proper_insts:           159
% 0.98/1.01  inst_num_of_duplicates:                 0
% 0.98/1.01  inst_inst_num_from_inst_to_res:         0
% 0.98/1.01  inst_dismatching_checking_time:         0.
% 0.98/1.01  
% 0.98/1.01  ------ Resolution
% 0.98/1.01  
% 0.98/1.01  res_num_of_clauses:                     0
% 0.98/1.01  res_num_in_passive:                     0
% 0.98/1.01  res_num_in_active:                      0
% 0.98/1.01  res_num_of_loops:                       56
% 0.98/1.01  res_forward_subset_subsumed:            20
% 0.98/1.01  res_backward_subset_subsumed:           2
% 0.98/1.01  res_forward_subsumed:                   0
% 0.98/1.01  res_backward_subsumed:                  0
% 0.98/1.01  res_forward_subsumption_resolution:     0
% 0.98/1.01  res_backward_subsumption_resolution:    0
% 0.98/1.01  res_clause_to_clause_subsumption:       33
% 0.98/1.01  res_orphan_elimination:                 0
% 0.98/1.01  res_tautology_del:                      24
% 0.98/1.01  res_num_eq_res_simplified:              0
% 0.98/1.01  res_num_sel_changes:                    0
% 0.98/1.01  res_moves_from_active_to_pass:          0
% 0.98/1.01  
% 0.98/1.01  ------ Superposition
% 0.98/1.01  
% 0.98/1.01  sup_time_total:                         0.
% 0.98/1.01  sup_time_generating:                    0.
% 0.98/1.01  sup_time_sim_full:                      0.
% 0.98/1.01  sup_time_sim_immed:                     0.
% 0.98/1.01  
% 0.98/1.01  sup_num_of_clauses:                     9
% 0.98/1.01  sup_num_in_active:                      7
% 0.98/1.01  sup_num_in_passive:                     2
% 0.98/1.01  sup_num_of_loops:                       24
% 0.98/1.02  sup_fw_superposition:                   5
% 0.98/1.02  sup_bw_superposition:                   6
% 0.98/1.02  sup_immediate_simplified:               0
% 0.98/1.02  sup_given_eliminated:                   0
% 0.98/1.02  comparisons_done:                       0
% 0.98/1.02  comparisons_avoided:                    0
% 0.98/1.02  
% 0.98/1.02  ------ Simplifications
% 0.98/1.02  
% 0.98/1.02  
% 0.98/1.02  sim_fw_subset_subsumed:                 0
% 0.98/1.02  sim_bw_subset_subsumed:                 1
% 0.98/1.02  sim_fw_subsumed:                        0
% 0.98/1.02  sim_bw_subsumed:                        0
% 0.98/1.02  sim_fw_subsumption_res:                 0
% 0.98/1.02  sim_bw_subsumption_res:                 0
% 0.98/1.02  sim_tautology_del:                      0
% 0.98/1.02  sim_eq_tautology_del:                   4
% 0.98/1.02  sim_eq_res_simp:                        0
% 0.98/1.02  sim_fw_demodulated:                     3
% 0.98/1.02  sim_bw_demodulated:                     17
% 0.98/1.02  sim_light_normalised:                   0
% 0.98/1.02  sim_joinable_taut:                      0
% 0.98/1.02  sim_joinable_simp:                      0
% 0.98/1.02  sim_ac_normalised:                      0
% 0.98/1.02  sim_smt_subsumption:                    0
% 0.98/1.02  
%------------------------------------------------------------------------------
