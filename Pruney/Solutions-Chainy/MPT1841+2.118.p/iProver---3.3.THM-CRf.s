%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:11 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 196 expanded)
%              Number of clauses        :   35 (  49 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  185 ( 592 expanded)
%              Number of equality atoms :   54 ( 105 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK1),X0)
        & m1_subset_1(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).

fof(f32,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f31,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(definition_unfolding,[],[f26,f35])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f33,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_454,plain,
    ( m1_subset_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_455,plain,
    ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_569,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1)
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_455])).

cnf(c_9,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_505,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_624,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_9,c_8,c_505])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_456,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_685,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_624,c_456])).

cnf(c_702,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK1,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_457,plain,
    ( v1_xboole_0(k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_627,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_624,c_457])).

cnf(c_315,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_535,plain,
    ( X0 != X1
    | X0 = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_536,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_314,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_325,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_149,plain,
    ( sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_7,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_53,plain,
    ( ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_3])).

cnf(c_54,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_53])).

cnf(c_6,negated_conjecture,
    ( v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_110,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_54,c_6])).

cnf(c_111,plain,
    ( ~ v1_subset_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_110])).

cnf(c_131,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
    | v1_xboole_0(X0)
    | k6_domain_1(sK0,sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_111])).

cnf(c_132,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_131])).

cnf(c_133,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_132])).

cnf(c_11,plain,
    ( m1_subset_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_702,c_627,c_536,c_325,c_149,c_133,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.71/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.71/1.05  
% 0.71/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.71/1.05  
% 0.71/1.05  ------  iProver source info
% 0.71/1.05  
% 0.71/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.71/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.71/1.05  git: non_committed_changes: false
% 0.71/1.05  git: last_make_outside_of_git: false
% 0.71/1.05  
% 0.71/1.05  ------ 
% 0.71/1.05  
% 0.71/1.05  ------ Input Options
% 0.71/1.05  
% 0.71/1.05  --out_options                           all
% 0.71/1.05  --tptp_safe_out                         true
% 0.71/1.05  --problem_path                          ""
% 0.71/1.05  --include_path                          ""
% 0.71/1.05  --clausifier                            res/vclausify_rel
% 0.71/1.05  --clausifier_options                    --mode clausify
% 0.71/1.05  --stdin                                 false
% 0.71/1.05  --stats_out                             all
% 0.71/1.05  
% 0.71/1.05  ------ General Options
% 0.71/1.05  
% 0.71/1.05  --fof                                   false
% 0.71/1.05  --time_out_real                         305.
% 0.71/1.05  --time_out_virtual                      -1.
% 0.71/1.05  --symbol_type_check                     false
% 0.71/1.05  --clausify_out                          false
% 0.71/1.05  --sig_cnt_out                           false
% 0.71/1.05  --trig_cnt_out                          false
% 0.71/1.05  --trig_cnt_out_tolerance                1.
% 0.71/1.05  --trig_cnt_out_sk_spl                   false
% 0.71/1.05  --abstr_cl_out                          false
% 0.71/1.05  
% 0.71/1.05  ------ Global Options
% 0.71/1.05  
% 0.71/1.05  --schedule                              default
% 0.71/1.05  --add_important_lit                     false
% 0.71/1.05  --prop_solver_per_cl                    1000
% 0.71/1.05  --min_unsat_core                        false
% 0.71/1.05  --soft_assumptions                      false
% 0.71/1.05  --soft_lemma_size                       3
% 0.71/1.05  --prop_impl_unit_size                   0
% 0.71/1.05  --prop_impl_unit                        []
% 0.71/1.05  --share_sel_clauses                     true
% 0.71/1.05  --reset_solvers                         false
% 0.71/1.05  --bc_imp_inh                            [conj_cone]
% 0.71/1.05  --conj_cone_tolerance                   3.
% 0.71/1.05  --extra_neg_conj                        none
% 0.71/1.05  --large_theory_mode                     true
% 0.71/1.05  --prolific_symb_bound                   200
% 0.71/1.05  --lt_threshold                          2000
% 0.71/1.05  --clause_weak_htbl                      true
% 0.71/1.05  --gc_record_bc_elim                     false
% 0.71/1.05  
% 0.71/1.05  ------ Preprocessing Options
% 0.71/1.05  
% 0.71/1.05  --preprocessing_flag                    true
% 0.71/1.05  --time_out_prep_mult                    0.1
% 0.71/1.05  --splitting_mode                        input
% 0.71/1.05  --splitting_grd                         true
% 0.71/1.05  --splitting_cvd                         false
% 0.71/1.05  --splitting_cvd_svl                     false
% 0.71/1.05  --splitting_nvd                         32
% 0.71/1.05  --sub_typing                            true
% 0.71/1.05  --prep_gs_sim                           true
% 0.71/1.05  --prep_unflatten                        true
% 0.71/1.05  --prep_res_sim                          true
% 0.71/1.05  --prep_upred                            true
% 0.71/1.05  --prep_sem_filter                       exhaustive
% 0.71/1.05  --prep_sem_filter_out                   false
% 0.71/1.05  --pred_elim                             true
% 0.71/1.05  --res_sim_input                         true
% 0.71/1.05  --eq_ax_congr_red                       true
% 0.71/1.05  --pure_diseq_elim                       true
% 0.71/1.05  --brand_transform                       false
% 0.71/1.05  --non_eq_to_eq                          false
% 0.71/1.05  --prep_def_merge                        true
% 0.71/1.05  --prep_def_merge_prop_impl              false
% 0.71/1.05  --prep_def_merge_mbd                    true
% 0.71/1.05  --prep_def_merge_tr_red                 false
% 0.71/1.05  --prep_def_merge_tr_cl                  false
% 0.71/1.05  --smt_preprocessing                     true
% 0.71/1.05  --smt_ac_axioms                         fast
% 0.71/1.05  --preprocessed_out                      false
% 0.71/1.05  --preprocessed_stats                    false
% 0.71/1.05  
% 0.71/1.05  ------ Abstraction refinement Options
% 0.71/1.05  
% 0.71/1.05  --abstr_ref                             []
% 0.71/1.05  --abstr_ref_prep                        false
% 0.71/1.05  --abstr_ref_until_sat                   false
% 0.71/1.05  --abstr_ref_sig_restrict                funpre
% 0.71/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.71/1.05  --abstr_ref_under                       []
% 0.71/1.05  
% 0.71/1.05  ------ SAT Options
% 0.71/1.05  
% 0.71/1.05  --sat_mode                              false
% 0.71/1.05  --sat_fm_restart_options                ""
% 0.71/1.05  --sat_gr_def                            false
% 0.71/1.05  --sat_epr_types                         true
% 0.71/1.05  --sat_non_cyclic_types                  false
% 0.71/1.05  --sat_finite_models                     false
% 0.71/1.05  --sat_fm_lemmas                         false
% 0.71/1.05  --sat_fm_prep                           false
% 0.71/1.05  --sat_fm_uc_incr                        true
% 0.71/1.05  --sat_out_model                         small
% 0.71/1.05  --sat_out_clauses                       false
% 0.71/1.05  
% 0.71/1.05  ------ QBF Options
% 0.71/1.05  
% 0.71/1.05  --qbf_mode                              false
% 0.71/1.05  --qbf_elim_univ                         false
% 0.71/1.05  --qbf_dom_inst                          none
% 0.71/1.05  --qbf_dom_pre_inst                      false
% 0.71/1.05  --qbf_sk_in                             false
% 0.71/1.05  --qbf_pred_elim                         true
% 0.71/1.05  --qbf_split                             512
% 0.71/1.05  
% 0.71/1.05  ------ BMC1 Options
% 0.71/1.05  
% 0.71/1.05  --bmc1_incremental                      false
% 0.71/1.05  --bmc1_axioms                           reachable_all
% 0.71/1.05  --bmc1_min_bound                        0
% 0.71/1.05  --bmc1_max_bound                        -1
% 0.71/1.05  --bmc1_max_bound_default                -1
% 0.71/1.05  --bmc1_symbol_reachability              true
% 0.71/1.05  --bmc1_property_lemmas                  false
% 0.71/1.05  --bmc1_k_induction                      false
% 0.71/1.05  --bmc1_non_equiv_states                 false
% 0.71/1.05  --bmc1_deadlock                         false
% 0.71/1.05  --bmc1_ucm                              false
% 0.71/1.05  --bmc1_add_unsat_core                   none
% 0.71/1.05  --bmc1_unsat_core_children              false
% 0.71/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.71/1.05  --bmc1_out_stat                         full
% 0.71/1.05  --bmc1_ground_init                      false
% 0.71/1.05  --bmc1_pre_inst_next_state              false
% 0.71/1.05  --bmc1_pre_inst_state                   false
% 0.71/1.05  --bmc1_pre_inst_reach_state             false
% 0.71/1.05  --bmc1_out_unsat_core                   false
% 0.71/1.05  --bmc1_aig_witness_out                  false
% 0.71/1.05  --bmc1_verbose                          false
% 0.71/1.05  --bmc1_dump_clauses_tptp                false
% 0.71/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.71/1.05  --bmc1_dump_file                        -
% 0.71/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.71/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.71/1.05  --bmc1_ucm_extend_mode                  1
% 0.71/1.05  --bmc1_ucm_init_mode                    2
% 0.71/1.05  --bmc1_ucm_cone_mode                    none
% 0.71/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.71/1.05  --bmc1_ucm_relax_model                  4
% 0.71/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.71/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.71/1.05  --bmc1_ucm_layered_model                none
% 0.71/1.05  --bmc1_ucm_max_lemma_size               10
% 0.71/1.05  
% 0.71/1.05  ------ AIG Options
% 0.71/1.05  
% 0.71/1.05  --aig_mode                              false
% 0.71/1.05  
% 0.71/1.05  ------ Instantiation Options
% 0.71/1.05  
% 0.71/1.05  --instantiation_flag                    true
% 0.71/1.05  --inst_sos_flag                         false
% 0.71/1.05  --inst_sos_phase                        true
% 0.71/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.71/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.71/1.05  --inst_lit_sel_side                     num_symb
% 0.71/1.05  --inst_solver_per_active                1400
% 0.71/1.05  --inst_solver_calls_frac                1.
% 0.71/1.05  --inst_passive_queue_type               priority_queues
% 0.71/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.71/1.05  --inst_passive_queues_freq              [25;2]
% 0.71/1.05  --inst_dismatching                      true
% 0.71/1.05  --inst_eager_unprocessed_to_passive     true
% 0.71/1.05  --inst_prop_sim_given                   true
% 0.71/1.05  --inst_prop_sim_new                     false
% 0.71/1.05  --inst_subs_new                         false
% 0.71/1.05  --inst_eq_res_simp                      false
% 0.71/1.05  --inst_subs_given                       false
% 0.71/1.05  --inst_orphan_elimination               true
% 0.71/1.05  --inst_learning_loop_flag               true
% 0.71/1.05  --inst_learning_start                   3000
% 0.71/1.05  --inst_learning_factor                  2
% 0.71/1.05  --inst_start_prop_sim_after_learn       3
% 0.71/1.05  --inst_sel_renew                        solver
% 0.71/1.05  --inst_lit_activity_flag                true
% 0.71/1.05  --inst_restr_to_given                   false
% 0.71/1.05  --inst_activity_threshold               500
% 0.71/1.05  --inst_out_proof                        true
% 0.71/1.05  
% 0.71/1.05  ------ Resolution Options
% 0.71/1.05  
% 0.71/1.05  --resolution_flag                       true
% 0.71/1.05  --res_lit_sel                           adaptive
% 0.71/1.05  --res_lit_sel_side                      none
% 0.71/1.05  --res_ordering                          kbo
% 0.71/1.05  --res_to_prop_solver                    active
% 0.71/1.05  --res_prop_simpl_new                    false
% 0.71/1.05  --res_prop_simpl_given                  true
% 0.71/1.05  --res_passive_queue_type                priority_queues
% 0.71/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.71/1.05  --res_passive_queues_freq               [15;5]
% 0.71/1.05  --res_forward_subs                      full
% 0.71/1.05  --res_backward_subs                     full
% 0.71/1.05  --res_forward_subs_resolution           true
% 0.71/1.05  --res_backward_subs_resolution          true
% 0.71/1.05  --res_orphan_elimination                true
% 0.71/1.05  --res_time_limit                        2.
% 0.71/1.05  --res_out_proof                         true
% 0.71/1.05  
% 0.71/1.05  ------ Superposition Options
% 0.71/1.05  
% 0.71/1.05  --superposition_flag                    true
% 0.71/1.05  --sup_passive_queue_type                priority_queues
% 0.71/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.71/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.71/1.05  --demod_completeness_check              fast
% 0.71/1.05  --demod_use_ground                      true
% 0.71/1.05  --sup_to_prop_solver                    passive
% 0.71/1.05  --sup_prop_simpl_new                    true
% 0.71/1.05  --sup_prop_simpl_given                  true
% 0.71/1.05  --sup_fun_splitting                     false
% 0.71/1.05  --sup_smt_interval                      50000
% 0.71/1.05  
% 0.71/1.05  ------ Superposition Simplification Setup
% 0.71/1.05  
% 0.71/1.05  --sup_indices_passive                   []
% 0.71/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.71/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.05  --sup_full_bw                           [BwDemod]
% 0.71/1.05  --sup_immed_triv                        [TrivRules]
% 0.71/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.71/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.05  --sup_immed_bw_main                     []
% 0.71/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.71/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.71/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.71/1.05  
% 0.71/1.05  ------ Combination Options
% 0.71/1.05  
% 0.71/1.05  --comb_res_mult                         3
% 0.71/1.05  --comb_sup_mult                         2
% 0.71/1.05  --comb_inst_mult                        10
% 0.71/1.05  
% 0.71/1.05  ------ Debug Options
% 0.71/1.05  
% 0.71/1.05  --dbg_backtrace                         false
% 0.71/1.05  --dbg_dump_prop_clauses                 false
% 0.71/1.05  --dbg_dump_prop_clauses_file            -
% 0.71/1.05  --dbg_out_stat                          false
% 0.71/1.05  ------ Parsing...
% 0.71/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.71/1.05  
% 0.71/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.71/1.05  
% 0.71/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.71/1.05  
% 0.71/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.71/1.05  ------ Proving...
% 0.71/1.05  ------ Problem Properties 
% 0.71/1.05  
% 0.71/1.05  
% 0.71/1.05  clauses                                 7
% 0.71/1.05  conjectures                             2
% 0.71/1.05  EPR                                     3
% 0.71/1.05  Horn                                    5
% 0.71/1.05  unary                                   4
% 0.71/1.05  binary                                  1
% 0.71/1.05  lits                                    12
% 0.71/1.05  lits eq                                 2
% 0.71/1.05  fd_pure                                 0
% 0.71/1.05  fd_pseudo                               0
% 0.71/1.05  fd_cond                                 1
% 0.71/1.05  fd_pseudo_cond                          0
% 0.71/1.05  AC symbols                              0
% 0.71/1.05  
% 0.71/1.05  ------ Schedule dynamic 5 is on 
% 0.71/1.05  
% 0.71/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.71/1.05  
% 0.71/1.05  
% 0.71/1.05  ------ 
% 0.71/1.05  Current options:
% 0.71/1.05  ------ 
% 0.71/1.05  
% 0.71/1.05  ------ Input Options
% 0.71/1.05  
% 0.71/1.05  --out_options                           all
% 0.71/1.05  --tptp_safe_out                         true
% 0.71/1.05  --problem_path                          ""
% 0.71/1.05  --include_path                          ""
% 0.71/1.05  --clausifier                            res/vclausify_rel
% 0.71/1.05  --clausifier_options                    --mode clausify
% 0.71/1.05  --stdin                                 false
% 0.71/1.05  --stats_out                             all
% 0.71/1.05  
% 0.71/1.05  ------ General Options
% 0.71/1.05  
% 0.71/1.05  --fof                                   false
% 0.71/1.05  --time_out_real                         305.
% 0.71/1.05  --time_out_virtual                      -1.
% 0.71/1.05  --symbol_type_check                     false
% 0.71/1.05  --clausify_out                          false
% 0.71/1.05  --sig_cnt_out                           false
% 0.71/1.05  --trig_cnt_out                          false
% 0.71/1.05  --trig_cnt_out_tolerance                1.
% 0.71/1.05  --trig_cnt_out_sk_spl                   false
% 0.71/1.05  --abstr_cl_out                          false
% 0.71/1.05  
% 0.71/1.05  ------ Global Options
% 0.71/1.05  
% 0.71/1.05  --schedule                              default
% 0.71/1.05  --add_important_lit                     false
% 0.71/1.05  --prop_solver_per_cl                    1000
% 0.71/1.05  --min_unsat_core                        false
% 0.71/1.05  --soft_assumptions                      false
% 0.71/1.05  --soft_lemma_size                       3
% 0.71/1.05  --prop_impl_unit_size                   0
% 0.71/1.05  --prop_impl_unit                        []
% 0.71/1.05  --share_sel_clauses                     true
% 0.71/1.05  --reset_solvers                         false
% 0.71/1.05  --bc_imp_inh                            [conj_cone]
% 0.71/1.05  --conj_cone_tolerance                   3.
% 0.71/1.05  --extra_neg_conj                        none
% 0.71/1.05  --large_theory_mode                     true
% 0.71/1.05  --prolific_symb_bound                   200
% 0.71/1.05  --lt_threshold                          2000
% 0.71/1.05  --clause_weak_htbl                      true
% 0.71/1.05  --gc_record_bc_elim                     false
% 0.71/1.05  
% 0.71/1.05  ------ Preprocessing Options
% 0.71/1.05  
% 0.71/1.05  --preprocessing_flag                    true
% 0.71/1.05  --time_out_prep_mult                    0.1
% 0.71/1.05  --splitting_mode                        input
% 0.71/1.05  --splitting_grd                         true
% 0.71/1.05  --splitting_cvd                         false
% 0.71/1.05  --splitting_cvd_svl                     false
% 0.71/1.05  --splitting_nvd                         32
% 0.71/1.05  --sub_typing                            true
% 0.71/1.05  --prep_gs_sim                           true
% 0.71/1.05  --prep_unflatten                        true
% 0.71/1.05  --prep_res_sim                          true
% 0.71/1.05  --prep_upred                            true
% 0.71/1.05  --prep_sem_filter                       exhaustive
% 0.71/1.05  --prep_sem_filter_out                   false
% 0.71/1.05  --pred_elim                             true
% 0.71/1.05  --res_sim_input                         true
% 0.71/1.05  --eq_ax_congr_red                       true
% 0.71/1.05  --pure_diseq_elim                       true
% 0.71/1.05  --brand_transform                       false
% 0.71/1.05  --non_eq_to_eq                          false
% 0.71/1.05  --prep_def_merge                        true
% 0.71/1.05  --prep_def_merge_prop_impl              false
% 0.71/1.05  --prep_def_merge_mbd                    true
% 0.71/1.05  --prep_def_merge_tr_red                 false
% 0.71/1.05  --prep_def_merge_tr_cl                  false
% 0.71/1.05  --smt_preprocessing                     true
% 0.71/1.05  --smt_ac_axioms                         fast
% 0.71/1.05  --preprocessed_out                      false
% 0.71/1.05  --preprocessed_stats                    false
% 0.71/1.05  
% 0.71/1.05  ------ Abstraction refinement Options
% 0.71/1.05  
% 0.71/1.05  --abstr_ref                             []
% 0.71/1.05  --abstr_ref_prep                        false
% 0.71/1.05  --abstr_ref_until_sat                   false
% 0.71/1.05  --abstr_ref_sig_restrict                funpre
% 0.71/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.71/1.05  --abstr_ref_under                       []
% 0.71/1.05  
% 0.71/1.05  ------ SAT Options
% 0.71/1.05  
% 0.71/1.05  --sat_mode                              false
% 0.71/1.05  --sat_fm_restart_options                ""
% 0.71/1.05  --sat_gr_def                            false
% 0.71/1.05  --sat_epr_types                         true
% 0.71/1.05  --sat_non_cyclic_types                  false
% 0.71/1.05  --sat_finite_models                     false
% 0.71/1.05  --sat_fm_lemmas                         false
% 0.71/1.05  --sat_fm_prep                           false
% 0.71/1.05  --sat_fm_uc_incr                        true
% 0.71/1.05  --sat_out_model                         small
% 0.71/1.05  --sat_out_clauses                       false
% 0.71/1.05  
% 0.71/1.05  ------ QBF Options
% 0.71/1.05  
% 0.71/1.05  --qbf_mode                              false
% 0.71/1.05  --qbf_elim_univ                         false
% 0.71/1.05  --qbf_dom_inst                          none
% 0.71/1.05  --qbf_dom_pre_inst                      false
% 0.71/1.05  --qbf_sk_in                             false
% 0.71/1.05  --qbf_pred_elim                         true
% 0.71/1.05  --qbf_split                             512
% 0.71/1.05  
% 0.71/1.05  ------ BMC1 Options
% 0.71/1.05  
% 0.71/1.05  --bmc1_incremental                      false
% 0.71/1.05  --bmc1_axioms                           reachable_all
% 0.71/1.05  --bmc1_min_bound                        0
% 0.71/1.05  --bmc1_max_bound                        -1
% 0.71/1.05  --bmc1_max_bound_default                -1
% 0.71/1.05  --bmc1_symbol_reachability              true
% 0.71/1.05  --bmc1_property_lemmas                  false
% 0.71/1.05  --bmc1_k_induction                      false
% 0.71/1.05  --bmc1_non_equiv_states                 false
% 0.71/1.05  --bmc1_deadlock                         false
% 0.71/1.05  --bmc1_ucm                              false
% 0.71/1.05  --bmc1_add_unsat_core                   none
% 0.71/1.05  --bmc1_unsat_core_children              false
% 0.71/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.71/1.05  --bmc1_out_stat                         full
% 0.71/1.05  --bmc1_ground_init                      false
% 0.71/1.05  --bmc1_pre_inst_next_state              false
% 0.71/1.05  --bmc1_pre_inst_state                   false
% 0.71/1.05  --bmc1_pre_inst_reach_state             false
% 0.71/1.05  --bmc1_out_unsat_core                   false
% 0.71/1.05  --bmc1_aig_witness_out                  false
% 0.71/1.05  --bmc1_verbose                          false
% 0.71/1.05  --bmc1_dump_clauses_tptp                false
% 0.71/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.71/1.05  --bmc1_dump_file                        -
% 0.71/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.71/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.71/1.05  --bmc1_ucm_extend_mode                  1
% 0.71/1.05  --bmc1_ucm_init_mode                    2
% 0.71/1.05  --bmc1_ucm_cone_mode                    none
% 0.71/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.71/1.05  --bmc1_ucm_relax_model                  4
% 0.71/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.71/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.71/1.05  --bmc1_ucm_layered_model                none
% 0.71/1.05  --bmc1_ucm_max_lemma_size               10
% 0.71/1.05  
% 0.71/1.05  ------ AIG Options
% 0.71/1.05  
% 0.71/1.05  --aig_mode                              false
% 0.71/1.05  
% 0.71/1.05  ------ Instantiation Options
% 0.71/1.05  
% 0.71/1.05  --instantiation_flag                    true
% 0.71/1.05  --inst_sos_flag                         false
% 0.71/1.05  --inst_sos_phase                        true
% 0.71/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.71/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.71/1.05  --inst_lit_sel_side                     none
% 0.71/1.05  --inst_solver_per_active                1400
% 0.71/1.05  --inst_solver_calls_frac                1.
% 0.71/1.05  --inst_passive_queue_type               priority_queues
% 0.71/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.71/1.05  --inst_passive_queues_freq              [25;2]
% 0.71/1.05  --inst_dismatching                      true
% 0.71/1.05  --inst_eager_unprocessed_to_passive     true
% 0.71/1.05  --inst_prop_sim_given                   true
% 0.71/1.05  --inst_prop_sim_new                     false
% 0.71/1.05  --inst_subs_new                         false
% 0.71/1.05  --inst_eq_res_simp                      false
% 0.71/1.05  --inst_subs_given                       false
% 0.71/1.05  --inst_orphan_elimination               true
% 0.71/1.05  --inst_learning_loop_flag               true
% 0.71/1.05  --inst_learning_start                   3000
% 0.71/1.05  --inst_learning_factor                  2
% 0.71/1.05  --inst_start_prop_sim_after_learn       3
% 0.71/1.05  --inst_sel_renew                        solver
% 0.71/1.05  --inst_lit_activity_flag                true
% 0.71/1.05  --inst_restr_to_given                   false
% 0.71/1.05  --inst_activity_threshold               500
% 0.71/1.05  --inst_out_proof                        true
% 0.71/1.05  
% 0.71/1.05  ------ Resolution Options
% 0.71/1.05  
% 0.71/1.05  --resolution_flag                       false
% 0.71/1.05  --res_lit_sel                           adaptive
% 0.71/1.05  --res_lit_sel_side                      none
% 0.71/1.05  --res_ordering                          kbo
% 0.71/1.05  --res_to_prop_solver                    active
% 0.71/1.05  --res_prop_simpl_new                    false
% 0.71/1.05  --res_prop_simpl_given                  true
% 0.71/1.05  --res_passive_queue_type                priority_queues
% 0.71/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.71/1.05  --res_passive_queues_freq               [15;5]
% 0.71/1.05  --res_forward_subs                      full
% 0.71/1.05  --res_backward_subs                     full
% 0.71/1.05  --res_forward_subs_resolution           true
% 0.71/1.05  --res_backward_subs_resolution          true
% 0.71/1.05  --res_orphan_elimination                true
% 0.71/1.05  --res_time_limit                        2.
% 0.71/1.05  --res_out_proof                         true
% 0.71/1.05  
% 0.71/1.05  ------ Superposition Options
% 0.71/1.05  
% 0.71/1.05  --superposition_flag                    true
% 0.71/1.05  --sup_passive_queue_type                priority_queues
% 0.71/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.71/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.71/1.05  --demod_completeness_check              fast
% 0.71/1.05  --demod_use_ground                      true
% 0.71/1.05  --sup_to_prop_solver                    passive
% 0.71/1.05  --sup_prop_simpl_new                    true
% 0.71/1.05  --sup_prop_simpl_given                  true
% 0.71/1.05  --sup_fun_splitting                     false
% 0.71/1.05  --sup_smt_interval                      50000
% 0.71/1.05  
% 0.71/1.05  ------ Superposition Simplification Setup
% 0.71/1.05  
% 0.71/1.05  --sup_indices_passive                   []
% 0.71/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.71/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.05  --sup_full_bw                           [BwDemod]
% 0.71/1.05  --sup_immed_triv                        [TrivRules]
% 0.71/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.71/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.05  --sup_immed_bw_main                     []
% 0.71/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.71/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.71/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.71/1.05  
% 0.71/1.05  ------ Combination Options
% 0.71/1.05  
% 0.71/1.05  --comb_res_mult                         3
% 0.71/1.05  --comb_sup_mult                         2
% 0.71/1.05  --comb_inst_mult                        10
% 0.71/1.05  
% 0.71/1.05  ------ Debug Options
% 0.71/1.05  
% 0.71/1.05  --dbg_backtrace                         false
% 0.71/1.05  --dbg_dump_prop_clauses                 false
% 0.71/1.05  --dbg_dump_prop_clauses_file            -
% 0.71/1.05  --dbg_out_stat                          false
% 0.71/1.05  
% 0.71/1.05  
% 0.71/1.05  
% 0.71/1.05  
% 0.71/1.05  ------ Proving...
% 0.71/1.05  
% 0.71/1.05  
% 0.71/1.05  % SZS status Theorem for theBenchmark.p
% 0.71/1.05  
% 0.71/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 0.71/1.05  
% 0.71/1.05  fof(f9,conjecture,(
% 0.71/1.05    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.71/1.05  
% 0.71/1.05  fof(f10,negated_conjecture,(
% 0.71/1.05    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.71/1.05    inference(negated_conjecture,[],[f9])).
% 0.71/1.05  
% 0.71/1.05  fof(f18,plain,(
% 0.71/1.05    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.71/1.05    inference(ennf_transformation,[],[f10])).
% 0.71/1.05  
% 0.71/1.05  fof(f19,plain,(
% 0.71/1.05    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.71/1.05    inference(flattening,[],[f18])).
% 0.71/1.05  
% 0.71/1.05  fof(f21,plain,(
% 0.71/1.05    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK1),X0) & m1_subset_1(sK1,X0))) )),
% 0.71/1.05    introduced(choice_axiom,[])).
% 0.71/1.05  
% 0.71/1.05  fof(f20,plain,(
% 0.71/1.05    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.71/1.05    introduced(choice_axiom,[])).
% 0.71/1.05  
% 0.71/1.05  fof(f22,plain,(
% 0.71/1.05    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.71/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).
% 0.71/1.05  
% 0.71/1.05  fof(f32,plain,(
% 0.71/1.05    m1_subset_1(sK1,sK0)),
% 0.71/1.05    inference(cnf_transformation,[],[f22])).
% 0.71/1.05  
% 0.71/1.05  fof(f7,axiom,(
% 0.71/1.05    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.71/1.05  
% 0.71/1.05  fof(f14,plain,(
% 0.71/1.05    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.71/1.05    inference(ennf_transformation,[],[f7])).
% 0.71/1.05  
% 0.71/1.05  fof(f15,plain,(
% 0.71/1.05    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.71/1.05    inference(flattening,[],[f14])).
% 0.71/1.05  
% 0.71/1.05  fof(f29,plain,(
% 0.71/1.05    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.71/1.05    inference(cnf_transformation,[],[f15])).
% 0.71/1.05  
% 0.71/1.05  fof(f2,axiom,(
% 0.71/1.05    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.71/1.05  
% 0.71/1.05  fof(f24,plain,(
% 0.71/1.05    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.71/1.05    inference(cnf_transformation,[],[f2])).
% 0.71/1.05  
% 0.71/1.05  fof(f3,axiom,(
% 0.71/1.05    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.71/1.05  
% 0.71/1.05  fof(f25,plain,(
% 0.71/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.71/1.05    inference(cnf_transformation,[],[f3])).
% 0.71/1.05  
% 0.71/1.05  fof(f35,plain,(
% 0.71/1.05    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.71/1.05    inference(definition_unfolding,[],[f24,f25])).
% 0.71/1.05  
% 0.71/1.05  fof(f38,plain,(
% 0.71/1.05    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.71/1.05    inference(definition_unfolding,[],[f29,f35])).
% 0.71/1.05  
% 0.71/1.05  fof(f31,plain,(
% 0.71/1.05    ~v1_xboole_0(sK0)),
% 0.71/1.05    inference(cnf_transformation,[],[f22])).
% 0.71/1.05  
% 0.71/1.05  fof(f5,axiom,(
% 0.71/1.05    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.71/1.05  
% 0.71/1.05  fof(f11,plain,(
% 0.71/1.05    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.71/1.05    inference(ennf_transformation,[],[f5])).
% 0.71/1.05  
% 0.71/1.05  fof(f12,plain,(
% 0.71/1.05    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.71/1.05    inference(flattening,[],[f11])).
% 0.71/1.05  
% 0.71/1.05  fof(f27,plain,(
% 0.71/1.05    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.71/1.05    inference(cnf_transformation,[],[f12])).
% 0.71/1.05  
% 0.71/1.05  fof(f37,plain,(
% 0.71/1.05    ( ! [X0,X1] : (m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.71/1.05    inference(definition_unfolding,[],[f27,f35])).
% 0.71/1.05  
% 0.71/1.05  fof(f4,axiom,(
% 0.71/1.05    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.71/1.05  
% 0.71/1.05  fof(f26,plain,(
% 0.71/1.05    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.71/1.05    inference(cnf_transformation,[],[f4])).
% 0.71/1.05  
% 0.71/1.05  fof(f36,plain,(
% 0.71/1.05    ( ! [X0] : (~v1_xboole_0(k1_enumset1(X0,X0,X0))) )),
% 0.71/1.05    inference(definition_unfolding,[],[f26,f35])).
% 0.71/1.05  
% 0.71/1.05  fof(f1,axiom,(
% 0.71/1.05    v1_xboole_0(k1_xboole_0)),
% 0.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.71/1.05  
% 0.71/1.05  fof(f23,plain,(
% 0.71/1.05    v1_xboole_0(k1_xboole_0)),
% 0.71/1.05    inference(cnf_transformation,[],[f1])).
% 0.71/1.05  
% 0.71/1.05  fof(f33,plain,(
% 0.71/1.05    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.71/1.05    inference(cnf_transformation,[],[f22])).
% 0.71/1.05  
% 0.71/1.05  fof(f8,axiom,(
% 0.71/1.05    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.71/1.05  
% 0.71/1.05  fof(f16,plain,(
% 0.71/1.05    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.71/1.05    inference(ennf_transformation,[],[f8])).
% 0.71/1.05  
% 0.71/1.05  fof(f17,plain,(
% 0.71/1.05    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.71/1.05    inference(flattening,[],[f16])).
% 0.71/1.05  
% 0.71/1.05  fof(f30,plain,(
% 0.71/1.05    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.71/1.05    inference(cnf_transformation,[],[f17])).
% 0.71/1.05  
% 0.71/1.05  fof(f6,axiom,(
% 0.71/1.05    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.71/1.05  
% 0.71/1.05  fof(f13,plain,(
% 0.71/1.05    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.71/1.05    inference(ennf_transformation,[],[f6])).
% 0.71/1.05  
% 0.71/1.05  fof(f28,plain,(
% 0.71/1.05    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.71/1.05    inference(cnf_transformation,[],[f13])).
% 0.71/1.05  
% 0.71/1.05  fof(f34,plain,(
% 0.71/1.05    v1_zfmisc_1(sK0)),
% 0.71/1.05    inference(cnf_transformation,[],[f22])).
% 0.71/1.05  
% 0.71/1.05  cnf(c_8,negated_conjecture,
% 0.71/1.05      ( m1_subset_1(sK1,sK0) ),
% 0.71/1.05      inference(cnf_transformation,[],[f32]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_454,plain,
% 0.71/1.05      ( m1_subset_1(sK1,sK0) = iProver_top ),
% 0.71/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_4,plain,
% 0.71/1.05      ( ~ m1_subset_1(X0,X1)
% 0.71/1.05      | v1_xboole_0(X1)
% 0.71/1.05      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 0.71/1.05      inference(cnf_transformation,[],[f38]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_455,plain,
% 0.71/1.05      ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
% 0.71/1.05      | m1_subset_1(X0,X1) != iProver_top
% 0.71/1.05      | v1_xboole_0(X1) = iProver_top ),
% 0.71/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_569,plain,
% 0.71/1.05      ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1)
% 0.71/1.05      | v1_xboole_0(sK0) = iProver_top ),
% 0.71/1.05      inference(superposition,[status(thm)],[c_454,c_455]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_9,negated_conjecture,
% 0.71/1.05      ( ~ v1_xboole_0(sK0) ),
% 0.71/1.05      inference(cnf_transformation,[],[f31]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_505,plain,
% 0.71/1.05      ( ~ m1_subset_1(sK1,sK0)
% 0.71/1.05      | v1_xboole_0(sK0)
% 0.71/1.05      | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1) ),
% 0.71/1.05      inference(instantiation,[status(thm)],[c_4]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_624,plain,
% 0.71/1.05      ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1) ),
% 0.71/1.05      inference(global_propositional_subsumption,
% 0.71/1.05                [status(thm)],
% 0.71/1.05                [c_569,c_9,c_8,c_505]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_2,plain,
% 0.71/1.05      ( ~ m1_subset_1(X0,X1)
% 0.71/1.05      | m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
% 0.71/1.05      | k1_xboole_0 = X1 ),
% 0.71/1.05      inference(cnf_transformation,[],[f37]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_456,plain,
% 0.71/1.05      ( k1_xboole_0 = X0
% 0.71/1.05      | m1_subset_1(X1,X0) != iProver_top
% 0.71/1.05      | m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 0.71/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_685,plain,
% 0.71/1.05      ( k1_xboole_0 = X0
% 0.71/1.05      | m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(X0)) = iProver_top
% 0.71/1.05      | m1_subset_1(sK1,X0) != iProver_top ),
% 0.71/1.05      inference(superposition,[status(thm)],[c_624,c_456]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_702,plain,
% 0.71/1.05      ( k1_xboole_0 = sK0
% 0.71/1.05      | m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
% 0.71/1.05      | m1_subset_1(sK1,sK0) != iProver_top ),
% 0.71/1.05      inference(instantiation,[status(thm)],[c_685]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_1,plain,
% 0.71/1.05      ( ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
% 0.71/1.05      inference(cnf_transformation,[],[f36]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_457,plain,
% 0.71/1.05      ( v1_xboole_0(k1_enumset1(X0,X0,X0)) != iProver_top ),
% 0.71/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_627,plain,
% 0.71/1.05      ( v1_xboole_0(k6_domain_1(sK0,sK1)) != iProver_top ),
% 0.71/1.05      inference(superposition,[status(thm)],[c_624,c_457]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_315,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_535,plain,
% 0.71/1.05      ( X0 != X1 | X0 = k1_xboole_0 | k1_xboole_0 != X1 ),
% 0.71/1.05      inference(instantiation,[status(thm)],[c_315]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_536,plain,
% 0.71/1.05      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 0.71/1.05      inference(instantiation,[status(thm)],[c_535]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_314,plain,( X0 = X0 ),theory(equality) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_325,plain,
% 0.71/1.05      ( sK0 = sK0 ),
% 0.71/1.05      inference(instantiation,[status(thm)],[c_314]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_0,plain,
% 0.71/1.05      ( v1_xboole_0(k1_xboole_0) ),
% 0.71/1.05      inference(cnf_transformation,[],[f23]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_149,plain,
% 0.71/1.05      ( sK0 != k1_xboole_0 ),
% 0.71/1.05      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_7,negated_conjecture,
% 0.71/1.05      ( v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
% 0.71/1.05      inference(cnf_transformation,[],[f33]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_5,plain,
% 0.71/1.05      ( ~ v1_subset_1(X0,X1)
% 0.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.71/1.05      | ~ v1_zfmisc_1(X1)
% 0.71/1.05      | v1_xboole_0(X1)
% 0.71/1.05      | v1_xboole_0(X0) ),
% 0.71/1.05      inference(cnf_transformation,[],[f30]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_3,plain,
% 0.71/1.05      ( ~ v1_subset_1(X0,X1)
% 0.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.71/1.05      | ~ v1_xboole_0(X1) ),
% 0.71/1.05      inference(cnf_transformation,[],[f28]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_53,plain,
% 0.71/1.05      ( ~ v1_zfmisc_1(X1)
% 0.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.71/1.05      | ~ v1_subset_1(X0,X1)
% 0.71/1.05      | v1_xboole_0(X0) ),
% 0.71/1.05      inference(global_propositional_subsumption,[status(thm)],[c_5,c_3]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_54,plain,
% 0.71/1.05      ( ~ v1_subset_1(X0,X1)
% 0.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.71/1.05      | ~ v1_zfmisc_1(X1)
% 0.71/1.05      | v1_xboole_0(X0) ),
% 0.71/1.05      inference(renaming,[status(thm)],[c_53]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_6,negated_conjecture,
% 0.71/1.05      ( v1_zfmisc_1(sK0) ),
% 0.71/1.05      inference(cnf_transformation,[],[f34]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_110,plain,
% 0.71/1.05      ( ~ v1_subset_1(X0,X1)
% 0.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.71/1.05      | v1_xboole_0(X0)
% 0.71/1.05      | sK0 != X1 ),
% 0.71/1.05      inference(resolution_lifted,[status(thm)],[c_54,c_6]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_111,plain,
% 0.71/1.05      ( ~ v1_subset_1(X0,sK0)
% 0.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
% 0.71/1.05      | v1_xboole_0(X0) ),
% 0.71/1.05      inference(unflattening,[status(thm)],[c_110]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_131,plain,
% 0.71/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
% 0.71/1.05      | v1_xboole_0(X0)
% 0.71/1.05      | k6_domain_1(sK0,sK1) != X0
% 0.71/1.05      | sK0 != sK0 ),
% 0.71/1.05      inference(resolution_lifted,[status(thm)],[c_7,c_111]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_132,plain,
% 0.71/1.05      ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
% 0.71/1.05      | v1_xboole_0(k6_domain_1(sK0,sK1)) ),
% 0.71/1.05      inference(unflattening,[status(thm)],[c_131]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_133,plain,
% 0.71/1.05      ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 0.71/1.05      | v1_xboole_0(k6_domain_1(sK0,sK1)) = iProver_top ),
% 0.71/1.05      inference(predicate_to_equality,[status(thm)],[c_132]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(c_11,plain,
% 0.71/1.05      ( m1_subset_1(sK1,sK0) = iProver_top ),
% 0.71/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.71/1.05  
% 0.71/1.05  cnf(contradiction,plain,
% 0.71/1.05      ( $false ),
% 0.71/1.05      inference(minisat,
% 0.71/1.05                [status(thm)],
% 0.71/1.05                [c_702,c_627,c_536,c_325,c_149,c_133,c_11]) ).
% 0.71/1.05  
% 0.71/1.05  
% 0.71/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 0.71/1.05  
% 0.71/1.05  ------                               Statistics
% 0.71/1.05  
% 0.71/1.05  ------ General
% 0.71/1.05  
% 0.71/1.05  abstr_ref_over_cycles:                  0
% 0.71/1.05  abstr_ref_under_cycles:                 0
% 0.71/1.05  gc_basic_clause_elim:                   0
% 0.71/1.05  forced_gc_time:                         0
% 0.71/1.05  parsing_time:                           0.01
% 0.71/1.05  unif_index_cands_time:                  0.
% 0.71/1.05  unif_index_add_time:                    0.
% 0.71/1.05  orderings_time:                         0.
% 0.71/1.05  out_proof_time:                         0.015
% 0.71/1.05  total_time:                             0.079
% 0.71/1.05  num_of_symbols:                         41
% 0.71/1.05  num_of_terms:                           490
% 0.71/1.05  
% 0.71/1.05  ------ Preprocessing
% 0.71/1.05  
% 0.71/1.05  num_of_splits:                          0
% 0.71/1.05  num_of_split_atoms:                     0
% 0.71/1.05  num_of_reused_defs:                     0
% 0.71/1.05  num_eq_ax_congr_red:                    10
% 0.71/1.05  num_of_sem_filtered_clauses:            1
% 0.71/1.05  num_of_subtypes:                        1
% 0.71/1.05  monotx_restored_types:                  0
% 0.71/1.05  sat_num_of_epr_types:                   0
% 0.71/1.05  sat_num_of_non_cyclic_types:            0
% 0.71/1.05  sat_guarded_non_collapsed_types:        1
% 0.71/1.05  num_pure_diseq_elim:                    0
% 0.71/1.05  simp_replaced_by:                       0
% 0.71/1.05  res_preprocessed:                       44
% 0.71/1.05  prep_upred:                             0
% 0.71/1.05  prep_unflattend:                        8
% 0.71/1.05  smt_new_axioms:                         0
% 0.71/1.05  pred_elim_cands:                        2
% 0.71/1.05  pred_elim:                              2
% 0.71/1.05  pred_elim_cl:                           3
% 0.71/1.05  pred_elim_cycles:                       4
% 0.71/1.05  merged_defs:                            0
% 0.71/1.05  merged_defs_ncl:                        0
% 0.71/1.05  bin_hyper_res:                          0
% 0.71/1.05  prep_cycles:                            4
% 0.71/1.05  pred_elim_time:                         0.011
% 0.71/1.05  splitting_time:                         0.
% 0.71/1.05  sem_filter_time:                        0.
% 0.71/1.05  monotx_time:                            0.
% 0.71/1.05  subtype_inf_time:                       0.
% 0.71/1.05  
% 0.71/1.05  ------ Problem properties
% 0.71/1.05  
% 0.71/1.05  clauses:                                7
% 0.71/1.05  conjectures:                            2
% 0.71/1.05  epr:                                    3
% 0.71/1.05  horn:                                   5
% 0.71/1.05  ground:                                 4
% 0.71/1.05  unary:                                  4
% 0.71/1.05  binary:                                 1
% 0.71/1.05  lits:                                   12
% 0.71/1.05  lits_eq:                                2
% 0.71/1.05  fd_pure:                                0
% 0.71/1.05  fd_pseudo:                              0
% 0.71/1.05  fd_cond:                                1
% 0.71/1.05  fd_pseudo_cond:                         0
% 0.71/1.05  ac_symbols:                             0
% 0.71/1.05  
% 0.71/1.05  ------ Propositional Solver
% 0.71/1.05  
% 0.71/1.05  prop_solver_calls:                      26
% 0.71/1.05  prop_fast_solver_calls:                 222
% 0.71/1.05  smt_solver_calls:                       0
% 0.71/1.05  smt_fast_solver_calls:                  0
% 0.71/1.05  prop_num_of_clauses:                    162
% 0.71/1.05  prop_preprocess_simplified:             1163
% 0.71/1.05  prop_fo_subsumed:                       2
% 0.71/1.05  prop_solver_time:                       0.
% 0.71/1.05  smt_solver_time:                        0.
% 0.71/1.05  smt_fast_solver_time:                   0.
% 0.71/1.05  prop_fast_solver_time:                  0.
% 0.71/1.05  prop_unsat_core_time:                   0.
% 0.71/1.05  
% 0.71/1.05  ------ QBF
% 0.71/1.05  
% 0.71/1.05  qbf_q_res:                              0
% 0.71/1.06  qbf_num_tautologies:                    0
% 0.71/1.06  qbf_prep_cycles:                        0
% 0.71/1.06  
% 0.71/1.06  ------ BMC1
% 0.71/1.06  
% 0.71/1.06  bmc1_current_bound:                     -1
% 0.71/1.06  bmc1_last_solved_bound:                 -1
% 0.71/1.06  bmc1_unsat_core_size:                   -1
% 0.71/1.06  bmc1_unsat_core_parents_size:           -1
% 0.71/1.06  bmc1_merge_next_fun:                    0
% 0.71/1.06  bmc1_unsat_core_clauses_time:           0.
% 0.71/1.06  
% 0.71/1.06  ------ Instantiation
% 0.71/1.06  
% 0.71/1.06  inst_num_of_clauses:                    57
% 0.71/1.06  inst_num_in_passive:                    0
% 0.71/1.06  inst_num_in_active:                     41
% 0.71/1.06  inst_num_in_unprocessed:                16
% 0.71/1.06  inst_num_of_loops:                      50
% 0.71/1.06  inst_num_of_learning_restarts:          0
% 0.71/1.06  inst_num_moves_active_passive:          6
% 0.71/1.06  inst_lit_activity:                      0
% 0.71/1.06  inst_lit_activity_moves:                0
% 0.71/1.06  inst_num_tautologies:                   0
% 0.71/1.06  inst_num_prop_implied:                  0
% 0.71/1.06  inst_num_existing_simplified:           0
% 0.71/1.06  inst_num_eq_res_simplified:             0
% 0.71/1.06  inst_num_child_elim:                    0
% 0.71/1.06  inst_num_of_dismatching_blockings:      3
% 0.71/1.06  inst_num_of_non_proper_insts:           36
% 0.71/1.06  inst_num_of_duplicates:                 0
% 0.71/1.06  inst_inst_num_from_inst_to_res:         0
% 0.71/1.06  inst_dismatching_checking_time:         0.
% 0.71/1.06  
% 0.71/1.06  ------ Resolution
% 0.71/1.06  
% 0.71/1.06  res_num_of_clauses:                     0
% 0.71/1.06  res_num_in_passive:                     0
% 0.71/1.06  res_num_in_active:                      0
% 0.71/1.06  res_num_of_loops:                       48
% 0.71/1.06  res_forward_subset_subsumed:            5
% 0.71/1.06  res_backward_subset_subsumed:           0
% 0.71/1.06  res_forward_subsumed:                   0
% 0.71/1.06  res_backward_subsumed:                  0
% 0.71/1.06  res_forward_subsumption_resolution:     0
% 0.71/1.06  res_backward_subsumption_resolution:    0
% 0.71/1.06  res_clause_to_clause_subsumption:       14
% 0.71/1.06  res_orphan_elimination:                 0
% 0.71/1.06  res_tautology_del:                      7
% 0.71/1.06  res_num_eq_res_simplified:              0
% 0.71/1.06  res_num_sel_changes:                    0
% 0.71/1.06  res_moves_from_active_to_pass:          0
% 0.71/1.06  
% 0.71/1.06  ------ Superposition
% 0.71/1.06  
% 0.71/1.06  sup_time_total:                         0.
% 0.71/1.06  sup_time_generating:                    0.
% 0.71/1.06  sup_time_sim_full:                      0.
% 0.71/1.06  sup_time_sim_immed:                     0.
% 0.71/1.06  
% 0.71/1.06  sup_num_of_clauses:                     10
% 0.71/1.06  sup_num_in_active:                      9
% 0.71/1.06  sup_num_in_passive:                     1
% 0.71/1.06  sup_num_of_loops:                       8
% 0.71/1.06  sup_fw_superposition:                   2
% 0.71/1.06  sup_bw_superposition:                   2
% 0.71/1.06  sup_immediate_simplified:               0
% 0.71/1.06  sup_given_eliminated:                   0
% 0.71/1.06  comparisons_done:                       0
% 0.71/1.06  comparisons_avoided:                    0
% 0.71/1.06  
% 0.71/1.06  ------ Simplifications
% 0.71/1.06  
% 0.71/1.06  
% 0.71/1.06  sim_fw_subset_subsumed:                 0
% 0.71/1.06  sim_bw_subset_subsumed:                 0
% 0.71/1.06  sim_fw_subsumed:                        0
% 0.71/1.06  sim_bw_subsumed:                        0
% 0.71/1.06  sim_fw_subsumption_res:                 0
% 0.71/1.06  sim_bw_subsumption_res:                 0
% 0.71/1.06  sim_tautology_del:                      0
% 0.71/1.06  sim_eq_tautology_del:                   0
% 0.71/1.06  sim_eq_res_simp:                        0
% 0.71/1.06  sim_fw_demodulated:                     0
% 0.71/1.06  sim_bw_demodulated:                     0
% 0.71/1.06  sim_light_normalised:                   0
% 0.71/1.06  sim_joinable_taut:                      0
% 0.71/1.06  sim_joinable_simp:                      0
% 0.71/1.06  sim_ac_normalised:                      0
% 0.71/1.06  sim_smt_subsumption:                    0
% 0.71/1.06  
%------------------------------------------------------------------------------
