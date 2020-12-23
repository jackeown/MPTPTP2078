%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:13 EST 2020

% Result     : Theorem 11.85s
% Output     : CNFRefutation 11.85s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 232 expanded)
%              Number of clauses        :   37 (  83 expanded)
%              Number of leaves         :    9 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  120 ( 502 expanded)
%              Number of equality atoms :   73 ( 252 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).

fof(f28,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(definition_unfolding,[],[f26,f25,f25,f25])).

fof(f29,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))) != k2_zfmisc_1(sK0,sK2) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f25,f25])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_365,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_368,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1222,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_365,c_368])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_366,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_370,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1428,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_366,c_370])).

cnf(c_34133,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2
    | r1_tarski(sK2,k4_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1428])).

cnf(c_34221,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = sK2
    | r1_tarski(sK2,k4_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34133,c_1222])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_13462,plain,
    ( r1_tarski(sK2,X0)
    | k4_xboole_0(sK2,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_34075,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK2,k1_xboole_0))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13462])).

cnf(c_34326,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK2,k1_xboole_0))
    | k4_xboole_0(sK2,k1_xboole_0) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_34221])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_34446,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_34688,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34221,c_34075,c_34326,c_34446])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_364,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1223,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_364,c_368])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1349,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1223,c_8])).

cnf(c_9,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))) != k2_zfmisc_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3042,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) != k2_zfmisc_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_1349,c_9])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1238,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1222,c_0])).

cnf(c_3043,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)) != k2_zfmisc_1(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3042,c_1238])).

cnf(c_34752,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),sK2) != k2_zfmisc_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_34688,c_3043])).

cnf(c_367,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_857,plain,
    ( r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_367])).

cnf(c_34134,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK0
    | r1_tarski(sK0,k4_xboole_0(sK0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_1428])).

cnf(c_34220,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = sK0
    | r1_tarski(sK0,k4_xboole_0(sK0,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34134,c_1223])).

cnf(c_34686,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(superposition,[status(thm)],[c_857,c_34220])).

cnf(c_34759,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_34752,c_34686])).

cnf(c_34760,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_34759])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:18:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.85/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.85/2.01  
% 11.85/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.85/2.01  
% 11.85/2.01  ------  iProver source info
% 11.85/2.01  
% 11.85/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.85/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.85/2.01  git: non_committed_changes: false
% 11.85/2.01  git: last_make_outside_of_git: false
% 11.85/2.01  
% 11.85/2.01  ------ 
% 11.85/2.01  
% 11.85/2.01  ------ Input Options
% 11.85/2.01  
% 11.85/2.01  --out_options                           all
% 11.85/2.01  --tptp_safe_out                         true
% 11.85/2.01  --problem_path                          ""
% 11.85/2.01  --include_path                          ""
% 11.85/2.01  --clausifier                            res/vclausify_rel
% 11.85/2.01  --clausifier_options                    ""
% 11.85/2.01  --stdin                                 false
% 11.85/2.01  --stats_out                             all
% 11.85/2.01  
% 11.85/2.01  ------ General Options
% 11.85/2.01  
% 11.85/2.01  --fof                                   false
% 11.85/2.01  --time_out_real                         305.
% 11.85/2.01  --time_out_virtual                      -1.
% 11.85/2.01  --symbol_type_check                     false
% 11.85/2.01  --clausify_out                          false
% 11.85/2.01  --sig_cnt_out                           false
% 11.85/2.01  --trig_cnt_out                          false
% 11.85/2.01  --trig_cnt_out_tolerance                1.
% 11.85/2.01  --trig_cnt_out_sk_spl                   false
% 11.85/2.01  --abstr_cl_out                          false
% 11.85/2.01  
% 11.85/2.01  ------ Global Options
% 11.85/2.01  
% 11.85/2.01  --schedule                              default
% 11.85/2.01  --add_important_lit                     false
% 11.85/2.01  --prop_solver_per_cl                    1000
% 11.85/2.01  --min_unsat_core                        false
% 11.85/2.01  --soft_assumptions                      false
% 11.85/2.01  --soft_lemma_size                       3
% 11.85/2.01  --prop_impl_unit_size                   0
% 11.85/2.01  --prop_impl_unit                        []
% 11.85/2.01  --share_sel_clauses                     true
% 11.85/2.01  --reset_solvers                         false
% 11.85/2.01  --bc_imp_inh                            [conj_cone]
% 11.85/2.01  --conj_cone_tolerance                   3.
% 11.85/2.01  --extra_neg_conj                        none
% 11.85/2.01  --large_theory_mode                     true
% 11.85/2.01  --prolific_symb_bound                   200
% 11.85/2.01  --lt_threshold                          2000
% 11.85/2.01  --clause_weak_htbl                      true
% 11.85/2.01  --gc_record_bc_elim                     false
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing Options
% 11.85/2.01  
% 11.85/2.01  --preprocessing_flag                    true
% 11.85/2.01  --time_out_prep_mult                    0.1
% 11.85/2.01  --splitting_mode                        input
% 11.85/2.01  --splitting_grd                         true
% 11.85/2.01  --splitting_cvd                         false
% 11.85/2.01  --splitting_cvd_svl                     false
% 11.85/2.01  --splitting_nvd                         32
% 11.85/2.01  --sub_typing                            true
% 11.85/2.01  --prep_gs_sim                           true
% 11.85/2.01  --prep_unflatten                        true
% 11.85/2.01  --prep_res_sim                          true
% 11.85/2.01  --prep_upred                            true
% 11.85/2.01  --prep_sem_filter                       exhaustive
% 11.85/2.01  --prep_sem_filter_out                   false
% 11.85/2.01  --pred_elim                             true
% 11.85/2.01  --res_sim_input                         true
% 11.85/2.01  --eq_ax_congr_red                       true
% 11.85/2.01  --pure_diseq_elim                       true
% 11.85/2.01  --brand_transform                       false
% 11.85/2.01  --non_eq_to_eq                          false
% 11.85/2.01  --prep_def_merge                        true
% 11.85/2.01  --prep_def_merge_prop_impl              false
% 11.85/2.01  --prep_def_merge_mbd                    true
% 11.85/2.01  --prep_def_merge_tr_red                 false
% 11.85/2.01  --prep_def_merge_tr_cl                  false
% 11.85/2.01  --smt_preprocessing                     true
% 11.85/2.01  --smt_ac_axioms                         fast
% 11.85/2.01  --preprocessed_out                      false
% 11.85/2.01  --preprocessed_stats                    false
% 11.85/2.01  
% 11.85/2.01  ------ Abstraction refinement Options
% 11.85/2.01  
% 11.85/2.01  --abstr_ref                             []
% 11.85/2.01  --abstr_ref_prep                        false
% 11.85/2.01  --abstr_ref_until_sat                   false
% 11.85/2.01  --abstr_ref_sig_restrict                funpre
% 11.85/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.85/2.01  --abstr_ref_under                       []
% 11.85/2.01  
% 11.85/2.01  ------ SAT Options
% 11.85/2.01  
% 11.85/2.01  --sat_mode                              false
% 11.85/2.01  --sat_fm_restart_options                ""
% 11.85/2.01  --sat_gr_def                            false
% 11.85/2.01  --sat_epr_types                         true
% 11.85/2.01  --sat_non_cyclic_types                  false
% 11.85/2.01  --sat_finite_models                     false
% 11.85/2.01  --sat_fm_lemmas                         false
% 11.85/2.01  --sat_fm_prep                           false
% 11.85/2.01  --sat_fm_uc_incr                        true
% 11.85/2.01  --sat_out_model                         small
% 11.85/2.01  --sat_out_clauses                       false
% 11.85/2.01  
% 11.85/2.01  ------ QBF Options
% 11.85/2.01  
% 11.85/2.01  --qbf_mode                              false
% 11.85/2.01  --qbf_elim_univ                         false
% 11.85/2.01  --qbf_dom_inst                          none
% 11.85/2.01  --qbf_dom_pre_inst                      false
% 11.85/2.01  --qbf_sk_in                             false
% 11.85/2.01  --qbf_pred_elim                         true
% 11.85/2.01  --qbf_split                             512
% 11.85/2.01  
% 11.85/2.01  ------ BMC1 Options
% 11.85/2.01  
% 11.85/2.01  --bmc1_incremental                      false
% 11.85/2.01  --bmc1_axioms                           reachable_all
% 11.85/2.01  --bmc1_min_bound                        0
% 11.85/2.01  --bmc1_max_bound                        -1
% 11.85/2.01  --bmc1_max_bound_default                -1
% 11.85/2.01  --bmc1_symbol_reachability              true
% 11.85/2.01  --bmc1_property_lemmas                  false
% 11.85/2.01  --bmc1_k_induction                      false
% 11.85/2.01  --bmc1_non_equiv_states                 false
% 11.85/2.01  --bmc1_deadlock                         false
% 11.85/2.01  --bmc1_ucm                              false
% 11.85/2.01  --bmc1_add_unsat_core                   none
% 11.85/2.01  --bmc1_unsat_core_children              false
% 11.85/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.85/2.01  --bmc1_out_stat                         full
% 11.85/2.01  --bmc1_ground_init                      false
% 11.85/2.01  --bmc1_pre_inst_next_state              false
% 11.85/2.01  --bmc1_pre_inst_state                   false
% 11.85/2.01  --bmc1_pre_inst_reach_state             false
% 11.85/2.01  --bmc1_out_unsat_core                   false
% 11.85/2.01  --bmc1_aig_witness_out                  false
% 11.85/2.01  --bmc1_verbose                          false
% 11.85/2.01  --bmc1_dump_clauses_tptp                false
% 11.85/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.85/2.01  --bmc1_dump_file                        -
% 11.85/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.85/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.85/2.01  --bmc1_ucm_extend_mode                  1
% 11.85/2.01  --bmc1_ucm_init_mode                    2
% 11.85/2.01  --bmc1_ucm_cone_mode                    none
% 11.85/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.85/2.01  --bmc1_ucm_relax_model                  4
% 11.85/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.85/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.85/2.01  --bmc1_ucm_layered_model                none
% 11.85/2.01  --bmc1_ucm_max_lemma_size               10
% 11.85/2.01  
% 11.85/2.01  ------ AIG Options
% 11.85/2.01  
% 11.85/2.01  --aig_mode                              false
% 11.85/2.01  
% 11.85/2.01  ------ Instantiation Options
% 11.85/2.01  
% 11.85/2.01  --instantiation_flag                    true
% 11.85/2.01  --inst_sos_flag                         true
% 11.85/2.01  --inst_sos_phase                        true
% 11.85/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.85/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.85/2.01  --inst_lit_sel_side                     num_symb
% 11.85/2.01  --inst_solver_per_active                1400
% 11.85/2.01  --inst_solver_calls_frac                1.
% 11.85/2.01  --inst_passive_queue_type               priority_queues
% 11.85/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.85/2.01  --inst_passive_queues_freq              [25;2]
% 11.85/2.01  --inst_dismatching                      true
% 11.85/2.01  --inst_eager_unprocessed_to_passive     true
% 11.85/2.01  --inst_prop_sim_given                   true
% 11.85/2.01  --inst_prop_sim_new                     false
% 11.85/2.01  --inst_subs_new                         false
% 11.85/2.01  --inst_eq_res_simp                      false
% 11.85/2.01  --inst_subs_given                       false
% 11.85/2.01  --inst_orphan_elimination               true
% 11.85/2.01  --inst_learning_loop_flag               true
% 11.85/2.01  --inst_learning_start                   3000
% 11.85/2.01  --inst_learning_factor                  2
% 11.85/2.01  --inst_start_prop_sim_after_learn       3
% 11.85/2.01  --inst_sel_renew                        solver
% 11.85/2.01  --inst_lit_activity_flag                true
% 11.85/2.01  --inst_restr_to_given                   false
% 11.85/2.01  --inst_activity_threshold               500
% 11.85/2.01  --inst_out_proof                        true
% 11.85/2.01  
% 11.85/2.01  ------ Resolution Options
% 11.85/2.01  
% 11.85/2.01  --resolution_flag                       true
% 11.85/2.01  --res_lit_sel                           adaptive
% 11.85/2.01  --res_lit_sel_side                      none
% 11.85/2.01  --res_ordering                          kbo
% 11.85/2.01  --res_to_prop_solver                    active
% 11.85/2.01  --res_prop_simpl_new                    false
% 11.85/2.01  --res_prop_simpl_given                  true
% 11.85/2.01  --res_passive_queue_type                priority_queues
% 11.85/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.85/2.01  --res_passive_queues_freq               [15;5]
% 11.85/2.01  --res_forward_subs                      full
% 11.85/2.01  --res_backward_subs                     full
% 11.85/2.01  --res_forward_subs_resolution           true
% 11.85/2.01  --res_backward_subs_resolution          true
% 11.85/2.01  --res_orphan_elimination                true
% 11.85/2.01  --res_time_limit                        2.
% 11.85/2.01  --res_out_proof                         true
% 11.85/2.01  
% 11.85/2.01  ------ Superposition Options
% 11.85/2.01  
% 11.85/2.01  --superposition_flag                    true
% 11.85/2.01  --sup_passive_queue_type                priority_queues
% 11.85/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.85/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.85/2.01  --demod_completeness_check              fast
% 11.85/2.01  --demod_use_ground                      true
% 11.85/2.01  --sup_to_prop_solver                    passive
% 11.85/2.01  --sup_prop_simpl_new                    true
% 11.85/2.01  --sup_prop_simpl_given                  true
% 11.85/2.01  --sup_fun_splitting                     true
% 11.85/2.01  --sup_smt_interval                      50000
% 11.85/2.01  
% 11.85/2.01  ------ Superposition Simplification Setup
% 11.85/2.01  
% 11.85/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.85/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.85/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.85/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.85/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.85/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.85/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.85/2.01  --sup_immed_triv                        [TrivRules]
% 11.85/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.01  --sup_immed_bw_main                     []
% 11.85/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.85/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.85/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.01  --sup_input_bw                          []
% 11.85/2.01  
% 11.85/2.01  ------ Combination Options
% 11.85/2.01  
% 11.85/2.01  --comb_res_mult                         3
% 11.85/2.01  --comb_sup_mult                         2
% 11.85/2.01  --comb_inst_mult                        10
% 11.85/2.01  
% 11.85/2.01  ------ Debug Options
% 11.85/2.01  
% 11.85/2.01  --dbg_backtrace                         false
% 11.85/2.01  --dbg_dump_prop_clauses                 false
% 11.85/2.01  --dbg_dump_prop_clauses_file            -
% 11.85/2.01  --dbg_out_stat                          false
% 11.85/2.01  ------ Parsing...
% 11.85/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  ------ Proving...
% 11.85/2.01  ------ Problem Properties 
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  clauses                                 11
% 11.85/2.01  conjectures                             3
% 11.85/2.01  EPR                                     4
% 11.85/2.01  Horn                                    11
% 11.85/2.01  unary                                   8
% 11.85/2.01  binary                                  2
% 11.85/2.01  lits                                    15
% 11.85/2.01  lits eq                                 7
% 11.85/2.01  fd_pure                                 0
% 11.85/2.01  fd_pseudo                               0
% 11.85/2.01  fd_cond                                 0
% 11.85/2.01  fd_pseudo_cond                          1
% 11.85/2.01  AC symbols                              0
% 11.85/2.01  
% 11.85/2.01  ------ Schedule dynamic 5 is on 
% 11.85/2.01  
% 11.85/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ 
% 11.85/2.01  Current options:
% 11.85/2.01  ------ 
% 11.85/2.01  
% 11.85/2.01  ------ Input Options
% 11.85/2.01  
% 11.85/2.01  --out_options                           all
% 11.85/2.01  --tptp_safe_out                         true
% 11.85/2.01  --problem_path                          ""
% 11.85/2.01  --include_path                          ""
% 11.85/2.01  --clausifier                            res/vclausify_rel
% 11.85/2.01  --clausifier_options                    ""
% 11.85/2.01  --stdin                                 false
% 11.85/2.01  --stats_out                             all
% 11.85/2.01  
% 11.85/2.01  ------ General Options
% 11.85/2.01  
% 11.85/2.01  --fof                                   false
% 11.85/2.01  --time_out_real                         305.
% 11.85/2.01  --time_out_virtual                      -1.
% 11.85/2.01  --symbol_type_check                     false
% 11.85/2.01  --clausify_out                          false
% 11.85/2.01  --sig_cnt_out                           false
% 11.85/2.01  --trig_cnt_out                          false
% 11.85/2.01  --trig_cnt_out_tolerance                1.
% 11.85/2.01  --trig_cnt_out_sk_spl                   false
% 11.85/2.01  --abstr_cl_out                          false
% 11.85/2.01  
% 11.85/2.01  ------ Global Options
% 11.85/2.01  
% 11.85/2.01  --schedule                              default
% 11.85/2.01  --add_important_lit                     false
% 11.85/2.01  --prop_solver_per_cl                    1000
% 11.85/2.01  --min_unsat_core                        false
% 11.85/2.01  --soft_assumptions                      false
% 11.85/2.01  --soft_lemma_size                       3
% 11.85/2.01  --prop_impl_unit_size                   0
% 11.85/2.01  --prop_impl_unit                        []
% 11.85/2.01  --share_sel_clauses                     true
% 11.85/2.01  --reset_solvers                         false
% 11.85/2.01  --bc_imp_inh                            [conj_cone]
% 11.85/2.01  --conj_cone_tolerance                   3.
% 11.85/2.01  --extra_neg_conj                        none
% 11.85/2.01  --large_theory_mode                     true
% 11.85/2.01  --prolific_symb_bound                   200
% 11.85/2.01  --lt_threshold                          2000
% 11.85/2.01  --clause_weak_htbl                      true
% 11.85/2.01  --gc_record_bc_elim                     false
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing Options
% 11.85/2.01  
% 11.85/2.01  --preprocessing_flag                    true
% 11.85/2.01  --time_out_prep_mult                    0.1
% 11.85/2.01  --splitting_mode                        input
% 11.85/2.01  --splitting_grd                         true
% 11.85/2.01  --splitting_cvd                         false
% 11.85/2.01  --splitting_cvd_svl                     false
% 11.85/2.01  --splitting_nvd                         32
% 11.85/2.01  --sub_typing                            true
% 11.85/2.01  --prep_gs_sim                           true
% 11.85/2.01  --prep_unflatten                        true
% 11.85/2.01  --prep_res_sim                          true
% 11.85/2.01  --prep_upred                            true
% 11.85/2.01  --prep_sem_filter                       exhaustive
% 11.85/2.01  --prep_sem_filter_out                   false
% 11.85/2.01  --pred_elim                             true
% 11.85/2.01  --res_sim_input                         true
% 11.85/2.01  --eq_ax_congr_red                       true
% 11.85/2.01  --pure_diseq_elim                       true
% 11.85/2.01  --brand_transform                       false
% 11.85/2.01  --non_eq_to_eq                          false
% 11.85/2.01  --prep_def_merge                        true
% 11.85/2.01  --prep_def_merge_prop_impl              false
% 11.85/2.01  --prep_def_merge_mbd                    true
% 11.85/2.01  --prep_def_merge_tr_red                 false
% 11.85/2.01  --prep_def_merge_tr_cl                  false
% 11.85/2.01  --smt_preprocessing                     true
% 11.85/2.01  --smt_ac_axioms                         fast
% 11.85/2.01  --preprocessed_out                      false
% 11.85/2.01  --preprocessed_stats                    false
% 11.85/2.01  
% 11.85/2.01  ------ Abstraction refinement Options
% 11.85/2.01  
% 11.85/2.01  --abstr_ref                             []
% 11.85/2.01  --abstr_ref_prep                        false
% 11.85/2.01  --abstr_ref_until_sat                   false
% 11.85/2.01  --abstr_ref_sig_restrict                funpre
% 11.85/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.85/2.01  --abstr_ref_under                       []
% 11.85/2.01  
% 11.85/2.01  ------ SAT Options
% 11.85/2.01  
% 11.85/2.01  --sat_mode                              false
% 11.85/2.01  --sat_fm_restart_options                ""
% 11.85/2.01  --sat_gr_def                            false
% 11.85/2.01  --sat_epr_types                         true
% 11.85/2.01  --sat_non_cyclic_types                  false
% 11.85/2.01  --sat_finite_models                     false
% 11.85/2.01  --sat_fm_lemmas                         false
% 11.85/2.01  --sat_fm_prep                           false
% 11.85/2.01  --sat_fm_uc_incr                        true
% 11.85/2.01  --sat_out_model                         small
% 11.85/2.01  --sat_out_clauses                       false
% 11.85/2.01  
% 11.85/2.01  ------ QBF Options
% 11.85/2.01  
% 11.85/2.01  --qbf_mode                              false
% 11.85/2.01  --qbf_elim_univ                         false
% 11.85/2.01  --qbf_dom_inst                          none
% 11.85/2.01  --qbf_dom_pre_inst                      false
% 11.85/2.01  --qbf_sk_in                             false
% 11.85/2.01  --qbf_pred_elim                         true
% 11.85/2.01  --qbf_split                             512
% 11.85/2.01  
% 11.85/2.01  ------ BMC1 Options
% 11.85/2.01  
% 11.85/2.01  --bmc1_incremental                      false
% 11.85/2.01  --bmc1_axioms                           reachable_all
% 11.85/2.01  --bmc1_min_bound                        0
% 11.85/2.01  --bmc1_max_bound                        -1
% 11.85/2.01  --bmc1_max_bound_default                -1
% 11.85/2.01  --bmc1_symbol_reachability              true
% 11.85/2.01  --bmc1_property_lemmas                  false
% 11.85/2.01  --bmc1_k_induction                      false
% 11.85/2.01  --bmc1_non_equiv_states                 false
% 11.85/2.01  --bmc1_deadlock                         false
% 11.85/2.01  --bmc1_ucm                              false
% 11.85/2.01  --bmc1_add_unsat_core                   none
% 11.85/2.01  --bmc1_unsat_core_children              false
% 11.85/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.85/2.01  --bmc1_out_stat                         full
% 11.85/2.01  --bmc1_ground_init                      false
% 11.85/2.01  --bmc1_pre_inst_next_state              false
% 11.85/2.01  --bmc1_pre_inst_state                   false
% 11.85/2.01  --bmc1_pre_inst_reach_state             false
% 11.85/2.01  --bmc1_out_unsat_core                   false
% 11.85/2.01  --bmc1_aig_witness_out                  false
% 11.85/2.01  --bmc1_verbose                          false
% 11.85/2.01  --bmc1_dump_clauses_tptp                false
% 11.85/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.85/2.01  --bmc1_dump_file                        -
% 11.85/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.85/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.85/2.01  --bmc1_ucm_extend_mode                  1
% 11.85/2.01  --bmc1_ucm_init_mode                    2
% 11.85/2.01  --bmc1_ucm_cone_mode                    none
% 11.85/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.85/2.01  --bmc1_ucm_relax_model                  4
% 11.85/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.85/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.85/2.01  --bmc1_ucm_layered_model                none
% 11.85/2.01  --bmc1_ucm_max_lemma_size               10
% 11.85/2.01  
% 11.85/2.01  ------ AIG Options
% 11.85/2.01  
% 11.85/2.01  --aig_mode                              false
% 11.85/2.01  
% 11.85/2.01  ------ Instantiation Options
% 11.85/2.01  
% 11.85/2.01  --instantiation_flag                    true
% 11.85/2.01  --inst_sos_flag                         true
% 11.85/2.01  --inst_sos_phase                        true
% 11.85/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.85/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.85/2.01  --inst_lit_sel_side                     none
% 11.85/2.01  --inst_solver_per_active                1400
% 11.85/2.01  --inst_solver_calls_frac                1.
% 11.85/2.01  --inst_passive_queue_type               priority_queues
% 11.85/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.85/2.01  --inst_passive_queues_freq              [25;2]
% 11.85/2.01  --inst_dismatching                      true
% 11.85/2.01  --inst_eager_unprocessed_to_passive     true
% 11.85/2.01  --inst_prop_sim_given                   true
% 11.85/2.01  --inst_prop_sim_new                     false
% 11.85/2.01  --inst_subs_new                         false
% 11.85/2.01  --inst_eq_res_simp                      false
% 11.85/2.01  --inst_subs_given                       false
% 11.85/2.01  --inst_orphan_elimination               true
% 11.85/2.01  --inst_learning_loop_flag               true
% 11.85/2.01  --inst_learning_start                   3000
% 11.85/2.01  --inst_learning_factor                  2
% 11.85/2.01  --inst_start_prop_sim_after_learn       3
% 11.85/2.01  --inst_sel_renew                        solver
% 11.85/2.01  --inst_lit_activity_flag                true
% 11.85/2.01  --inst_restr_to_given                   false
% 11.85/2.01  --inst_activity_threshold               500
% 11.85/2.01  --inst_out_proof                        true
% 11.85/2.01  
% 11.85/2.01  ------ Resolution Options
% 11.85/2.01  
% 11.85/2.01  --resolution_flag                       false
% 11.85/2.01  --res_lit_sel                           adaptive
% 11.85/2.01  --res_lit_sel_side                      none
% 11.85/2.01  --res_ordering                          kbo
% 11.85/2.01  --res_to_prop_solver                    active
% 11.85/2.01  --res_prop_simpl_new                    false
% 11.85/2.01  --res_prop_simpl_given                  true
% 11.85/2.01  --res_passive_queue_type                priority_queues
% 11.85/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.85/2.01  --res_passive_queues_freq               [15;5]
% 11.85/2.01  --res_forward_subs                      full
% 11.85/2.01  --res_backward_subs                     full
% 11.85/2.01  --res_forward_subs_resolution           true
% 11.85/2.01  --res_backward_subs_resolution          true
% 11.85/2.01  --res_orphan_elimination                true
% 11.85/2.01  --res_time_limit                        2.
% 11.85/2.01  --res_out_proof                         true
% 11.85/2.01  
% 11.85/2.01  ------ Superposition Options
% 11.85/2.01  
% 11.85/2.01  --superposition_flag                    true
% 11.85/2.01  --sup_passive_queue_type                priority_queues
% 11.85/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.85/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.85/2.01  --demod_completeness_check              fast
% 11.85/2.01  --demod_use_ground                      true
% 11.85/2.01  --sup_to_prop_solver                    passive
% 11.85/2.01  --sup_prop_simpl_new                    true
% 11.85/2.01  --sup_prop_simpl_given                  true
% 11.85/2.01  --sup_fun_splitting                     true
% 11.85/2.01  --sup_smt_interval                      50000
% 11.85/2.01  
% 11.85/2.01  ------ Superposition Simplification Setup
% 11.85/2.01  
% 11.85/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.85/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.85/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.85/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.85/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.85/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.85/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.85/2.01  --sup_immed_triv                        [TrivRules]
% 11.85/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.01  --sup_immed_bw_main                     []
% 11.85/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.85/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.85/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.01  --sup_input_bw                          []
% 11.85/2.01  
% 11.85/2.01  ------ Combination Options
% 11.85/2.01  
% 11.85/2.01  --comb_res_mult                         3
% 11.85/2.01  --comb_sup_mult                         2
% 11.85/2.01  --comb_inst_mult                        10
% 11.85/2.01  
% 11.85/2.01  ------ Debug Options
% 11.85/2.01  
% 11.85/2.01  --dbg_backtrace                         false
% 11.85/2.01  --dbg_dump_prop_clauses                 false
% 11.85/2.01  --dbg_dump_prop_clauses_file            -
% 11.85/2.01  --dbg_out_stat                          false
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  % SZS status Theorem for theBenchmark.p
% 11.85/2.01  
% 11.85/2.01   Resolution empty clause
% 11.85/2.01  
% 11.85/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.85/2.01  
% 11.85/2.01  fof(f8,conjecture,(
% 11.85/2.01    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2))),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f9,negated_conjecture,(
% 11.85/2.01    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2))),
% 11.85/2.01    inference(negated_conjecture,[],[f8])).
% 11.85/2.01  
% 11.85/2.01  fof(f10,plain,(
% 11.85/2.01    ? [X0,X1,X2,X3] : (k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 11.85/2.01    inference(ennf_transformation,[],[f9])).
% 11.85/2.01  
% 11.85/2.01  fof(f11,plain,(
% 11.85/2.01    ? [X0,X1,X2,X3] : (k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 11.85/2.01    inference(flattening,[],[f10])).
% 11.85/2.01  
% 11.85/2.01  fof(f15,plain,(
% 11.85/2.01    ? [X0,X1,X2,X3] : (k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 11.85/2.01    introduced(choice_axiom,[])).
% 11.85/2.01  
% 11.85/2.01  fof(f16,plain,(
% 11.85/2.01    k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 11.85/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).
% 11.85/2.01  
% 11.85/2.01  fof(f28,plain,(
% 11.85/2.01    r1_tarski(sK2,sK3)),
% 11.85/2.01    inference(cnf_transformation,[],[f16])).
% 11.85/2.01  
% 11.85/2.01  fof(f3,axiom,(
% 11.85/2.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f14,plain,(
% 11.85/2.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.85/2.01    inference(nnf_transformation,[],[f3])).
% 11.85/2.01  
% 11.85/2.01  fof(f22,plain,(
% 11.85/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.85/2.01    inference(cnf_transformation,[],[f14])).
% 11.85/2.01  
% 11.85/2.01  fof(f4,axiom,(
% 11.85/2.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f23,plain,(
% 11.85/2.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.85/2.01    inference(cnf_transformation,[],[f4])).
% 11.85/2.01  
% 11.85/2.01  fof(f6,axiom,(
% 11.85/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f25,plain,(
% 11.85/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.85/2.01    inference(cnf_transformation,[],[f6])).
% 11.85/2.01  
% 11.85/2.01  fof(f31,plain,(
% 11.85/2.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 11.85/2.01    inference(definition_unfolding,[],[f23,f25])).
% 11.85/2.01  
% 11.85/2.01  fof(f2,axiom,(
% 11.85/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f12,plain,(
% 11.85/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.85/2.01    inference(nnf_transformation,[],[f2])).
% 11.85/2.01  
% 11.85/2.01  fof(f13,plain,(
% 11.85/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.85/2.01    inference(flattening,[],[f12])).
% 11.85/2.01  
% 11.85/2.01  fof(f20,plain,(
% 11.85/2.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.85/2.01    inference(cnf_transformation,[],[f13])).
% 11.85/2.01  
% 11.85/2.01  fof(f21,plain,(
% 11.85/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.85/2.01    inference(cnf_transformation,[],[f14])).
% 11.85/2.01  
% 11.85/2.01  fof(f5,axiom,(
% 11.85/2.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f24,plain,(
% 11.85/2.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.85/2.01    inference(cnf_transformation,[],[f5])).
% 11.85/2.01  
% 11.85/2.01  fof(f32,plain,(
% 11.85/2.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 11.85/2.01    inference(definition_unfolding,[],[f24,f25])).
% 11.85/2.01  
% 11.85/2.01  fof(f27,plain,(
% 11.85/2.01    r1_tarski(sK0,sK1)),
% 11.85/2.01    inference(cnf_transformation,[],[f16])).
% 11.85/2.01  
% 11.85/2.01  fof(f7,axiom,(
% 11.85/2.01    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f26,plain,(
% 11.85/2.01    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) )),
% 11.85/2.01    inference(cnf_transformation,[],[f7])).
% 11.85/2.01  
% 11.85/2.01  fof(f33,plain,(
% 11.85/2.01    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 11.85/2.01    inference(definition_unfolding,[],[f26,f25,f25,f25])).
% 11.85/2.01  
% 11.85/2.01  fof(f29,plain,(
% 11.85/2.01    k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2)),
% 11.85/2.01    inference(cnf_transformation,[],[f16])).
% 11.85/2.01  
% 11.85/2.01  fof(f34,plain,(
% 11.85/2.01    k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))) != k2_zfmisc_1(sK0,sK2)),
% 11.85/2.01    inference(definition_unfolding,[],[f29,f25])).
% 11.85/2.01  
% 11.85/2.01  fof(f1,axiom,(
% 11.85/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f17,plain,(
% 11.85/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.85/2.01    inference(cnf_transformation,[],[f1])).
% 11.85/2.01  
% 11.85/2.01  fof(f30,plain,(
% 11.85/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.85/2.01    inference(definition_unfolding,[],[f17,f25,f25])).
% 11.85/2.01  
% 11.85/2.01  cnf(c_10,negated_conjecture,
% 11.85/2.01      ( r1_tarski(sK2,sK3) ),
% 11.85/2.01      inference(cnf_transformation,[],[f28]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_365,plain,
% 11.85/2.01      ( r1_tarski(sK2,sK3) = iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_4,plain,
% 11.85/2.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.85/2.01      inference(cnf_transformation,[],[f22]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_368,plain,
% 11.85/2.01      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_1222,plain,
% 11.85/2.01      ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_365,c_368]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_6,plain,
% 11.85/2.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 11.85/2.01      inference(cnf_transformation,[],[f31]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_366,plain,
% 11.85/2.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_1,plain,
% 11.85/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.85/2.01      inference(cnf_transformation,[],[f20]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_370,plain,
% 11.85/2.01      ( X0 = X1
% 11.85/2.01      | r1_tarski(X0,X1) != iProver_top
% 11.85/2.01      | r1_tarski(X1,X0) != iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_1428,plain,
% 11.85/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 11.85/2.01      | r1_tarski(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_366,c_370]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34133,plain,
% 11.85/2.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2
% 11.85/2.01      | r1_tarski(sK2,k4_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_1222,c_1428]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34221,plain,
% 11.85/2.01      ( k4_xboole_0(sK2,k1_xboole_0) = sK2
% 11.85/2.01      | r1_tarski(sK2,k4_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
% 11.85/2.01      inference(light_normalisation,[status(thm)],[c_34133,c_1222]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_5,plain,
% 11.85/2.01      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.85/2.01      inference(cnf_transformation,[],[f21]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_13462,plain,
% 11.85/2.01      ( r1_tarski(sK2,X0) | k4_xboole_0(sK2,X0) != k1_xboole_0 ),
% 11.85/2.01      inference(instantiation,[status(thm)],[c_5]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34075,plain,
% 11.85/2.01      ( r1_tarski(sK2,k4_xboole_0(sK2,k1_xboole_0))
% 11.85/2.01      | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0 ),
% 11.85/2.01      inference(instantiation,[status(thm)],[c_13462]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34326,plain,
% 11.85/2.01      ( ~ r1_tarski(sK2,k4_xboole_0(sK2,k1_xboole_0))
% 11.85/2.01      | k4_xboole_0(sK2,k1_xboole_0) = sK2 ),
% 11.85/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_34221]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_7,plain,
% 11.85/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.85/2.01      inference(cnf_transformation,[],[f32]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34446,plain,
% 11.85/2.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 11.85/2.01      inference(instantiation,[status(thm)],[c_7]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34688,plain,
% 11.85/2.01      ( k4_xboole_0(sK2,k1_xboole_0) = sK2 ),
% 11.85/2.01      inference(global_propositional_subsumption,
% 11.85/2.01                [status(thm)],
% 11.85/2.01                [c_34221,c_34075,c_34326,c_34446]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_11,negated_conjecture,
% 11.85/2.01      ( r1_tarski(sK0,sK1) ),
% 11.85/2.01      inference(cnf_transformation,[],[f27]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_364,plain,
% 11.85/2.01      ( r1_tarski(sK0,sK1) = iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_1223,plain,
% 11.85/2.01      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_364,c_368]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_8,plain,
% 11.85/2.01      ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
% 11.85/2.01      inference(cnf_transformation,[],[f33]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_1349,plain,
% 11.85/2.01      ( k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_1223,c_8]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_9,negated_conjecture,
% 11.85/2.01      ( k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))) != k2_zfmisc_1(sK0,sK2) ),
% 11.85/2.01      inference(cnf_transformation,[],[f34]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_3042,plain,
% 11.85/2.01      ( k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) != k2_zfmisc_1(sK0,sK2) ),
% 11.85/2.01      inference(demodulation,[status(thm)],[c_1349,c_9]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_0,plain,
% 11.85/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.85/2.01      inference(cnf_transformation,[],[f30]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_1238,plain,
% 11.85/2.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_1222,c_0]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_3043,plain,
% 11.85/2.01      ( k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)) != k2_zfmisc_1(sK0,sK2) ),
% 11.85/2.01      inference(light_normalisation,[status(thm)],[c_3042,c_1238]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34752,plain,
% 11.85/2.01      ( k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),sK2) != k2_zfmisc_1(sK0,sK2) ),
% 11.85/2.01      inference(demodulation,[status(thm)],[c_34688,c_3043]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_367,plain,
% 11.85/2.01      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_857,plain,
% 11.85/2.01      ( r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_7,c_367]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34134,plain,
% 11.85/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK0
% 11.85/2.01      | r1_tarski(sK0,k4_xboole_0(sK0,k1_xboole_0)) != iProver_top ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_1223,c_1428]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34220,plain,
% 11.85/2.01      ( k4_xboole_0(sK0,k1_xboole_0) = sK0
% 11.85/2.01      | r1_tarski(sK0,k4_xboole_0(sK0,k1_xboole_0)) != iProver_top ),
% 11.85/2.01      inference(light_normalisation,[status(thm)],[c_34134,c_1223]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34686,plain,
% 11.85/2.01      ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_857,c_34220]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34759,plain,
% 11.85/2.01      ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) ),
% 11.85/2.01      inference(light_normalisation,[status(thm)],[c_34752,c_34686]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_34760,plain,
% 11.85/2.01      ( $false ),
% 11.85/2.01      inference(equality_resolution_simp,[status(thm)],[c_34759]) ).
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.85/2.01  
% 11.85/2.01  ------                               Statistics
% 11.85/2.01  
% 11.85/2.01  ------ General
% 11.85/2.01  
% 11.85/2.01  abstr_ref_over_cycles:                  0
% 11.85/2.01  abstr_ref_under_cycles:                 0
% 11.85/2.01  gc_basic_clause_elim:                   0
% 11.85/2.01  forced_gc_time:                         0
% 11.85/2.01  parsing_time:                           0.008
% 11.85/2.01  unif_index_cands_time:                  0.
% 11.85/2.01  unif_index_add_time:                    0.
% 11.85/2.01  orderings_time:                         0.
% 11.85/2.01  out_proof_time:                         0.009
% 11.85/2.01  total_time:                             1.37
% 11.85/2.01  num_of_symbols:                         41
% 11.85/2.01  num_of_terms:                           66173
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing
% 11.85/2.01  
% 11.85/2.01  num_of_splits:                          0
% 11.85/2.01  num_of_split_atoms:                     2
% 11.85/2.01  num_of_reused_defs:                     0
% 11.85/2.01  num_eq_ax_congr_red:                    0
% 11.85/2.01  num_of_sem_filtered_clauses:            1
% 11.85/2.01  num_of_subtypes:                        0
% 11.85/2.01  monotx_restored_types:                  0
% 11.85/2.01  sat_num_of_epr_types:                   0
% 11.85/2.01  sat_num_of_non_cyclic_types:            0
% 11.85/2.01  sat_guarded_non_collapsed_types:        0
% 11.85/2.01  num_pure_diseq_elim:                    0
% 11.85/2.01  simp_replaced_by:                       0
% 11.85/2.01  res_preprocessed:                       55
% 11.85/2.01  prep_upred:                             0
% 11.85/2.01  prep_unflattend:                        0
% 11.85/2.01  smt_new_axioms:                         0
% 11.85/2.01  pred_elim_cands:                        1
% 11.85/2.01  pred_elim:                              0
% 11.85/2.01  pred_elim_cl:                           0
% 11.85/2.01  pred_elim_cycles:                       2
% 11.85/2.01  merged_defs:                            8
% 11.85/2.01  merged_defs_ncl:                        0
% 11.85/2.01  bin_hyper_res:                          8
% 11.85/2.01  prep_cycles:                            4
% 11.85/2.01  pred_elim_time:                         0.
% 11.85/2.01  splitting_time:                         0.
% 11.85/2.01  sem_filter_time:                        0.
% 11.85/2.01  monotx_time:                            0.
% 11.85/2.01  subtype_inf_time:                       0.
% 11.85/2.01  
% 11.85/2.01  ------ Problem properties
% 11.85/2.01  
% 11.85/2.01  clauses:                                11
% 11.85/2.01  conjectures:                            3
% 11.85/2.01  epr:                                    4
% 11.85/2.01  horn:                                   11
% 11.85/2.01  ground:                                 3
% 11.85/2.01  unary:                                  8
% 11.85/2.01  binary:                                 2
% 11.85/2.01  lits:                                   15
% 11.85/2.01  lits_eq:                                7
% 11.85/2.01  fd_pure:                                0
% 11.85/2.01  fd_pseudo:                              0
% 11.85/2.01  fd_cond:                                0
% 11.85/2.01  fd_pseudo_cond:                         1
% 11.85/2.01  ac_symbols:                             0
% 11.85/2.01  
% 11.85/2.01  ------ Propositional Solver
% 11.85/2.01  
% 11.85/2.01  prop_solver_calls:                      32
% 11.85/2.01  prop_fast_solver_calls:                 421
% 11.85/2.01  smt_solver_calls:                       0
% 11.85/2.01  smt_fast_solver_calls:                  0
% 11.85/2.01  prop_num_of_clauses:                    17652
% 11.85/2.01  prop_preprocess_simplified:             14093
% 11.85/2.01  prop_fo_subsumed:                       1
% 11.85/2.01  prop_solver_time:                       0.
% 11.85/2.01  smt_solver_time:                        0.
% 11.85/2.01  smt_fast_solver_time:                   0.
% 11.85/2.01  prop_fast_solver_time:                  0.
% 11.85/2.01  prop_unsat_core_time:                   0.
% 11.85/2.01  
% 11.85/2.01  ------ QBF
% 11.85/2.01  
% 11.85/2.01  qbf_q_res:                              0
% 11.85/2.01  qbf_num_tautologies:                    0
% 11.85/2.01  qbf_prep_cycles:                        0
% 11.85/2.01  
% 11.85/2.01  ------ BMC1
% 11.85/2.01  
% 11.85/2.01  bmc1_current_bound:                     -1
% 11.85/2.01  bmc1_last_solved_bound:                 -1
% 11.85/2.01  bmc1_unsat_core_size:                   -1
% 11.85/2.01  bmc1_unsat_core_parents_size:           -1
% 11.85/2.01  bmc1_merge_next_fun:                    0
% 11.85/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.85/2.01  
% 11.85/2.01  ------ Instantiation
% 11.85/2.01  
% 11.85/2.01  inst_num_of_clauses:                    2254
% 11.85/2.01  inst_num_in_passive:                    560
% 11.85/2.01  inst_num_in_active:                     1046
% 11.85/2.01  inst_num_in_unprocessed:                648
% 11.85/2.01  inst_num_of_loops:                      1100
% 11.85/2.01  inst_num_of_learning_restarts:          0
% 11.85/2.01  inst_num_moves_active_passive:          52
% 11.85/2.01  inst_lit_activity:                      0
% 11.85/2.01  inst_lit_activity_moves:                0
% 11.85/2.01  inst_num_tautologies:                   0
% 11.85/2.01  inst_num_prop_implied:                  0
% 11.85/2.01  inst_num_existing_simplified:           0
% 11.85/2.01  inst_num_eq_res_simplified:             0
% 11.85/2.01  inst_num_child_elim:                    0
% 11.85/2.01  inst_num_of_dismatching_blockings:      2062
% 11.85/2.01  inst_num_of_non_proper_insts:           3564
% 11.85/2.01  inst_num_of_duplicates:                 0
% 11.85/2.01  inst_inst_num_from_inst_to_res:         0
% 11.85/2.01  inst_dismatching_checking_time:         0.
% 11.85/2.01  
% 11.85/2.01  ------ Resolution
% 11.85/2.01  
% 11.85/2.01  res_num_of_clauses:                     0
% 11.85/2.01  res_num_in_passive:                     0
% 11.85/2.01  res_num_in_active:                      0
% 11.85/2.01  res_num_of_loops:                       59
% 11.85/2.01  res_forward_subset_subsumed:            216
% 11.85/2.01  res_backward_subset_subsumed:           0
% 11.85/2.01  res_forward_subsumed:                   0
% 11.85/2.01  res_backward_subsumed:                  0
% 11.85/2.01  res_forward_subsumption_resolution:     0
% 11.85/2.01  res_backward_subsumption_resolution:    0
% 11.85/2.01  res_clause_to_clause_subsumption:       26352
% 11.85/2.01  res_orphan_elimination:                 0
% 11.85/2.01  res_tautology_del:                      252
% 11.85/2.01  res_num_eq_res_simplified:              0
% 11.85/2.01  res_num_sel_changes:                    0
% 11.85/2.01  res_moves_from_active_to_pass:          0
% 11.85/2.01  
% 11.85/2.01  ------ Superposition
% 11.85/2.01  
% 11.85/2.01  sup_time_total:                         0.
% 11.85/2.01  sup_time_generating:                    0.
% 11.85/2.01  sup_time_sim_full:                      0.
% 11.85/2.01  sup_time_sim_immed:                     0.
% 11.85/2.01  
% 11.85/2.01  sup_num_of_clauses:                     4790
% 11.85/2.01  sup_num_in_active:                      122
% 11.85/2.01  sup_num_in_passive:                     4668
% 11.85/2.01  sup_num_of_loops:                       219
% 11.85/2.01  sup_fw_superposition:                   4369
% 11.85/2.01  sup_bw_superposition:                   4540
% 11.85/2.01  sup_immediate_simplified:               3310
% 11.85/2.01  sup_given_eliminated:                   1
% 11.85/2.01  comparisons_done:                       0
% 11.85/2.01  comparisons_avoided:                    0
% 11.85/2.01  
% 11.85/2.01  ------ Simplifications
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  sim_fw_subset_subsumed:                 1
% 11.85/2.01  sim_bw_subset_subsumed:                 2
% 11.85/2.01  sim_fw_subsumed:                        410
% 11.85/2.01  sim_bw_subsumed:                        250
% 11.85/2.01  sim_fw_subsumption_res:                 0
% 11.85/2.01  sim_bw_subsumption_res:                 0
% 11.85/2.01  sim_tautology_del:                      0
% 11.85/2.01  sim_eq_tautology_del:                   715
% 11.85/2.01  sim_eq_res_simp:                        6
% 11.85/2.01  sim_fw_demodulated:                     1910
% 11.85/2.01  sim_bw_demodulated:                     135
% 11.85/2.01  sim_light_normalised:                   1079
% 11.85/2.01  sim_joinable_taut:                      0
% 11.85/2.01  sim_joinable_simp:                      0
% 11.85/2.01  sim_ac_normalised:                      0
% 11.85/2.01  sim_smt_subsumption:                    0
% 11.85/2.01  
%------------------------------------------------------------------------------
