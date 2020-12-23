%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:03 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 233 expanded)
%              Number of clauses        :   29 (  71 expanded)
%              Number of leaves         :   10 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  129 ( 414 expanded)
%              Number of equality atoms :   45 ( 183 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) )
   => ( r1_xboole_0(sK2,sK3)
      & ~ r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( r1_xboole_0(sK2,sK3)
    & ~ r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f23])).

fof(f39,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f33,f36,f36,f36,f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f21])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f38,plain,(
    ~ r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ~ r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
    inference(definition_unfolding,[],[f38,f36])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_614,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_620,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1322,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_614,c_620])).

cnf(c_1393,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1322,c_10])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1399,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) ),
    inference(superposition,[status(thm)],[c_1393,c_8])).

cnf(c_1394,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1393,c_1322])).

cnf(c_1405,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1399,c_1394])).

cnf(c_1632,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_10,c_1405])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_617,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_616,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2661,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_616])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1323,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1324,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0
    | r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_2846,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2661,c_1324,c_1394])).

cnf(c_2853,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_2846])).

cnf(c_2997,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2853,c_620])).

cnf(c_3054,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1632,c_2997])).

cnf(c_621,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3068,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3054,c_621])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_613,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7401,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3068,c_613])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:19:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.94/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.02  
% 2.94/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/1.02  
% 2.94/1.02  ------  iProver source info
% 2.94/1.02  
% 2.94/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.94/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/1.02  git: non_committed_changes: false
% 2.94/1.02  git: last_make_outside_of_git: false
% 2.94/1.02  
% 2.94/1.02  ------ 
% 2.94/1.02  
% 2.94/1.02  ------ Input Options
% 2.94/1.02  
% 2.94/1.02  --out_options                           all
% 2.94/1.02  --tptp_safe_out                         true
% 2.94/1.02  --problem_path                          ""
% 2.94/1.02  --include_path                          ""
% 2.94/1.02  --clausifier                            res/vclausify_rel
% 2.94/1.02  --clausifier_options                    ""
% 2.94/1.02  --stdin                                 false
% 2.94/1.02  --stats_out                             all
% 2.94/1.02  
% 2.94/1.02  ------ General Options
% 2.94/1.02  
% 2.94/1.02  --fof                                   false
% 2.94/1.02  --time_out_real                         305.
% 2.94/1.02  --time_out_virtual                      -1.
% 2.94/1.02  --symbol_type_check                     false
% 2.94/1.02  --clausify_out                          false
% 2.94/1.02  --sig_cnt_out                           false
% 2.94/1.02  --trig_cnt_out                          false
% 2.94/1.02  --trig_cnt_out_tolerance                1.
% 2.94/1.02  --trig_cnt_out_sk_spl                   false
% 2.94/1.02  --abstr_cl_out                          false
% 2.94/1.02  
% 2.94/1.02  ------ Global Options
% 2.94/1.02  
% 2.94/1.02  --schedule                              default
% 2.94/1.02  --add_important_lit                     false
% 2.94/1.02  --prop_solver_per_cl                    1000
% 2.94/1.02  --min_unsat_core                        false
% 2.94/1.02  --soft_assumptions                      false
% 2.94/1.02  --soft_lemma_size                       3
% 2.94/1.02  --prop_impl_unit_size                   0
% 2.94/1.02  --prop_impl_unit                        []
% 2.94/1.02  --share_sel_clauses                     true
% 2.94/1.02  --reset_solvers                         false
% 2.94/1.02  --bc_imp_inh                            [conj_cone]
% 2.94/1.02  --conj_cone_tolerance                   3.
% 2.94/1.02  --extra_neg_conj                        none
% 2.94/1.02  --large_theory_mode                     true
% 2.94/1.02  --prolific_symb_bound                   200
% 2.94/1.02  --lt_threshold                          2000
% 2.94/1.02  --clause_weak_htbl                      true
% 2.94/1.02  --gc_record_bc_elim                     false
% 2.94/1.02  
% 2.94/1.02  ------ Preprocessing Options
% 2.94/1.02  
% 2.94/1.02  --preprocessing_flag                    true
% 2.94/1.02  --time_out_prep_mult                    0.1
% 2.94/1.02  --splitting_mode                        input
% 2.94/1.02  --splitting_grd                         true
% 2.94/1.02  --splitting_cvd                         false
% 2.94/1.02  --splitting_cvd_svl                     false
% 2.94/1.02  --splitting_nvd                         32
% 2.94/1.02  --sub_typing                            true
% 2.94/1.02  --prep_gs_sim                           true
% 2.94/1.02  --prep_unflatten                        true
% 2.94/1.02  --prep_res_sim                          true
% 2.94/1.02  --prep_upred                            true
% 2.94/1.02  --prep_sem_filter                       exhaustive
% 2.94/1.02  --prep_sem_filter_out                   false
% 2.94/1.02  --pred_elim                             true
% 2.94/1.02  --res_sim_input                         true
% 2.94/1.02  --eq_ax_congr_red                       true
% 2.94/1.02  --pure_diseq_elim                       true
% 2.94/1.02  --brand_transform                       false
% 2.94/1.02  --non_eq_to_eq                          false
% 2.94/1.02  --prep_def_merge                        true
% 2.94/1.02  --prep_def_merge_prop_impl              false
% 2.94/1.02  --prep_def_merge_mbd                    true
% 2.94/1.02  --prep_def_merge_tr_red                 false
% 2.94/1.02  --prep_def_merge_tr_cl                  false
% 2.94/1.02  --smt_preprocessing                     true
% 2.94/1.02  --smt_ac_axioms                         fast
% 2.94/1.02  --preprocessed_out                      false
% 2.94/1.02  --preprocessed_stats                    false
% 2.94/1.02  
% 2.94/1.02  ------ Abstraction refinement Options
% 2.94/1.02  
% 2.94/1.02  --abstr_ref                             []
% 2.94/1.02  --abstr_ref_prep                        false
% 2.94/1.02  --abstr_ref_until_sat                   false
% 2.94/1.02  --abstr_ref_sig_restrict                funpre
% 2.94/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.02  --abstr_ref_under                       []
% 2.94/1.02  
% 2.94/1.02  ------ SAT Options
% 2.94/1.02  
% 2.94/1.02  --sat_mode                              false
% 2.94/1.02  --sat_fm_restart_options                ""
% 2.94/1.02  --sat_gr_def                            false
% 2.94/1.02  --sat_epr_types                         true
% 2.94/1.02  --sat_non_cyclic_types                  false
% 2.94/1.02  --sat_finite_models                     false
% 2.94/1.02  --sat_fm_lemmas                         false
% 2.94/1.02  --sat_fm_prep                           false
% 2.94/1.02  --sat_fm_uc_incr                        true
% 2.94/1.02  --sat_out_model                         small
% 2.94/1.02  --sat_out_clauses                       false
% 2.94/1.02  
% 2.94/1.02  ------ QBF Options
% 2.94/1.02  
% 2.94/1.02  --qbf_mode                              false
% 2.94/1.02  --qbf_elim_univ                         false
% 2.94/1.02  --qbf_dom_inst                          none
% 2.94/1.02  --qbf_dom_pre_inst                      false
% 2.94/1.02  --qbf_sk_in                             false
% 2.94/1.02  --qbf_pred_elim                         true
% 2.94/1.02  --qbf_split                             512
% 2.94/1.02  
% 2.94/1.02  ------ BMC1 Options
% 2.94/1.02  
% 2.94/1.02  --bmc1_incremental                      false
% 2.94/1.02  --bmc1_axioms                           reachable_all
% 2.94/1.02  --bmc1_min_bound                        0
% 2.94/1.02  --bmc1_max_bound                        -1
% 2.94/1.02  --bmc1_max_bound_default                -1
% 2.94/1.02  --bmc1_symbol_reachability              true
% 2.94/1.02  --bmc1_property_lemmas                  false
% 2.94/1.02  --bmc1_k_induction                      false
% 2.94/1.02  --bmc1_non_equiv_states                 false
% 2.94/1.02  --bmc1_deadlock                         false
% 2.94/1.02  --bmc1_ucm                              false
% 2.94/1.02  --bmc1_add_unsat_core                   none
% 2.94/1.02  --bmc1_unsat_core_children              false
% 2.94/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.02  --bmc1_out_stat                         full
% 2.94/1.02  --bmc1_ground_init                      false
% 2.94/1.02  --bmc1_pre_inst_next_state              false
% 2.94/1.02  --bmc1_pre_inst_state                   false
% 2.94/1.02  --bmc1_pre_inst_reach_state             false
% 2.94/1.02  --bmc1_out_unsat_core                   false
% 2.94/1.02  --bmc1_aig_witness_out                  false
% 2.94/1.02  --bmc1_verbose                          false
% 2.94/1.02  --bmc1_dump_clauses_tptp                false
% 2.94/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.02  --bmc1_dump_file                        -
% 2.94/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.02  --bmc1_ucm_extend_mode                  1
% 2.94/1.02  --bmc1_ucm_init_mode                    2
% 2.94/1.02  --bmc1_ucm_cone_mode                    none
% 2.94/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.02  --bmc1_ucm_relax_model                  4
% 2.94/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.02  --bmc1_ucm_layered_model                none
% 2.94/1.02  --bmc1_ucm_max_lemma_size               10
% 2.94/1.02  
% 2.94/1.02  ------ AIG Options
% 2.94/1.02  
% 2.94/1.02  --aig_mode                              false
% 2.94/1.02  
% 2.94/1.02  ------ Instantiation Options
% 2.94/1.02  
% 2.94/1.02  --instantiation_flag                    true
% 2.94/1.02  --inst_sos_flag                         true
% 2.94/1.02  --inst_sos_phase                        true
% 2.94/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.02  --inst_lit_sel_side                     num_symb
% 2.94/1.02  --inst_solver_per_active                1400
% 2.94/1.02  --inst_solver_calls_frac                1.
% 2.94/1.02  --inst_passive_queue_type               priority_queues
% 2.94/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.02  --inst_passive_queues_freq              [25;2]
% 2.94/1.02  --inst_dismatching                      true
% 2.94/1.02  --inst_eager_unprocessed_to_passive     true
% 2.94/1.02  --inst_prop_sim_given                   true
% 2.94/1.02  --inst_prop_sim_new                     false
% 2.94/1.02  --inst_subs_new                         false
% 2.94/1.02  --inst_eq_res_simp                      false
% 2.94/1.02  --inst_subs_given                       false
% 2.94/1.02  --inst_orphan_elimination               true
% 2.94/1.02  --inst_learning_loop_flag               true
% 2.94/1.02  --inst_learning_start                   3000
% 2.94/1.02  --inst_learning_factor                  2
% 2.94/1.02  --inst_start_prop_sim_after_learn       3
% 2.94/1.02  --inst_sel_renew                        solver
% 2.94/1.02  --inst_lit_activity_flag                true
% 2.94/1.02  --inst_restr_to_given                   false
% 2.94/1.02  --inst_activity_threshold               500
% 2.94/1.02  --inst_out_proof                        true
% 2.94/1.02  
% 2.94/1.02  ------ Resolution Options
% 2.94/1.02  
% 2.94/1.02  --resolution_flag                       true
% 2.94/1.02  --res_lit_sel                           adaptive
% 2.94/1.02  --res_lit_sel_side                      none
% 2.94/1.02  --res_ordering                          kbo
% 2.94/1.02  --res_to_prop_solver                    active
% 2.94/1.02  --res_prop_simpl_new                    false
% 2.94/1.02  --res_prop_simpl_given                  true
% 2.94/1.02  --res_passive_queue_type                priority_queues
% 2.94/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.02  --res_passive_queues_freq               [15;5]
% 2.94/1.02  --res_forward_subs                      full
% 2.94/1.02  --res_backward_subs                     full
% 2.94/1.02  --res_forward_subs_resolution           true
% 2.94/1.02  --res_backward_subs_resolution          true
% 2.94/1.02  --res_orphan_elimination                true
% 2.94/1.02  --res_time_limit                        2.
% 2.94/1.02  --res_out_proof                         true
% 2.94/1.02  
% 2.94/1.02  ------ Superposition Options
% 2.94/1.02  
% 2.94/1.02  --superposition_flag                    true
% 2.94/1.02  --sup_passive_queue_type                priority_queues
% 2.94/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.02  --demod_completeness_check              fast
% 2.94/1.02  --demod_use_ground                      true
% 2.94/1.02  --sup_to_prop_solver                    passive
% 2.94/1.02  --sup_prop_simpl_new                    true
% 2.94/1.02  --sup_prop_simpl_given                  true
% 2.94/1.02  --sup_fun_splitting                     true
% 2.94/1.02  --sup_smt_interval                      50000
% 2.94/1.02  
% 2.94/1.02  ------ Superposition Simplification Setup
% 2.94/1.02  
% 2.94/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.94/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.94/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.94/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.94/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.94/1.02  --sup_immed_triv                        [TrivRules]
% 2.94/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.02  --sup_immed_bw_main                     []
% 2.94/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.94/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.02  --sup_input_bw                          []
% 2.94/1.02  
% 2.94/1.02  ------ Combination Options
% 2.94/1.02  
% 2.94/1.02  --comb_res_mult                         3
% 2.94/1.02  --comb_sup_mult                         2
% 2.94/1.02  --comb_inst_mult                        10
% 2.94/1.02  
% 2.94/1.02  ------ Debug Options
% 2.94/1.02  
% 2.94/1.02  --dbg_backtrace                         false
% 2.94/1.02  --dbg_dump_prop_clauses                 false
% 2.94/1.02  --dbg_dump_prop_clauses_file            -
% 2.94/1.02  --dbg_out_stat                          false
% 2.94/1.02  ------ Parsing...
% 2.94/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/1.02  
% 2.94/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.94/1.02  
% 2.94/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/1.02  
% 2.94/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/1.02  ------ Proving...
% 2.94/1.02  ------ Problem Properties 
% 2.94/1.02  
% 2.94/1.02  
% 2.94/1.02  clauses                                 14
% 2.94/1.02  conjectures                             2
% 2.94/1.02  EPR                                     2
% 2.94/1.02  Horn                                    11
% 2.94/1.02  unary                                   7
% 2.94/1.02  binary                                  6
% 2.94/1.02  lits                                    22
% 2.94/1.02  lits eq                                 7
% 2.94/1.02  fd_pure                                 0
% 2.94/1.02  fd_pseudo                               0
% 2.94/1.02  fd_cond                                 0
% 2.94/1.02  fd_pseudo_cond                          0
% 2.94/1.02  AC symbols                              0
% 2.94/1.02  
% 2.94/1.02  ------ Schedule dynamic 5 is on 
% 2.94/1.02  
% 2.94/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.94/1.02  
% 2.94/1.02  
% 2.94/1.02  ------ 
% 2.94/1.02  Current options:
% 2.94/1.02  ------ 
% 2.94/1.02  
% 2.94/1.02  ------ Input Options
% 2.94/1.02  
% 2.94/1.02  --out_options                           all
% 2.94/1.02  --tptp_safe_out                         true
% 2.94/1.02  --problem_path                          ""
% 2.94/1.02  --include_path                          ""
% 2.94/1.02  --clausifier                            res/vclausify_rel
% 2.94/1.02  --clausifier_options                    ""
% 2.94/1.02  --stdin                                 false
% 2.94/1.02  --stats_out                             all
% 2.94/1.02  
% 2.94/1.02  ------ General Options
% 2.94/1.02  
% 2.94/1.02  --fof                                   false
% 2.94/1.02  --time_out_real                         305.
% 2.94/1.02  --time_out_virtual                      -1.
% 2.94/1.02  --symbol_type_check                     false
% 2.94/1.02  --clausify_out                          false
% 2.94/1.02  --sig_cnt_out                           false
% 2.94/1.02  --trig_cnt_out                          false
% 2.94/1.02  --trig_cnt_out_tolerance                1.
% 2.94/1.02  --trig_cnt_out_sk_spl                   false
% 2.94/1.02  --abstr_cl_out                          false
% 2.94/1.02  
% 2.94/1.02  ------ Global Options
% 2.94/1.02  
% 2.94/1.02  --schedule                              default
% 2.94/1.02  --add_important_lit                     false
% 2.94/1.02  --prop_solver_per_cl                    1000
% 2.94/1.02  --min_unsat_core                        false
% 2.94/1.02  --soft_assumptions                      false
% 2.94/1.02  --soft_lemma_size                       3
% 2.94/1.02  --prop_impl_unit_size                   0
% 2.94/1.02  --prop_impl_unit                        []
% 2.94/1.02  --share_sel_clauses                     true
% 2.94/1.02  --reset_solvers                         false
% 2.94/1.02  --bc_imp_inh                            [conj_cone]
% 2.94/1.02  --conj_cone_tolerance                   3.
% 2.94/1.02  --extra_neg_conj                        none
% 2.94/1.02  --large_theory_mode                     true
% 2.94/1.02  --prolific_symb_bound                   200
% 2.94/1.02  --lt_threshold                          2000
% 2.94/1.02  --clause_weak_htbl                      true
% 2.94/1.02  --gc_record_bc_elim                     false
% 2.94/1.02  
% 2.94/1.02  ------ Preprocessing Options
% 2.94/1.02  
% 2.94/1.02  --preprocessing_flag                    true
% 2.94/1.02  --time_out_prep_mult                    0.1
% 2.94/1.02  --splitting_mode                        input
% 2.94/1.02  --splitting_grd                         true
% 2.94/1.02  --splitting_cvd                         false
% 2.94/1.02  --splitting_cvd_svl                     false
% 2.94/1.02  --splitting_nvd                         32
% 2.94/1.02  --sub_typing                            true
% 2.94/1.02  --prep_gs_sim                           true
% 2.94/1.02  --prep_unflatten                        true
% 2.94/1.02  --prep_res_sim                          true
% 2.94/1.02  --prep_upred                            true
% 2.94/1.02  --prep_sem_filter                       exhaustive
% 2.94/1.02  --prep_sem_filter_out                   false
% 2.94/1.02  --pred_elim                             true
% 2.94/1.02  --res_sim_input                         true
% 2.94/1.02  --eq_ax_congr_red                       true
% 2.94/1.02  --pure_diseq_elim                       true
% 2.94/1.02  --brand_transform                       false
% 2.94/1.02  --non_eq_to_eq                          false
% 2.94/1.02  --prep_def_merge                        true
% 2.94/1.02  --prep_def_merge_prop_impl              false
% 2.94/1.02  --prep_def_merge_mbd                    true
% 2.94/1.02  --prep_def_merge_tr_red                 false
% 2.94/1.02  --prep_def_merge_tr_cl                  false
% 2.94/1.02  --smt_preprocessing                     true
% 2.94/1.02  --smt_ac_axioms                         fast
% 2.94/1.02  --preprocessed_out                      false
% 2.94/1.02  --preprocessed_stats                    false
% 2.94/1.02  
% 2.94/1.02  ------ Abstraction refinement Options
% 2.94/1.02  
% 2.94/1.02  --abstr_ref                             []
% 2.94/1.02  --abstr_ref_prep                        false
% 2.94/1.02  --abstr_ref_until_sat                   false
% 2.94/1.02  --abstr_ref_sig_restrict                funpre
% 2.94/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.02  --abstr_ref_under                       []
% 2.94/1.02  
% 2.94/1.02  ------ SAT Options
% 2.94/1.02  
% 2.94/1.02  --sat_mode                              false
% 2.94/1.02  --sat_fm_restart_options                ""
% 2.94/1.02  --sat_gr_def                            false
% 2.94/1.02  --sat_epr_types                         true
% 2.94/1.02  --sat_non_cyclic_types                  false
% 2.94/1.02  --sat_finite_models                     false
% 2.94/1.02  --sat_fm_lemmas                         false
% 2.94/1.02  --sat_fm_prep                           false
% 2.94/1.02  --sat_fm_uc_incr                        true
% 2.94/1.02  --sat_out_model                         small
% 2.94/1.02  --sat_out_clauses                       false
% 2.94/1.02  
% 2.94/1.02  ------ QBF Options
% 2.94/1.02  
% 2.94/1.02  --qbf_mode                              false
% 2.94/1.02  --qbf_elim_univ                         false
% 2.94/1.02  --qbf_dom_inst                          none
% 2.94/1.02  --qbf_dom_pre_inst                      false
% 2.94/1.02  --qbf_sk_in                             false
% 2.94/1.02  --qbf_pred_elim                         true
% 2.94/1.02  --qbf_split                             512
% 2.94/1.02  
% 2.94/1.02  ------ BMC1 Options
% 2.94/1.02  
% 2.94/1.02  --bmc1_incremental                      false
% 2.94/1.02  --bmc1_axioms                           reachable_all
% 2.94/1.02  --bmc1_min_bound                        0
% 2.94/1.02  --bmc1_max_bound                        -1
% 2.94/1.02  --bmc1_max_bound_default                -1
% 2.94/1.02  --bmc1_symbol_reachability              true
% 2.94/1.02  --bmc1_property_lemmas                  false
% 2.94/1.02  --bmc1_k_induction                      false
% 2.94/1.02  --bmc1_non_equiv_states                 false
% 2.94/1.02  --bmc1_deadlock                         false
% 2.94/1.02  --bmc1_ucm                              false
% 2.94/1.02  --bmc1_add_unsat_core                   none
% 2.94/1.02  --bmc1_unsat_core_children              false
% 2.94/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.02  --bmc1_out_stat                         full
% 2.94/1.02  --bmc1_ground_init                      false
% 2.94/1.02  --bmc1_pre_inst_next_state              false
% 2.94/1.02  --bmc1_pre_inst_state                   false
% 2.94/1.02  --bmc1_pre_inst_reach_state             false
% 2.94/1.02  --bmc1_out_unsat_core                   false
% 2.94/1.02  --bmc1_aig_witness_out                  false
% 2.94/1.02  --bmc1_verbose                          false
% 2.94/1.02  --bmc1_dump_clauses_tptp                false
% 2.94/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.02  --bmc1_dump_file                        -
% 2.94/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.02  --bmc1_ucm_extend_mode                  1
% 2.94/1.02  --bmc1_ucm_init_mode                    2
% 2.94/1.02  --bmc1_ucm_cone_mode                    none
% 2.94/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.02  --bmc1_ucm_relax_model                  4
% 2.94/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.02  --bmc1_ucm_layered_model                none
% 2.94/1.02  --bmc1_ucm_max_lemma_size               10
% 2.94/1.02  
% 2.94/1.02  ------ AIG Options
% 2.94/1.02  
% 2.94/1.02  --aig_mode                              false
% 2.94/1.02  
% 2.94/1.02  ------ Instantiation Options
% 2.94/1.02  
% 2.94/1.02  --instantiation_flag                    true
% 2.94/1.02  --inst_sos_flag                         true
% 2.94/1.02  --inst_sos_phase                        true
% 2.94/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.02  --inst_lit_sel_side                     none
% 2.94/1.02  --inst_solver_per_active                1400
% 2.94/1.02  --inst_solver_calls_frac                1.
% 2.94/1.02  --inst_passive_queue_type               priority_queues
% 2.94/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.02  --inst_passive_queues_freq              [25;2]
% 2.94/1.02  --inst_dismatching                      true
% 2.94/1.02  --inst_eager_unprocessed_to_passive     true
% 2.94/1.02  --inst_prop_sim_given                   true
% 2.94/1.02  --inst_prop_sim_new                     false
% 2.94/1.02  --inst_subs_new                         false
% 2.94/1.02  --inst_eq_res_simp                      false
% 2.94/1.02  --inst_subs_given                       false
% 2.94/1.02  --inst_orphan_elimination               true
% 2.94/1.02  --inst_learning_loop_flag               true
% 2.94/1.02  --inst_learning_start                   3000
% 2.94/1.02  --inst_learning_factor                  2
% 2.94/1.02  --inst_start_prop_sim_after_learn       3
% 2.94/1.02  --inst_sel_renew                        solver
% 2.94/1.02  --inst_lit_activity_flag                true
% 2.94/1.02  --inst_restr_to_given                   false
% 2.94/1.02  --inst_activity_threshold               500
% 2.94/1.02  --inst_out_proof                        true
% 2.94/1.02  
% 2.94/1.02  ------ Resolution Options
% 2.94/1.02  
% 2.94/1.02  --resolution_flag                       false
% 2.94/1.02  --res_lit_sel                           adaptive
% 2.94/1.02  --res_lit_sel_side                      none
% 2.94/1.02  --res_ordering                          kbo
% 2.94/1.02  --res_to_prop_solver                    active
% 2.94/1.02  --res_prop_simpl_new                    false
% 2.94/1.02  --res_prop_simpl_given                  true
% 2.94/1.02  --res_passive_queue_type                priority_queues
% 2.94/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.02  --res_passive_queues_freq               [15;5]
% 2.94/1.02  --res_forward_subs                      full
% 2.94/1.02  --res_backward_subs                     full
% 2.94/1.02  --res_forward_subs_resolution           true
% 2.94/1.02  --res_backward_subs_resolution          true
% 2.94/1.02  --res_orphan_elimination                true
% 2.94/1.02  --res_time_limit                        2.
% 2.94/1.02  --res_out_proof                         true
% 2.94/1.02  
% 2.94/1.02  ------ Superposition Options
% 2.94/1.02  
% 2.94/1.02  --superposition_flag                    true
% 2.94/1.02  --sup_passive_queue_type                priority_queues
% 2.94/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.02  --demod_completeness_check              fast
% 2.94/1.02  --demod_use_ground                      true
% 2.94/1.02  --sup_to_prop_solver                    passive
% 2.94/1.02  --sup_prop_simpl_new                    true
% 2.94/1.02  --sup_prop_simpl_given                  true
% 2.94/1.02  --sup_fun_splitting                     true
% 2.94/1.02  --sup_smt_interval                      50000
% 2.94/1.02  
% 2.94/1.02  ------ Superposition Simplification Setup
% 2.94/1.02  
% 2.94/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.94/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.94/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.94/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.94/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.94/1.02  --sup_immed_triv                        [TrivRules]
% 2.94/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.02  --sup_immed_bw_main                     []
% 2.94/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.94/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.02  --sup_input_bw                          []
% 2.94/1.02  
% 2.94/1.02  ------ Combination Options
% 2.94/1.02  
% 2.94/1.02  --comb_res_mult                         3
% 2.94/1.02  --comb_sup_mult                         2
% 2.94/1.02  --comb_inst_mult                        10
% 2.94/1.02  
% 2.94/1.02  ------ Debug Options
% 2.94/1.02  
% 2.94/1.02  --dbg_backtrace                         false
% 2.94/1.02  --dbg_dump_prop_clauses                 false
% 2.94/1.02  --dbg_dump_prop_clauses_file            -
% 2.94/1.02  --dbg_out_stat                          false
% 2.94/1.02  
% 2.94/1.02  
% 2.94/1.02  
% 2.94/1.02  
% 2.94/1.02  ------ Proving...
% 2.94/1.02  
% 2.94/1.02  
% 2.94/1.02  % SZS status Theorem for theBenchmark.p
% 2.94/1.02  
% 2.94/1.02   Resolution empty clause
% 2.94/1.02  
% 2.94/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/1.02  
% 2.94/1.02  fof(f7,axiom,(
% 2.94/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.02  
% 2.94/1.02  fof(f35,plain,(
% 2.94/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.94/1.02    inference(cnf_transformation,[],[f7])).
% 2.94/1.02  
% 2.94/1.02  fof(f8,axiom,(
% 2.94/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.02  
% 2.94/1.02  fof(f36,plain,(
% 2.94/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.94/1.02    inference(cnf_transformation,[],[f8])).
% 2.94/1.02  
% 2.94/1.02  fof(f47,plain,(
% 2.94/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.94/1.02    inference(definition_unfolding,[],[f35,f36])).
% 2.94/1.02  
% 2.94/1.02  fof(f10,conjecture,(
% 2.94/1.02    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 2.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.02  
% 2.94/1.02  fof(f11,negated_conjecture,(
% 2.94/1.02    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 2.94/1.02    inference(negated_conjecture,[],[f10])).
% 2.94/1.02  
% 2.94/1.02  fof(f17,plain,(
% 2.94/1.02    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 2.94/1.02    inference(ennf_transformation,[],[f11])).
% 2.94/1.02  
% 2.94/1.02  fof(f23,plain,(
% 2.94/1.02    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2))) => (r1_xboole_0(sK2,sK3) & ~r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)))),
% 2.94/1.02    introduced(choice_axiom,[])).
% 2.94/1.02  
% 2.94/1.02  fof(f24,plain,(
% 2.94/1.02    r1_xboole_0(sK2,sK3) & ~r1_xboole_0(sK2,k3_xboole_0(sK3,sK4))),
% 2.94/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f23])).
% 2.94/1.02  
% 2.94/1.02  fof(f39,plain,(
% 2.94/1.02    r1_xboole_0(sK2,sK3)),
% 2.94/1.02    inference(cnf_transformation,[],[f24])).
% 2.94/1.02  
% 2.94/1.02  fof(f1,axiom,(
% 2.94/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.02  
% 2.94/1.02  fof(f18,plain,(
% 2.94/1.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.94/1.02    inference(nnf_transformation,[],[f1])).
% 2.94/1.02  
% 2.94/1.02  fof(f25,plain,(
% 2.94/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.94/1.02    inference(cnf_transformation,[],[f18])).
% 2.94/1.02  
% 2.94/1.02  fof(f41,plain,(
% 2.94/1.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.94/1.02    inference(definition_unfolding,[],[f25,f36])).
% 2.94/1.02  
% 2.94/1.02  fof(f5,axiom,(
% 2.94/1.02    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.02  
% 2.94/1.02  fof(f33,plain,(
% 2.94/1.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.94/1.02    inference(cnf_transformation,[],[f5])).
% 2.94/1.02  
% 2.94/1.02  fof(f45,plain,(
% 2.94/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 2.94/1.02    inference(definition_unfolding,[],[f33,f36,f36,f36,f36])).
% 2.94/1.02  
% 2.94/1.02  fof(f3,axiom,(
% 2.94/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.02  
% 2.94/1.02  fof(f13,plain,(
% 2.94/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.94/1.02    inference(rectify,[],[f3])).
% 2.94/1.02  
% 2.94/1.02  fof(f15,plain,(
% 2.94/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.94/1.02    inference(ennf_transformation,[],[f13])).
% 2.94/1.02  
% 2.94/1.02  fof(f19,plain,(
% 2.94/1.02    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.94/1.02    introduced(choice_axiom,[])).
% 2.94/1.02  
% 2.94/1.02  fof(f20,plain,(
% 2.94/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.94/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).
% 2.94/1.02  
% 2.94/1.02  fof(f28,plain,(
% 2.94/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.94/1.02    inference(cnf_transformation,[],[f20])).
% 2.94/1.02  
% 2.94/1.02  fof(f4,axiom,(
% 2.94/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.02  
% 2.94/1.02  fof(f14,plain,(
% 2.94/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.94/1.02    inference(rectify,[],[f4])).
% 2.94/1.02  
% 2.94/1.02  fof(f16,plain,(
% 2.94/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.94/1.02    inference(ennf_transformation,[],[f14])).
% 2.94/1.02  
% 2.94/1.02  fof(f21,plain,(
% 2.94/1.02    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 2.94/1.02    introduced(choice_axiom,[])).
% 2.94/1.02  
% 2.94/1.02  fof(f22,plain,(
% 2.94/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.94/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f21])).
% 2.94/1.02  
% 2.94/1.02  fof(f32,plain,(
% 2.94/1.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.94/1.02    inference(cnf_transformation,[],[f22])).
% 2.94/1.02  
% 2.94/1.02  fof(f43,plain,(
% 2.94/1.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.94/1.02    inference(definition_unfolding,[],[f32,f36])).
% 2.94/1.02  
% 2.94/1.02  fof(f26,plain,(
% 2.94/1.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.94/1.02    inference(cnf_transformation,[],[f18])).
% 2.94/1.02  
% 2.94/1.02  fof(f40,plain,(
% 2.94/1.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.94/1.02    inference(definition_unfolding,[],[f26,f36])).
% 2.94/1.02  
% 2.94/1.02  fof(f38,plain,(
% 2.94/1.02    ~r1_xboole_0(sK2,k3_xboole_0(sK3,sK4))),
% 2.94/1.02    inference(cnf_transformation,[],[f24])).
% 2.94/1.02  
% 2.94/1.02  fof(f49,plain,(
% 2.94/1.02    ~r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))),
% 2.94/1.02    inference(definition_unfolding,[],[f38,f36])).
% 2.94/1.02  
% 2.94/1.02  cnf(c_10,plain,
% 2.94/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.94/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_12,negated_conjecture,
% 2.94/1.02      ( r1_xboole_0(sK2,sK3) ),
% 2.94/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_614,plain,
% 2.94/1.02      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 2.94/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_1,plain,
% 2.94/1.02      ( ~ r1_xboole_0(X0,X1)
% 2.94/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 2.94/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_620,plain,
% 2.94/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 2.94/1.02      | r1_xboole_0(X0,X1) != iProver_top ),
% 2.94/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_1322,plain,
% 2.94/1.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 2.94/1.02      inference(superposition,[status(thm)],[c_614,c_620]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_1393,plain,
% 2.94/1.02      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK3) ),
% 2.94/1.02      inference(superposition,[status(thm)],[c_1322,c_10]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_8,plain,
% 2.94/1.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 2.94/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_1399,plain,
% 2.94/1.02      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) ),
% 2.94/1.02      inference(superposition,[status(thm)],[c_1393,c_8]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_1394,plain,
% 2.94/1.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 2.94/1.02      inference(demodulation,[status(thm)],[c_1393,c_1322]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_1405,plain,
% 2.94/1.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 2.94/1.02      inference(light_normalisation,[status(thm)],[c_1399,c_1394]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_1632,plain,
% 2.94/1.02      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,X0))) ),
% 2.94/1.02      inference(superposition,[status(thm)],[c_10,c_1405]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_5,plain,
% 2.94/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 2.94/1.02      inference(cnf_transformation,[],[f28]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_617,plain,
% 2.94/1.02      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.94/1.02      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.94/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_6,plain,
% 2.94/1.02      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 2.94/1.02      | ~ r1_xboole_0(X1,X2) ),
% 2.94/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_616,plain,
% 2.94/1.02      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 2.94/1.02      | r1_xboole_0(X1,X2) != iProver_top ),
% 2.94/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_2661,plain,
% 2.94/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 2.94/1.02      | r1_xboole_0(sK2,k1_xboole_0) != iProver_top ),
% 2.94/1.02      inference(superposition,[status(thm)],[c_1394,c_616]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_0,plain,
% 2.94/1.02      ( r1_xboole_0(X0,X1)
% 2.94/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 2.94/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_1323,plain,
% 2.94/1.02      ( r1_xboole_0(sK2,k1_xboole_0)
% 2.94/1.02      | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0 ),
% 2.94/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_1324,plain,
% 2.94/1.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0
% 2.94/1.02      | r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
% 2.94/1.02      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_2846,plain,
% 2.94/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.94/1.02      inference(global_propositional_subsumption,
% 2.94/1.02                [status(thm)],
% 2.94/1.02                [c_2661,c_1324,c_1394]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_2853,plain,
% 2.94/1.02      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 2.94/1.02      inference(superposition,[status(thm)],[c_617,c_2846]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_2997,plain,
% 2.94/1.02      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 2.94/1.02      inference(superposition,[status(thm)],[c_2853,c_620]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_3054,plain,
% 2.94/1.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,X0))) = k1_xboole_0 ),
% 2.94/1.02      inference(demodulation,[status(thm)],[c_1632,c_2997]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_621,plain,
% 2.94/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 2.94/1.02      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.94/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_3068,plain,
% 2.94/1.02      ( r1_xboole_0(sK2,k4_xboole_0(sK3,X0)) = iProver_top ),
% 2.94/1.02      inference(superposition,[status(thm)],[c_3054,c_621]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_13,negated_conjecture,
% 2.94/1.02      ( ~ r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
% 2.94/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_613,plain,
% 2.94/1.02      ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top ),
% 2.94/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.94/1.02  
% 2.94/1.02  cnf(c_7401,plain,
% 2.94/1.02      ( $false ),
% 2.94/1.02      inference(superposition,[status(thm)],[c_3068,c_613]) ).
% 2.94/1.02  
% 2.94/1.02  
% 2.94/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/1.02  
% 2.94/1.02  ------                               Statistics
% 2.94/1.02  
% 2.94/1.02  ------ General
% 2.94/1.02  
% 2.94/1.02  abstr_ref_over_cycles:                  0
% 2.94/1.02  abstr_ref_under_cycles:                 0
% 2.94/1.02  gc_basic_clause_elim:                   0
% 2.94/1.02  forced_gc_time:                         0
% 2.94/1.02  parsing_time:                           0.01
% 2.94/1.02  unif_index_cands_time:                  0.
% 2.94/1.02  unif_index_add_time:                    0.
% 2.94/1.02  orderings_time:                         0.
% 2.94/1.02  out_proof_time:                         0.007
% 2.94/1.02  total_time:                             0.312
% 2.94/1.02  num_of_symbols:                         41
% 2.94/1.02  num_of_terms:                           10376
% 2.94/1.02  
% 2.94/1.02  ------ Preprocessing
% 2.94/1.02  
% 2.94/1.02  num_of_splits:                          0
% 2.94/1.02  num_of_split_atoms:                     0
% 2.94/1.02  num_of_reused_defs:                     0
% 2.94/1.02  num_eq_ax_congr_red:                    8
% 2.94/1.02  num_of_sem_filtered_clauses:            1
% 2.94/1.02  num_of_subtypes:                        0
% 2.94/1.02  monotx_restored_types:                  0
% 2.94/1.02  sat_num_of_epr_types:                   0
% 2.94/1.02  sat_num_of_non_cyclic_types:            0
% 2.94/1.02  sat_guarded_non_collapsed_types:        0
% 2.94/1.02  num_pure_diseq_elim:                    0
% 2.94/1.02  simp_replaced_by:                       0
% 2.94/1.02  res_preprocessed:                       55
% 2.94/1.02  prep_upred:                             0
% 2.94/1.02  prep_unflattend:                        30
% 2.94/1.02  smt_new_axioms:                         0
% 2.94/1.02  pred_elim_cands:                        2
% 2.94/1.02  pred_elim:                              0
% 2.94/1.02  pred_elim_cl:                           0
% 2.94/1.02  pred_elim_cycles:                       1
% 2.94/1.02  merged_defs:                            6
% 2.94/1.02  merged_defs_ncl:                        0
% 2.94/1.02  bin_hyper_res:                          6
% 2.94/1.02  prep_cycles:                            3
% 2.94/1.02  pred_elim_time:                         0.005
% 2.94/1.02  splitting_time:                         0.
% 2.94/1.02  sem_filter_time:                        0.
% 2.94/1.02  monotx_time:                            0.001
% 2.94/1.02  subtype_inf_time:                       0.
% 2.94/1.02  
% 2.94/1.02  ------ Problem properties
% 2.94/1.02  
% 2.94/1.02  clauses:                                14
% 2.94/1.02  conjectures:                            2
% 2.94/1.02  epr:                                    2
% 2.94/1.02  horn:                                   11
% 2.94/1.02  ground:                                 2
% 2.94/1.02  unary:                                  7
% 2.94/1.02  binary:                                 6
% 2.94/1.02  lits:                                   22
% 2.94/1.02  lits_eq:                                7
% 2.94/1.02  fd_pure:                                0
% 2.94/1.02  fd_pseudo:                              0
% 2.94/1.02  fd_cond:                                0
% 2.94/1.02  fd_pseudo_cond:                         0
% 2.94/1.02  ac_symbols:                             0
% 2.94/1.02  
% 2.94/1.02  ------ Propositional Solver
% 2.94/1.02  
% 2.94/1.02  prop_solver_calls:                      25
% 2.94/1.02  prop_fast_solver_calls:                 392
% 2.94/1.02  smt_solver_calls:                       0
% 2.94/1.02  smt_fast_solver_calls:                  0
% 2.94/1.02  prop_num_of_clauses:                    3104
% 2.94/1.02  prop_preprocess_simplified:             6737
% 2.94/1.02  prop_fo_subsumed:                       6
% 2.94/1.02  prop_solver_time:                       0.
% 2.94/1.02  smt_solver_time:                        0.
% 2.94/1.02  smt_fast_solver_time:                   0.
% 2.94/1.02  prop_fast_solver_time:                  0.
% 2.94/1.02  prop_unsat_core_time:                   0.
% 2.94/1.02  
% 2.94/1.02  ------ QBF
% 2.94/1.02  
% 2.94/1.02  qbf_q_res:                              0
% 2.94/1.02  qbf_num_tautologies:                    0
% 2.94/1.02  qbf_prep_cycles:                        0
% 2.94/1.02  
% 2.94/1.02  ------ BMC1
% 2.94/1.02  
% 2.94/1.02  bmc1_current_bound:                     -1
% 2.94/1.02  bmc1_last_solved_bound:                 -1
% 2.94/1.02  bmc1_unsat_core_size:                   -1
% 2.94/1.02  bmc1_unsat_core_parents_size:           -1
% 2.94/1.02  bmc1_merge_next_fun:                    0
% 2.94/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.94/1.02  
% 2.94/1.02  ------ Instantiation
% 2.94/1.02  
% 2.94/1.02  inst_num_of_clauses:                    901
% 2.94/1.02  inst_num_in_passive:                    169
% 2.94/1.02  inst_num_in_active:                     390
% 2.94/1.02  inst_num_in_unprocessed:                342
% 2.94/1.02  inst_num_of_loops:                      430
% 2.94/1.02  inst_num_of_learning_restarts:          0
% 2.94/1.02  inst_num_moves_active_passive:          40
% 2.94/1.02  inst_lit_activity:                      0
% 2.94/1.02  inst_lit_activity_moves:                0
% 2.94/1.02  inst_num_tautologies:                   0
% 2.94/1.02  inst_num_prop_implied:                  0
% 2.94/1.02  inst_num_existing_simplified:           0
% 2.94/1.02  inst_num_eq_res_simplified:             0
% 2.94/1.02  inst_num_child_elim:                    0
% 2.94/1.02  inst_num_of_dismatching_blockings:      244
% 2.94/1.02  inst_num_of_non_proper_insts:           821
% 2.94/1.02  inst_num_of_duplicates:                 0
% 2.94/1.02  inst_inst_num_from_inst_to_res:         0
% 2.94/1.02  inst_dismatching_checking_time:         0.
% 2.94/1.02  
% 2.94/1.02  ------ Resolution
% 2.94/1.02  
% 2.94/1.02  res_num_of_clauses:                     0
% 2.94/1.02  res_num_in_passive:                     0
% 2.94/1.02  res_num_in_active:                      0
% 2.94/1.02  res_num_of_loops:                       58
% 2.94/1.02  res_forward_subset_subsumed:            114
% 2.94/1.02  res_backward_subset_subsumed:           0
% 2.94/1.02  res_forward_subsumed:                   0
% 2.94/1.02  res_backward_subsumed:                  0
% 2.94/1.02  res_forward_subsumption_resolution:     0
% 2.94/1.02  res_backward_subsumption_resolution:    0
% 2.94/1.02  res_clause_to_clause_subsumption:       2185
% 2.94/1.02  res_orphan_elimination:                 0
% 2.94/1.02  res_tautology_del:                      143
% 2.94/1.02  res_num_eq_res_simplified:              0
% 2.94/1.02  res_num_sel_changes:                    0
% 2.94/1.02  res_moves_from_active_to_pass:          0
% 2.94/1.02  
% 2.94/1.02  ------ Superposition
% 2.94/1.02  
% 2.94/1.02  sup_time_total:                         0.
% 2.94/1.02  sup_time_generating:                    0.
% 2.94/1.02  sup_time_sim_full:                      0.
% 2.94/1.02  sup_time_sim_immed:                     0.
% 2.94/1.02  
% 2.94/1.02  sup_num_of_clauses:                     197
% 2.94/1.02  sup_num_in_active:                      40
% 2.94/1.02  sup_num_in_passive:                     157
% 2.94/1.02  sup_num_of_loops:                       85
% 2.94/1.02  sup_fw_superposition:                   504
% 2.94/1.02  sup_bw_superposition:                   607
% 2.94/1.02  sup_immediate_simplified:               535
% 2.94/1.02  sup_given_eliminated:                   25
% 2.94/1.02  comparisons_done:                       0
% 2.94/1.02  comparisons_avoided:                    0
% 2.94/1.02  
% 2.94/1.02  ------ Simplifications
% 2.94/1.02  
% 2.94/1.02  
% 2.94/1.02  sim_fw_subset_subsumed:                 25
% 2.94/1.02  sim_bw_subset_subsumed:                 2
% 2.94/1.02  sim_fw_subsumed:                        107
% 2.94/1.02  sim_bw_subsumed:                        74
% 2.94/1.02  sim_fw_subsumption_res:                 0
% 2.94/1.02  sim_bw_subsumption_res:                 0
% 2.94/1.02  sim_tautology_del:                      14
% 2.94/1.02  sim_eq_tautology_del:                   198
% 2.94/1.02  sim_eq_res_simp:                        8
% 2.94/1.02  sim_fw_demodulated:                     348
% 2.94/1.02  sim_bw_demodulated:                     29
% 2.94/1.02  sim_light_normalised:                   288
% 2.94/1.02  sim_joinable_taut:                      0
% 2.94/1.02  sim_joinable_simp:                      0
% 2.94/1.02  sim_ac_normalised:                      0
% 2.94/1.02  sim_smt_subsumption:                    0
% 2.94/1.02  
%------------------------------------------------------------------------------
