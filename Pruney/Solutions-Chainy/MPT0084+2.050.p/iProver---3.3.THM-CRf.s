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
% DateTime   : Thu Dec  3 11:24:20 EST 2020

% Result     : Theorem 43.43s
% Output     : CNFRefutation 43.43s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 146 expanded)
%              Number of clauses        :   46 (  69 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  157 ( 309 expanded)
%              Number of equality atoms :   62 (  87 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f32,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_320,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_315,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_317,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_966,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_317])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_323,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3537,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,k3_xboole_0(X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_966,c_323])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_319,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1049,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_xboole_0(X0,X3) = iProver_top
    | r1_xboole_0(k3_xboole_0(X1,X2),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_319,c_317])).

cnf(c_7813,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_xboole_0(X3,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X3,X4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3537,c_1049])).

cnf(c_151691,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(sK0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_315,c_7813])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_316,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k3_xboole_0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_151997,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),sK2) != iProver_top
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),sK1) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(sK0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_151691,c_316])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_314,plain,
    ( r1_tarski(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_321,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_673,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_320,c_321])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_322,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_956,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_322])).

cnf(c_3134,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = X2
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_321])).

cnf(c_3817,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,X0),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_314,c_3134])).

cnf(c_5,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_318,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_955,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_318,c_322])).

cnf(c_3925,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3817,c_955])).

cnf(c_154589,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),sK1) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(sK0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_151997,c_3925])).

cnf(c_154595,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_154589])).

cnf(c_4848,plain,
    ( r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top
    | r1_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3537,c_316])).

cnf(c_155116,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_154595,c_4848])).

cnf(c_155125,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_155116])).

cnf(c_401,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK0),sK0)
    | ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_402,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK0),sK0) = iProver_top
    | r1_xboole_0(sK0,k3_xboole_0(sK1,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_353,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK0),sK0)
    | r1_xboole_0(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_354,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK0),sK0) != iProver_top
    | r1_xboole_0(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_338,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | r1_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_339,plain,
    ( r1_xboole_0(sK1,sK0) != iProver_top
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,plain,
    ( r1_xboole_0(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_155125,c_402,c_354,c_339,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.43/5.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.43/5.99  
% 43.43/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.43/5.99  
% 43.43/5.99  ------  iProver source info
% 43.43/5.99  
% 43.43/5.99  git: date: 2020-06-30 10:37:57 +0100
% 43.43/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.43/5.99  git: non_committed_changes: false
% 43.43/5.99  git: last_make_outside_of_git: false
% 43.43/5.99  
% 43.43/5.99  ------ 
% 43.43/5.99  
% 43.43/5.99  ------ Input Options
% 43.43/5.99  
% 43.43/5.99  --out_options                           all
% 43.43/5.99  --tptp_safe_out                         true
% 43.43/5.99  --problem_path                          ""
% 43.43/5.99  --include_path                          ""
% 43.43/5.99  --clausifier                            res/vclausify_rel
% 43.43/5.99  --clausifier_options                    ""
% 43.43/5.99  --stdin                                 false
% 43.43/5.99  --stats_out                             all
% 43.43/5.99  
% 43.43/5.99  ------ General Options
% 43.43/5.99  
% 43.43/5.99  --fof                                   false
% 43.43/5.99  --time_out_real                         305.
% 43.43/5.99  --time_out_virtual                      -1.
% 43.43/5.99  --symbol_type_check                     false
% 43.43/5.99  --clausify_out                          false
% 43.43/5.99  --sig_cnt_out                           false
% 43.43/5.99  --trig_cnt_out                          false
% 43.43/5.99  --trig_cnt_out_tolerance                1.
% 43.43/5.99  --trig_cnt_out_sk_spl                   false
% 43.43/5.99  --abstr_cl_out                          false
% 43.43/5.99  
% 43.43/5.99  ------ Global Options
% 43.43/5.99  
% 43.43/5.99  --schedule                              default
% 43.43/5.99  --add_important_lit                     false
% 43.43/5.99  --prop_solver_per_cl                    1000
% 43.43/5.99  --min_unsat_core                        false
% 43.43/5.99  --soft_assumptions                      false
% 43.43/5.99  --soft_lemma_size                       3
% 43.43/5.99  --prop_impl_unit_size                   0
% 43.43/5.99  --prop_impl_unit                        []
% 43.43/5.99  --share_sel_clauses                     true
% 43.43/5.99  --reset_solvers                         false
% 43.43/5.99  --bc_imp_inh                            [conj_cone]
% 43.43/5.99  --conj_cone_tolerance                   3.
% 43.43/5.99  --extra_neg_conj                        none
% 43.43/5.99  --large_theory_mode                     true
% 43.43/5.99  --prolific_symb_bound                   200
% 43.43/5.99  --lt_threshold                          2000
% 43.43/5.99  --clause_weak_htbl                      true
% 43.43/5.99  --gc_record_bc_elim                     false
% 43.43/5.99  
% 43.43/5.99  ------ Preprocessing Options
% 43.43/5.99  
% 43.43/5.99  --preprocessing_flag                    true
% 43.43/5.99  --time_out_prep_mult                    0.1
% 43.43/5.99  --splitting_mode                        input
% 43.43/5.99  --splitting_grd                         true
% 43.43/5.99  --splitting_cvd                         false
% 43.43/5.99  --splitting_cvd_svl                     false
% 43.43/5.99  --splitting_nvd                         32
% 43.43/5.99  --sub_typing                            true
% 43.43/5.99  --prep_gs_sim                           true
% 43.43/5.99  --prep_unflatten                        true
% 43.43/5.99  --prep_res_sim                          true
% 43.43/5.99  --prep_upred                            true
% 43.43/5.99  --prep_sem_filter                       exhaustive
% 43.43/5.99  --prep_sem_filter_out                   false
% 43.43/5.99  --pred_elim                             true
% 43.43/5.99  --res_sim_input                         true
% 43.43/5.99  --eq_ax_congr_red                       true
% 43.43/5.99  --pure_diseq_elim                       true
% 43.43/5.99  --brand_transform                       false
% 43.43/5.99  --non_eq_to_eq                          false
% 43.43/5.99  --prep_def_merge                        true
% 43.43/5.99  --prep_def_merge_prop_impl              false
% 43.43/5.99  --prep_def_merge_mbd                    true
% 43.43/5.99  --prep_def_merge_tr_red                 false
% 43.43/5.99  --prep_def_merge_tr_cl                  false
% 43.43/5.99  --smt_preprocessing                     true
% 43.43/5.99  --smt_ac_axioms                         fast
% 43.43/5.99  --preprocessed_out                      false
% 43.43/5.99  --preprocessed_stats                    false
% 43.43/5.99  
% 43.43/5.99  ------ Abstraction refinement Options
% 43.43/5.99  
% 43.43/5.99  --abstr_ref                             []
% 43.43/5.99  --abstr_ref_prep                        false
% 43.43/5.99  --abstr_ref_until_sat                   false
% 43.43/5.99  --abstr_ref_sig_restrict                funpre
% 43.43/5.99  --abstr_ref_af_restrict_to_split_sk     false
% 43.43/5.99  --abstr_ref_under                       []
% 43.43/5.99  
% 43.43/5.99  ------ SAT Options
% 43.43/5.99  
% 43.43/5.99  --sat_mode                              false
% 43.43/5.99  --sat_fm_restart_options                ""
% 43.43/5.99  --sat_gr_def                            false
% 43.43/5.99  --sat_epr_types                         true
% 43.43/5.99  --sat_non_cyclic_types                  false
% 43.43/5.99  --sat_finite_models                     false
% 43.43/5.99  --sat_fm_lemmas                         false
% 43.43/5.99  --sat_fm_prep                           false
% 43.43/5.99  --sat_fm_uc_incr                        true
% 43.43/5.99  --sat_out_model                         small
% 43.43/5.99  --sat_out_clauses                       false
% 43.43/5.99  
% 43.43/5.99  ------ QBF Options
% 43.43/5.99  
% 43.43/5.99  --qbf_mode                              false
% 43.43/5.99  --qbf_elim_univ                         false
% 43.43/5.99  --qbf_dom_inst                          none
% 43.43/5.99  --qbf_dom_pre_inst                      false
% 43.43/5.99  --qbf_sk_in                             false
% 43.43/5.99  --qbf_pred_elim                         true
% 43.43/5.99  --qbf_split                             512
% 43.43/5.99  
% 43.43/5.99  ------ BMC1 Options
% 43.43/5.99  
% 43.43/5.99  --bmc1_incremental                      false
% 43.43/5.99  --bmc1_axioms                           reachable_all
% 43.43/5.99  --bmc1_min_bound                        0
% 43.43/5.99  --bmc1_max_bound                        -1
% 43.43/5.99  --bmc1_max_bound_default                -1
% 43.43/5.99  --bmc1_symbol_reachability              true
% 43.43/5.99  --bmc1_property_lemmas                  false
% 43.43/5.99  --bmc1_k_induction                      false
% 43.43/5.99  --bmc1_non_equiv_states                 false
% 43.43/5.99  --bmc1_deadlock                         false
% 43.43/5.99  --bmc1_ucm                              false
% 43.43/5.99  --bmc1_add_unsat_core                   none
% 43.43/5.99  --bmc1_unsat_core_children              false
% 43.43/5.99  --bmc1_unsat_core_extrapolate_axioms    false
% 43.43/5.99  --bmc1_out_stat                         full
% 43.43/5.99  --bmc1_ground_init                      false
% 43.43/5.99  --bmc1_pre_inst_next_state              false
% 43.43/5.99  --bmc1_pre_inst_state                   false
% 43.43/5.99  --bmc1_pre_inst_reach_state             false
% 43.43/5.99  --bmc1_out_unsat_core                   false
% 43.43/5.99  --bmc1_aig_witness_out                  false
% 43.43/5.99  --bmc1_verbose                          false
% 43.43/5.99  --bmc1_dump_clauses_tptp                false
% 43.43/5.99  --bmc1_dump_unsat_core_tptp             false
% 43.43/5.99  --bmc1_dump_file                        -
% 43.43/5.99  --bmc1_ucm_expand_uc_limit              128
% 43.43/5.99  --bmc1_ucm_n_expand_iterations          6
% 43.43/5.99  --bmc1_ucm_extend_mode                  1
% 43.43/5.99  --bmc1_ucm_init_mode                    2
% 43.43/5.99  --bmc1_ucm_cone_mode                    none
% 43.43/5.99  --bmc1_ucm_reduced_relation_type        0
% 43.43/5.99  --bmc1_ucm_relax_model                  4
% 43.43/5.99  --bmc1_ucm_full_tr_after_sat            true
% 43.43/5.99  --bmc1_ucm_expand_neg_assumptions       false
% 43.43/5.99  --bmc1_ucm_layered_model                none
% 43.43/5.99  --bmc1_ucm_max_lemma_size               10
% 43.43/5.99  
% 43.43/5.99  ------ AIG Options
% 43.43/5.99  
% 43.43/5.99  --aig_mode                              false
% 43.43/5.99  
% 43.43/5.99  ------ Instantiation Options
% 43.43/5.99  
% 43.43/5.99  --instantiation_flag                    true
% 43.43/5.99  --inst_sos_flag                         true
% 43.43/5.99  --inst_sos_phase                        true
% 43.43/5.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.43/5.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.43/5.99  --inst_lit_sel_side                     num_symb
% 43.43/5.99  --inst_solver_per_active                1400
% 43.43/5.99  --inst_solver_calls_frac                1.
% 43.43/5.99  --inst_passive_queue_type               priority_queues
% 43.43/5.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.43/5.99  --inst_passive_queues_freq              [25;2]
% 43.43/5.99  --inst_dismatching                      true
% 43.43/5.99  --inst_eager_unprocessed_to_passive     true
% 43.43/5.99  --inst_prop_sim_given                   true
% 43.43/5.99  --inst_prop_sim_new                     false
% 43.43/5.99  --inst_subs_new                         false
% 43.43/5.99  --inst_eq_res_simp                      false
% 43.43/5.99  --inst_subs_given                       false
% 43.43/5.99  --inst_orphan_elimination               true
% 43.43/5.99  --inst_learning_loop_flag               true
% 43.43/5.99  --inst_learning_start                   3000
% 43.43/5.99  --inst_learning_factor                  2
% 43.43/5.99  --inst_start_prop_sim_after_learn       3
% 43.43/5.99  --inst_sel_renew                        solver
% 43.43/5.99  --inst_lit_activity_flag                true
% 43.43/5.99  --inst_restr_to_given                   false
% 43.43/5.99  --inst_activity_threshold               500
% 43.43/5.99  --inst_out_proof                        true
% 43.43/5.99  
% 43.43/5.99  ------ Resolution Options
% 43.43/5.99  
% 43.43/5.99  --resolution_flag                       true
% 43.43/5.99  --res_lit_sel                           adaptive
% 43.43/5.99  --res_lit_sel_side                      none
% 43.43/5.99  --res_ordering                          kbo
% 43.43/5.99  --res_to_prop_solver                    active
% 43.43/5.99  --res_prop_simpl_new                    false
% 43.43/5.99  --res_prop_simpl_given                  true
% 43.43/5.99  --res_passive_queue_type                priority_queues
% 43.43/5.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.43/5.99  --res_passive_queues_freq               [15;5]
% 43.43/5.99  --res_forward_subs                      full
% 43.43/5.99  --res_backward_subs                     full
% 43.43/5.99  --res_forward_subs_resolution           true
% 43.43/5.99  --res_backward_subs_resolution          true
% 43.43/5.99  --res_orphan_elimination                true
% 43.43/5.99  --res_time_limit                        2.
% 43.43/5.99  --res_out_proof                         true
% 43.43/5.99  
% 43.43/5.99  ------ Superposition Options
% 43.43/5.99  
% 43.43/5.99  --superposition_flag                    true
% 43.43/5.99  --sup_passive_queue_type                priority_queues
% 43.43/5.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.43/5.99  --sup_passive_queues_freq               [8;1;4]
% 43.43/5.99  --demod_completeness_check              fast
% 43.43/5.99  --demod_use_ground                      true
% 43.43/5.99  --sup_to_prop_solver                    passive
% 43.43/5.99  --sup_prop_simpl_new                    true
% 43.43/5.99  --sup_prop_simpl_given                  true
% 43.43/5.99  --sup_fun_splitting                     true
% 43.43/5.99  --sup_smt_interval                      50000
% 43.43/5.99  
% 43.43/5.99  ------ Superposition Simplification Setup
% 43.43/5.99  
% 43.43/5.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.43/5.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.43/5.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.43/5.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.43/5.99  --sup_full_triv                         [TrivRules;PropSubs]
% 43.43/5.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.43/5.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.43/5.99  --sup_immed_triv                        [TrivRules]
% 43.43/5.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.43/5.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.43/5.99  --sup_immed_bw_main                     []
% 43.43/5.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.43/5.99  --sup_input_triv                        [Unflattening;TrivRules]
% 43.43/5.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.43/5.99  --sup_input_bw                          []
% 43.43/5.99  
% 43.43/5.99  ------ Combination Options
% 43.43/5.99  
% 43.43/5.99  --comb_res_mult                         3
% 43.43/5.99  --comb_sup_mult                         2
% 43.43/5.99  --comb_inst_mult                        10
% 43.43/5.99  
% 43.43/5.99  ------ Debug Options
% 43.43/5.99  
% 43.43/5.99  --dbg_backtrace                         false
% 43.43/5.99  --dbg_dump_prop_clauses                 false
% 43.43/5.99  --dbg_dump_prop_clauses_file            -
% 43.43/5.99  --dbg_out_stat                          false
% 43.43/5.99  ------ Parsing...
% 43.43/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.43/5.99  
% 43.43/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.43/5.99  
% 43.43/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.43/5.99  
% 43.43/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.43/5.99  ------ Proving...
% 43.43/5.99  ------ Problem Properties 
% 43.43/5.99  
% 43.43/5.99  
% 43.43/5.99  clauses                                 11
% 43.43/5.99  conjectures                             3
% 43.43/5.99  EPR                                     4
% 43.43/5.99  Horn                                    11
% 43.43/5.99  unary                                   5
% 43.43/5.99  binary                                  4
% 43.43/5.99  lits                                    19
% 43.43/5.99  lits eq                                 1
% 43.43/5.99  fd_pure                                 0
% 43.43/5.99  fd_pseudo                               0
% 43.43/5.99  fd_cond                                 0
% 43.43/5.99  fd_pseudo_cond                          0
% 43.43/5.99  AC symbols                              0
% 43.43/5.99  
% 43.43/5.99  ------ Schedule dynamic 5 is on 
% 43.43/5.99  
% 43.43/5.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.43/5.99  
% 43.43/5.99  
% 43.43/5.99  ------ 
% 43.43/5.99  Current options:
% 43.43/5.99  ------ 
% 43.43/5.99  
% 43.43/5.99  ------ Input Options
% 43.43/5.99  
% 43.43/5.99  --out_options                           all
% 43.43/5.99  --tptp_safe_out                         true
% 43.43/5.99  --problem_path                          ""
% 43.43/5.99  --include_path                          ""
% 43.43/5.99  --clausifier                            res/vclausify_rel
% 43.43/5.99  --clausifier_options                    ""
% 43.43/5.99  --stdin                                 false
% 43.43/5.99  --stats_out                             all
% 43.43/5.99  
% 43.43/5.99  ------ General Options
% 43.43/5.99  
% 43.43/5.99  --fof                                   false
% 43.43/5.99  --time_out_real                         305.
% 43.43/5.99  --time_out_virtual                      -1.
% 43.43/5.99  --symbol_type_check                     false
% 43.43/5.99  --clausify_out                          false
% 43.43/5.99  --sig_cnt_out                           false
% 43.43/5.99  --trig_cnt_out                          false
% 43.43/5.99  --trig_cnt_out_tolerance                1.
% 43.43/5.99  --trig_cnt_out_sk_spl                   false
% 43.43/5.99  --abstr_cl_out                          false
% 43.43/5.99  
% 43.43/5.99  ------ Global Options
% 43.43/5.99  
% 43.43/5.99  --schedule                              default
% 43.43/5.99  --add_important_lit                     false
% 43.43/5.99  --prop_solver_per_cl                    1000
% 43.43/5.99  --min_unsat_core                        false
% 43.43/5.99  --soft_assumptions                      false
% 43.43/5.99  --soft_lemma_size                       3
% 43.43/5.99  --prop_impl_unit_size                   0
% 43.43/5.99  --prop_impl_unit                        []
% 43.43/5.99  --share_sel_clauses                     true
% 43.43/5.99  --reset_solvers                         false
% 43.43/5.99  --bc_imp_inh                            [conj_cone]
% 43.43/5.99  --conj_cone_tolerance                   3.
% 43.43/5.99  --extra_neg_conj                        none
% 43.43/5.99  --large_theory_mode                     true
% 43.43/5.99  --prolific_symb_bound                   200
% 43.43/5.99  --lt_threshold                          2000
% 43.43/5.99  --clause_weak_htbl                      true
% 43.43/5.99  --gc_record_bc_elim                     false
% 43.43/5.99  
% 43.43/5.99  ------ Preprocessing Options
% 43.43/5.99  
% 43.43/5.99  --preprocessing_flag                    true
% 43.43/5.99  --time_out_prep_mult                    0.1
% 43.43/5.99  --splitting_mode                        input
% 43.43/5.99  --splitting_grd                         true
% 43.43/5.99  --splitting_cvd                         false
% 43.43/5.99  --splitting_cvd_svl                     false
% 43.43/5.99  --splitting_nvd                         32
% 43.43/5.99  --sub_typing                            true
% 43.43/5.99  --prep_gs_sim                           true
% 43.43/5.99  --prep_unflatten                        true
% 43.43/5.99  --prep_res_sim                          true
% 43.43/5.99  --prep_upred                            true
% 43.43/5.99  --prep_sem_filter                       exhaustive
% 43.43/5.99  --prep_sem_filter_out                   false
% 43.43/5.99  --pred_elim                             true
% 43.43/5.99  --res_sim_input                         true
% 43.43/5.99  --eq_ax_congr_red                       true
% 43.43/5.99  --pure_diseq_elim                       true
% 43.43/5.99  --brand_transform                       false
% 43.43/5.99  --non_eq_to_eq                          false
% 43.43/5.99  --prep_def_merge                        true
% 43.43/5.99  --prep_def_merge_prop_impl              false
% 43.43/5.99  --prep_def_merge_mbd                    true
% 43.43/5.99  --prep_def_merge_tr_red                 false
% 43.43/5.99  --prep_def_merge_tr_cl                  false
% 43.43/5.99  --smt_preprocessing                     true
% 43.43/5.99  --smt_ac_axioms                         fast
% 43.43/5.99  --preprocessed_out                      false
% 43.43/5.99  --preprocessed_stats                    false
% 43.43/5.99  
% 43.43/5.99  ------ Abstraction refinement Options
% 43.43/5.99  
% 43.43/5.99  --abstr_ref                             []
% 43.43/5.99  --abstr_ref_prep                        false
% 43.43/5.99  --abstr_ref_until_sat                   false
% 43.43/5.99  --abstr_ref_sig_restrict                funpre
% 43.43/5.99  --abstr_ref_af_restrict_to_split_sk     false
% 43.43/5.99  --abstr_ref_under                       []
% 43.43/5.99  
% 43.43/5.99  ------ SAT Options
% 43.43/5.99  
% 43.43/5.99  --sat_mode                              false
% 43.43/5.99  --sat_fm_restart_options                ""
% 43.43/5.99  --sat_gr_def                            false
% 43.43/5.99  --sat_epr_types                         true
% 43.43/5.99  --sat_non_cyclic_types                  false
% 43.43/5.99  --sat_finite_models                     false
% 43.43/5.99  --sat_fm_lemmas                         false
% 43.43/5.99  --sat_fm_prep                           false
% 43.43/5.99  --sat_fm_uc_incr                        true
% 43.43/5.99  --sat_out_model                         small
% 43.43/5.99  --sat_out_clauses                       false
% 43.43/5.99  
% 43.43/5.99  ------ QBF Options
% 43.43/5.99  
% 43.43/5.99  --qbf_mode                              false
% 43.43/5.99  --qbf_elim_univ                         false
% 43.43/5.99  --qbf_dom_inst                          none
% 43.43/5.99  --qbf_dom_pre_inst                      false
% 43.43/5.99  --qbf_sk_in                             false
% 43.43/5.99  --qbf_pred_elim                         true
% 43.43/5.99  --qbf_split                             512
% 43.43/5.99  
% 43.43/5.99  ------ BMC1 Options
% 43.43/5.99  
% 43.43/5.99  --bmc1_incremental                      false
% 43.43/5.99  --bmc1_axioms                           reachable_all
% 43.43/5.99  --bmc1_min_bound                        0
% 43.43/5.99  --bmc1_max_bound                        -1
% 43.43/5.99  --bmc1_max_bound_default                -1
% 43.43/5.99  --bmc1_symbol_reachability              true
% 43.43/5.99  --bmc1_property_lemmas                  false
% 43.43/5.99  --bmc1_k_induction                      false
% 43.43/5.99  --bmc1_non_equiv_states                 false
% 43.43/5.99  --bmc1_deadlock                         false
% 43.43/5.99  --bmc1_ucm                              false
% 43.43/5.99  --bmc1_add_unsat_core                   none
% 43.43/5.99  --bmc1_unsat_core_children              false
% 43.43/5.99  --bmc1_unsat_core_extrapolate_axioms    false
% 43.43/5.99  --bmc1_out_stat                         full
% 43.43/5.99  --bmc1_ground_init                      false
% 43.43/5.99  --bmc1_pre_inst_next_state              false
% 43.43/5.99  --bmc1_pre_inst_state                   false
% 43.43/5.99  --bmc1_pre_inst_reach_state             false
% 43.43/5.99  --bmc1_out_unsat_core                   false
% 43.43/5.99  --bmc1_aig_witness_out                  false
% 43.43/5.99  --bmc1_verbose                          false
% 43.43/5.99  --bmc1_dump_clauses_tptp                false
% 43.43/5.99  --bmc1_dump_unsat_core_tptp             false
% 43.43/5.99  --bmc1_dump_file                        -
% 43.43/5.99  --bmc1_ucm_expand_uc_limit              128
% 43.43/5.99  --bmc1_ucm_n_expand_iterations          6
% 43.43/5.99  --bmc1_ucm_extend_mode                  1
% 43.43/5.99  --bmc1_ucm_init_mode                    2
% 43.43/5.99  --bmc1_ucm_cone_mode                    none
% 43.43/5.99  --bmc1_ucm_reduced_relation_type        0
% 43.43/5.99  --bmc1_ucm_relax_model                  4
% 43.43/5.99  --bmc1_ucm_full_tr_after_sat            true
% 43.43/5.99  --bmc1_ucm_expand_neg_assumptions       false
% 43.43/5.99  --bmc1_ucm_layered_model                none
% 43.43/5.99  --bmc1_ucm_max_lemma_size               10
% 43.43/5.99  
% 43.43/5.99  ------ AIG Options
% 43.43/5.99  
% 43.43/5.99  --aig_mode                              false
% 43.43/5.99  
% 43.43/5.99  ------ Instantiation Options
% 43.43/5.99  
% 43.43/5.99  --instantiation_flag                    true
% 43.43/5.99  --inst_sos_flag                         true
% 43.43/5.99  --inst_sos_phase                        true
% 43.43/5.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.43/5.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.43/5.99  --inst_lit_sel_side                     none
% 43.43/5.99  --inst_solver_per_active                1400
% 43.43/5.99  --inst_solver_calls_frac                1.
% 43.43/5.99  --inst_passive_queue_type               priority_queues
% 43.43/5.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.43/5.99  --inst_passive_queues_freq              [25;2]
% 43.43/5.99  --inst_dismatching                      true
% 43.43/5.99  --inst_eager_unprocessed_to_passive     true
% 43.43/5.99  --inst_prop_sim_given                   true
% 43.43/5.99  --inst_prop_sim_new                     false
% 43.43/5.99  --inst_subs_new                         false
% 43.43/5.99  --inst_eq_res_simp                      false
% 43.43/5.99  --inst_subs_given                       false
% 43.43/5.99  --inst_orphan_elimination               true
% 43.43/5.99  --inst_learning_loop_flag               true
% 43.43/5.99  --inst_learning_start                   3000
% 43.43/5.99  --inst_learning_factor                  2
% 43.43/5.99  --inst_start_prop_sim_after_learn       3
% 43.43/5.99  --inst_sel_renew                        solver
% 43.43/5.99  --inst_lit_activity_flag                true
% 43.43/5.99  --inst_restr_to_given                   false
% 43.43/5.99  --inst_activity_threshold               500
% 43.43/5.99  --inst_out_proof                        true
% 43.43/5.99  
% 43.43/5.99  ------ Resolution Options
% 43.43/5.99  
% 43.43/5.99  --resolution_flag                       false
% 43.43/5.99  --res_lit_sel                           adaptive
% 43.43/5.99  --res_lit_sel_side                      none
% 43.43/5.99  --res_ordering                          kbo
% 43.43/5.99  --res_to_prop_solver                    active
% 43.43/5.99  --res_prop_simpl_new                    false
% 43.43/5.99  --res_prop_simpl_given                  true
% 43.43/5.99  --res_passive_queue_type                priority_queues
% 43.43/5.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.43/5.99  --res_passive_queues_freq               [15;5]
% 43.43/5.99  --res_forward_subs                      full
% 43.43/5.99  --res_backward_subs                     full
% 43.43/5.99  --res_forward_subs_resolution           true
% 43.43/5.99  --res_backward_subs_resolution          true
% 43.43/5.99  --res_orphan_elimination                true
% 43.43/5.99  --res_time_limit                        2.
% 43.43/5.99  --res_out_proof                         true
% 43.43/5.99  
% 43.43/5.99  ------ Superposition Options
% 43.43/5.99  
% 43.43/5.99  --superposition_flag                    true
% 43.43/5.99  --sup_passive_queue_type                priority_queues
% 43.43/5.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.43/5.99  --sup_passive_queues_freq               [8;1;4]
% 43.43/5.99  --demod_completeness_check              fast
% 43.43/5.99  --demod_use_ground                      true
% 43.43/5.99  --sup_to_prop_solver                    passive
% 43.43/5.99  --sup_prop_simpl_new                    true
% 43.43/5.99  --sup_prop_simpl_given                  true
% 43.43/5.99  --sup_fun_splitting                     true
% 43.43/5.99  --sup_smt_interval                      50000
% 43.43/5.99  
% 43.43/5.99  ------ Superposition Simplification Setup
% 43.43/5.99  
% 43.43/5.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.43/5.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.43/5.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.43/5.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.43/5.99  --sup_full_triv                         [TrivRules;PropSubs]
% 43.43/5.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.43/5.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.43/5.99  --sup_immed_triv                        [TrivRules]
% 43.43/5.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.43/5.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.43/5.99  --sup_immed_bw_main                     []
% 43.43/5.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.43/5.99  --sup_input_triv                        [Unflattening;TrivRules]
% 43.43/5.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.43/5.99  --sup_input_bw                          []
% 43.43/5.99  
% 43.43/5.99  ------ Combination Options
% 43.43/5.99  
% 43.43/5.99  --comb_res_mult                         3
% 43.43/5.99  --comb_sup_mult                         2
% 43.43/5.99  --comb_inst_mult                        10
% 43.43/5.99  
% 43.43/5.99  ------ Debug Options
% 43.43/5.99  
% 43.43/5.99  --dbg_backtrace                         false
% 43.43/5.99  --dbg_dump_prop_clauses                 false
% 43.43/5.99  --dbg_dump_prop_clauses_file            -
% 43.43/5.99  --dbg_out_stat                          false
% 43.43/5.99  
% 43.43/5.99  
% 43.43/5.99  
% 43.43/5.99  
% 43.43/5.99  ------ Proving...
% 43.43/5.99  
% 43.43/5.99  
% 43.43/5.99  % SZS status Theorem for theBenchmark.p
% 43.43/5.99  
% 43.43/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 43.43/5.99  
% 43.43/5.99  fof(f4,axiom,(
% 43.43/5.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 43.43/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.43/5.99  
% 43.43/5.99  fof(f25,plain,(
% 43.43/5.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 43.43/5.99    inference(cnf_transformation,[],[f4])).
% 43.43/5.99  
% 43.43/5.99  fof(f9,conjecture,(
% 43.43/5.99    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 43.43/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.43/5.99  
% 43.43/5.99  fof(f10,negated_conjecture,(
% 43.43/5.99    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 43.43/5.99    inference(negated_conjecture,[],[f9])).
% 43.43/5.99  
% 43.43/5.99  fof(f19,plain,(
% 43.43/5.99    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 43.43/5.99    inference(ennf_transformation,[],[f10])).
% 43.43/5.99  
% 43.43/5.99  fof(f20,plain,(
% 43.43/5.99    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 43.43/5.99    introduced(choice_axiom,[])).
% 43.43/5.99  
% 43.43/5.99  fof(f21,plain,(
% 43.43/5.99    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 43.43/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 43.43/5.99  
% 43.43/5.99  fof(f32,plain,(
% 43.43/5.99    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 43.43/5.99    inference(cnf_transformation,[],[f21])).
% 43.43/5.99  
% 43.43/5.99  fof(f7,axiom,(
% 43.43/5.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 43.43/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.43/5.99  
% 43.43/5.99  fof(f16,plain,(
% 43.43/5.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 43.43/5.99    inference(ennf_transformation,[],[f7])).
% 43.43/5.99  
% 43.43/5.99  fof(f17,plain,(
% 43.43/5.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 43.43/5.99    inference(flattening,[],[f16])).
% 43.43/5.99  
% 43.43/5.99  fof(f28,plain,(
% 43.43/5.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 43.43/5.99    inference(cnf_transformation,[],[f17])).
% 43.43/5.99  
% 43.43/5.99  fof(f1,axiom,(
% 43.43/5.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 43.43/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.43/5.99  
% 43.43/5.99  fof(f11,plain,(
% 43.43/5.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 43.43/5.99    inference(ennf_transformation,[],[f1])).
% 43.43/5.99  
% 43.43/5.99  fof(f22,plain,(
% 43.43/5.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 43.43/5.99    inference(cnf_transformation,[],[f11])).
% 43.43/5.99  
% 43.43/5.99  fof(f5,axiom,(
% 43.43/5.99    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 43.43/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.43/5.99  
% 43.43/5.99  fof(f14,plain,(
% 43.43/5.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 43.43/5.99    inference(ennf_transformation,[],[f5])).
% 43.43/5.99  
% 43.43/5.99  fof(f15,plain,(
% 43.43/5.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 43.43/5.99    inference(flattening,[],[f14])).
% 43.43/5.99  
% 43.43/5.99  fof(f26,plain,(
% 43.43/5.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 43.43/5.99    inference(cnf_transformation,[],[f15])).
% 43.43/5.99  
% 43.43/5.99  fof(f8,axiom,(
% 43.43/5.99    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 43.43/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.43/5.99  
% 43.43/5.99  fof(f18,plain,(
% 43.43/5.99    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 43.43/5.99    inference(ennf_transformation,[],[f8])).
% 43.43/5.99  
% 43.43/5.99  fof(f29,plain,(
% 43.43/5.99    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 43.43/5.99    inference(cnf_transformation,[],[f18])).
% 43.43/5.99  
% 43.43/5.99  fof(f31,plain,(
% 43.43/5.99    r1_tarski(sK0,sK2)),
% 43.43/5.99    inference(cnf_transformation,[],[f21])).
% 43.43/5.99  
% 43.43/5.99  fof(f3,axiom,(
% 43.43/5.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 43.43/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.43/5.99  
% 43.43/5.99  fof(f13,plain,(
% 43.43/5.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 43.43/5.99    inference(ennf_transformation,[],[f3])).
% 43.43/5.99  
% 43.43/5.99  fof(f24,plain,(
% 43.43/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 43.43/5.99    inference(cnf_transformation,[],[f13])).
% 43.43/5.99  
% 43.43/5.99  fof(f2,axiom,(
% 43.43/5.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 43.43/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.43/5.99  
% 43.43/5.99  fof(f12,plain,(
% 43.43/5.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 43.43/5.99    inference(ennf_transformation,[],[f2])).
% 43.43/5.99  
% 43.43/5.99  fof(f23,plain,(
% 43.43/5.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 43.43/5.99    inference(cnf_transformation,[],[f12])).
% 43.43/5.99  
% 43.43/5.99  fof(f6,axiom,(
% 43.43/5.99    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 43.43/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.43/5.99  
% 43.43/5.99  fof(f27,plain,(
% 43.43/5.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 43.43/5.99    inference(cnf_transformation,[],[f6])).
% 43.43/5.99  
% 43.43/5.99  fof(f30,plain,(
% 43.43/5.99    ~r1_xboole_0(sK0,sK1)),
% 43.43/5.99    inference(cnf_transformation,[],[f21])).
% 43.43/5.99  
% 43.43/5.99  cnf(c_3,plain,
% 43.43/5.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 43.43/5.99      inference(cnf_transformation,[],[f25]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_320,plain,
% 43.43/5.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_8,negated_conjecture,
% 43.43/5.99      ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 43.43/5.99      inference(cnf_transformation,[],[f32]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_315,plain,
% 43.43/5.99      ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_6,plain,
% 43.43/5.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 43.43/5.99      inference(cnf_transformation,[],[f28]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_317,plain,
% 43.43/5.99      ( r1_tarski(X0,X1) != iProver_top
% 43.43/5.99      | r1_xboole_0(X1,X2) != iProver_top
% 43.43/5.99      | r1_xboole_0(X0,X2) = iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_966,plain,
% 43.43/5.99      ( r1_xboole_0(X0,X1) != iProver_top
% 43.43/5.99      | r1_xboole_0(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_320,c_317]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_0,plain,
% 43.43/5.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 43.43/5.99      inference(cnf_transformation,[],[f22]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_323,plain,
% 43.43/5.99      ( r1_xboole_0(X0,X1) != iProver_top
% 43.43/5.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_3537,plain,
% 43.43/5.99      ( r1_xboole_0(X0,X1) != iProver_top
% 43.43/5.99      | r1_xboole_0(X1,k3_xboole_0(X0,X2)) = iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_966,c_323]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_4,plain,
% 43.43/5.99      ( ~ r1_tarski(X0,X1)
% 43.43/5.99      | ~ r1_tarski(X0,X2)
% 43.43/5.99      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 43.43/5.99      inference(cnf_transformation,[],[f26]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_319,plain,
% 43.43/5.99      ( r1_tarski(X0,X1) != iProver_top
% 43.43/5.99      | r1_tarski(X0,X2) != iProver_top
% 43.43/5.99      | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_1049,plain,
% 43.43/5.99      ( r1_tarski(X0,X1) != iProver_top
% 43.43/5.99      | r1_tarski(X0,X2) != iProver_top
% 43.43/5.99      | r1_xboole_0(X0,X3) = iProver_top
% 43.43/5.99      | r1_xboole_0(k3_xboole_0(X1,X2),X3) != iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_319,c_317]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_7813,plain,
% 43.43/5.99      ( r1_tarski(X0,X1) != iProver_top
% 43.43/5.99      | r1_tarski(X0,X2) != iProver_top
% 43.43/5.99      | r1_xboole_0(X3,k3_xboole_0(X1,X2)) != iProver_top
% 43.43/5.99      | r1_xboole_0(X0,k3_xboole_0(X3,X4)) = iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_3537,c_1049]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_151691,plain,
% 43.43/5.99      ( r1_tarski(X0,sK2) != iProver_top
% 43.43/5.99      | r1_tarski(X0,sK1) != iProver_top
% 43.43/5.99      | r1_xboole_0(X0,k3_xboole_0(sK0,X1)) = iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_315,c_7813]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_7,plain,
% 43.43/5.99      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 43.43/5.99      inference(cnf_transformation,[],[f29]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_316,plain,
% 43.43/5.99      ( r1_xboole_0(X0,X1) = iProver_top
% 43.43/5.99      | r1_xboole_0(k3_xboole_0(X0,X1),X1) != iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_151997,plain,
% 43.43/5.99      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),sK2) != iProver_top
% 43.43/5.99      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),sK1) != iProver_top
% 43.43/5.99      | r1_xboole_0(X0,k3_xboole_0(sK0,X1)) = iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_151691,c_316]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_9,negated_conjecture,
% 43.43/5.99      ( r1_tarski(sK0,sK2) ),
% 43.43/5.99      inference(cnf_transformation,[],[f31]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_314,plain,
% 43.43/5.99      ( r1_tarski(sK0,sK2) = iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_2,plain,
% 43.43/5.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 43.43/5.99      inference(cnf_transformation,[],[f24]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_321,plain,
% 43.43/5.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_673,plain,
% 43.43/5.99      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_320,c_321]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_1,plain,
% 43.43/5.99      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 43.43/5.99      inference(cnf_transformation,[],[f23]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_322,plain,
% 43.43/5.99      ( r1_tarski(X0,X1) = iProver_top
% 43.43/5.99      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_956,plain,
% 43.43/5.99      ( r1_tarski(X0,X1) != iProver_top
% 43.43/5.99      | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_673,c_322]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_3134,plain,
% 43.43/5.99      ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = X2
% 43.43/5.99      | r1_tarski(X0,X2) != iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_956,c_321]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_3817,plain,
% 43.43/5.99      ( k2_xboole_0(k3_xboole_0(sK0,X0),sK2) = sK2 ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_314,c_3134]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_5,plain,
% 43.43/5.99      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
% 43.43/5.99      inference(cnf_transformation,[],[f27]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_318,plain,
% 43.43/5.99      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_955,plain,
% 43.43/5.99      ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_318,c_322]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_3925,plain,
% 43.43/5.99      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),sK2) = iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_3817,c_955]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_154589,plain,
% 43.43/5.99      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),sK1) != iProver_top
% 43.43/5.99      | r1_xboole_0(X0,k3_xboole_0(sK0,X1)) = iProver_top ),
% 43.43/5.99      inference(global_propositional_subsumption,
% 43.43/5.99                [status(thm)],
% 43.43/5.99                [c_151997,c_3925]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_154595,plain,
% 43.43/5.99      ( r1_xboole_0(sK1,k3_xboole_0(sK0,X0)) = iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_320,c_154589]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_4848,plain,
% 43.43/5.99      ( r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top
% 43.43/5.99      | r1_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X1,X2))) != iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_3537,c_316]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_155116,plain,
% 43.43/5.99      ( r1_xboole_0(sK0,k3_xboole_0(sK1,X0)) = iProver_top ),
% 43.43/5.99      inference(superposition,[status(thm)],[c_154595,c_4848]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_155125,plain,
% 43.43/5.99      ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = iProver_top ),
% 43.43/5.99      inference(instantiation,[status(thm)],[c_155116]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_401,plain,
% 43.43/5.99      ( r1_xboole_0(k3_xboole_0(sK1,sK0),sK0)
% 43.43/5.99      | ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
% 43.43/5.99      inference(instantiation,[status(thm)],[c_0]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_402,plain,
% 43.43/5.99      ( r1_xboole_0(k3_xboole_0(sK1,sK0),sK0) = iProver_top
% 43.43/5.99      | r1_xboole_0(sK0,k3_xboole_0(sK1,sK0)) != iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_353,plain,
% 43.43/5.99      ( ~ r1_xboole_0(k3_xboole_0(sK1,sK0),sK0) | r1_xboole_0(sK1,sK0) ),
% 43.43/5.99      inference(instantiation,[status(thm)],[c_7]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_354,plain,
% 43.43/5.99      ( r1_xboole_0(k3_xboole_0(sK1,sK0),sK0) != iProver_top
% 43.43/5.99      | r1_xboole_0(sK1,sK0) = iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_338,plain,
% 43.43/5.99      ( ~ r1_xboole_0(sK1,sK0) | r1_xboole_0(sK0,sK1) ),
% 43.43/5.99      inference(instantiation,[status(thm)],[c_0]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_339,plain,
% 43.43/5.99      ( r1_xboole_0(sK1,sK0) != iProver_top
% 43.43/5.99      | r1_xboole_0(sK0,sK1) = iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_10,negated_conjecture,
% 43.43/5.99      ( ~ r1_xboole_0(sK0,sK1) ),
% 43.43/5.99      inference(cnf_transformation,[],[f30]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(c_11,plain,
% 43.43/5.99      ( r1_xboole_0(sK0,sK1) != iProver_top ),
% 43.43/5.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 43.43/5.99  
% 43.43/5.99  cnf(contradiction,plain,
% 43.43/5.99      ( $false ),
% 43.43/5.99      inference(minisat,[status(thm)],[c_155125,c_402,c_354,c_339,c_11]) ).
% 43.43/5.99  
% 43.43/5.99  
% 43.43/5.99  % SZS output end CNFRefutation for theBenchmark.p
% 43.43/5.99  
% 43.43/5.99  ------                               Statistics
% 43.43/5.99  
% 43.43/5.99  ------ General
% 43.43/5.99  
% 43.43/5.99  abstr_ref_over_cycles:                  0
% 43.43/5.99  abstr_ref_under_cycles:                 0
% 43.43/5.99  gc_basic_clause_elim:                   0
% 43.43/5.99  forced_gc_time:                         0
% 43.43/5.99  parsing_time:                           0.011
% 43.43/5.99  unif_index_cands_time:                  0.
% 43.43/5.99  unif_index_add_time:                    0.
% 43.43/5.99  orderings_time:                         0.
% 43.43/5.99  out_proof_time:                         0.024
% 43.43/5.99  total_time:                             5.29
% 43.43/5.99  num_of_symbols:                         38
% 43.43/5.99  num_of_terms:                           239651
% 43.43/5.99  
% 43.43/5.99  ------ Preprocessing
% 43.43/5.99  
% 43.43/5.99  num_of_splits:                          0
% 43.43/5.99  num_of_split_atoms:                     0
% 43.43/5.99  num_of_reused_defs:                     0
% 43.43/5.99  num_eq_ax_congr_red:                    0
% 43.43/5.99  num_of_sem_filtered_clauses:            1
% 43.43/5.99  num_of_subtypes:                        0
% 43.43/5.99  monotx_restored_types:                  0
% 43.43/5.99  sat_num_of_epr_types:                   0
% 43.43/5.99  sat_num_of_non_cyclic_types:            0
% 43.43/5.99  sat_guarded_non_collapsed_types:        0
% 43.43/5.99  num_pure_diseq_elim:                    0
% 43.43/5.99  simp_replaced_by:                       0
% 43.43/5.99  res_preprocessed:                       46
% 43.43/5.99  prep_upred:                             0
% 43.43/5.99  prep_unflattend:                        0
% 43.43/5.99  smt_new_axioms:                         0
% 43.43/5.99  pred_elim_cands:                        2
% 43.43/5.99  pred_elim:                              0
% 43.43/5.99  pred_elim_cl:                           0
% 43.43/5.99  pred_elim_cycles:                       1
% 43.43/5.99  merged_defs:                            0
% 43.43/5.99  merged_defs_ncl:                        0
% 43.43/5.99  bin_hyper_res:                          0
% 43.43/5.99  prep_cycles:                            3
% 43.43/5.99  pred_elim_time:                         0.
% 43.43/5.99  splitting_time:                         0.
% 43.43/5.99  sem_filter_time:                        0.
% 43.43/5.99  monotx_time:                            0.
% 43.43/5.99  subtype_inf_time:                       0.
% 43.43/5.99  
% 43.43/5.99  ------ Problem properties
% 43.43/5.99  
% 43.43/5.99  clauses:                                11
% 43.43/5.99  conjectures:                            3
% 43.43/5.99  epr:                                    4
% 43.43/5.99  horn:                                   11
% 43.43/5.99  ground:                                 3
% 43.43/5.99  unary:                                  5
% 43.43/5.99  binary:                                 4
% 43.43/5.99  lits:                                   19
% 43.43/5.99  lits_eq:                                1
% 43.43/5.99  fd_pure:                                0
% 43.43/5.99  fd_pseudo:                              0
% 43.43/5.99  fd_cond:                                0
% 43.43/5.99  fd_pseudo_cond:                         0
% 43.43/5.99  ac_symbols:                             0
% 43.43/5.99  
% 43.43/5.99  ------ Propositional Solver
% 43.43/5.99  
% 43.43/5.99  prop_solver_calls:                      67
% 43.43/5.99  prop_fast_solver_calls:                 2111
% 43.43/5.99  smt_solver_calls:                       0
% 43.43/5.99  smt_fast_solver_calls:                  0
% 43.43/5.99  prop_num_of_clauses:                    66100
% 43.43/5.99  prop_preprocess_simplified:             81313
% 43.43/5.99  prop_fo_subsumed:                       9
% 43.43/5.99  prop_solver_time:                       0.
% 43.43/5.99  smt_solver_time:                        0.
% 43.43/5.99  smt_fast_solver_time:                   0.
% 43.43/5.99  prop_fast_solver_time:                  0.
% 43.43/5.99  prop_unsat_core_time:                   0.008
% 43.43/5.99  
% 43.43/5.99  ------ QBF
% 43.43/5.99  
% 43.43/5.99  qbf_q_res:                              0
% 43.43/5.99  qbf_num_tautologies:                    0
% 43.43/5.99  qbf_prep_cycles:                        0
% 43.43/5.99  
% 43.43/5.99  ------ BMC1
% 43.43/5.99  
% 43.43/5.99  bmc1_current_bound:                     -1
% 43.43/5.99  bmc1_last_solved_bound:                 -1
% 43.43/5.99  bmc1_unsat_core_size:                   -1
% 43.43/5.99  bmc1_unsat_core_parents_size:           -1
% 43.43/5.99  bmc1_merge_next_fun:                    0
% 43.43/5.99  bmc1_unsat_core_clauses_time:           0.
% 43.43/5.99  
% 43.43/5.99  ------ Instantiation
% 43.43/5.99  
% 43.43/5.99  inst_num_of_clauses:                    4722
% 43.43/5.99  inst_num_in_passive:                    2076
% 43.43/5.99  inst_num_in_active:                     4258
% 43.43/5.99  inst_num_in_unprocessed:                1309
% 43.43/5.99  inst_num_of_loops:                      4599
% 43.43/5.99  inst_num_of_learning_restarts:          1
% 43.43/5.99  inst_num_moves_active_passive:          335
% 43.43/5.99  inst_lit_activity:                      0
% 43.43/5.99  inst_lit_activity_moves:                4
% 43.43/5.99  inst_num_tautologies:                   0
% 43.43/5.99  inst_num_prop_implied:                  0
% 43.43/5.99  inst_num_existing_simplified:           0
% 43.43/5.99  inst_num_eq_res_simplified:             0
% 43.43/5.99  inst_num_child_elim:                    0
% 43.43/5.99  inst_num_of_dismatching_blockings:      41127
% 43.43/5.99  inst_num_of_non_proper_insts:           13332
% 43.43/5.99  inst_num_of_duplicates:                 0
% 43.43/5.99  inst_inst_num_from_inst_to_res:         0
% 43.43/5.99  inst_dismatching_checking_time:         0.
% 43.43/5.99  
% 43.43/5.99  ------ Resolution
% 43.43/5.99  
% 43.43/5.99  res_num_of_clauses:                     17
% 43.43/5.99  res_num_in_passive:                     17
% 43.43/5.99  res_num_in_active:                      0
% 43.43/5.99  res_num_of_loops:                       49
% 43.43/5.99  res_forward_subset_subsumed:            699
% 43.43/5.99  res_backward_subset_subsumed:           26
% 43.43/5.99  res_forward_subsumed:                   0
% 43.43/5.99  res_backward_subsumed:                  0
% 43.43/5.99  res_forward_subsumption_resolution:     0
% 43.43/5.99  res_backward_subsumption_resolution:    0
% 43.43/5.99  res_clause_to_clause_subsumption:       197498
% 43.43/5.99  res_orphan_elimination:                 0
% 43.43/5.99  res_tautology_del:                      1858
% 43.43/5.99  res_num_eq_res_simplified:              0
% 43.43/5.99  res_num_sel_changes:                    0
% 43.43/5.99  res_moves_from_active_to_pass:          0
% 43.43/5.99  
% 43.43/5.99  ------ Superposition
% 43.43/5.99  
% 43.43/5.99  sup_time_total:                         0.
% 43.43/5.99  sup_time_generating:                    0.
% 43.43/5.99  sup_time_sim_full:                      0.
% 43.43/5.99  sup_time_sim_immed:                     0.
% 43.43/5.99  
% 43.43/5.99  sup_num_of_clauses:                     11281
% 43.43/5.99  sup_num_in_active:                      862
% 43.43/5.99  sup_num_in_passive:                     10419
% 43.43/5.99  sup_num_of_loops:                       919
% 43.43/5.99  sup_fw_superposition:                   10974
% 43.43/5.99  sup_bw_superposition:                   10948
% 43.43/5.99  sup_immediate_simplified:               6681
% 43.43/5.99  sup_given_eliminated:                   4
% 43.43/5.99  comparisons_done:                       0
% 43.43/5.99  comparisons_avoided:                    0
% 43.43/5.99  
% 43.43/5.99  ------ Simplifications
% 43.43/5.99  
% 43.43/5.99  
% 43.43/5.99  sim_fw_subset_subsumed:                 308
% 43.43/5.99  sim_bw_subset_subsumed:                 204
% 43.43/5.99  sim_fw_subsumed:                        1148
% 43.43/5.99  sim_bw_subsumed:                        599
% 43.43/5.99  sim_fw_subsumption_res:                 0
% 43.43/5.99  sim_bw_subsumption_res:                 0
% 43.43/5.99  sim_tautology_del:                      4
% 43.43/5.99  sim_eq_tautology_del:                   533
% 43.43/5.99  sim_eq_res_simp:                        0
% 43.43/5.99  sim_fw_demodulated:                     3567
% 43.43/5.99  sim_bw_demodulated:                     5
% 43.43/5.99  sim_light_normalised:                   1686
% 43.43/5.99  sim_joinable_taut:                      0
% 43.43/5.99  sim_joinable_simp:                      0
% 43.43/5.99  sim_ac_normalised:                      0
% 43.43/5.99  sim_smt_subsumption:                    0
% 43.43/5.99  
%------------------------------------------------------------------------------
