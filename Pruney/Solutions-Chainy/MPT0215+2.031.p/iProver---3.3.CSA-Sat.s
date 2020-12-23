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
% DateTime   : Thu Dec  3 11:28:58 EST 2020

% Result     : CounterSatisfiable 3.85s
% Output     : Saturation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   91 (1048 expanded)
%              Number of clauses        :   48 ( 155 expanded)
%              Number of leaves         :   17 ( 332 expanded)
%              Depth                    :   18
%              Number of atoms          :  198 (1530 expanded)
%              Number of equality atoms :  185 (1485 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f41,f32,f58,f60,f59])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).

fof(f53,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f35,f54,f56,f56])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_389,plain,
    ( ~ iProver_ARSWP_12
    | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_2])).

cnf(c_489,plain,
    ( arAF0_k5_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_12 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_7,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_392,plain,
    ( ~ iProver_ARSWP_15
    | X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_486,plain,
    ( X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_15 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_727,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X0
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_486])).

cnf(c_1032,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_727])).

cnf(c_1354,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1032])).

cnf(c_1489,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_1354])).

cnf(c_11,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_948,plain,
    ( ~ iProver_ARSWP_15
    | X0 = sK1
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(resolution,[status(thm)],[c_392,c_11])).

cnf(c_950,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_1097,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_11,c_950])).

cnf(c_27,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_26,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_604,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_27,c_26])).

cnf(c_1227,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_1097,c_604])).

cnf(c_1244,plain,
    ( ~ iProver_ARSWP_15
    | X0 != arAF0_k5_xboole_0_0
    | arAF0_k5_enumset1_0 = X0 ),
    inference(resolution,[status(thm)],[c_1227,c_27])).

cnf(c_622,plain,
    ( ~ iProver_ARSWP_12
    | k1_xboole_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_604,c_389])).

cnf(c_1646,plain,
    ( ~ iProver_ARSWP_15
    | ~ iProver_ARSWP_12
    | arAF0_k5_enumset1_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1244,c_622])).

cnf(c_1647,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1646])).

cnf(c_1713,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1489,c_1647])).

cnf(c_728,plain,
    ( arAF0_k5_enumset1_0 != X0
    | arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_486])).

cnf(c_1730,plain,
    ( arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1713,c_728])).

cnf(c_730,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 != X1
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_486])).

cnf(c_1729,plain,
    ( X0 = X1
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X1
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1713,c_730])).

cnf(c_1500,plain,
    ( arAF0_k5_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1354])).

cnf(c_713,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(superposition,[status(thm)],[c_486,c_11])).

cnf(c_33,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_179,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_180,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_718,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = X0
    | sK0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(superposition,[status(thm)],[c_486,c_11])).

cnf(c_887,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = sK0
    | sK0 != sK0
    | iProver_ARSWP_15 != iProver_top ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_904,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_15 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_713,c_11,c_33,c_180,c_887])).

cnf(c_729,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_486])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_387,plain,
    ( ~ iProver_ARSWP_10
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_491,plain,
    ( arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_711,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_10 != iProver_top ),
    inference(superposition,[status(thm)],[c_486,c_491])).

cnf(c_722,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_486])).

cnf(c_852,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_10 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_711,c_722])).

cnf(c_620,plain,
    ( ~ iProver_ARSWP_10
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_604,c_387])).

cnf(c_621,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_1312,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_852,c_621])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_388,plain,
    ( ~ iProver_ARSWP_11
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_490,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | iProver_ARSWP_11 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.85/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/1.00  
% 3.85/1.00  ------  iProver source info
% 3.85/1.00  
% 3.85/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.85/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/1.00  git: non_committed_changes: false
% 3.85/1.00  git: last_make_outside_of_git: false
% 3.85/1.00  
% 3.85/1.00  ------ 
% 3.85/1.00  ------ Parsing...
% 3.85/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.85/1.00  ------ Proving...
% 3.85/1.00  ------ Problem Properties 
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  clauses                                 13
% 3.85/1.00  conjectures                             2
% 3.85/1.00  EPR                                     1
% 3.85/1.00  Horn                                    12
% 3.85/1.00  unary                                   12
% 3.85/1.00  binary                                  0
% 3.85/1.00  lits                                    15
% 3.85/1.00  lits eq                                 15
% 3.85/1.00  fd_pure                                 0
% 3.85/1.00  fd_pseudo                               0
% 3.85/1.00  fd_cond                                 0
% 3.85/1.00  fd_pseudo_cond                          1
% 3.85/1.00  AC symbols                              0
% 3.85/1.00  
% 3.85/1.00  ------ Input Options Time Limit: Unbounded
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.85/1.00  Current options:
% 3.85/1.00  ------ 
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ Proving...
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.85/1.00  
% 3.85/1.00  ------ Proving...
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.85/1.00  
% 3.85/1.00  ------ Proving...
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.85/1.00  
% 3.85/1.00  ------ Proving...
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  % SZS output start Saturation for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  fof(f4,axiom,(
% 3.85/1.00    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f33,plain,(
% 3.85/1.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f4])).
% 3.85/1.00  
% 3.85/1.00  fof(f12,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f27,plain,(
% 3.85/1.00    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.85/1.00    inference(ennf_transformation,[],[f12])).
% 3.85/1.00  
% 3.85/1.00  fof(f41,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.85/1.00    inference(cnf_transformation,[],[f27])).
% 3.85/1.00  
% 3.85/1.00  fof(f3,axiom,(
% 3.85/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f32,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f3])).
% 3.85/1.00  
% 3.85/1.00  fof(f16,axiom,(
% 3.85/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f45,plain,(
% 3.85/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f16])).
% 3.85/1.00  
% 3.85/1.00  fof(f60,plain,(
% 3.85/1.00    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f45,f59])).
% 3.85/1.00  
% 3.85/1.00  fof(f17,axiom,(
% 3.85/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f46,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f17])).
% 3.85/1.00  
% 3.85/1.00  fof(f18,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f47,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f18])).
% 3.85/1.00  
% 3.85/1.00  fof(f19,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f48,plain,(
% 3.85/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f19])).
% 3.85/1.00  
% 3.85/1.00  fof(f20,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f49,plain,(
% 3.85/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f20])).
% 3.85/1.00  
% 3.85/1.00  fof(f21,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f50,plain,(
% 3.85/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f21])).
% 3.85/1.00  
% 3.85/1.00  fof(f55,plain,(
% 3.85/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f49,f50])).
% 3.85/1.00  
% 3.85/1.00  fof(f56,plain,(
% 3.85/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f48,f55])).
% 3.85/1.00  
% 3.85/1.00  fof(f58,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f47,f56])).
% 3.85/1.00  
% 3.85/1.00  fof(f59,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f46,f58])).
% 3.85/1.00  
% 3.85/1.00  fof(f67,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.85/1.00    inference(definition_unfolding,[],[f41,f32,f58,f60,f59])).
% 3.85/1.00  
% 3.85/1.00  fof(f23,conjecture,(
% 3.85/1.00    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f24,negated_conjecture,(
% 3.85/1.00    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.85/1.00    inference(negated_conjecture,[],[f23])).
% 3.85/1.00  
% 3.85/1.00  fof(f28,plain,(
% 3.85/1.00    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 3.85/1.00    inference(ennf_transformation,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f29,plain,(
% 3.85/1.00    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f30,plain,(
% 3.85/1.00    sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 3.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).
% 3.85/1.00  
% 3.85/1.00  fof(f53,plain,(
% 3.85/1.00    sK0 != sK1),
% 3.85/1.00    inference(cnf_transformation,[],[f30])).
% 3.85/1.00  
% 3.85/1.00  fof(f22,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f51,plain,(
% 3.85/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f22])).
% 3.85/1.00  
% 3.85/1.00  fof(f6,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f35,plain,(
% 3.85/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f6])).
% 3.85/1.00  
% 3.85/1.00  fof(f5,axiom,(
% 3.85/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f34,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f5])).
% 3.85/1.00  
% 3.85/1.00  fof(f54,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f34,f32])).
% 3.85/1.00  
% 3.85/1.00  fof(f57,plain,(
% 3.85/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f35,f54,f56,f56])).
% 3.85/1.00  
% 3.85/1.00  fof(f62,plain,(
% 3.85/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f51,f57])).
% 3.85/1.00  
% 3.85/1.00  fof(f2,axiom,(
% 3.85/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f25,plain,(
% 3.85/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.85/1.00    inference(rectify,[],[f2])).
% 3.85/1.00  
% 3.85/1.00  fof(f31,plain,(
% 3.85/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.85/1.00    inference(cnf_transformation,[],[f25])).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2,plain,
% 3.85/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_389,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_12 | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
% 3.85/1.00      inference(arg_filter_abstr,[status(unp)],[c_2]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_489,plain,
% 3.85/1.00      ( arAF0_k5_xboole_0_0 = k1_xboole_0 | iProver_ARSWP_12 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | X2 = X1
% 3.85/1.00      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
% 3.85/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_392,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_15
% 3.85/1.00      | X0 = X1
% 3.85/1.00      | X2 = X1
% 3.85/1.00      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.85/1.00      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_486,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | X2 = X1
% 3.85/1.00      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_727,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 = X0
% 3.85/1.00      | arAF0_k5_enumset1_0 = X1
% 3.85/1.00      | arAF0_k5_xboole_0_0 != X0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.85/1.00      inference(equality_factoring,[status(thm)],[c_486]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1032,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 = X0
% 3.85/1.00      | arAF0_k5_enumset1_0 = X1
% 3.85/1.00      | k1_xboole_0 != X0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top
% 3.85/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_489,c_727]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1354,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 = X0
% 3.85/1.00      | arAF0_k5_enumset1_0 = k1_xboole_0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top
% 3.85/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.85/1.00      inference(equality_resolution,[status(thm)],[c_1032]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1489,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | arAF0_k5_enumset1_0 = k1_xboole_0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top
% 3.85/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1354,c_1354]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_11,negated_conjecture,
% 3.85/1.00      ( sK0 != sK1 ),
% 3.85/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_948,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_15
% 3.85/1.00      | X0 = sK1
% 3.85/1.00      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.85/1.00      inference(resolution,[status(thm)],[c_392,c_11]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_950,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_15
% 3.85/1.00      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
% 3.85/1.00      | sK0 = sK1 ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_948]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1097,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_15 | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_948,c_11,c_950]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_27,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_26,plain,( X0 = X0 ),theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_604,plain,
% 3.85/1.00      ( X0 != X1 | X1 = X0 ),
% 3.85/1.00      inference(resolution,[status(thm)],[c_27,c_26]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1227,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_15 | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
% 3.85/1.00      inference(resolution,[status(thm)],[c_1097,c_604]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1244,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_15
% 3.85/1.00      | X0 != arAF0_k5_xboole_0_0
% 3.85/1.00      | arAF0_k5_enumset1_0 = X0 ),
% 3.85/1.00      inference(resolution,[status(thm)],[c_1227,c_27]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_622,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_12 | k1_xboole_0 = arAF0_k5_xboole_0_0 ),
% 3.85/1.00      inference(resolution,[status(thm)],[c_604,c_389]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1646,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_15
% 3.85/1.00      | ~ iProver_ARSWP_12
% 3.85/1.00      | arAF0_k5_enumset1_0 = k1_xboole_0 ),
% 3.85/1.00      inference(resolution,[status(thm)],[c_1244,c_622]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1647,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top
% 3.85/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1646]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1713,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top
% 3.85/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1489,c_1647]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_728,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 != X0
% 3.85/1.00      | arAF0_k5_xboole_0_0 = X0
% 3.85/1.00      | arAF0_k5_xboole_0_0 = X1
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.85/1.00      inference(equality_factoring,[status(thm)],[c_486]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1730,plain,
% 3.85/1.00      ( arAF0_k5_xboole_0_0 = X0
% 3.85/1.00      | arAF0_k5_xboole_0_0 = X1
% 3.85/1.00      | k1_xboole_0 != X0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top
% 3.85/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1713,c_728]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_730,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | arAF0_k5_enumset1_0 != X1
% 3.85/1.00      | arAF0_k5_xboole_0_0 = X1
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.85/1.00      inference(equality_factoring,[status(thm)],[c_486]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1729,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | arAF0_k5_xboole_0_0 = X1
% 3.85/1.00      | k1_xboole_0 != X1
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top
% 3.85/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1713,c_730]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1500,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 = X0
% 3.85/1.00      | k1_xboole_0 != X0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top
% 3.85/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.85/1.00      inference(equality_factoring,[status(thm)],[c_1354]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_713,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.85/1.00      | sK0 != X1
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_486,c_11]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_33,plain,( sK0 = sK0 ),inference(instantiation,[status(thm)],[c_26]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_179,plain,
% 3.85/1.00      ( sK1 != X0 | sK0 != X0 | sK0 = sK1 ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_180,plain,
% 3.85/1.00      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_179]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_718,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.85/1.00      | sK1 = X0
% 3.85/1.00      | sK0 != X1
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_486,c_11]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_887,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.85/1.00      | sK1 = sK0
% 3.85/1.00      | sK0 != sK0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_718]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_904,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_713,c_11,c_33,c_180,c_887]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_729,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | arAF0_k5_enumset1_0 = X1
% 3.85/1.00      | arAF0_k5_xboole_0_0 != X1
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.85/1.00      inference(equality_factoring,[status(thm)],[c_486]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_0,plain,
% 3.85/1.00      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.85/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_387,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_10 | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.85/1.00      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_491,plain,
% 3.85/1.00      ( arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
% 3.85/1.00      | iProver_ARSWP_10 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_711,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.85/1.00      | arAF0_k5_xboole_0_0 = X1
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top
% 3.85/1.00      | iProver_ARSWP_10 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_486,c_491]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_722,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.85/1.00      | arAF0_k5_xboole_0_0 != X1
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.85/1.00      inference(equality_factoring,[status(thm)],[c_486]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_852,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.85/1.00      | iProver_ARSWP_15 != iProver_top
% 3.85/1.00      | iProver_ARSWP_10 != iProver_top ),
% 3.85/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_711,c_722]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_620,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_10 | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
% 3.85/1.00      inference(resolution,[status(thm)],[c_604,c_387]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_621,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.85/1.00      | iProver_ARSWP_10 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1312,plain,
% 3.85/1.00      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.85/1.00      | iProver_ARSWP_10 != iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,[status(thm)],[c_852,c_621]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1,plain,
% 3.85/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_388,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_11 | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.85/1.00      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_490,plain,
% 3.85/1.00      ( arAF0_k3_xboole_0_0_1(X0) = X0 | iProver_ARSWP_11 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  % SZS output end Saturation for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  ------                               Statistics
% 3.85/1.00  
% 3.85/1.00  ------ Selected
% 3.85/1.00  
% 3.85/1.00  total_time:                             0.109
% 3.85/1.00  
%------------------------------------------------------------------------------
