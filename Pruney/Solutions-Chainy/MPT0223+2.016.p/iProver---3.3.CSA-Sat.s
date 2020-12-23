%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:47 EST 2020

% Result     : CounterSatisfiable 7.67s
% Output     : Saturation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  302 (17947 expanded)
%              Number of clauses        :  239 (4715 expanded)
%              Number of leaves         :   25 (5045 expanded)
%              Depth                    :   22
%              Number of atoms          : 1155 (31248 expanded)
%              Number of equality atoms : 1100 (27508 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    7 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f71,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f17,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f18,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f53,f45,f66,f57])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f25])).

fof(f33,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( sK2 != sK3
    & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f38])).

fof(f64,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f54,f65,f66,f62])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f55,f65,f62,f66])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f36])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f47,f45])).

fof(f63,plain,(
    k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    k3_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_enumset1(sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f63,f66,f66,f66])).

cnf(c_60,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1617,plain,
    ( ~ iProver_ARSWP_43
    | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1780,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1617])).

cnf(c_12,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1624,plain,
    ( ~ iProver_ARSWP_50
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_1773,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_50 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1624])).

cnf(c_14,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1881,plain,
    ( ~ iProver_ARSWP_50
    | X0 = sK3
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_1882,plain,
    ( X0 = sK3
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK2 = sK3
    | iProver_ARSWP_50 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1881])).

cnf(c_1884,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK2 = sK3
    | iProver_ARSWP_50 != iProver_top ),
    inference(instantiation,[status(thm)],[c_1882])).

cnf(c_2211,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_50 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1773,c_14,c_1884])).

cnf(c_2217,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_2211])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1618,plain,
    ( ~ iProver_ARSWP_44
    | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_1779,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1618])).

cnf(c_5972,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_1779])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_5983,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5972,c_9])).

cnf(c_6028,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5983,c_2217])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1945,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_3])).

cnf(c_6108,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6028,c_1945])).

cnf(c_6434,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_2211])).

cnf(c_6446,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6434,c_9])).

cnf(c_6040,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5983,c_1779])).

cnf(c_6074,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6040,c_1945])).

cnf(c_9306,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6446,c_6074])).

cnf(c_9359,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_9306,c_1945])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1621,plain,
    ( r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0)
    | r1_xboole_0(X0,X1)
    | ~ iProver_ARSWP_47 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_1776,plain,
    ( r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1621])).

cnf(c_9396,plain,
    ( r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_9359,c_1776])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1620,plain,
    ( ~ r2_hidden(X0,arAF0_k3_xboole_0_0)
    | ~ r1_xboole_0(X1,X2)
    | ~ iProver_ARSWP_46 ),
    inference(arg_filter_abstr,[status(unp)],[c_4])).

cnf(c_1777,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1620])).

cnf(c_20741,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_9396,c_1777])).

cnf(c_22306,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_9359,c_20741])).

cnf(c_25368,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5983,c_22306])).

cnf(c_13,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1625,plain,
    ( ~ iProver_ARSWP_51
    | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_13])).

cnf(c_1772,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1625])).

cnf(c_2219,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top ),
    inference(superposition,[status(thm)],[c_2211,c_1772])).

cnf(c_7596,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_2219])).

cnf(c_7606,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7596,c_9])).

cnf(c_2059,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1772])).

cnf(c_7650,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7606,c_2059])).

cnf(c_7713,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7650,c_1945])).

cnf(c_7940,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7713,c_2217])).

cnf(c_8051,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7940,c_9])).

cnf(c_7642,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7606,c_2217])).

cnf(c_7743,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7642,c_1945])).

cnf(c_8412,plain,
    ( r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7743,c_1776])).

cnf(c_19958,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_8412,c_1777])).

cnf(c_22054,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7743,c_19958])).

cnf(c_24401,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_8051,c_22054])).

cnf(c_7949,plain,
    ( r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7713,c_1776])).

cnf(c_19682,plain,
    ( r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7606,c_7949])).

cnf(c_19911,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_19682,c_1777])).

cnf(c_21968,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7743,c_19911])).

cnf(c_24151,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_8051,c_21968])).

cnf(c_19685,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7949,c_1777])).

cnf(c_21659,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7743,c_19685])).

cnf(c_23597,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_8051,c_21659])).

cnf(c_6432,plain,
    ( r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_1776])).

cnf(c_18403,plain,
    ( r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6446,c_6432])).

cnf(c_19113,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_18403,c_1777])).

cnf(c_21571,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_9359,c_19113])).

cnf(c_23324,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5983,c_21571])).

cnf(c_18407,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6432,c_1777])).

cnf(c_21313,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_9359,c_18407])).

cnf(c_22381,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5983,c_21313])).

cnf(c_22309,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_20741])).

cnf(c_22055,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7713,c_19958])).

cnf(c_21969,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7713,c_19911])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1783,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21959,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_19911])).

cnf(c_21660,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7713,c_19685])).

cnf(c_21574,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_19113])).

cnf(c_21316,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_18407])).

cnf(c_3444,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1777])).

cnf(c_12351,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_3444])).

cnf(c_15920,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_9359,c_12351])).

cnf(c_21050,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5983,c_15920])).

cnf(c_12354,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7743,c_3444])).

cnf(c_20448,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_8051,c_12354])).

cnf(c_12353,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_9359,c_3444])).

cnf(c_20374,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5983,c_12353])).

cnf(c_8,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1622,plain,
    ( r1_xboole_0(k5_xboole_0(X0,arAF0_k3_xboole_0_0),X1)
    | ~ iProver_ARSWP_48 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_1775,plain,
    ( r1_xboole_0(k5_xboole_0(X0,arAF0_k3_xboole_0_0),X1) = iProver_top
    | iProver_ARSWP_48 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1622])).

cnf(c_2382,plain,
    ( r1_xboole_0(arAF0_k3_xboole_0_0,X0) = iProver_top
    | iProver_ARSWP_48 != iProver_top ),
    inference(superposition,[status(thm)],[c_1945,c_1775])).

cnf(c_3450,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_1777])).

cnf(c_11557,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_3450])).

cnf(c_12753,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_11557,c_2059])).

cnf(c_12798,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_12753,c_7,c_9])).

cnf(c_15470,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_12798,c_2059])).

cnf(c_15544,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_15470,c_1945])).

cnf(c_16039,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_15544,c_1772])).

cnf(c_19405,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_16039])).

cnf(c_2378,plain,
    ( r1_xboole_0(k5_xboole_0(arAF0_k3_xboole_0_0,X0),X1) = iProver_top
    | iProver_ARSWP_48 != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1775])).

cnf(c_7948,plain,
    ( r1_xboole_0(k5_xboole_0(arAF0_k6_enumset1_0,X0),X1) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7713,c_2378])).

cnf(c_17493,plain,
    ( r1_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7606,c_7948])).

cnf(c_17508,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17493,c_1945])).

cnf(c_3389,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1779])).

cnf(c_12739,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_11557,c_3389])).

cnf(c_12854,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_12739,c_7,c_9])).

cnf(c_15756,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_12854,c_1779])).

cnf(c_15787,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_15756,c_1945])).

cnf(c_17408,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_15787])).

cnf(c_15478,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_12798,c_1772])).

cnf(c_15484,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_15478,c_1945])).

cnf(c_17240,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_15544,c_15484])).

cnf(c_17238,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_15484])).

cnf(c_15733,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_12854,c_3389])).

cnf(c_15861,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_15733,c_1945])).

cnf(c_17059,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_15861,c_3450])).

cnf(c_16018,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_15544,c_3450])).

cnf(c_15923,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_12351])).

cnf(c_15922,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7713,c_12351])).

cnf(c_15921,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7743,c_12351])).

cnf(c_15,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_enumset1(sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1626,negated_conjecture,
    ( ~ iProver_ARSWP_52
    | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_15])).

cnf(c_1771,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_52 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1626])).

cnf(c_2218,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_2211])).

cnf(c_2229,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2218,c_9])).

cnf(c_2351,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_1780])).

cnf(c_4512,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_2351,c_2059])).

cnf(c_4529,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4512,c_1945])).

cnf(c_70,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2090,plain,
    ( ~ iProver_ARSWP_52
    | X0 != arAF0_k1_enumset1_0
    | arAF0_k3_xboole_0_0 = X0 ),
    inference(resolution,[status(thm)],[c_70,c_1626])).

cnf(c_2264,plain,
    ( ~ iProver_ARSWP_52
    | ~ iProver_ARSWP_43
    | arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(resolution,[status(thm)],[c_2090,c_1617])).

cnf(c_2265,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2264])).

cnf(c_5123,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4529,c_2265])).

cnf(c_11564,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_3450])).

cnf(c_11672,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_11564])).

cnf(c_11931,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_11672,c_1780])).

cnf(c_14508,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_11931,c_1772])).

cnf(c_14515,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_14508,c_1945])).

cnf(c_15292,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_14515])).

cnf(c_12755,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(superposition,[status(thm)],[c_11557,c_1779])).

cnf(c_12788,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(demodulation,[status(thm)],[c_12755,c_7])).

cnf(c_14081,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(superposition,[status(thm)],[c_12788,c_3])).

cnf(c_12358,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_3444])).

cnf(c_12898,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_12358])).

cnf(c_3137,plain,
    ( r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_1776])).

cnf(c_3667,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_3137,c_1777])).

cnf(c_3899,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_3667])).

cnf(c_3933,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_3899])).

cnf(c_4146,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_3933])).

cnf(c_12890,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_4146,c_12358])).

cnf(c_3930,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_3899])).

cnf(c_12892,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_3930,c_12358])).

cnf(c_12759,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_11557,c_1775])).

cnf(c_12780,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12759,c_7])).

cnf(c_12761,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_11557,c_1772])).

cnf(c_12767,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(demodulation,[status(thm)],[c_12761,c_7])).

cnf(c_12737,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_11557,c_3450])).

cnf(c_12357,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_3444])).

cnf(c_12356,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_3444])).

cnf(c_12355,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7713,c_3444])).

cnf(c_11925,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(superposition,[status(thm)],[c_11672,c_1779])).

cnf(c_11973,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(demodulation,[status(thm)],[c_11925,c_1945])).

cnf(c_2383,plain,
    ( r1_xboole_0(k5_xboole_0(X0,arAF0_k1_enumset1_0),X1) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_1775])).

cnf(c_11928,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_11672,c_2383])).

cnf(c_11963,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11928,c_7])).

cnf(c_11930,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_11672,c_1772])).

cnf(c_11947,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(demodulation,[status(thm)],[c_11930,c_1945])).

cnf(c_11903,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_11672,c_11564])).

cnf(c_11563,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_3450])).

cnf(c_11562,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_3450])).

cnf(c_11560,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7743,c_3450])).

cnf(c_6431,plain,
    ( r1_xboole_0(k5_xboole_0(arAF0_k1_enumset1_0,X0),X1) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_2378])).

cnf(c_10701,plain,
    ( r1_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6446,c_6431])).

cnf(c_10711,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10701,c_1945])).

cnf(c_10346,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_3389])).

cnf(c_10344,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_3389])).

cnf(c_7658,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7606,c_1772])).

cnf(c_7663,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7658,c_1945])).

cnf(c_9765,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7713,c_7663])).

cnf(c_6552,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6446,c_1779])).

cnf(c_6574,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6552,c_1945])).

cnf(c_9730,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_6574])).

cnf(c_9398,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_9359,c_2211])).

cnf(c_9383,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_9359,c_6074])).

cnf(c_2381,plain,
    ( r1_xboole_0(arAF0_k1_enumset1_0,X0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top ),
    inference(superposition,[status(thm)],[c_2211,c_1775])).

cnf(c_9021,plain,
    ( r1_xboole_0(arAF0_k6_enumset1_0,X0) = iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_2381])).

cnf(c_8407,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7743,c_2059])).

cnf(c_8402,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7743,c_2217])).

cnf(c_8124,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_8051,c_1772])).

cnf(c_8130,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_8124,c_1945])).

cnf(c_7952,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7713,c_1772])).

cnf(c_7951,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_7713,c_2211])).

cnf(c_7379,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_4146])).

cnf(c_3666,plain,
    ( r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_3137])).

cnf(c_5517,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3666,c_1777])).

cnf(c_6985,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_5517])).

cnf(c_7220,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_6985])).

cnf(c_6984,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_5517])).

cnf(c_6981,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_5517])).

cnf(c_6429,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_1779])).

cnf(c_6422,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_6108,c_2217])).

cnf(c_5967,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_2217])).

cnf(c_3665,plain,
    ( r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_3137])).

cnf(c_4304,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_3665,c_1777])).

cnf(c_5544,plain,
    ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_4304])).

cnf(c_5742,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_5544])).

cnf(c_5543,plain,
    ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_4304])).

cnf(c_5541,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_4304])).

cnf(c_5141,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_1772])).

cnf(c_5140,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_2211])).

cnf(c_3388,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_1779])).

cnf(c_3428,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3388,c_1945])).

cnf(c_4818,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(superposition,[status(thm)],[c_3428,c_1779])).

cnf(c_4815,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_3428])).

cnf(c_4514,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_2059])).

cnf(c_4277,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_3930])).

cnf(c_3932,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_3899])).

cnf(c_3897,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_3667])).

cnf(c_2544,plain,
    ( r1_xboole_0(k5_xboole_0(arAF0_k1_enumset1_0,X0),X1) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_2383])).

cnf(c_3392,plain,
    ( r1_xboole_0(arAF0_k6_enumset1_0,X0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_2544])).

cnf(c_3391,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_1779])).

cnf(c_5142,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_1771])).

cnf(c_69,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2085,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_70,c_69])).

cnf(c_3153,plain,
    ( ~ iProver_ARSWP_43
    | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
    inference(resolution,[status(thm)],[c_2085,c_1617])).

cnf(c_3154,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3153])).

cnf(c_5190,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5142,c_3154])).

cnf(c_2734,plain,
    ( r1_xboole_0(k5_xboole_0(arAF0_k6_enumset1_0,X0),X1) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_2544])).

cnf(c_2547,plain,
    ( r1_xboole_0(arAF0_k1_enumset1_0,X0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top ),
    inference(superposition,[status(thm)],[c_1945,c_2383])).

cnf(c_2708,plain,
    ( r1_xboole_0(arAF0_k6_enumset1_0,X0) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_2547])).

cnf(c_2548,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_2383])).

cnf(c_2562,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_48 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2548,c_7])).

cnf(c_2549,plain,
    ( r1_xboole_0(k5_xboole_0(X0,arAF0_k6_enumset1_0),X1) = iProver_top
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_2383])).

cnf(c_2380,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top
    | iProver_ARSWP_48 != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1775])).

cnf(c_2350,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_1772])).

cnf(c_2364,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2350,c_1945])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.67/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/1.47  
% 7.67/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.47  
% 7.67/1.47  ------  iProver source info
% 7.67/1.47  
% 7.67/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.47  git: non_committed_changes: false
% 7.67/1.47  git: last_make_outside_of_git: false
% 7.67/1.47  
% 7.67/1.47  ------ 
% 7.67/1.47  ------ Parsing...
% 7.67/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.47  
% 7.67/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.67/1.47  
% 7.67/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.47  
% 7.67/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.47  ------ Proving...
% 7.67/1.47  ------ Problem Properties 
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  clauses                                 16
% 7.67/1.47  conjectures                             2
% 7.67/1.47  EPR                                     1
% 7.67/1.47  Horn                                    13
% 7.67/1.47  unary                                   12
% 7.67/1.47  binary                                  3
% 7.67/1.47  lits                                    21
% 7.67/1.47  lits eq                                 15
% 7.67/1.47  fd_pure                                 0
% 7.67/1.47  fd_pseudo                               0
% 7.67/1.47  fd_cond                                 1
% 7.67/1.47  fd_pseudo_cond                          1
% 7.67/1.47  AC symbols                              0
% 7.67/1.47  
% 7.67/1.47  ------ Input Options Time Limit: Unbounded
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.67/1.47  Current options:
% 7.67/1.47  ------ 
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  ------ Proving...
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.47  
% 7.67/1.47  ------ Proving...
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.47  
% 7.67/1.47  ------ Proving...
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.47  
% 7.67/1.47  ------ Proving...
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.47  
% 7.67/1.47  ------ Proving...
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.47  
% 7.67/1.47  ------ Proving...
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.47  
% 7.67/1.47  ------ Proving...
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.47  
% 7.67/1.47  ------ Proving...
% 7.67/1.47  
% 7.67/1.47  
% 7.67/1.47  % SZS status CounterSatisfiable for theBenchmark.p
% 7.67/1.47  
% 7.67/1.47  % SZS output start Saturation for theBenchmark.p
% 7.67/1.47  
% 7.67/1.47  fof(f19,axiom,(
% 7.67/1.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f58,plain,(
% 7.67/1.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f19])).
% 7.67/1.48  
% 7.67/1.48  fof(f20,axiom,(
% 7.67/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f59,plain,(
% 7.67/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f20])).
% 7.67/1.48  
% 7.67/1.48  fof(f21,axiom,(
% 7.67/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f60,plain,(
% 7.67/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f21])).
% 7.67/1.48  
% 7.67/1.48  fof(f22,axiom,(
% 7.67/1.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f61,plain,(
% 7.67/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f22])).
% 7.67/1.48  
% 7.67/1.48  fof(f23,axiom,(
% 7.67/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f62,plain,(
% 7.67/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f23])).
% 7.67/1.48  
% 7.67/1.48  fof(f67,plain,(
% 7.67/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.67/1.48    inference(definition_unfolding,[],[f61,f62])).
% 7.67/1.48  
% 7.67/1.48  fof(f68,plain,(
% 7.67/1.48    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.67/1.48    inference(definition_unfolding,[],[f60,f67])).
% 7.67/1.48  
% 7.67/1.48  fof(f69,plain,(
% 7.67/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.67/1.48    inference(definition_unfolding,[],[f59,f68])).
% 7.67/1.48  
% 7.67/1.48  fof(f71,plain,(
% 7.67/1.48    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.67/1.48    inference(definition_unfolding,[],[f58,f69])).
% 7.67/1.48  
% 7.67/1.48  fof(f14,axiom,(
% 7.67/1.48    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f32,plain,(
% 7.67/1.48    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 7.67/1.48    inference(ennf_transformation,[],[f14])).
% 7.67/1.48  
% 7.67/1.48  fof(f53,plain,(
% 7.67/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 7.67/1.48    inference(cnf_transformation,[],[f32])).
% 7.67/1.48  
% 7.67/1.48  fof(f5,axiom,(
% 7.67/1.48    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f45,plain,(
% 7.67/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f5])).
% 7.67/1.48  
% 7.67/1.48  fof(f17,axiom,(
% 7.67/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f56,plain,(
% 7.67/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f17])).
% 7.67/1.48  
% 7.67/1.48  fof(f66,plain,(
% 7.67/1.48    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 7.67/1.48    inference(definition_unfolding,[],[f56,f57])).
% 7.67/1.48  
% 7.67/1.48  fof(f18,axiom,(
% 7.67/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f57,plain,(
% 7.67/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f18])).
% 7.67/1.48  
% 7.67/1.48  fof(f76,plain,(
% 7.67/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 7.67/1.48    inference(definition_unfolding,[],[f53,f45,f66,f57])).
% 7.67/1.48  
% 7.67/1.48  fof(f25,conjecture,(
% 7.67/1.48    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f26,negated_conjecture,(
% 7.67/1.48    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.67/1.48    inference(negated_conjecture,[],[f25])).
% 7.67/1.48  
% 7.67/1.48  fof(f33,plain,(
% 7.67/1.48    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 7.67/1.48    inference(ennf_transformation,[],[f26])).
% 7.67/1.48  
% 7.67/1.48  fof(f38,plain,(
% 7.67/1.48    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 7.67/1.48    introduced(choice_axiom,[])).
% 7.67/1.48  
% 7.67/1.48  fof(f39,plain,(
% 7.67/1.48    sK2 != sK3 & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 7.67/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f38])).
% 7.67/1.48  
% 7.67/1.48  fof(f64,plain,(
% 7.67/1.48    sK2 != sK3),
% 7.67/1.48    inference(cnf_transformation,[],[f39])).
% 7.67/1.48  
% 7.67/1.48  fof(f15,axiom,(
% 7.67/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f54,plain,(
% 7.67/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f15])).
% 7.67/1.48  
% 7.67/1.48  fof(f10,axiom,(
% 7.67/1.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f49,plain,(
% 7.67/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f10])).
% 7.67/1.48  
% 7.67/1.48  fof(f65,plain,(
% 7.67/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.67/1.48    inference(definition_unfolding,[],[f49,f45])).
% 7.67/1.48  
% 7.67/1.48  fof(f72,plain,(
% 7.67/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.67/1.48    inference(definition_unfolding,[],[f54,f65,f66,f62])).
% 7.67/1.48  
% 7.67/1.48  fof(f9,axiom,(
% 7.67/1.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f48,plain,(
% 7.67/1.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.67/1.48    inference(cnf_transformation,[],[f9])).
% 7.67/1.48  
% 7.67/1.48  fof(f6,axiom,(
% 7.67/1.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f46,plain,(
% 7.67/1.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.67/1.48    inference(cnf_transformation,[],[f6])).
% 7.67/1.48  
% 7.67/1.48  fof(f2,axiom,(
% 7.67/1.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f41,plain,(
% 7.67/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f2])).
% 7.67/1.48  
% 7.67/1.48  fof(f3,axiom,(
% 7.67/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f27,plain,(
% 7.67/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.67/1.48    inference(rectify,[],[f3])).
% 7.67/1.48  
% 7.67/1.48  fof(f30,plain,(
% 7.67/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.67/1.48    inference(ennf_transformation,[],[f27])).
% 7.67/1.48  
% 7.67/1.48  fof(f34,plain,(
% 7.67/1.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.67/1.48    introduced(choice_axiom,[])).
% 7.67/1.48  
% 7.67/1.48  fof(f35,plain,(
% 7.67/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.67/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f34])).
% 7.67/1.48  
% 7.67/1.48  fof(f42,plain,(
% 7.67/1.48    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f35])).
% 7.67/1.48  
% 7.67/1.48  fof(f43,plain,(
% 7.67/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.67/1.48    inference(cnf_transformation,[],[f35])).
% 7.67/1.48  
% 7.67/1.48  fof(f16,axiom,(
% 7.67/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f55,plain,(
% 7.67/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f16])).
% 7.67/1.48  
% 7.67/1.48  fof(f77,plain,(
% 7.67/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.67/1.48    inference(definition_unfolding,[],[f55,f65,f62,f66])).
% 7.67/1.48  
% 7.67/1.48  fof(f4,axiom,(
% 7.67/1.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f31,plain,(
% 7.67/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.67/1.48    inference(ennf_transformation,[],[f4])).
% 7.67/1.48  
% 7.67/1.48  fof(f36,plain,(
% 7.67/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.67/1.48    introduced(choice_axiom,[])).
% 7.67/1.48  
% 7.67/1.48  fof(f37,plain,(
% 7.67/1.48    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 7.67/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f36])).
% 7.67/1.48  
% 7.67/1.48  fof(f44,plain,(
% 7.67/1.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 7.67/1.48    inference(cnf_transformation,[],[f37])).
% 7.67/1.48  
% 7.67/1.48  fof(f8,axiom,(
% 7.67/1.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f47,plain,(
% 7.67/1.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f8])).
% 7.67/1.48  
% 7.67/1.48  fof(f73,plain,(
% 7.67/1.48    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 7.67/1.48    inference(definition_unfolding,[],[f47,f45])).
% 7.67/1.48  
% 7.67/1.48  fof(f63,plain,(
% 7.67/1.48    k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 7.67/1.48    inference(cnf_transformation,[],[f39])).
% 7.67/1.48  
% 7.67/1.48  fof(f78,plain,(
% 7.67/1.48    k3_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_enumset1(sK2,sK2,sK2)),
% 7.67/1.48    inference(definition_unfolding,[],[f63,f66,f66,f66])).
% 7.67/1.48  
% 7.67/1.48  cnf(c_60,plain,( X0_2 = X0_2 ),theory(equality) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_0,plain,
% 7.67/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 7.67/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1617,plain,
% 7.67/1.48      ( ~ iProver_ARSWP_43 | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
% 7.67/1.48      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1780,plain,
% 7.67/1.48      ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_1617]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12,plain,
% 7.67/1.48      ( X0 = X1
% 7.67/1.48      | X2 = X1
% 7.67/1.48      | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
% 7.67/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1624,plain,
% 7.67/1.48      ( ~ iProver_ARSWP_50
% 7.67/1.48      | X0 = X1
% 7.67/1.48      | X2 = X1
% 7.67/1.48      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 7.67/1.48      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1773,plain,
% 7.67/1.48      ( X0 = X1
% 7.67/1.48      | X2 = X1
% 7.67/1.48      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_1624]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_14,negated_conjecture,
% 7.67/1.48      ( sK2 != sK3 ),
% 7.67/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1881,plain,
% 7.67/1.48      ( ~ iProver_ARSWP_50
% 7.67/1.48      | X0 = sK3
% 7.67/1.48      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | sK2 = sK3 ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_1624]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1882,plain,
% 7.67/1.48      ( X0 = sK3
% 7.67/1.48      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | sK2 = sK3
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_1881]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1884,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | sK2 = sK3
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_1882]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2211,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_1773,c_14,c_1884]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2217,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_2211]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1,plain,
% 7.67/1.48      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 7.67/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1618,plain,
% 7.67/1.48      ( ~ iProver_ARSWP_44
% 7.67/1.48      | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 7.67/1.48      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1779,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_1618]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5972,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2217,c_1779]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9,plain,
% 7.67/1.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.67/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5983,plain,
% 7.67/1.48      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_5972,c_9]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6028,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5983,c_2217]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7,plain,
% 7.67/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.67/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3,plain,
% 7.67/1.48      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.67/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1945,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7,c_3]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6108,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_6028,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6434,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_2211]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6446,plain,
% 7.67/1.48      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_6434,c_9]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6040,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5983,c_1779]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6074,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_6040,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9306,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6446,c_6074]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9359,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_9306,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5,plain,
% 7.67/1.48      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 7.67/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1621,plain,
% 7.67/1.48      ( r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0)
% 7.67/1.48      | r1_xboole_0(X0,X1)
% 7.67/1.48      | ~ iProver_ARSWP_47 ),
% 7.67/1.48      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1776,plain,
% 7.67/1.48      ( r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_1621]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9396,plain,
% 7.67/1.48      ( r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_9359,c_1776]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_4,plain,
% 7.67/1.48      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.67/1.48      inference(cnf_transformation,[],[f43]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1620,plain,
% 7.67/1.48      ( ~ r2_hidden(X0,arAF0_k3_xboole_0_0)
% 7.67/1.48      | ~ r1_xboole_0(X1,X2)
% 7.67/1.48      | ~ iProver_ARSWP_46 ),
% 7.67/1.48      inference(arg_filter_abstr,[status(unp)],[c_4]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1777,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | r1_xboole_0(X1,X2) != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_1620]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_20741,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_9396,c_1777]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_22306,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_9359,c_20741]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_25368,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5983,c_22306]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_13,plain,
% 7.67/1.48      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 7.67/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1625,plain,
% 7.67/1.48      ( ~ iProver_ARSWP_51
% 7.67/1.48      | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 7.67/1.48      inference(arg_filter_abstr,[status(unp)],[c_13]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1772,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_1625]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2219,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2211,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7596,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_2219]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7606,plain,
% 7.67/1.48      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_7596,c_9]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2059,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7650,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7606,c_2059]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7713,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_7650,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7940,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7713,c_2217]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_8051,plain,
% 7.67/1.48      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_7940,c_9]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7642,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7606,c_2217]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7743,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_7642,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_8412,plain,
% 7.67/1.48      ( r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7743,c_1776]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_19958,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_8412,c_1777]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_22054,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7743,c_19958]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_24401,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_8051,c_22054]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7949,plain,
% 7.67/1.48      ( r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7713,c_1776]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_19682,plain,
% 7.67/1.48      ( r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7606,c_7949]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_19911,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_19682,c_1777]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_21968,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7743,c_19911]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_24151,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_8051,c_21968]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_19685,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7949,c_1777]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_21659,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7743,c_19685]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_23597,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_8051,c_21659]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6432,plain,
% 7.67/1.48      ( r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_1776]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_18403,plain,
% 7.67/1.48      ( r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6446,c_6432]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_19113,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_18403,c_1777]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_21571,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_9359,c_19113]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_23324,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5983,c_21571]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_18407,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6432,c_1777]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_21313,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_9359,c_18407]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_22381,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5983,c_21313]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_22309,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_20741]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_22055,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7713,c_19958]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_21969,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7713,c_19911]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6,plain,
% 7.67/1.48      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 7.67/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1783,plain,
% 7.67/1.48      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_21959,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1783,c_19911]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_21660,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7713,c_19685]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_21574,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_19113]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_21316,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_18407]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3444,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1776,c_1777]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12351,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1783,c_3444]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15920,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_9359,c_12351]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_21050,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5983,c_15920]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12354,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7743,c_3444]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_20448,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_8051,c_12354]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12353,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_9359,c_3444]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_20374,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5983,c_12353]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_8,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 7.67/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1622,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(X0,arAF0_k3_xboole_0_0),X1)
% 7.67/1.48      | ~ iProver_ARSWP_48 ),
% 7.67/1.48      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1775,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(X0,arAF0_k3_xboole_0_0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_1622]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2382,plain,
% 7.67/1.48      ( r1_xboole_0(arAF0_k3_xboole_0_0,X0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1945,c_1775]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3450,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2382,c_1777]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11557,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1783,c_3450]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12753,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11557,c_2059]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12798,plain,
% 7.67/1.48      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_12753,c_7,c_9]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15470,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_12798,c_2059]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15544,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_15470,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_16039,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_15544,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_19405,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_3,c_16039]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2378,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(arAF0_k3_xboole_0_0,X0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_3,c_1775]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7948,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(arAF0_k6_enumset1_0,X0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7713,c_2378]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_17493,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7606,c_7948]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_17508,plain,
% 7.67/1.48      ( r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(light_normalisation,[status(thm)],[c_17493,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3389,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_1779]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12739,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11557,c_3389]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12854,plain,
% 7.67/1.48      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_12739,c_7,c_9]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15756,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_12854,c_1779]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15787,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_15756,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_17408,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_15787]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15478,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_12798,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15484,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_15478,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_17240,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_15544,c_15484]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_17238,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_15484]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15733,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_12854,c_3389]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15861,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_15733,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_17059,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_15861,c_3450]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_16018,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_15544,c_3450]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15923,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_12351]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15922,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7713,c_12351]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15921,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7743,c_12351]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15,negated_conjecture,
% 7.67/1.48      ( k3_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_enumset1(sK2,sK2,sK2) ),
% 7.67/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1626,negated_conjecture,
% 7.67/1.48      ( ~ iProver_ARSWP_52 | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
% 7.67/1.48      inference(arg_filter_abstr,[status(unp)],[c_15]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1771,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_1626]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2218,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_2211]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2229,plain,
% 7.67/1.48      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_2218,c_9]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2351,plain,
% 7.67/1.48      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2229,c_1780]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_4512,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2351,c_2059]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_4529,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_4512,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_70,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2090,plain,
% 7.67/1.48      ( ~ iProver_ARSWP_52
% 7.67/1.48      | X0 != arAF0_k1_enumset1_0
% 7.67/1.48      | arAF0_k3_xboole_0_0 = X0 ),
% 7.67/1.48      inference(resolution,[status(thm)],[c_70,c_1626]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2264,plain,
% 7.67/1.48      ( ~ iProver_ARSWP_52
% 7.67/1.48      | ~ iProver_ARSWP_43
% 7.67/1.48      | arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 7.67/1.48      inference(resolution,[status(thm)],[c_2090,c_1617]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2265,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_2264]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5123,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(global_propositional_subsumption,[status(thm)],[c_4529,c_2265]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11564,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_3450]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11672,plain,
% 7.67/1.48      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1783,c_11564]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11931,plain,
% 7.67/1.48      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11672,c_1780]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_14508,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11931,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_14515,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_14508,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_15292,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5123,c_14515]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12755,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11557,c_1779]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12788,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_12755,c_7]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_14081,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_12788,c_3]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12358,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_3444]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12898,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2229,c_12358]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3137,plain,
% 7.67/1.48      ( r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_1776]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3667,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_3137,c_1777]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3899,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_3667]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3933,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_3899]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_4146,plain,
% 7.67/1.48      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1783,c_3933]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12890,plain,
% 7.67/1.48      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_4146,c_12358]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3930,plain,
% 7.67/1.48      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1783,c_3899]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12892,plain,
% 7.67/1.48      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_3930,c_12358]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12759,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11557,c_1775]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12780,plain,
% 7.67/1.48      ( r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(light_normalisation,[status(thm)],[c_12759,c_7]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12761,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11557,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12767,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_12761,c_7]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12737,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11557,c_3450]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12357,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5123,c_3444]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12356,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_3444]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12355,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7713,c_3444]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11925,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11672,c_1779]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11973,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_11925,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2383,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(X0,arAF0_k1_enumset1_0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_1775]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11928,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11672,c_2383]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11963,plain,
% 7.67/1.48      ( r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(light_normalisation,[status(thm)],[c_11928,c_7]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11930,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11672,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11947,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_11930,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11903,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_11672,c_11564]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11563,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5123,c_3450]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11562,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_3450]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_11560,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7743,c_3450]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6431,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(arAF0_k1_enumset1_0,X0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_2378]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_10701,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6446,c_6431]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_10711,plain,
% 7.67/1.48      ( r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(light_normalisation,[status(thm)],[c_10701,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_10346,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_3389]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_10344,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_3389]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7658,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7606,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7663,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_7658,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9765,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7713,c_7663]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6552,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6446,c_1779]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6574,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_6552,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9730,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_6574]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9398,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_9359,c_2211]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9383,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_9359,c_6074]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2381,plain,
% 7.67/1.48      ( r1_xboole_0(arAF0_k1_enumset1_0,X0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2211,c_1775]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9021,plain,
% 7.67/1.48      ( r1_xboole_0(arAF0_k6_enumset1_0,X0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_2381]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_8407,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7743,c_2059]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_8402,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7743,c_2217]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_8124,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_8051,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_8130,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_8124,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7952,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7713,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7951,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7713,c_2211]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7379,plain,
% 7.67/1.48      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_4146]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3666,plain,
% 7.67/1.48      ( r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_3137]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5517,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_3666,c_1777]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6985,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_5517]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7220,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2229,c_6985]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6984,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5123,c_5517]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6981,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1783,c_5517]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6429,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_1779]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6422,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_6108,c_2217]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5967,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_2217]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3665,plain,
% 7.67/1.48      ( r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2229,c_3137]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_4304,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_3665,c_1777]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5544,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k1_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_4304]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5742,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2229,c_5544]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5543,plain,
% 7.67/1.48      ( r2_hidden(X0,arAF0_k6_enumset1_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5123,c_4304]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5541,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,k1_xboole_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1783,c_4304]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5141,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5123,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5140,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5123,c_2211]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3388,plain,
% 7.67/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2229,c_1779]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3428,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_3388,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_4818,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_3428,c_1779]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_4815,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_3428]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_4514,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_2059]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_4277,plain,
% 7.67/1.48      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k6_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_3930]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3932,plain,
% 7.67/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2229,c_3899]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3897,plain,
% 7.67/1.48      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 7.67/1.48      | r2_hidden(arAF0_sK0_0,arAF0_k1_enumset1_0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_47 != iProver_top
% 7.67/1.48      | iProver_ARSWP_46 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1783,c_3667]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2544,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(arAF0_k1_enumset1_0,X0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_3,c_2383]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3392,plain,
% 7.67/1.48      ( r1_xboole_0(arAF0_k6_enumset1_0,X0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1779,c_2544]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3391,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_44 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1771,c_1779]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5142,plain,
% 7.67/1.48      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5123,c_1771]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_69,plain,( X0 = X0 ),theory(equality) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2085,plain,
% 7.67/1.48      ( X0 != X1 | X1 = X0 ),
% 7.67/1.48      inference(resolution,[status(thm)],[c_70,c_69]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3153,plain,
% 7.67/1.48      ( ~ iProver_ARSWP_43 | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
% 7.67/1.48      inference(resolution,[status(thm)],[c_2085,c_1617]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3154,plain,
% 7.67/1.48      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_3153]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5190,plain,
% 7.67/1.48      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(global_propositional_subsumption,[status(thm)],[c_5142,c_3154]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2734,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(arAF0_k6_enumset1_0,X0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_2544]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2547,plain,
% 7.67/1.48      ( r1_xboole_0(arAF0_k1_enumset1_0,X0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1945,c_2383]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2708,plain,
% 7.67/1.48      ( r1_xboole_0(arAF0_k6_enumset1_0,X0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_2547]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2548,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2229,c_2383]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2562,plain,
% 7.67/1.48      ( r1_xboole_0(X0,X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top ),
% 7.67/1.48      inference(light_normalisation,[status(thm)],[c_2548,c_7]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2549,plain,
% 7.67/1.48      ( r1_xboole_0(k5_xboole_0(X0,arAF0_k6_enumset1_0),X1) = iProver_top
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top
% 7.67/1.48      | iProver_ARSWP_43 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1780,c_2383]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2380,plain,
% 7.67/1.48      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top
% 7.67/1.48      | iProver_ARSWP_48 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_9,c_1775]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2350,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2229,c_1772]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2364,plain,
% 7.67/1.48      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 7.67/1.48      | iProver_ARSWP_52 != iProver_top
% 7.67/1.48      | iProver_ARSWP_51 != iProver_top
% 7.67/1.48      | iProver_ARSWP_50 != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_2350,c_1945]) ).
% 7.67/1.48  
% 7.67/1.48  
% 7.67/1.48  % SZS output end Saturation for theBenchmark.p
% 7.67/1.48  
% 7.67/1.48  ------                               Statistics
% 7.67/1.48  
% 7.67/1.48  ------ Selected
% 7.67/1.48  
% 7.67/1.48  total_time:                             0.607
% 7.67/1.48  
%------------------------------------------------------------------------------
