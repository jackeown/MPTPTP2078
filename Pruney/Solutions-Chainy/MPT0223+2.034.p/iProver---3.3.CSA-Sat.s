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
% DateTime   : Thu Dec  3 11:29:49 EST 2020

% Result     : CounterSatisfiable 3.90s
% Output     : Saturation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  142 (3434 expanded)
%              Number of clauses        :   87 ( 763 expanded)
%              Number of leaves         :   24 (1006 expanded)
%              Depth                    :   16
%              Number of atoms          :  377 (5672 expanded)
%              Number of equality atoms :  337 (5431 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f27,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( sK1 != sK2
    & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f30])).

fof(f53,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f67,plain,(
    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f53,f56,f56,f56])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f61,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f43,f36,f56,f47])).

fof(f54,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f45,f55,f52,f56])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f44,f55,f56,f52])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

cnf(c_55,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_54,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_48,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_5,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1222,negated_conjecture,
    ( ~ iProver_ARSWP_30
    | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_13])).

cnf(c_1311,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1222])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1216,plain,
    ( ~ iProver_ARSWP_24
    | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1317,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_24 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_10,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1220,plain,
    ( ~ iProver_ARSWP_28
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_1313,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_28 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1220])).

cnf(c_12,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1381,plain,
    ( ~ iProver_ARSWP_28
    | X0 = sK2
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_1382,plain,
    ( X0 = sK2
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_28 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1381])).

cnf(c_1384,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_28 != iProver_top ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_1727,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_28 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1313,c_12,c_1384])).

cnf(c_11,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1221,plain,
    ( ~ iProver_ARSWP_29
    | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_1312,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1221])).

cnf(c_1735,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_1312])).

cnf(c_5598,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_1735])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5623,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5598,c_7])).

cnf(c_5667,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5623,c_1312])).

cnf(c_7292,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_5667])).

cnf(c_7566,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_7292])).

cnf(c_1733,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_1727])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1217,plain,
    ( ~ iProver_ARSWP_25
    | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_1316,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_25 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1217])).

cnf(c_2973,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1733,c_1316])).

cnf(c_2978,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2973,c_7])).

cnf(c_3188,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2978,c_1316])).

cnf(c_4469,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_3188])).

cnf(c_7272,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_4469])).

cnf(c_3179,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2978,c_1733])).

cnf(c_1616,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_1316])).

cnf(c_4432,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2978,c_1616])).

cnf(c_4670,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_3179,c_4432])).

cnf(c_6681,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_4670])).

cnf(c_5640,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5623,c_1735])).

cnf(c_5972,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_5640])).

cnf(c_1486,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_1312])).

cnf(c_5658,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5623,c_1486])).

cnf(c_5657,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5623,c_1733])).

cnf(c_1617,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_1316])).

cnf(c_5603,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_1617])).

cnf(c_4434,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_1616])).

cnf(c_4431,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1733,c_1616])).

cnf(c_1734,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_1727])).

cnf(c_1745,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1734,c_7])).

cnf(c_1763,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_1727])).

cnf(c_1925,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_1763])).

cnf(c_1768,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_1317])).

cnf(c_1767,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_1312])).

cnf(c_2790,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_1767])).

cnf(c_3471,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1768,c_2790])).

cnf(c_3701,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1925,c_3471])).

cnf(c_3905,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_3701])).

cnf(c_3704,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_3471])).

cnf(c_3476,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_2790])).

cnf(c_3189,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2978,c_1312])).

cnf(c_2970,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_1733])).

cnf(c_2826,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_1486])).

cnf(c_1766,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_1316])).

cnf(c_2402,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_1766])).

cnf(c_2428,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1768,c_2402])).

cnf(c_2615,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1925,c_2428])).

cnf(c_2037,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1768,c_1617])).

cnf(c_2650,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2615,c_2037])).

cnf(c_2617,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_2428])).

cnf(c_2264,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_2037])).

cnf(c_2084,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_1925])).

cnf(c_1764,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_1617])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1797,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1764,c_6])).

cnf(c_2237,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_1797])).

cnf(c_62,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_61,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1507,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_62,c_61])).

cnf(c_1648,plain,
    ( ~ iProver_ARSWP_24
    | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
    inference(resolution,[status(thm)],[c_1507,c_1216])).

cnf(c_1649,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_24 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1648])).

cnf(c_2946,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_24 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2237,c_1649])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:10:03 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.90/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/0.99  
% 3.90/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.90/0.99  
% 3.90/0.99  ------  iProver source info
% 3.90/0.99  
% 3.90/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.90/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.90/0.99  git: non_committed_changes: false
% 3.90/0.99  git: last_make_outside_of_git: false
% 3.90/0.99  
% 3.90/0.99  ------ 
% 3.90/0.99  ------ Parsing...
% 3.90/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.99  ------ Proving...
% 3.90/0.99  ------ Problem Properties 
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  clauses                                 11
% 3.90/0.99  conjectures                             2
% 3.90/0.99  EPR                                     1
% 3.90/0.99  Horn                                    10
% 3.90/0.99  unary                                   10
% 3.90/0.99  binary                                  0
% 3.90/0.99  lits                                    13
% 3.90/0.99  lits eq                                 13
% 3.90/0.99  fd_pure                                 0
% 3.90/0.99  fd_pseudo                               0
% 3.90/0.99  fd_cond                                 0
% 3.90/0.99  fd_pseudo_cond                          1
% 3.90/0.99  AC symbols                              0
% 3.90/0.99  
% 3.90/0.99  ------ Input Options Time Limit: Unbounded
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.90/0.99  Current options:
% 3.90/0.99  ------ 
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ Proving...
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.99  
% 3.90/0.99  ------ Proving...
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.99  
% 3.90/0.99  ------ Proving...
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.99  
% 3.90/0.99  ------ Proving...
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.99  
% 3.90/0.99  ------ Proving...
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.99  
% 3.90/0.99  ------ Proving...
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.99  
% 3.90/0.99  ------ Proving...
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.90/0.99  
% 3.90/0.99  % SZS output start Saturation for theBenchmark.p
% 3.90/0.99  
% 3.90/0.99  fof(f4,axiom,(
% 3.90/0.99    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f35,plain,(
% 3.90/0.99    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f4])).
% 3.90/0.99  
% 3.90/0.99  fof(f3,axiom,(
% 3.90/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f24,plain,(
% 3.90/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.90/0.99    inference(rectify,[],[f3])).
% 3.90/0.99  
% 3.90/0.99  fof(f25,plain,(
% 3.90/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.90/0.99    inference(ennf_transformation,[],[f24])).
% 3.90/0.99  
% 3.90/0.99  fof(f28,plain,(
% 3.90/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.90/0.99    introduced(choice_axiom,[])).
% 3.90/0.99  
% 3.90/0.99  fof(f29,plain,(
% 3.90/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.90/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f28])).
% 3.90/0.99  
% 3.90/0.99  fof(f33,plain,(
% 3.90/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f29])).
% 3.90/0.99  
% 3.90/0.99  fof(f34,plain,(
% 3.90/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f29])).
% 3.90/0.99  
% 3.90/0.99  fof(f22,conjecture,(
% 3.90/0.99    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f23,negated_conjecture,(
% 3.90/0.99    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.90/0.99    inference(negated_conjecture,[],[f22])).
% 3.90/0.99  
% 3.90/0.99  fof(f27,plain,(
% 3.90/0.99    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.90/0.99    inference(ennf_transformation,[],[f23])).
% 3.90/0.99  
% 3.90/0.99  fof(f30,plain,(
% 3.90/0.99    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 3.90/1.00    introduced(choice_axiom,[])).
% 3.90/1.00  
% 3.90/1.00  fof(f31,plain,(
% 3.90/1.00    sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 3.90/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f30])).
% 3.90/1.00  
% 3.90/1.00  fof(f53,plain,(
% 3.90/1.00    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 3.90/1.00    inference(cnf_transformation,[],[f31])).
% 3.90/1.00  
% 3.90/1.00  fof(f15,axiom,(
% 3.90/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f46,plain,(
% 3.90/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f15])).
% 3.90/1.00  
% 3.90/1.00  fof(f16,axiom,(
% 3.90/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f47,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f16])).
% 3.90/1.00  
% 3.90/1.00  fof(f56,plain,(
% 3.90/1.00    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.90/1.00    inference(definition_unfolding,[],[f46,f47])).
% 3.90/1.00  
% 3.90/1.00  fof(f67,plain,(
% 3.90/1.00    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1)),
% 3.90/1.00    inference(definition_unfolding,[],[f53,f56,f56,f56])).
% 3.90/1.00  
% 3.90/1.00  fof(f17,axiom,(
% 3.90/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f48,plain,(
% 3.90/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f17])).
% 3.90/1.00  
% 3.90/1.00  fof(f18,axiom,(
% 3.90/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f49,plain,(
% 3.90/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f18])).
% 3.90/1.00  
% 3.90/1.00  fof(f19,axiom,(
% 3.90/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f50,plain,(
% 3.90/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f19])).
% 3.90/1.00  
% 3.90/1.00  fof(f20,axiom,(
% 3.90/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f51,plain,(
% 3.90/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f20])).
% 3.90/1.00  
% 3.90/1.00  fof(f21,axiom,(
% 3.90/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f52,plain,(
% 3.90/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f21])).
% 3.90/1.00  
% 3.90/1.00  fof(f57,plain,(
% 3.90/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.90/1.00    inference(definition_unfolding,[],[f51,f52])).
% 3.90/1.00  
% 3.90/1.00  fof(f58,plain,(
% 3.90/1.00    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.90/1.00    inference(definition_unfolding,[],[f50,f57])).
% 3.90/1.00  
% 3.90/1.00  fof(f59,plain,(
% 3.90/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.90/1.00    inference(definition_unfolding,[],[f49,f58])).
% 3.90/1.00  
% 3.90/1.00  fof(f61,plain,(
% 3.90/1.00    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.90/1.00    inference(definition_unfolding,[],[f48,f59])).
% 3.90/1.00  
% 3.90/1.00  fof(f12,axiom,(
% 3.90/1.00    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f26,plain,(
% 3.90/1.00    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.90/1.00    inference(ennf_transformation,[],[f12])).
% 3.90/1.00  
% 3.90/1.00  fof(f43,plain,(
% 3.90/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.90/1.00    inference(cnf_transformation,[],[f26])).
% 3.90/1.00  
% 3.90/1.00  fof(f5,axiom,(
% 3.90/1.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f36,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f5])).
% 3.90/1.00  
% 3.90/1.00  fof(f65,plain,(
% 3.90/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.90/1.00    inference(definition_unfolding,[],[f43,f36,f56,f47])).
% 3.90/1.00  
% 3.90/1.00  fof(f54,plain,(
% 3.90/1.00    sK1 != sK2),
% 3.90/1.00    inference(cnf_transformation,[],[f31])).
% 3.90/1.00  
% 3.90/1.00  fof(f14,axiom,(
% 3.90/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f45,plain,(
% 3.90/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f14])).
% 3.90/1.00  
% 3.90/1.00  fof(f8,axiom,(
% 3.90/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f39,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f8])).
% 3.90/1.00  
% 3.90/1.00  fof(f55,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.90/1.00    inference(definition_unfolding,[],[f39,f36])).
% 3.90/1.00  
% 3.90/1.00  fof(f66,plain,(
% 3.90/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.90/1.00    inference(definition_unfolding,[],[f45,f55,f52,f56])).
% 3.90/1.00  
% 3.90/1.00  fof(f7,axiom,(
% 3.90/1.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f38,plain,(
% 3.90/1.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.90/1.00    inference(cnf_transformation,[],[f7])).
% 3.90/1.00  
% 3.90/1.00  fof(f13,axiom,(
% 3.90/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f44,plain,(
% 3.90/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f13])).
% 3.90/1.00  
% 3.90/1.00  fof(f62,plain,(
% 3.90/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.90/1.00    inference(definition_unfolding,[],[f44,f55,f56,f52])).
% 3.90/1.00  
% 3.90/1.00  fof(f6,axiom,(
% 3.90/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f37,plain,(
% 3.90/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.90/1.00    inference(cnf_transformation,[],[f6])).
% 3.90/1.00  
% 3.90/1.00  cnf(c_55,plain,
% 3.90/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.90/1.00      theory(equality) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_54,plain,
% 3.90/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.90/1.00      theory(equality) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_48,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5,plain,
% 3.90/1.00      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 3.90/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4,plain,
% 3.90/1.00      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 3.90/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3,plain,
% 3.90/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.90/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_13,negated_conjecture,
% 3.90/1.00      ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
% 3.90/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1222,negated_conjecture,
% 3.90/1.00      ( ~ iProver_ARSWP_30 | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
% 3.90/1.00      inference(arg_filter_abstr,[status(unp)],[c_13]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1311,plain,
% 3.90/1.00      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1222]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_0,plain,
% 3.90/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 3.90/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1216,plain,
% 3.90/1.00      ( ~ iProver_ARSWP_24 | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
% 3.90/1.00      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1317,plain,
% 3.90/1.00      ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1216]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_10,plain,
% 3.90/1.00      ( X0 = X1
% 3.90/1.00      | X2 = X1
% 3.90/1.00      | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
% 3.90/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1220,plain,
% 3.90/1.00      ( ~ iProver_ARSWP_28
% 3.90/1.00      | X0 = X1
% 3.90/1.00      | X2 = X1
% 3.90/1.00      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 3.90/1.00      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1313,plain,
% 3.90/1.00      ( X0 = X1
% 3.90/1.00      | X2 = X1
% 3.90/1.00      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1220]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12,negated_conjecture,
% 3.90/1.00      ( sK1 != sK2 ),
% 3.90/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1381,plain,
% 3.90/1.00      ( ~ iProver_ARSWP_28
% 3.90/1.00      | X0 = sK2
% 3.90/1.00      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | sK1 = sK2 ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1220]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1382,plain,
% 3.90/1.00      ( X0 = sK2
% 3.90/1.00      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | sK1 = sK2
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1381]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1384,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | sK1 = sK2
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1382]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1727,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_1313,c_12,c_1384]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_11,plain,
% 3.90/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.90/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1221,plain,
% 3.90/1.00      ( ~ iProver_ARSWP_29
% 3.90/1.00      | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 3.90/1.00      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1312,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1221]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1735,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1727,c_1312]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5598,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_1735]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7,plain,
% 3.90/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.90/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5623,plain,
% 3.90/1.00      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_5598,c_7]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5667,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_5623,c_1312]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7292,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_5667]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7566,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1311,c_7292]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1733,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_1727]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1,plain,
% 3.90/1.00      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.90/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1217,plain,
% 3.90/1.00      ( ~ iProver_ARSWP_25
% 3.90/1.00      | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 3.90/1.00      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1316,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1217]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2973,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1733,c_1316]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2978,plain,
% 3.90/1.00      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_2973,c_7]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3188,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2978,c_1316]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4469,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_3188]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7272,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1311,c_4469]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3179,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2978,c_1733]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1616,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_1316]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4432,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2978,c_1616]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4670,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_3179,c_4432]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6681,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_4670]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5640,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_5623,c_1735]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5972,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_5640]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1486,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_1312]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5658,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_5623,c_1486]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5657,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_5623,c_1733]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1617,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1311,c_1316]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5603,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1735,c_1617]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4434,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1311,c_1616]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4431,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1733,c_1616]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1734,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1311,c_1727]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1745,plain,
% 3.90/1.00      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_1734,c_7]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1763,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1745,c_1727]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1925,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1311,c_1763]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1768,plain,
% 3.90/1.00      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1745,c_1317]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1767,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1745,c_1312]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2790,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1311,c_1767]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3471,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1768,c_2790]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3701,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1925,c_3471]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3905,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_3701]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3704,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_3471]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3476,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_2790]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3189,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2978,c_1312]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2970,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1311,c_1733]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2826,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_29 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1311,c_1486]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1766,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1745,c_1316]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2402,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1311,c_1766]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2428,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1768,c_2402]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2615,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1925,c_2428]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2037,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1768,c_1617]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2650,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2615,c_2037]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2617,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_2428]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2264,plain,
% 3.90/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_2037]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2084,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1317,c_1925]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1764,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1745,c_1617]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.90/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1797,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_1764,c_6]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2237,plain,
% 3.90/1.00      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_30 != iProver_top
% 3.90/1.00      | iProver_ARSWP_28 != iProver_top
% 3.90/1.00      | iProver_ARSWP_25 != iProver_top
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2084,c_1797]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_62,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_61,plain,( X0 = X0 ),theory(equality) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1507,plain,
% 3.90/1.00      ( X0 != X1 | X1 = X0 ),
% 3.90/1.00      inference(resolution,[status(thm)],[c_62,c_61]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1648,plain,
% 3.90/1.00      ( ~ iProver_ARSWP_24 | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
% 3.90/1.00      inference(resolution,[status(thm)],[c_1507,c_1216]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1649,plain,
% 3.90/1.00      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1648]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2946,plain,
% 3.90/1.00      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.90/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.90/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2237,c_1649]) ).
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  % SZS output end Saturation for theBenchmark.p
% 3.90/1.00  
% 3.90/1.00  ------                               Statistics
% 3.90/1.00  
% 3.90/1.00  ------ Selected
% 3.90/1.00  
% 3.90/1.00  total_time:                             0.255
% 3.90/1.00  
%------------------------------------------------------------------------------
