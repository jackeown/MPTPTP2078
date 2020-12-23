%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:50 EST 2020

% Result     : CounterSatisfiable 0.35s
% Output     : Saturation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   82 (1055 expanded)
%              Number of clauses        :   32 ( 110 expanded)
%              Number of leaves         :   20 ( 339 expanded)
%              Depth                    :   17
%              Number of atoms          :  162 (1429 expanded)
%              Number of equality atoms :  125 (1352 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f24])).

fof(f29,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( sK1 != sK2
    & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f32])).

fof(f57,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f17,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f74,plain,(
    k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f57,f64,f64,f64])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f43,f38,f62,f64,f63])).

fof(f58,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f44,f59,f55,f64])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

cnf(c_56,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_55,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_49,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_4,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1058,negated_conjecture,
    ( ~ iProver_ARSWP_28
    | arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_15])).

cnf(c_1136,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_28 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1058])).

cnf(c_8,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1056,plain,
    ( ~ iProver_ARSWP_26
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_1138,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_14,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1183,plain,
    ( ~ iProver_ARSWP_26
    | X0 = sK2
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_1184,plain,
    ( X0 = sK2
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1183])).

cnf(c_1186,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_26 != iProver_top ),
    inference(instantiation,[status(thm)],[c_1184])).

cnf(c_1348,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1138,c_14,c_1186])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1053,plain,
    ( ~ iProver_ARSWP_23
    | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1141,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_23 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1053])).

cnf(c_1355,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_1141])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1359,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1355,c_6])).

cnf(c_1562,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_1141])).

cnf(c_1693,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1562])).

cnf(c_1561,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_1348])).

cnf(c_1691,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(superposition,[status(thm)],[c_1561,c_1562])).

cnf(c_1354,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1348])).

cnf(c_1366,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1354,c_6])).

cnf(c_1438,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_1348])).

cnf(c_1461,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1438])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:51:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.35/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.35/1.03  
% 0.35/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.35/1.03  
% 0.35/1.03  ------  iProver source info
% 0.35/1.03  
% 0.35/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.35/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.35/1.03  git: non_committed_changes: false
% 0.35/1.03  git: last_make_outside_of_git: false
% 0.35/1.03  
% 0.35/1.03  ------ 
% 0.35/1.03  ------ Parsing...
% 0.35/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.35/1.03  
% 0.35/1.03  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 0.35/1.03  
% 0.35/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.35/1.03  
% 0.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.35/1.03  ------ Proving...
% 0.35/1.03  ------ Problem Properties 
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  clauses                                 13
% 0.35/1.03  conjectures                             2
% 0.35/1.03  EPR                                     1
% 0.35/1.03  Horn                                    12
% 0.35/1.03  unary                                   12
% 0.35/1.03  binary                                  0
% 0.35/1.03  lits                                    15
% 0.35/1.03  lits eq                                 15
% 0.35/1.03  fd_pure                                 0
% 0.35/1.03  fd_pseudo                               0
% 0.35/1.03  fd_cond                                 0
% 0.35/1.03  fd_pseudo_cond                          1
% 0.35/1.03  AC symbols                              0
% 0.35/1.03  
% 0.35/1.03  ------ Input Options Time Limit: Unbounded
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 0.35/1.03  Current options:
% 0.35/1.03  ------ 
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  ------ Proving...
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.35/1.03  
% 0.35/1.03  ------ Proving...
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.35/1.03  
% 0.35/1.03  ------ Proving...
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.35/1.03  
% 0.35/1.03  ------ Proving...
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.35/1.03  
% 0.35/1.03  ------ Proving...
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.35/1.03  
% 0.35/1.03  ------ Proving...
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.35/1.03  
% 0.35/1.03  ------ Proving...
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  % SZS status CounterSatisfiable for theBenchmark.p
% 0.35/1.03  
% 0.35/1.03  % SZS output start Saturation for theBenchmark.p
% 0.35/1.03  
% 0.35/1.03  fof(f4,axiom,(
% 0.35/1.03    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f37,plain,(
% 0.35/1.03    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.35/1.03    inference(cnf_transformation,[],[f4])).
% 0.35/1.03  
% 0.35/1.03  fof(f3,axiom,(
% 0.35/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f26,plain,(
% 0.35/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.35/1.03    inference(rectify,[],[f3])).
% 0.35/1.03  
% 0.35/1.03  fof(f27,plain,(
% 0.35/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.35/1.03    inference(ennf_transformation,[],[f26])).
% 0.35/1.03  
% 0.35/1.03  fof(f30,plain,(
% 0.35/1.03    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 0.35/1.03    introduced(choice_axiom,[])).
% 0.35/1.03  
% 0.35/1.03  fof(f31,plain,(
% 0.35/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.35/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f30])).
% 0.35/1.03  
% 0.35/1.03  fof(f35,plain,(
% 0.35/1.03    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.35/1.03    inference(cnf_transformation,[],[f31])).
% 0.35/1.03  
% 0.35/1.03  fof(f36,plain,(
% 0.35/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.35/1.03    inference(cnf_transformation,[],[f31])).
% 0.35/1.03  
% 0.35/1.03  fof(f24,conjecture,(
% 0.35/1.03    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f25,negated_conjecture,(
% 0.35/1.03    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 0.35/1.03    inference(negated_conjecture,[],[f24])).
% 0.35/1.03  
% 0.35/1.03  fof(f29,plain,(
% 0.35/1.03    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 0.35/1.03    inference(ennf_transformation,[],[f25])).
% 0.35/1.03  
% 0.35/1.03  fof(f32,plain,(
% 0.35/1.03    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 0.35/1.03    introduced(choice_axiom,[])).
% 0.35/1.03  
% 0.35/1.03  fof(f33,plain,(
% 0.35/1.03    sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 0.35/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f32])).
% 0.35/1.03  
% 0.35/1.03  fof(f57,plain,(
% 0.35/1.03    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 0.35/1.03    inference(cnf_transformation,[],[f33])).
% 0.35/1.03  
% 0.35/1.03  fof(f17,axiom,(
% 0.35/1.03    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f50,plain,(
% 0.35/1.03    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.35/1.03    inference(cnf_transformation,[],[f17])).
% 0.35/1.03  
% 0.35/1.03  fof(f18,axiom,(
% 0.35/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f51,plain,(
% 0.35/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.35/1.03    inference(cnf_transformation,[],[f18])).
% 0.35/1.03  
% 0.35/1.03  fof(f19,axiom,(
% 0.35/1.03    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f52,plain,(
% 0.35/1.03    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.35/1.03    inference(cnf_transformation,[],[f19])).
% 0.35/1.03  
% 0.35/1.03  fof(f20,axiom,(
% 0.35/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f53,plain,(
% 0.35/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.35/1.03    inference(cnf_transformation,[],[f20])).
% 0.35/1.03  
% 0.35/1.03  fof(f21,axiom,(
% 0.35/1.03    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f54,plain,(
% 0.35/1.03    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.35/1.03    inference(cnf_transformation,[],[f21])).
% 0.35/1.03  
% 0.35/1.03  fof(f22,axiom,(
% 0.35/1.03    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f55,plain,(
% 0.35/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.35/1.03    inference(cnf_transformation,[],[f22])).
% 0.35/1.03  
% 0.35/1.03  fof(f60,plain,(
% 0.35/1.03    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.35/1.03    inference(definition_unfolding,[],[f54,f55])).
% 0.35/1.03  
% 0.35/1.03  fof(f61,plain,(
% 0.35/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.35/1.03    inference(definition_unfolding,[],[f53,f60])).
% 0.35/1.03  
% 0.35/1.03  fof(f62,plain,(
% 0.35/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.35/1.03    inference(definition_unfolding,[],[f52,f61])).
% 0.35/1.03  
% 0.35/1.03  fof(f63,plain,(
% 0.35/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.35/1.03    inference(definition_unfolding,[],[f51,f62])).
% 0.35/1.03  
% 0.35/1.03  fof(f64,plain,(
% 0.35/1.03    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.35/1.03    inference(definition_unfolding,[],[f50,f63])).
% 0.35/1.03  
% 0.35/1.03  fof(f74,plain,(
% 0.35/1.03    k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.35/1.03    inference(definition_unfolding,[],[f57,f64,f64,f64])).
% 0.35/1.03  
% 0.35/1.03  fof(f10,axiom,(
% 0.35/1.03    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f28,plain,(
% 0.35/1.03    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 0.35/1.03    inference(ennf_transformation,[],[f10])).
% 0.35/1.03  
% 0.35/1.03  fof(f43,plain,(
% 0.35/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 0.35/1.03    inference(cnf_transformation,[],[f28])).
% 0.35/1.03  
% 0.35/1.03  fof(f5,axiom,(
% 0.35/1.03    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f38,plain,(
% 0.35/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.35/1.03    inference(cnf_transformation,[],[f5])).
% 0.35/1.03  
% 0.35/1.03  fof(f68,plain,(
% 0.35/1.03    ( ! [X2,X0,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 0.35/1.03    inference(definition_unfolding,[],[f43,f38,f62,f64,f63])).
% 0.35/1.03  
% 0.35/1.03  fof(f58,plain,(
% 0.35/1.03    sK1 != sK2),
% 0.35/1.03    inference(cnf_transformation,[],[f33])).
% 0.35/1.03  
% 0.35/1.03  fof(f11,axiom,(
% 0.35/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f44,plain,(
% 0.35/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.35/1.03    inference(cnf_transformation,[],[f11])).
% 0.35/1.03  
% 0.35/1.03  fof(f8,axiom,(
% 0.35/1.03    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f41,plain,(
% 0.35/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.35/1.03    inference(cnf_transformation,[],[f8])).
% 0.35/1.03  
% 0.35/1.03  fof(f59,plain,(
% 0.35/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 0.35/1.03    inference(definition_unfolding,[],[f41,f38])).
% 0.35/1.03  
% 0.35/1.03  fof(f66,plain,(
% 0.35/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.35/1.03    inference(definition_unfolding,[],[f44,f59,f55,f64])).
% 0.35/1.03  
% 0.35/1.03  fof(f7,axiom,(
% 0.35/1.03    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f40,plain,(
% 0.35/1.03    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.35/1.03    inference(cnf_transformation,[],[f7])).
% 0.35/1.03  
% 0.35/1.03  fof(f6,axiom,(
% 0.35/1.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.35/1.03  
% 0.35/1.03  fof(f39,plain,(
% 0.35/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.35/1.03    inference(cnf_transformation,[],[f6])).
% 0.35/1.03  
% 0.35/1.03  cnf(c_56,plain,
% 0.35/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 0.35/1.03      theory(equality) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_55,plain,
% 0.35/1.03      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 0.35/1.03      theory(equality) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_49,plain,( X0_2 = X0_2 ),theory(equality) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_4,plain,
% 0.35/1.03      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 0.35/1.03      inference(cnf_transformation,[],[f37]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_3,plain,
% 0.35/1.03      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 0.35/1.03      inference(cnf_transformation,[],[f35]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_2,plain,
% 0.35/1.03      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 0.35/1.03      inference(cnf_transformation,[],[f36]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_15,negated_conjecture,
% 0.35/1.03      ( k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 0.35/1.03      inference(cnf_transformation,[],[f74]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1058,negated_conjecture,
% 0.35/1.03      ( ~ iProver_ARSWP_28 | arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 0.35/1.03      inference(arg_filter_abstr,[status(unp)],[c_15]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1136,plain,
% 0.35/1.03      ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_28 != iProver_top ),
% 0.35/1.03      inference(predicate_to_equality,[status(thm)],[c_1058]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_8,plain,
% 0.35/1.03      ( X0 = X1
% 0.35/1.03      | X2 = X1
% 0.35/1.03      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
% 0.35/1.03      inference(cnf_transformation,[],[f68]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1056,plain,
% 0.35/1.03      ( ~ iProver_ARSWP_26
% 0.35/1.03      | X0 = X1
% 0.35/1.03      | X2 = X1
% 0.35/1.03      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0 ),
% 0.35/1.03      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1138,plain,
% 0.35/1.03      ( X0 = X1
% 0.35/1.03      | X2 = X1
% 0.35/1.03      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top ),
% 0.35/1.03      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_14,negated_conjecture,
% 0.35/1.03      ( sK1 != sK2 ),
% 0.35/1.03      inference(cnf_transformation,[],[f58]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1183,plain,
% 0.35/1.03      ( ~ iProver_ARSWP_26
% 0.35/1.03      | X0 = sK2
% 0.35/1.03      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 0.35/1.03      | sK1 = sK2 ),
% 0.35/1.03      inference(instantiation,[status(thm)],[c_1056]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1184,plain,
% 0.35/1.03      ( X0 = sK2
% 0.35/1.03      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 0.35/1.03      | sK1 = sK2
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top ),
% 0.35/1.03      inference(predicate_to_equality,[status(thm)],[c_1183]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1186,plain,
% 0.35/1.03      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 0.35/1.03      | sK1 = sK2
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top ),
% 0.35/1.03      inference(instantiation,[status(thm)],[c_1184]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1348,plain,
% 0.35/1.03      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top ),
% 0.35/1.03      inference(global_propositional_subsumption,
% 0.35/1.03                [status(thm)],
% 0.35/1.03                [c_1138,c_14,c_1186]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_0,plain,
% 0.35/1.03      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 0.35/1.03      inference(cnf_transformation,[],[f66]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1053,plain,
% 0.35/1.03      ( ~ iProver_ARSWP_23
% 0.35/1.03      | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0 ),
% 0.35/1.03      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1141,plain,
% 0.35/1.03      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_23 != iProver_top ),
% 0.35/1.03      inference(predicate_to_equality,[status(thm)],[c_1053]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1355,plain,
% 0.35/1.03      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top
% 0.35/1.03      | iProver_ARSWP_23 != iProver_top ),
% 0.35/1.03      inference(superposition,[status(thm)],[c_1348,c_1141]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_6,plain,
% 0.35/1.03      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 0.35/1.03      inference(cnf_transformation,[],[f40]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1359,plain,
% 0.35/1.03      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top
% 0.35/1.03      | iProver_ARSWP_23 != iProver_top ),
% 0.35/1.03      inference(demodulation,[status(thm)],[c_1355,c_6]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1562,plain,
% 0.35/1.03      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top
% 0.35/1.03      | iProver_ARSWP_23 != iProver_top ),
% 0.35/1.03      inference(superposition,[status(thm)],[c_1359,c_1141]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1693,plain,
% 0.35/1.03      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_28 != iProver_top
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top
% 0.35/1.03      | iProver_ARSWP_23 != iProver_top ),
% 0.35/1.03      inference(superposition,[status(thm)],[c_1136,c_1562]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1561,plain,
% 0.35/1.03      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top
% 0.35/1.03      | iProver_ARSWP_23 != iProver_top ),
% 0.35/1.03      inference(superposition,[status(thm)],[c_1359,c_1348]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1691,plain,
% 0.35/1.03      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top
% 0.35/1.03      | iProver_ARSWP_23 != iProver_top ),
% 0.35/1.03      inference(superposition,[status(thm)],[c_1561,c_1562]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1354,plain,
% 0.35/1.03      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_28 != iProver_top
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top ),
% 0.35/1.03      inference(superposition,[status(thm)],[c_1136,c_1348]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1366,plain,
% 0.35/1.03      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 0.35/1.03      | iProver_ARSWP_28 != iProver_top
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top ),
% 0.35/1.03      inference(demodulation,[status(thm)],[c_1354,c_6]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1438,plain,
% 0.35/1.03      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_28 != iProver_top
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top ),
% 0.35/1.03      inference(superposition,[status(thm)],[c_1366,c_1348]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_1461,plain,
% 0.35/1.03      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 0.35/1.03      | iProver_ARSWP_28 != iProver_top
% 0.35/1.03      | iProver_ARSWP_26 != iProver_top ),
% 0.35/1.03      inference(superposition,[status(thm)],[c_1136,c_1438]) ).
% 0.35/1.03  
% 0.35/1.03  cnf(c_5,plain,
% 0.35/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 0.35/1.03      inference(cnf_transformation,[],[f39]) ).
% 0.35/1.03  
% 0.35/1.03  
% 0.35/1.03  % SZS output end Saturation for theBenchmark.p
% 0.35/1.03  
% 0.35/1.03  ------                               Statistics
% 0.35/1.03  
% 0.35/1.03  ------ Selected
% 0.35/1.03  
% 0.35/1.03  total_time:                             0.164
% 0.35/1.03  
%------------------------------------------------------------------------------
