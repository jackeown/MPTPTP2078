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
% DateTime   : Thu Dec  3 11:29:50 EST 2020

% Result     : CounterSatisfiable 3.85s
% Output     : Saturation 3.85s
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

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f26,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK1 != sK2
    & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f29])).

fof(f51,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f64,plain,(
    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f51,f54,f54,f54])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f59,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f41,f35,f54,f45])).

fof(f52,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f43,f53,f50,f54])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f42,f53,f54,f50])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

cnf(c_54,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_53,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_47,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_5,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1221,negated_conjecture,
    ( ~ iProver_ARSWP_30
    | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_1310,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1221])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1215,plain,
    ( ~ iProver_ARSWP_24
    | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1316,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_24 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1215])).

cnf(c_9,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1219,plain,
    ( ~ iProver_ARSWP_28
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_1312,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_28 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1219])).

cnf(c_11,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1380,plain,
    ( ~ iProver_ARSWP_28
    | X0 = sK2
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_1381,plain,
    ( X0 = sK2
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_28 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1380])).

cnf(c_1383,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_28 != iProver_top ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_1726,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_28 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1312,c_11,c_1383])).

cnf(c_10,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1220,plain,
    ( ~ iProver_ARSWP_29
    | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_1311,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1220])).

cnf(c_1734,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_1311])).

cnf(c_5597,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1734])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5622,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5597,c_7])).

cnf(c_5666,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5622,c_1311])).

cnf(c_7291,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_5666])).

cnf(c_7565,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_7291])).

cnf(c_1732,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1726])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1216,plain,
    ( ~ iProver_ARSWP_25
    | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_1315,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_25 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_2972,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_1315])).

cnf(c_2977,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2972,c_7])).

cnf(c_3187,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_1315])).

cnf(c_4468,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_3187])).

cnf(c_7271,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_4468])).

cnf(c_3178,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_1732])).

cnf(c_1615,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1315])).

cnf(c_4431,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_1615])).

cnf(c_4669,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_3178,c_4431])).

cnf(c_6680,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_4669])).

cnf(c_5639,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5622,c_1734])).

cnf(c_5971,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_5639])).

cnf(c_1485,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1311])).

cnf(c_5657,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5622,c_1485])).

cnf(c_5656,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5622,c_1732])).

cnf(c_1616,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_1315])).

cnf(c_5602,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1616])).

cnf(c_4433,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_1615])).

cnf(c_4430,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_1615])).

cnf(c_1733,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_1726])).

cnf(c_1744,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1733,c_7])).

cnf(c_1762,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1726])).

cnf(c_1924,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_1762])).

cnf(c_1767,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1316])).

cnf(c_1766,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1311])).

cnf(c_2789,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_1766])).

cnf(c_3470,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1767,c_2789])).

cnf(c_3700,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1924,c_3470])).

cnf(c_3904,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_3700])).

cnf(c_3703,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_3470])).

cnf(c_3475,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_2789])).

cnf(c_3188,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_1311])).

cnf(c_2969,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_1732])).

cnf(c_2825,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_1485])).

cnf(c_1765,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1315])).

cnf(c_2401,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_1765])).

cnf(c_2427,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1767,c_2401])).

cnf(c_2614,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1924,c_2427])).

cnf(c_2036,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1767,c_1616])).

cnf(c_2649,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2614,c_2036])).

cnf(c_2616,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_2427])).

cnf(c_2263,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_2036])).

cnf(c_2083,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1924])).

cnf(c_1763,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1616])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1796,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1763,c_6])).

cnf(c_2236,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2083,c_1796])).

cnf(c_61,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_60,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1506,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_61,c_60])).

cnf(c_1647,plain,
    ( ~ iProver_ARSWP_24
    | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
    inference(resolution,[status(thm)],[c_1506,c_1215])).

cnf(c_1648,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_24 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1647])).

cnf(c_2945,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_24 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2236,c_1648])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:51 EST 2020
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
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.85/1.00  ------ Proving...
% 3.85/1.00  ------ Problem Properties 
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  clauses                                 10
% 3.85/1.00  conjectures                             2
% 3.85/1.00  EPR                                     1
% 3.85/1.00  Horn                                    9
% 3.85/1.00  unary                                   9
% 3.85/1.00  binary                                  0
% 3.85/1.00  lits                                    12
% 3.85/1.00  lits eq                                 12
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
% 3.85/1.00    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f34,plain,(
% 3.85/1.00    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f4])).
% 3.85/1.00  
% 3.85/1.00  fof(f3,axiom,(
% 3.85/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f23,plain,(
% 3.85/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.85/1.00    inference(rectify,[],[f3])).
% 3.85/1.00  
% 3.85/1.00  fof(f24,plain,(
% 3.85/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.85/1.00    inference(ennf_transformation,[],[f23])).
% 3.85/1.00  
% 3.85/1.00  fof(f27,plain,(
% 3.85/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f28,plain,(
% 3.85/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f27])).
% 3.85/1.00  
% 3.85/1.00  fof(f32,plain,(
% 3.85/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f28])).
% 3.85/1.00  
% 3.85/1.00  fof(f33,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f28])).
% 3.85/1.00  
% 3.85/1.00  fof(f21,conjecture,(
% 3.85/1.00    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f22,negated_conjecture,(
% 3.85/1.00    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.85/1.00    inference(negated_conjecture,[],[f21])).
% 3.85/1.00  
% 3.85/1.00  fof(f26,plain,(
% 3.85/1.00    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.85/1.00    inference(ennf_transformation,[],[f22])).
% 3.85/1.00  
% 3.85/1.00  fof(f29,plain,(
% 3.85/1.00    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f30,plain,(
% 3.85/1.00    sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 3.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f29])).
% 3.85/1.00  
% 3.85/1.00  fof(f51,plain,(
% 3.85/1.00    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 3.85/1.00    inference(cnf_transformation,[],[f30])).
% 3.85/1.00  
% 3.85/1.00  fof(f14,axiom,(
% 3.85/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f44,plain,(
% 3.85/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f14])).
% 3.85/1.00  
% 3.85/1.00  fof(f15,axiom,(
% 3.85/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f45,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f15])).
% 3.85/1.00  
% 3.85/1.00  fof(f54,plain,(
% 3.85/1.00    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f44,f45])).
% 3.85/1.00  
% 3.85/1.00  fof(f64,plain,(
% 3.85/1.00    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1)),
% 3.85/1.00    inference(definition_unfolding,[],[f51,f54,f54,f54])).
% 3.85/1.00  
% 3.85/1.00  fof(f16,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f46,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f16])).
% 3.85/1.00  
% 3.85/1.00  fof(f17,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f47,plain,(
% 3.85/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f17])).
% 3.85/1.00  
% 3.85/1.00  fof(f18,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f48,plain,(
% 3.85/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f18])).
% 3.85/1.00  
% 3.85/1.00  fof(f19,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f49,plain,(
% 3.85/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f19])).
% 3.85/1.00  
% 3.85/1.00  fof(f20,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f50,plain,(
% 3.85/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f20])).
% 3.85/1.00  
% 3.85/1.00  fof(f55,plain,(
% 3.85/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f49,f50])).
% 3.85/1.00  
% 3.85/1.00  fof(f56,plain,(
% 3.85/1.00    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f48,f55])).
% 3.85/1.00  
% 3.85/1.00  fof(f57,plain,(
% 3.85/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f47,f56])).
% 3.85/1.00  
% 3.85/1.00  fof(f59,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f46,f57])).
% 3.85/1.00  
% 3.85/1.00  fof(f11,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f25,plain,(
% 3.85/1.00    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.85/1.00    inference(ennf_transformation,[],[f11])).
% 3.85/1.00  
% 3.85/1.00  fof(f41,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.85/1.00    inference(cnf_transformation,[],[f25])).
% 3.85/1.00  
% 3.85/1.00  fof(f5,axiom,(
% 3.85/1.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f35,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f5])).
% 3.85/1.00  
% 3.85/1.00  fof(f62,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.85/1.00    inference(definition_unfolding,[],[f41,f35,f54,f45])).
% 3.85/1.00  
% 3.85/1.00  fof(f52,plain,(
% 3.85/1.00    sK1 != sK2),
% 3.85/1.00    inference(cnf_transformation,[],[f30])).
% 3.85/1.00  
% 3.85/1.00  fof(f13,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f43,plain,(
% 3.85/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f13])).
% 3.85/1.00  
% 3.85/1.00  fof(f8,axiom,(
% 3.85/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f38,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f8])).
% 3.85/1.00  
% 3.85/1.00  fof(f53,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f38,f35])).
% 3.85/1.00  
% 3.85/1.00  fof(f63,plain,(
% 3.85/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f43,f53,f50,f54])).
% 3.85/1.00  
% 3.85/1.00  fof(f7,axiom,(
% 3.85/1.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f37,plain,(
% 3.85/1.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.85/1.00    inference(cnf_transformation,[],[f7])).
% 3.85/1.00  
% 3.85/1.00  fof(f12,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f42,plain,(
% 3.85/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f12])).
% 3.85/1.00  
% 3.85/1.00  fof(f60,plain,(
% 3.85/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f42,f53,f54,f50])).
% 3.85/1.00  
% 3.85/1.00  fof(f6,axiom,(
% 3.85/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f36,plain,(
% 3.85/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.85/1.00    inference(cnf_transformation,[],[f6])).
% 3.85/1.00  
% 3.85/1.00  cnf(c_54,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.85/1.00      theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_53,plain,
% 3.85/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.85/1.00      theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_47,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5,plain,
% 3.85/1.00      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 3.85/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4,plain,
% 3.85/1.00      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 3.85/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.85/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_12,negated_conjecture,
% 3.85/1.00      ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
% 3.85/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1221,negated_conjecture,
% 3.85/1.00      ( ~ iProver_ARSWP_30 | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
% 3.85/1.00      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1310,plain,
% 3.85/1.00      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1221]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_0,plain,
% 3.85/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 3.85/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1215,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_24 | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
% 3.85/1.00      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1316,plain,
% 3.85/1.00      ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1215]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | X2 = X1
% 3.85/1.00      | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
% 3.85/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1219,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_28
% 3.85/1.00      | X0 = X1
% 3.85/1.00      | X2 = X1
% 3.85/1.00      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 3.85/1.00      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1312,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | X2 = X1
% 3.85/1.00      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1219]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_11,negated_conjecture,
% 3.85/1.00      ( sK1 != sK2 ),
% 3.85/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1380,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_28
% 3.85/1.00      | X0 = sK2
% 3.85/1.00      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | sK1 = sK2 ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1219]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1381,plain,
% 3.85/1.00      ( X0 = sK2
% 3.85/1.00      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | sK1 = sK2
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1380]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1383,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | sK1 = sK2
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1381]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1726,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_1312,c_11,c_1383]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_10,plain,
% 3.85/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.85/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1220,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_29
% 3.85/1.00      | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 3.85/1.00      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1311,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1220]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1734,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1726,c_1311]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5597,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_1734]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7,plain,
% 3.85/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5622,plain,
% 3.85/1.00      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_5597,c_7]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5666,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5622,c_1311]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7291,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_5666]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7565,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1310,c_7291]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1732,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_1726]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1,plain,
% 3.85/1.00      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.85/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1216,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_25
% 3.85/1.00      | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 3.85/1.00      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1315,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1216]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2972,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1732,c_1315]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2977,plain,
% 3.85/1.00      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_2972,c_7]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3187,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2977,c_1315]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4468,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_3187]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7271,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1310,c_4468]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3178,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2977,c_1732]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1615,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_1315]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4431,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2977,c_1615]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4669,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3178,c_4431]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6680,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_4669]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5639,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5622,c_1734]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5971,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_5639]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1485,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_1311]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5657,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5622,c_1485]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5656,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5622,c_1732]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1616,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1310,c_1315]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5602,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1734,c_1616]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4433,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1310,c_1615]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4430,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1732,c_1615]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1733,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1310,c_1726]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1744,plain,
% 3.85/1.00      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_1733,c_7]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1762,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1744,c_1726]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1924,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1310,c_1762]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1767,plain,
% 3.85/1.00      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1744,c_1316]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1766,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1744,c_1311]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2789,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1310,c_1766]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3470,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1767,c_2789]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3700,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1924,c_3470]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3904,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_3700]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3703,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_3470]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3475,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_2789]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3188,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2977,c_1311]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2969,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1310,c_1732]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2825,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_29 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1310,c_1485]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1765,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1744,c_1315]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2401,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1310,c_1765]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2427,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1767,c_2401]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2614,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1924,c_2427]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2036,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1767,c_1616]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2649,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2614,c_2036]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2616,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_2427]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2263,plain,
% 3.85/1.00      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_2036]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2083,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1316,c_1924]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1763,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1744,c_1616]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1796,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_1763,c_6]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2236,plain,
% 3.85/1.00      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_30 != iProver_top
% 3.85/1.00      | iProver_ARSWP_28 != iProver_top
% 3.85/1.00      | iProver_ARSWP_25 != iProver_top
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2083,c_1796]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_61,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_60,plain,( X0 = X0 ),theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1506,plain,
% 3.85/1.00      ( X0 != X1 | X1 = X0 ),
% 3.85/1.00      inference(resolution,[status(thm)],[c_61,c_60]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1647,plain,
% 3.85/1.00      ( ~ iProver_ARSWP_24 | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
% 3.85/1.00      inference(resolution,[status(thm)],[c_1506,c_1215]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1648,plain,
% 3.85/1.00      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1647]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2945,plain,
% 3.85/1.00      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.85/1.00      | iProver_ARSWP_24 != iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2236,c_1648]) ).
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  % SZS output end Saturation for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  ------                               Statistics
% 3.85/1.00  
% 3.85/1.00  ------ Selected
% 3.85/1.00  
% 3.85/1.00  total_time:                             0.332
% 3.85/1.00  
%------------------------------------------------------------------------------
