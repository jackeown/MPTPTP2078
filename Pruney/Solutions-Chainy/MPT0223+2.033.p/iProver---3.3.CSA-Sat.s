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
% DateTime   : Thu Dec  3 11:29:49 EST 2020

% Result     : CounterSatisfiable 7.71s
% Output     : Saturation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  171 (23813 expanded)
%              Number of clauses        :  115 (3011 expanded)
%              Number of leaves         :   22 (7737 expanded)
%              Depth                    :   22
%              Number of atoms          :  480 (33038 expanded)
%              Number of equality atoms :  442 (32281 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    4 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f31])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f18,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f67])).

fof(f19,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f62])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f50,f39,f62,f68,f67])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f25])).

fof(f30,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( sK1 != sK2
    & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f33])).

fof(f60,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f42,f39])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f61,f62,f62])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f58,f64])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f44,f61,f55,f55])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))),k5_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2))))))) ),
    inference(definition_unfolding,[],[f51,f61,f66,f68,f64])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f59,f68,f68,f68])).

cnf(c_58,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_57,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_51,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_4,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k3_enumset1(X1,X1,X1,X0,X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X0,X2),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1041,plain,
    ( ~ iProver_ARSWP_29
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_1141,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_29 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1041])).

cnf(c_14,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1193,plain,
    ( ~ iProver_ARSWP_29
    | X0 = sK2
    | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_1194,plain,
    ( X0 = sK2
    | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_29 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1193])).

cnf(c_1196,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_29 != iProver_top ),
    inference(instantiation,[status(thm)],[c_1194])).

cnf(c_1426,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_29 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1141,c_14,c_1196])).

cnf(c_0,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1037,plain,
    ( ~ iProver_ARSWP_25
    | k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1145,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_25 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_1436,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_1145])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1440,plain,
    ( arAF0_k3_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1436,c_6])).

cnf(c_1577,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1145])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))),k5_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2))))))) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1042,plain,
    ( ~ iProver_ARSWP_30
    | k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_1140,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1042])).

cnf(c_1574,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1140])).

cnf(c_2800,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1577,c_1574])).

cnf(c_1434,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_1140])).

cnf(c_1447,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1434,c_6])).

cnf(c_1760,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_1447])).

cnf(c_1813,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1760,c_6])).

cnf(c_1765,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_1140])).

cnf(c_2836,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_1765])).

cnf(c_14195,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_2836])).

cnf(c_14203,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_1140])).

cnf(c_16632,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_14203])).

cnf(c_16662,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_14195,c_16632])).

cnf(c_14204,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_1145])).

cnf(c_14201,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_1447])).

cnf(c_2841,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1765])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2852,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2841,c_5])).

cnf(c_14200,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_2852])).

cnf(c_2839,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_1765])).

cnf(c_12454,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_2839])).

cnf(c_12459,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(demodulation,[status(thm)],[c_12454,c_5])).

cnf(c_14194,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_12459])).

cnf(c_15,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1044,negated_conjecture,
    ( ~ iProver_ARSWP_32
    | arAF0_k3_xboole_0_0 = arAF0_k3_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_15])).

cnf(c_1138,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k3_enumset1_0
    | iProver_ARSWP_32 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(c_1432,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1426])).

cnf(c_1463,plain,
    ( arAF0_k3_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1432,c_6])).

cnf(c_1352,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1140])).

cnf(c_1354,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1352,c_5,c_6])).

cnf(c_1607,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_1354])).

cnf(c_1609,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_1140])).

cnf(c_4176,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1607,c_1609])).

cnf(c_8720,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4176,c_1140])).

cnf(c_13458,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_8720])).

cnf(c_2319,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1607])).

cnf(c_4182,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1609])).

cnf(c_5148,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2319,c_4182])).

cnf(c_6488,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2836,c_5148])).

cnf(c_5592,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5148,c_1140])).

cnf(c_8332,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_5592])).

cnf(c_11684,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_6488,c_8332])).

cnf(c_2840,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_1765])).

cnf(c_2861,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2840,c_5])).

cnf(c_4595,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2861,c_1140])).

cnf(c_10713,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_4595])).

cnf(c_3053,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_2852,c_1140])).

cnf(c_10676,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_3053])).

cnf(c_8719,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4176,c_1354])).

cnf(c_8718,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4176,c_1447])).

cnf(c_8716,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4176,c_2861])).

cnf(c_4589,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_2861])).

cnf(c_4614,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4589,c_6])).

cnf(c_4826,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_4614])).

cnf(c_5145,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4826,c_4182])).

cnf(c_8715,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4176,c_5145])).

cnf(c_8714,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4176,c_5148])).

cnf(c_5155,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_4182])).

cnf(c_5161,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5155,c_5])).

cnf(c_8713,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4176,c_5161])).

cnf(c_8712,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4176,c_2836])).

cnf(c_5530,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5145,c_1140])).

cnf(c_8082,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_5530])).

cnf(c_5526,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5145,c_2861])).

cnf(c_7210,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5526,c_1609])).

cnf(c_6483,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_2836])).

cnf(c_6572,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6483,c_6])).

cnf(c_6494,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2836,c_1140])).

cnf(c_6495,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_2836,c_1145])).

cnf(c_6493,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2836,c_1354])).

cnf(c_6492,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2836,c_1447])).

cnf(c_6491,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_2836,c_2852])).

cnf(c_6490,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2836,c_2861])).

cnf(c_6489,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2836,c_5145])).

cnf(c_5583,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_5148])).

cnf(c_5643,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5583,c_6])).

cnf(c_5591,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5148,c_1354])).

cnf(c_5590,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5148,c_1447])).

cnf(c_5588,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5148,c_2861])).

cnf(c_5587,plain,
    ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5148,c_5145])).

cnf(c_1762,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1447])).

cnf(c_4229,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1574])).

cnf(c_1761,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_1447])).

cnf(c_4175,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1761,c_1609])).

cnf(c_3049,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_2852])).

cnf(c_3077,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3049,c_6])).

cnf(c_2799,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1577])).

cnf(c_1571,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1426])).

cnf(c_2798,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1571,c_1577])).

cnf(c_2513,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1761])).

cnf(c_1606,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_1426])).

cnf(c_2123,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1606])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:30:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.71/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/1.48  
% 7.71/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.71/1.48  
% 7.71/1.48  ------  iProver source info
% 7.71/1.48  
% 7.71/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.71/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.71/1.48  git: non_committed_changes: false
% 7.71/1.48  git: last_make_outside_of_git: false
% 7.71/1.48  
% 7.71/1.48  ------ 
% 7.71/1.48  ------ Parsing...
% 7.71/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.71/1.48  
% 7.71/1.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 7.71/1.48  
% 7.71/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.71/1.48  
% 7.71/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.48  ------ Proving...
% 7.71/1.48  ------ Problem Properties 
% 7.71/1.48  
% 7.71/1.48  
% 7.71/1.48  clauses                                 13
% 7.71/1.48  conjectures                             2
% 7.71/1.48  EPR                                     1
% 7.71/1.48  Horn                                    12
% 7.71/1.48  unary                                   12
% 7.71/1.48  binary                                  0
% 7.71/1.48  lits                                    15
% 7.71/1.48  lits eq                                 15
% 7.71/1.48  fd_pure                                 0
% 7.71/1.49  fd_pseudo                               0
% 7.71/1.49  fd_cond                                 0
% 7.71/1.49  fd_pseudo_cond                          1
% 7.71/1.49  AC symbols                              0
% 7.71/1.49  
% 7.71/1.49  ------ Input Options Time Limit: Unbounded
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 7.71/1.49  Current options:
% 7.71/1.49  ------ 
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.71/1.49  
% 7.71/1.49  ------ Proving...
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  % SZS status CounterSatisfiable for theBenchmark.p
% 7.71/1.49  
% 7.71/1.49  % SZS output start Saturation for theBenchmark.p
% 7.71/1.49  
% 7.71/1.49  fof(f4,axiom,(
% 7.71/1.49    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f38,plain,(
% 7.71/1.49    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 7.71/1.49    inference(cnf_transformation,[],[f4])).
% 7.71/1.49  
% 7.71/1.49  fof(f3,axiom,(
% 7.71/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f27,plain,(
% 7.71/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.71/1.49    inference(rectify,[],[f3])).
% 7.71/1.49  
% 7.71/1.49  fof(f28,plain,(
% 7.71/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.71/1.49    inference(ennf_transformation,[],[f27])).
% 7.71/1.49  
% 7.71/1.49  fof(f31,plain,(
% 7.71/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.71/1.49    introduced(choice_axiom,[])).
% 7.71/1.49  
% 7.71/1.49  fof(f32,plain,(
% 7.71/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.71/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f31])).
% 7.71/1.49  
% 7.71/1.49  fof(f36,plain,(
% 7.71/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f32])).
% 7.71/1.49  
% 7.71/1.49  fof(f37,plain,(
% 7.71/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.71/1.49    inference(cnf_transformation,[],[f32])).
% 7.71/1.49  
% 7.71/1.49  fof(f16,axiom,(
% 7.71/1.49    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f29,plain,(
% 7.71/1.49    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 7.71/1.49    inference(ennf_transformation,[],[f16])).
% 7.71/1.49  
% 7.71/1.49  fof(f50,plain,(
% 7.71/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 7.71/1.49    inference(cnf_transformation,[],[f29])).
% 7.71/1.49  
% 7.71/1.49  fof(f5,axiom,(
% 7.71/1.49    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f39,plain,(
% 7.71/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f5])).
% 7.71/1.49  
% 7.71/1.49  fof(f18,axiom,(
% 7.71/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f52,plain,(
% 7.71/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f18])).
% 7.71/1.49  
% 7.71/1.49  fof(f68,plain,(
% 7.71/1.49    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.71/1.49    inference(definition_unfolding,[],[f52,f67])).
% 7.71/1.49  
% 7.71/1.49  fof(f19,axiom,(
% 7.71/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f53,plain,(
% 7.71/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f19])).
% 7.71/1.49  
% 7.71/1.49  fof(f20,axiom,(
% 7.71/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f54,plain,(
% 7.71/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f20])).
% 7.71/1.49  
% 7.71/1.49  fof(f21,axiom,(
% 7.71/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f55,plain,(
% 7.71/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f21])).
% 7.71/1.49  
% 7.71/1.49  fof(f62,plain,(
% 7.71/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.71/1.49    inference(definition_unfolding,[],[f54,f55])).
% 7.71/1.49  
% 7.71/1.49  fof(f67,plain,(
% 7.71/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.71/1.49    inference(definition_unfolding,[],[f53,f62])).
% 7.71/1.49  
% 7.71/1.49  fof(f74,plain,(
% 7.71/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X0,X0))) = k3_enumset1(X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 7.71/1.49    inference(definition_unfolding,[],[f50,f39,f62,f68,f67])).
% 7.71/1.49  
% 7.71/1.49  fof(f25,conjecture,(
% 7.71/1.49    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f26,negated_conjecture,(
% 7.71/1.49    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.71/1.49    inference(negated_conjecture,[],[f25])).
% 7.71/1.49  
% 7.71/1.49  fof(f30,plain,(
% 7.71/1.49    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 7.71/1.49    inference(ennf_transformation,[],[f26])).
% 7.71/1.49  
% 7.71/1.49  fof(f33,plain,(
% 7.71/1.49    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 7.71/1.49    introduced(choice_axiom,[])).
% 7.71/1.49  
% 7.71/1.49  fof(f34,plain,(
% 7.71/1.49    sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 7.71/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f33])).
% 7.71/1.49  
% 7.71/1.49  fof(f60,plain,(
% 7.71/1.49    sK1 != sK2),
% 7.71/1.49    inference(cnf_transformation,[],[f34])).
% 7.71/1.49  
% 7.71/1.49  fof(f22,axiom,(
% 7.71/1.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f56,plain,(
% 7.71/1.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f22])).
% 7.71/1.49  
% 7.71/1.49  fof(f9,axiom,(
% 7.71/1.49    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f43,plain,(
% 7.71/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f9])).
% 7.71/1.49  
% 7.71/1.49  fof(f8,axiom,(
% 7.71/1.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f42,plain,(
% 7.71/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f8])).
% 7.71/1.49  
% 7.71/1.49  fof(f61,plain,(
% 7.71/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.71/1.49    inference(definition_unfolding,[],[f42,f39])).
% 7.71/1.49  
% 7.71/1.49  fof(f63,plain,(
% 7.71/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.71/1.49    inference(definition_unfolding,[],[f43,f61,f62,f62])).
% 7.71/1.49  
% 7.71/1.49  fof(f69,plain,(
% 7.71/1.49    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.71/1.49    inference(definition_unfolding,[],[f56,f63])).
% 7.71/1.49  
% 7.71/1.49  fof(f7,axiom,(
% 7.71/1.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f41,plain,(
% 7.71/1.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.71/1.49    inference(cnf_transformation,[],[f7])).
% 7.71/1.49  
% 7.71/1.49  fof(f17,axiom,(
% 7.71/1.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f51,plain,(
% 7.71/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f17])).
% 7.71/1.49  
% 7.71/1.49  fof(f24,axiom,(
% 7.71/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f58,plain,(
% 7.71/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f24])).
% 7.71/1.49  
% 7.71/1.49  fof(f66,plain,(
% 7.71/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.71/1.49    inference(definition_unfolding,[],[f58,f64])).
% 7.71/1.49  
% 7.71/1.49  fof(f10,axiom,(
% 7.71/1.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f44,plain,(
% 7.71/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f10])).
% 7.71/1.49  
% 7.71/1.49  fof(f64,plain,(
% 7.71/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.71/1.49    inference(definition_unfolding,[],[f44,f61,f55,f55])).
% 7.71/1.49  
% 7.71/1.49  fof(f75,plain,(
% 7.71/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))),k5_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))))))) )),
% 7.71/1.49    inference(definition_unfolding,[],[f51,f61,f66,f68,f64])).
% 7.71/1.49  
% 7.71/1.49  fof(f6,axiom,(
% 7.71/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.71/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f40,plain,(
% 7.71/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.71/1.49    inference(cnf_transformation,[],[f6])).
% 7.71/1.49  
% 7.71/1.49  fof(f59,plain,(
% 7.71/1.49    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 7.71/1.49    inference(cnf_transformation,[],[f34])).
% 7.71/1.49  
% 7.71/1.49  fof(f77,plain,(
% 7.71/1.49    k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 7.71/1.49    inference(definition_unfolding,[],[f59,f68,f68,f68])).
% 7.71/1.49  
% 7.71/1.49  cnf(c_58,plain,
% 7.71/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.71/1.49      theory(equality) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_57,plain,
% 7.71/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.71/1.49      theory(equality) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_51,plain,( X0_2 = X0_2 ),theory(equality) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4,plain,
% 7.71/1.49      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 7.71/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_3,plain,
% 7.71/1.49      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 7.71/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2,plain,
% 7.71/1.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.71/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_11,plain,
% 7.71/1.49      ( X0 = X1
% 7.71/1.49      | X2 = X1
% 7.71/1.49      | k5_xboole_0(k3_enumset1(X1,X1,X1,X0,X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X0,X2),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X0,X0,X0,X0,X2) ),
% 7.71/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1041,plain,
% 7.71/1.49      ( ~ iProver_ARSWP_29
% 7.71/1.49      | X0 = X1
% 7.71/1.49      | X2 = X1
% 7.71/1.49      | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0 ),
% 7.71/1.49      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1141,plain,
% 7.71/1.49      ( X0 = X1
% 7.71/1.49      | X2 = X1
% 7.71/1.49      | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_1041]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14,negated_conjecture,
% 7.71/1.49      ( sK1 != sK2 ),
% 7.71/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1193,plain,
% 7.71/1.49      ( ~ iProver_ARSWP_29
% 7.71/1.49      | X0 = sK2
% 7.71/1.49      | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
% 7.71/1.49      | sK1 = sK2 ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_1041]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1194,plain,
% 7.71/1.49      ( X0 = sK2
% 7.71/1.49      | k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
% 7.71/1.49      | sK1 = sK2
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_1193]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1196,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
% 7.71/1.49      | sK1 = sK2
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_1194]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1426,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_1141,c_14,c_1196]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_0,plain,
% 7.71/1.49      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_xboole_0(k3_enumset1(X2,X2,X2,X3,X4),k3_enumset1(X0,X0,X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 7.71/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1037,plain,
% 7.71/1.49      ( ~ iProver_ARSWP_25
% 7.71/1.49      | k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0 ),
% 7.71/1.49      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1145,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_1037]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1436,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_1145]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6,plain,
% 7.71/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1440,plain,
% 7.71/1.49      ( arAF0_k3_enumset1_0 = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_1436,c_6]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1577,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1440,c_1145]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_12,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2)))),k5_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X0,X0,X0,X1,X2))))))) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X4,X4,X5,X6,X7),k3_enumset1(X0,X0,X1,X2,X3)))) ),
% 7.71/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1042,plain,
% 7.71/1.49      ( ~ iProver_ARSWP_30
% 7.71/1.49      | k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) ),
% 7.71/1.49      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1140,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_1042]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1574,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1440,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2800,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1577,c_1574]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1434,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1447,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_1434,c_6]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1760,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_1447]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1813,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_1760,c_6]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1765,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1447,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2836,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1813,c_1765]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14195,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2800,c_2836]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14203,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2800,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_16632,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_14203]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_16662,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_14195,c_16632]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14204,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2800,c_1145]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14201,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2800,c_1447]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2841,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1440,c_1765]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5,plain,
% 7.71/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2852,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_2841,c_5]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14200,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2800,c_2852]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2839,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_1765]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_12454,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1440,c_2839]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_12459,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_12454,c_5]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14194,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2800,c_12459]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_15,negated_conjecture,
% 7.71/1.49      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 7.71/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1044,negated_conjecture,
% 7.71/1.49      ( ~ iProver_ARSWP_32 | arAF0_k3_xboole_0_0 = arAF0_k3_enumset1_0 ),
% 7.71/1.49      inference(arg_filter_abstr,[status(unp)],[c_15]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1138,plain,
% 7.71/1.49      ( arAF0_k3_xboole_0_0 = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_1044]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1432,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1138,c_1426]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1463,plain,
% 7.71/1.49      ( arAF0_k3_enumset1_0 = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_1432,c_6]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1352,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1138,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1354,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_1352,c_5,c_6]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1607,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1463,c_1354]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1609,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1463,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4176,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1607,c_1609]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8720,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4176,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_13458,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_8720]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2319,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1138,c_1607]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4182,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1138,c_1609]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5148,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2319,c_4182]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6488,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2836,c_5148]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5592,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_5148,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8332,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_5592]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_11684,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_6488,c_8332]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2840,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1463,c_1765]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2861,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_2840,c_5]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4595,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2861,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_10713,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_4595]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_3053,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2852,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_10676,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_3053]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8719,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4176,c_1354]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8718,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4176,c_1447]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8716,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4176,c_2861]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4589,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_2861]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4614,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_4589,c_6]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4826,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1138,c_4614]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5145,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4826,c_4182]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8715,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4176,c_5145]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8714,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4176,c_5148]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5155,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1463,c_4182]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5161,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_5155,c_5]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8713,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4176,c_5161]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8712,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4176,c_2836]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5530,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_5145,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8082,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),arAF0_k3_enumset1_0) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_5530]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5526,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_5145,c_2861]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7210,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_5526,c_1609]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6483,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_2836]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6572,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_6483,c_6]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6494,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2836,c_1140]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6495,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2836,c_1145]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6493,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2836,c_1354]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6492,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2836,c_1447]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6491,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2836,c_2852]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6490,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2836,c_2861]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6489,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2836,c_5145]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5583,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_5148]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5643,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_5583,c_6]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5591,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_5148,c_1354]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5590,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_5148,c_1447]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5588,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_5148,c_2861]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5587,plain,
% 7.71/1.49      ( k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_5148,c_5145]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1762,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1440,c_1447]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4229,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1762,c_1574]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1761,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1463,c_1447]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4175,plain,
% 7.71/1.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_xboole_0_0))
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1761,c_1609]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_3049,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k3_enumset1_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1426,c_2852]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_3077,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_3049,c_6]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2799,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1138,c_1577]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1571,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1440,c_1426]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2798,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top
% 7.71/1.49      | iProver_ARSWP_25 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1571,c_1577]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2513,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0)
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_30 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1138,c_1761]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1606,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1463,c_1426]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2123,plain,
% 7.71/1.49      ( k5_xboole_0(k1_xboole_0,arAF0_k3_enumset1_0) = arAF0_k3_enumset1_0
% 7.71/1.49      | iProver_ARSWP_32 != iProver_top
% 7.71/1.49      | iProver_ARSWP_29 != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1138,c_1606]) ).
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  % SZS output end Saturation for theBenchmark.p
% 7.71/1.49  
% 7.71/1.49  ------                               Statistics
% 7.71/1.49  
% 7.71/1.49  ------ Selected
% 7.71/1.49  
% 7.71/1.49  total_time:                             0.539
% 7.71/1.49  
%------------------------------------------------------------------------------
