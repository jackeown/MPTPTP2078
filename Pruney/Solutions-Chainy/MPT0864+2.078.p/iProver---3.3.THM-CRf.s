%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:00 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  106 (1138 expanded)
%              Number of clauses        :   50 ( 185 expanded)
%              Number of leaves         :   17 ( 345 expanded)
%              Depth                    :   17
%              Number of atoms          :  200 (1580 expanded)
%              Number of equality atoms :  168 (1393 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f37,f50,f50,f50])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f36,f50,f50,f50])).

fof(f59,plain,(
    ! [X1] : k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f15,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f19,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK2,sK3) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK1) = sK1
        | k1_mcart_1(sK1) = sK1 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK1 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( k2_mcart_1(sK1) = sK1
      | k1_mcart_1(sK1) = sK1 )
    & k4_tarski(sK2,sK3) = sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f25,f24])).

fof(f47,plain,
    ( k2_mcart_1(sK1) = sK1
    | k1_mcart_1(sK1) = sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    k4_tarski(sK2,sK3) = sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK0(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK0(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_365,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( X0 = X1
    | k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_368,plain,
    ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1450,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_368])).

cnf(c_1575,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k1_xboole_0
    | sK0(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_365,c_1450])).

cnf(c_5,plain,
    ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_721,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_722,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_732,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_722,c_3])).

cnf(c_724,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_726,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_724,c_2])).

cnf(c_733,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_732,c_726])).

cnf(c_737,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_721,c_733])).

cnf(c_1283,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5,c_737])).

cnf(c_1581,plain,
    ( sK0(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1575,c_1283])).

cnf(c_1585,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_365])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_450,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0))
    | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_451,plain,
    ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_2621,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1585,c_5,c_451])).

cnf(c_14,negated_conjecture,
    ( k1_mcart_1(sK1) = sK1
    | k2_mcart_1(sK1) = sK1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,negated_conjecture,
    ( k4_tarski(sK2,sK3) = sK1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_457,plain,
    ( k1_mcart_1(sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_15,c_10])).

cnf(c_500,plain,
    ( k2_mcart_1(sK1) = sK1
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_14,c_457])).

cnf(c_9,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_436,plain,
    ( k2_mcart_1(sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_15,c_9])).

cnf(c_502,plain,
    ( sK3 = sK1
    | sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_500,c_436])).

cnf(c_505,plain,
    ( k4_tarski(sK2,sK1) = sK1
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_502,c_15])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X2,X0) != sK0(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_367,plain,
    ( k4_tarski(X0,X1) != sK0(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_906,plain,
    ( sK0(X0) != sK1
    | sK2 = sK1
    | k1_xboole_0 = X0
    | r2_hidden(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_367])).

cnf(c_1586,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k1_xboole_0
    | sK2 = sK1
    | sK1 != X0
    | r2_hidden(sK1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_906])).

cnf(c_2270,plain,
    ( sK2 = sK1
    | sK1 != X0
    | r2_hidden(sK1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1586,c_1283])).

cnf(c_2279,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2270,c_1450])).

cnf(c_2629,plain,
    ( sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_2621,c_2279])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X0,X2) != sK0(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_366,plain,
    ( k4_tarski(X0,X1) != sK0(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_561,plain,
    ( sK0(X0) != sK1
    | k1_xboole_0 = X0
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_366])).

cnf(c_1588,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k1_xboole_0
    | sK1 != X0
    | r2_hidden(sK2,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_561])).

cnf(c_1912,plain,
    ( sK1 != X0
    | r2_hidden(sK2,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1588,c_1283])).

cnf(c_2757,plain,
    ( sK1 != X0
    | r2_hidden(sK1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2629,c_1912])).

cnf(c_3096,plain,
    ( r2_hidden(sK1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2757,c_1450])).

cnf(c_3101,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2621,c_3096])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:59:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.41/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/0.99  
% 2.41/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/0.99  
% 2.41/0.99  ------  iProver source info
% 2.41/0.99  
% 2.41/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.41/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/0.99  git: non_committed_changes: false
% 2.41/0.99  git: last_make_outside_of_git: false
% 2.41/0.99  
% 2.41/0.99  ------ 
% 2.41/0.99  
% 2.41/0.99  ------ Input Options
% 2.41/0.99  
% 2.41/0.99  --out_options                           all
% 2.41/0.99  --tptp_safe_out                         true
% 2.41/0.99  --problem_path                          ""
% 2.41/0.99  --include_path                          ""
% 2.41/0.99  --clausifier                            res/vclausify_rel
% 2.41/0.99  --clausifier_options                    --mode clausify
% 2.41/0.99  --stdin                                 false
% 2.41/0.99  --stats_out                             all
% 2.41/0.99  
% 2.41/0.99  ------ General Options
% 2.41/0.99  
% 2.41/0.99  --fof                                   false
% 2.41/0.99  --time_out_real                         305.
% 2.41/0.99  --time_out_virtual                      -1.
% 2.41/0.99  --symbol_type_check                     false
% 2.41/0.99  --clausify_out                          false
% 2.41/0.99  --sig_cnt_out                           false
% 2.41/0.99  --trig_cnt_out                          false
% 2.41/0.99  --trig_cnt_out_tolerance                1.
% 2.41/0.99  --trig_cnt_out_sk_spl                   false
% 2.41/0.99  --abstr_cl_out                          false
% 2.41/0.99  
% 2.41/0.99  ------ Global Options
% 2.41/0.99  
% 2.41/0.99  --schedule                              default
% 2.41/0.99  --add_important_lit                     false
% 2.41/0.99  --prop_solver_per_cl                    1000
% 2.41/0.99  --min_unsat_core                        false
% 2.41/0.99  --soft_assumptions                      false
% 2.41/0.99  --soft_lemma_size                       3
% 2.41/0.99  --prop_impl_unit_size                   0
% 2.41/0.99  --prop_impl_unit                        []
% 2.41/0.99  --share_sel_clauses                     true
% 2.41/0.99  --reset_solvers                         false
% 2.41/0.99  --bc_imp_inh                            [conj_cone]
% 2.41/0.99  --conj_cone_tolerance                   3.
% 2.41/0.99  --extra_neg_conj                        none
% 2.41/0.99  --large_theory_mode                     true
% 2.41/0.99  --prolific_symb_bound                   200
% 2.41/0.99  --lt_threshold                          2000
% 2.41/0.99  --clause_weak_htbl                      true
% 2.41/0.99  --gc_record_bc_elim                     false
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing Options
% 2.41/0.99  
% 2.41/0.99  --preprocessing_flag                    true
% 2.41/0.99  --time_out_prep_mult                    0.1
% 2.41/0.99  --splitting_mode                        input
% 2.41/0.99  --splitting_grd                         true
% 2.41/0.99  --splitting_cvd                         false
% 2.41/0.99  --splitting_cvd_svl                     false
% 2.41/0.99  --splitting_nvd                         32
% 2.41/0.99  --sub_typing                            true
% 2.41/0.99  --prep_gs_sim                           true
% 2.41/0.99  --prep_unflatten                        true
% 2.41/0.99  --prep_res_sim                          true
% 2.41/0.99  --prep_upred                            true
% 2.41/0.99  --prep_sem_filter                       exhaustive
% 2.41/0.99  --prep_sem_filter_out                   false
% 2.41/0.99  --pred_elim                             true
% 2.41/0.99  --res_sim_input                         true
% 2.41/0.99  --eq_ax_congr_red                       true
% 2.41/0.99  --pure_diseq_elim                       true
% 2.41/0.99  --brand_transform                       false
% 2.41/0.99  --non_eq_to_eq                          false
% 2.41/0.99  --prep_def_merge                        true
% 2.41/0.99  --prep_def_merge_prop_impl              false
% 2.41/0.99  --prep_def_merge_mbd                    true
% 2.41/0.99  --prep_def_merge_tr_red                 false
% 2.41/0.99  --prep_def_merge_tr_cl                  false
% 2.41/0.99  --smt_preprocessing                     true
% 2.41/0.99  --smt_ac_axioms                         fast
% 2.41/0.99  --preprocessed_out                      false
% 2.41/0.99  --preprocessed_stats                    false
% 2.41/0.99  
% 2.41/0.99  ------ Abstraction refinement Options
% 2.41/0.99  
% 2.41/0.99  --abstr_ref                             []
% 2.41/0.99  --abstr_ref_prep                        false
% 2.41/0.99  --abstr_ref_until_sat                   false
% 2.41/0.99  --abstr_ref_sig_restrict                funpre
% 2.41/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/0.99  --abstr_ref_under                       []
% 2.41/0.99  
% 2.41/0.99  ------ SAT Options
% 2.41/0.99  
% 2.41/0.99  --sat_mode                              false
% 2.41/0.99  --sat_fm_restart_options                ""
% 2.41/0.99  --sat_gr_def                            false
% 2.41/0.99  --sat_epr_types                         true
% 2.41/0.99  --sat_non_cyclic_types                  false
% 2.41/0.99  --sat_finite_models                     false
% 2.41/0.99  --sat_fm_lemmas                         false
% 2.41/0.99  --sat_fm_prep                           false
% 2.41/0.99  --sat_fm_uc_incr                        true
% 2.41/0.99  --sat_out_model                         small
% 2.41/0.99  --sat_out_clauses                       false
% 2.41/0.99  
% 2.41/0.99  ------ QBF Options
% 2.41/0.99  
% 2.41/0.99  --qbf_mode                              false
% 2.41/0.99  --qbf_elim_univ                         false
% 2.41/0.99  --qbf_dom_inst                          none
% 2.41/0.99  --qbf_dom_pre_inst                      false
% 2.41/0.99  --qbf_sk_in                             false
% 2.41/0.99  --qbf_pred_elim                         true
% 2.41/0.99  --qbf_split                             512
% 2.41/0.99  
% 2.41/0.99  ------ BMC1 Options
% 2.41/0.99  
% 2.41/0.99  --bmc1_incremental                      false
% 2.41/0.99  --bmc1_axioms                           reachable_all
% 2.41/0.99  --bmc1_min_bound                        0
% 2.41/0.99  --bmc1_max_bound                        -1
% 2.41/0.99  --bmc1_max_bound_default                -1
% 2.41/0.99  --bmc1_symbol_reachability              true
% 2.41/0.99  --bmc1_property_lemmas                  false
% 2.41/0.99  --bmc1_k_induction                      false
% 2.41/0.99  --bmc1_non_equiv_states                 false
% 2.41/0.99  --bmc1_deadlock                         false
% 2.41/0.99  --bmc1_ucm                              false
% 2.41/0.99  --bmc1_add_unsat_core                   none
% 2.41/0.99  --bmc1_unsat_core_children              false
% 2.41/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/0.99  --bmc1_out_stat                         full
% 2.41/0.99  --bmc1_ground_init                      false
% 2.41/0.99  --bmc1_pre_inst_next_state              false
% 2.41/0.99  --bmc1_pre_inst_state                   false
% 2.41/0.99  --bmc1_pre_inst_reach_state             false
% 2.41/0.99  --bmc1_out_unsat_core                   false
% 2.41/0.99  --bmc1_aig_witness_out                  false
% 2.41/0.99  --bmc1_verbose                          false
% 2.41/0.99  --bmc1_dump_clauses_tptp                false
% 2.41/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.41/0.99  --bmc1_dump_file                        -
% 2.41/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.41/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.41/0.99  --bmc1_ucm_extend_mode                  1
% 2.41/0.99  --bmc1_ucm_init_mode                    2
% 2.41/0.99  --bmc1_ucm_cone_mode                    none
% 2.41/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.41/0.99  --bmc1_ucm_relax_model                  4
% 2.41/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.41/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/0.99  --bmc1_ucm_layered_model                none
% 2.41/0.99  --bmc1_ucm_max_lemma_size               10
% 2.41/0.99  
% 2.41/0.99  ------ AIG Options
% 2.41/0.99  
% 2.41/0.99  --aig_mode                              false
% 2.41/0.99  
% 2.41/0.99  ------ Instantiation Options
% 2.41/0.99  
% 2.41/0.99  --instantiation_flag                    true
% 2.41/0.99  --inst_sos_flag                         false
% 2.41/0.99  --inst_sos_phase                        true
% 2.41/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/0.99  --inst_lit_sel_side                     num_symb
% 2.41/0.99  --inst_solver_per_active                1400
% 2.41/0.99  --inst_solver_calls_frac                1.
% 2.41/0.99  --inst_passive_queue_type               priority_queues
% 2.41/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/0.99  --inst_passive_queues_freq              [25;2]
% 2.41/0.99  --inst_dismatching                      true
% 2.41/0.99  --inst_eager_unprocessed_to_passive     true
% 2.41/0.99  --inst_prop_sim_given                   true
% 2.41/0.99  --inst_prop_sim_new                     false
% 2.41/0.99  --inst_subs_new                         false
% 2.41/0.99  --inst_eq_res_simp                      false
% 2.41/0.99  --inst_subs_given                       false
% 2.41/0.99  --inst_orphan_elimination               true
% 2.41/0.99  --inst_learning_loop_flag               true
% 2.41/0.99  --inst_learning_start                   3000
% 2.41/0.99  --inst_learning_factor                  2
% 2.41/0.99  --inst_start_prop_sim_after_learn       3
% 2.41/0.99  --inst_sel_renew                        solver
% 2.41/0.99  --inst_lit_activity_flag                true
% 2.41/0.99  --inst_restr_to_given                   false
% 2.41/0.99  --inst_activity_threshold               500
% 2.41/0.99  --inst_out_proof                        true
% 2.41/0.99  
% 2.41/0.99  ------ Resolution Options
% 2.41/0.99  
% 2.41/0.99  --resolution_flag                       true
% 2.41/0.99  --res_lit_sel                           adaptive
% 2.41/0.99  --res_lit_sel_side                      none
% 2.41/0.99  --res_ordering                          kbo
% 2.41/0.99  --res_to_prop_solver                    active
% 2.41/0.99  --res_prop_simpl_new                    false
% 2.41/0.99  --res_prop_simpl_given                  true
% 2.41/0.99  --res_passive_queue_type                priority_queues
% 2.41/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/0.99  --res_passive_queues_freq               [15;5]
% 2.41/0.99  --res_forward_subs                      full
% 2.41/0.99  --res_backward_subs                     full
% 2.41/0.99  --res_forward_subs_resolution           true
% 2.41/0.99  --res_backward_subs_resolution          true
% 2.41/0.99  --res_orphan_elimination                true
% 2.41/0.99  --res_time_limit                        2.
% 2.41/0.99  --res_out_proof                         true
% 2.41/0.99  
% 2.41/0.99  ------ Superposition Options
% 2.41/0.99  
% 2.41/0.99  --superposition_flag                    true
% 2.41/0.99  --sup_passive_queue_type                priority_queues
% 2.41/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.41/0.99  --demod_completeness_check              fast
% 2.41/0.99  --demod_use_ground                      true
% 2.41/0.99  --sup_to_prop_solver                    passive
% 2.41/0.99  --sup_prop_simpl_new                    true
% 2.41/0.99  --sup_prop_simpl_given                  true
% 2.41/0.99  --sup_fun_splitting                     false
% 2.41/0.99  --sup_smt_interval                      50000
% 2.41/0.99  
% 2.41/0.99  ------ Superposition Simplification Setup
% 2.41/0.99  
% 2.41/0.99  --sup_indices_passive                   []
% 2.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_full_bw                           [BwDemod]
% 2.41/0.99  --sup_immed_triv                        [TrivRules]
% 2.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_immed_bw_main                     []
% 2.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.99  
% 2.41/0.99  ------ Combination Options
% 2.41/0.99  
% 2.41/0.99  --comb_res_mult                         3
% 2.41/0.99  --comb_sup_mult                         2
% 2.41/0.99  --comb_inst_mult                        10
% 2.41/0.99  
% 2.41/0.99  ------ Debug Options
% 2.41/0.99  
% 2.41/0.99  --dbg_backtrace                         false
% 2.41/0.99  --dbg_dump_prop_clauses                 false
% 2.41/0.99  --dbg_dump_prop_clauses_file            -
% 2.41/0.99  --dbg_out_stat                          false
% 2.41/0.99  ------ Parsing...
% 2.41/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/0.99  ------ Proving...
% 2.41/0.99  ------ Problem Properties 
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  clauses                                 16
% 2.41/0.99  conjectures                             2
% 2.41/0.99  EPR                                     0
% 2.41/0.99  Horn                                    12
% 2.41/0.99  unary                                   9
% 2.41/0.99  binary                                  5
% 2.41/0.99  lits                                    25
% 2.41/0.99  lits eq                                 20
% 2.41/0.99  fd_pure                                 0
% 2.41/0.99  fd_pseudo                               0
% 2.41/0.99  fd_cond                                 3
% 2.41/0.99  fd_pseudo_cond                          1
% 2.41/0.99  AC symbols                              0
% 2.41/0.99  
% 2.41/0.99  ------ Schedule dynamic 5 is on 
% 2.41/0.99  
% 2.41/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  ------ 
% 2.41/0.99  Current options:
% 2.41/0.99  ------ 
% 2.41/0.99  
% 2.41/0.99  ------ Input Options
% 2.41/0.99  
% 2.41/0.99  --out_options                           all
% 2.41/0.99  --tptp_safe_out                         true
% 2.41/0.99  --problem_path                          ""
% 2.41/0.99  --include_path                          ""
% 2.41/0.99  --clausifier                            res/vclausify_rel
% 2.41/0.99  --clausifier_options                    --mode clausify
% 2.41/0.99  --stdin                                 false
% 2.41/0.99  --stats_out                             all
% 2.41/0.99  
% 2.41/0.99  ------ General Options
% 2.41/0.99  
% 2.41/0.99  --fof                                   false
% 2.41/0.99  --time_out_real                         305.
% 2.41/0.99  --time_out_virtual                      -1.
% 2.41/0.99  --symbol_type_check                     false
% 2.41/0.99  --clausify_out                          false
% 2.41/0.99  --sig_cnt_out                           false
% 2.41/0.99  --trig_cnt_out                          false
% 2.41/0.99  --trig_cnt_out_tolerance                1.
% 2.41/0.99  --trig_cnt_out_sk_spl                   false
% 2.41/0.99  --abstr_cl_out                          false
% 2.41/0.99  
% 2.41/0.99  ------ Global Options
% 2.41/0.99  
% 2.41/0.99  --schedule                              default
% 2.41/0.99  --add_important_lit                     false
% 2.41/0.99  --prop_solver_per_cl                    1000
% 2.41/0.99  --min_unsat_core                        false
% 2.41/0.99  --soft_assumptions                      false
% 2.41/0.99  --soft_lemma_size                       3
% 2.41/0.99  --prop_impl_unit_size                   0
% 2.41/0.99  --prop_impl_unit                        []
% 2.41/0.99  --share_sel_clauses                     true
% 2.41/0.99  --reset_solvers                         false
% 2.41/0.99  --bc_imp_inh                            [conj_cone]
% 2.41/0.99  --conj_cone_tolerance                   3.
% 2.41/0.99  --extra_neg_conj                        none
% 2.41/0.99  --large_theory_mode                     true
% 2.41/0.99  --prolific_symb_bound                   200
% 2.41/0.99  --lt_threshold                          2000
% 2.41/0.99  --clause_weak_htbl                      true
% 2.41/0.99  --gc_record_bc_elim                     false
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing Options
% 2.41/0.99  
% 2.41/0.99  --preprocessing_flag                    true
% 2.41/0.99  --time_out_prep_mult                    0.1
% 2.41/0.99  --splitting_mode                        input
% 2.41/0.99  --splitting_grd                         true
% 2.41/0.99  --splitting_cvd                         false
% 2.41/0.99  --splitting_cvd_svl                     false
% 2.41/0.99  --splitting_nvd                         32
% 2.41/0.99  --sub_typing                            true
% 2.41/0.99  --prep_gs_sim                           true
% 2.41/0.99  --prep_unflatten                        true
% 2.41/0.99  --prep_res_sim                          true
% 2.41/0.99  --prep_upred                            true
% 2.41/0.99  --prep_sem_filter                       exhaustive
% 2.41/0.99  --prep_sem_filter_out                   false
% 2.41/0.99  --pred_elim                             true
% 2.41/0.99  --res_sim_input                         true
% 2.41/0.99  --eq_ax_congr_red                       true
% 2.41/0.99  --pure_diseq_elim                       true
% 2.41/0.99  --brand_transform                       false
% 2.41/0.99  --non_eq_to_eq                          false
% 2.41/0.99  --prep_def_merge                        true
% 2.41/0.99  --prep_def_merge_prop_impl              false
% 2.41/0.99  --prep_def_merge_mbd                    true
% 2.41/0.99  --prep_def_merge_tr_red                 false
% 2.41/0.99  --prep_def_merge_tr_cl                  false
% 2.41/0.99  --smt_preprocessing                     true
% 2.41/0.99  --smt_ac_axioms                         fast
% 2.41/0.99  --preprocessed_out                      false
% 2.41/0.99  --preprocessed_stats                    false
% 2.41/0.99  
% 2.41/0.99  ------ Abstraction refinement Options
% 2.41/0.99  
% 2.41/0.99  --abstr_ref                             []
% 2.41/0.99  --abstr_ref_prep                        false
% 2.41/0.99  --abstr_ref_until_sat                   false
% 2.41/0.99  --abstr_ref_sig_restrict                funpre
% 2.41/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/0.99  --abstr_ref_under                       []
% 2.41/0.99  
% 2.41/0.99  ------ SAT Options
% 2.41/0.99  
% 2.41/0.99  --sat_mode                              false
% 2.41/0.99  --sat_fm_restart_options                ""
% 2.41/0.99  --sat_gr_def                            false
% 2.41/0.99  --sat_epr_types                         true
% 2.41/0.99  --sat_non_cyclic_types                  false
% 2.41/0.99  --sat_finite_models                     false
% 2.41/0.99  --sat_fm_lemmas                         false
% 2.41/0.99  --sat_fm_prep                           false
% 2.41/0.99  --sat_fm_uc_incr                        true
% 2.41/0.99  --sat_out_model                         small
% 2.41/0.99  --sat_out_clauses                       false
% 2.41/0.99  
% 2.41/0.99  ------ QBF Options
% 2.41/0.99  
% 2.41/0.99  --qbf_mode                              false
% 2.41/0.99  --qbf_elim_univ                         false
% 2.41/0.99  --qbf_dom_inst                          none
% 2.41/0.99  --qbf_dom_pre_inst                      false
% 2.41/0.99  --qbf_sk_in                             false
% 2.41/0.99  --qbf_pred_elim                         true
% 2.41/0.99  --qbf_split                             512
% 2.41/0.99  
% 2.41/0.99  ------ BMC1 Options
% 2.41/0.99  
% 2.41/0.99  --bmc1_incremental                      false
% 2.41/0.99  --bmc1_axioms                           reachable_all
% 2.41/0.99  --bmc1_min_bound                        0
% 2.41/0.99  --bmc1_max_bound                        -1
% 2.41/0.99  --bmc1_max_bound_default                -1
% 2.41/0.99  --bmc1_symbol_reachability              true
% 2.41/0.99  --bmc1_property_lemmas                  false
% 2.41/0.99  --bmc1_k_induction                      false
% 2.41/0.99  --bmc1_non_equiv_states                 false
% 2.41/0.99  --bmc1_deadlock                         false
% 2.41/0.99  --bmc1_ucm                              false
% 2.41/0.99  --bmc1_add_unsat_core                   none
% 2.41/0.99  --bmc1_unsat_core_children              false
% 2.41/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/0.99  --bmc1_out_stat                         full
% 2.41/0.99  --bmc1_ground_init                      false
% 2.41/0.99  --bmc1_pre_inst_next_state              false
% 2.41/0.99  --bmc1_pre_inst_state                   false
% 2.41/0.99  --bmc1_pre_inst_reach_state             false
% 2.41/0.99  --bmc1_out_unsat_core                   false
% 2.41/0.99  --bmc1_aig_witness_out                  false
% 2.41/0.99  --bmc1_verbose                          false
% 2.41/0.99  --bmc1_dump_clauses_tptp                false
% 2.41/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.41/0.99  --bmc1_dump_file                        -
% 2.41/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.41/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.41/0.99  --bmc1_ucm_extend_mode                  1
% 2.41/0.99  --bmc1_ucm_init_mode                    2
% 2.41/0.99  --bmc1_ucm_cone_mode                    none
% 2.41/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.41/0.99  --bmc1_ucm_relax_model                  4
% 2.41/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.41/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/0.99  --bmc1_ucm_layered_model                none
% 2.41/0.99  --bmc1_ucm_max_lemma_size               10
% 2.41/0.99  
% 2.41/0.99  ------ AIG Options
% 2.41/0.99  
% 2.41/0.99  --aig_mode                              false
% 2.41/0.99  
% 2.41/0.99  ------ Instantiation Options
% 2.41/0.99  
% 2.41/0.99  --instantiation_flag                    true
% 2.41/0.99  --inst_sos_flag                         false
% 2.41/0.99  --inst_sos_phase                        true
% 2.41/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/0.99  --inst_lit_sel_side                     none
% 2.41/0.99  --inst_solver_per_active                1400
% 2.41/0.99  --inst_solver_calls_frac                1.
% 2.41/0.99  --inst_passive_queue_type               priority_queues
% 2.41/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/0.99  --inst_passive_queues_freq              [25;2]
% 2.41/0.99  --inst_dismatching                      true
% 2.41/0.99  --inst_eager_unprocessed_to_passive     true
% 2.41/0.99  --inst_prop_sim_given                   true
% 2.41/0.99  --inst_prop_sim_new                     false
% 2.41/0.99  --inst_subs_new                         false
% 2.41/0.99  --inst_eq_res_simp                      false
% 2.41/0.99  --inst_subs_given                       false
% 2.41/0.99  --inst_orphan_elimination               true
% 2.41/0.99  --inst_learning_loop_flag               true
% 2.41/0.99  --inst_learning_start                   3000
% 2.41/0.99  --inst_learning_factor                  2
% 2.41/0.99  --inst_start_prop_sim_after_learn       3
% 2.41/0.99  --inst_sel_renew                        solver
% 2.41/0.99  --inst_lit_activity_flag                true
% 2.41/0.99  --inst_restr_to_given                   false
% 2.41/0.99  --inst_activity_threshold               500
% 2.41/0.99  --inst_out_proof                        true
% 2.41/0.99  
% 2.41/0.99  ------ Resolution Options
% 2.41/0.99  
% 2.41/0.99  --resolution_flag                       false
% 2.41/0.99  --res_lit_sel                           adaptive
% 2.41/0.99  --res_lit_sel_side                      none
% 2.41/0.99  --res_ordering                          kbo
% 2.41/0.99  --res_to_prop_solver                    active
% 2.41/0.99  --res_prop_simpl_new                    false
% 2.41/0.99  --res_prop_simpl_given                  true
% 2.41/0.99  --res_passive_queue_type                priority_queues
% 2.41/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/0.99  --res_passive_queues_freq               [15;5]
% 2.41/0.99  --res_forward_subs                      full
% 2.41/0.99  --res_backward_subs                     full
% 2.41/0.99  --res_forward_subs_resolution           true
% 2.41/0.99  --res_backward_subs_resolution          true
% 2.41/0.99  --res_orphan_elimination                true
% 2.41/0.99  --res_time_limit                        2.
% 2.41/0.99  --res_out_proof                         true
% 2.41/0.99  
% 2.41/0.99  ------ Superposition Options
% 2.41/0.99  
% 2.41/0.99  --superposition_flag                    true
% 2.41/0.99  --sup_passive_queue_type                priority_queues
% 2.41/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.41/0.99  --demod_completeness_check              fast
% 2.41/0.99  --demod_use_ground                      true
% 2.41/0.99  --sup_to_prop_solver                    passive
% 2.41/0.99  --sup_prop_simpl_new                    true
% 2.41/0.99  --sup_prop_simpl_given                  true
% 2.41/0.99  --sup_fun_splitting                     false
% 2.41/0.99  --sup_smt_interval                      50000
% 2.41/0.99  
% 2.41/0.99  ------ Superposition Simplification Setup
% 2.41/0.99  
% 2.41/0.99  --sup_indices_passive                   []
% 2.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_full_bw                           [BwDemod]
% 2.41/0.99  --sup_immed_triv                        [TrivRules]
% 2.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_immed_bw_main                     []
% 2.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.99  
% 2.41/0.99  ------ Combination Options
% 2.41/0.99  
% 2.41/0.99  --comb_res_mult                         3
% 2.41/0.99  --comb_sup_mult                         2
% 2.41/0.99  --comb_inst_mult                        10
% 2.41/0.99  
% 2.41/0.99  ------ Debug Options
% 2.41/0.99  
% 2.41/0.99  --dbg_backtrace                         false
% 2.41/0.99  --dbg_dump_prop_clauses                 false
% 2.41/0.99  --dbg_dump_prop_clauses_file            -
% 2.41/0.99  --dbg_out_stat                          false
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  ------ Proving...
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  % SZS status Theorem for theBenchmark.p
% 2.41/0.99  
% 2.41/0.99   Resolution empty clause
% 2.41/0.99  
% 2.41/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/0.99  
% 2.41/0.99  fof(f14,axiom,(
% 2.41/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f18,plain,(
% 2.41/0.99    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.41/0.99    inference(ennf_transformation,[],[f14])).
% 2.41/0.99  
% 2.41/0.99  fof(f22,plain,(
% 2.41/0.99    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 2.41/0.99    introduced(choice_axiom,[])).
% 2.41/0.99  
% 2.41/0.99  fof(f23,plain,(
% 2.41/0.99    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 2.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).
% 2.41/0.99  
% 2.41/0.99  fof(f43,plain,(
% 2.41/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.41/0.99    inference(cnf_transformation,[],[f23])).
% 2.41/0.99  
% 2.41/0.99  fof(f10,axiom,(
% 2.41/0.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f20,plain,(
% 2.41/0.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 2.41/0.99    inference(nnf_transformation,[],[f10])).
% 2.41/0.99  
% 2.41/0.99  fof(f37,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 2.41/0.99    inference(cnf_transformation,[],[f20])).
% 2.41/0.99  
% 2.41/0.99  fof(f6,axiom,(
% 2.41/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f32,plain,(
% 2.41/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f6])).
% 2.41/0.99  
% 2.41/0.99  fof(f7,axiom,(
% 2.41/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f33,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f7])).
% 2.41/0.99  
% 2.41/0.99  fof(f8,axiom,(
% 2.41/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f34,plain,(
% 2.41/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f8])).
% 2.41/0.99  
% 2.41/0.99  fof(f9,axiom,(
% 2.41/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f35,plain,(
% 2.41/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f9])).
% 2.41/0.99  
% 2.41/0.99  fof(f48,plain,(
% 2.41/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f34,f35])).
% 2.41/0.99  
% 2.41/0.99  fof(f49,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f33,f48])).
% 2.41/0.99  
% 2.41/0.99  fof(f50,plain,(
% 2.41/0.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f32,f49])).
% 2.41/0.99  
% 2.41/0.99  fof(f54,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X0,X0,X0,X0,X0) | X0 = X1) )),
% 2.41/0.99    inference(definition_unfolding,[],[f37,f50,f50,f50])).
% 2.41/0.99  
% 2.41/0.99  fof(f11,axiom,(
% 2.41/0.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f21,plain,(
% 2.41/0.99    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.41/0.99    inference(nnf_transformation,[],[f11])).
% 2.41/0.99  
% 2.41/0.99  fof(f38,plain,(
% 2.41/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 2.41/0.99    inference(cnf_transformation,[],[f21])).
% 2.41/0.99  
% 2.41/0.99  fof(f57,plain,(
% 2.41/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0) )),
% 2.41/0.99    inference(definition_unfolding,[],[f38,f50])).
% 2.41/0.99  
% 2.41/0.99  fof(f36,plain,(
% 2.41/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f20])).
% 2.41/0.99  
% 2.41/0.99  fof(f55,plain,(
% 2.41/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f36,f50,f50,f50])).
% 2.41/0.99  
% 2.41/0.99  fof(f59,plain,(
% 2.41/0.99    ( ! [X1] : (k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X1,X1,X1,X1,X1)) )),
% 2.41/0.99    inference(equality_resolution,[],[f55])).
% 2.41/0.99  
% 2.41/0.99  fof(f1,axiom,(
% 2.41/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f17,plain,(
% 2.41/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.41/0.99    inference(rectify,[],[f1])).
% 2.41/0.99  
% 2.41/0.99  fof(f27,plain,(
% 2.41/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.41/0.99    inference(cnf_transformation,[],[f17])).
% 2.41/0.99  
% 2.41/0.99  fof(f4,axiom,(
% 2.41/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f30,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.41/0.99    inference(cnf_transformation,[],[f4])).
% 2.41/0.99  
% 2.41/0.99  fof(f52,plain,(
% 2.41/0.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.41/0.99    inference(definition_unfolding,[],[f27,f30])).
% 2.41/0.99  
% 2.41/0.99  fof(f2,axiom,(
% 2.41/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f28,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.41/0.99    inference(cnf_transformation,[],[f2])).
% 2.41/0.99  
% 2.41/0.99  fof(f51,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.41/0.99    inference(definition_unfolding,[],[f28,f30])).
% 2.41/0.99  
% 2.41/0.99  fof(f3,axiom,(
% 2.41/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f29,plain,(
% 2.41/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.41/0.99    inference(cnf_transformation,[],[f3])).
% 2.41/0.99  
% 2.41/0.99  fof(f53,plain,(
% 2.41/0.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 2.41/0.99    inference(definition_unfolding,[],[f29,f30])).
% 2.41/0.99  
% 2.41/0.99  fof(f5,axiom,(
% 2.41/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f31,plain,(
% 2.41/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.41/0.99    inference(cnf_transformation,[],[f5])).
% 2.41/0.99  
% 2.41/0.99  fof(f39,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f21])).
% 2.41/0.99  
% 2.41/0.99  fof(f56,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f39,f50])).
% 2.41/0.99  
% 2.41/0.99  fof(f15,conjecture,(
% 2.41/0.99    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f16,negated_conjecture,(
% 2.41/0.99    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 2.41/0.99    inference(negated_conjecture,[],[f15])).
% 2.41/0.99  
% 2.41/0.99  fof(f19,plain,(
% 2.41/0.99    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 2.41/0.99    inference(ennf_transformation,[],[f16])).
% 2.41/0.99  
% 2.41/0.99  fof(f25,plain,(
% 2.41/0.99    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK2,sK3) = X0) )),
% 2.41/0.99    introduced(choice_axiom,[])).
% 2.41/0.99  
% 2.41/0.99  fof(f24,plain,(
% 2.41/0.99    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK1) = sK1 | k1_mcart_1(sK1) = sK1) & ? [X2,X1] : k4_tarski(X1,X2) = sK1)),
% 2.41/0.99    introduced(choice_axiom,[])).
% 2.41/0.99  
% 2.41/0.99  fof(f26,plain,(
% 2.41/0.99    (k2_mcart_1(sK1) = sK1 | k1_mcart_1(sK1) = sK1) & k4_tarski(sK2,sK3) = sK1),
% 2.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f25,f24])).
% 2.41/0.99  
% 2.41/0.99  fof(f47,plain,(
% 2.41/0.99    k2_mcart_1(sK1) = sK1 | k1_mcart_1(sK1) = sK1),
% 2.41/0.99    inference(cnf_transformation,[],[f26])).
% 2.41/0.99  
% 2.41/0.99  fof(f46,plain,(
% 2.41/0.99    k4_tarski(sK2,sK3) = sK1),
% 2.41/0.99    inference(cnf_transformation,[],[f26])).
% 2.41/0.99  
% 2.41/0.99  fof(f13,axiom,(
% 2.41/0.99    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.41/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f41,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.41/0.99    inference(cnf_transformation,[],[f13])).
% 2.41/0.99  
% 2.41/0.99  fof(f42,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.41/0.99    inference(cnf_transformation,[],[f13])).
% 2.41/0.99  
% 2.41/0.99  fof(f45,plain,(
% 2.41/0.99    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK0(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 2.41/0.99    inference(cnf_transformation,[],[f23])).
% 2.41/0.99  
% 2.41/0.99  fof(f44,plain,(
% 2.41/0.99    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK0(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 2.41/0.99    inference(cnf_transformation,[],[f23])).
% 2.41/0.99  
% 2.41/0.99  cnf(c_13,plain,
% 2.41/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.41/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_365,plain,
% 2.41/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_4,plain,
% 2.41/0.99      ( X0 = X1
% 2.41/0.99      | k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X1,X1,X1,X1,X1) ),
% 2.41/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_7,plain,
% 2.41/0.99      ( ~ r2_hidden(X0,X1)
% 2.41/0.99      | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) != X1 ),
% 2.41/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_368,plain,
% 2.41/0.99      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0
% 2.41/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1450,plain,
% 2.41/0.99      ( X0 = X1 | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_4,c_368]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1575,plain,
% 2.41/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) = k1_xboole_0
% 2.41/0.99      | sK0(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_365,c_1450]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_5,plain,
% 2.41/0.99      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) != k3_enumset1(X0,X0,X0,X0,X0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1,plain,
% 2.41/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 2.41/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_0,plain,
% 2.41/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.41/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_721,plain,
% 2.41/0.99      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_2,plain,
% 2.41/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.41/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_722,plain,
% 2.41/0.99      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3,plain,
% 2.41/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.41/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_732,plain,
% 2.41/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_722,c_3]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_724,plain,
% 2.41/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_726,plain,
% 2.41/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_724,c_2]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_733,plain,
% 2.41/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.41/0.99      inference(demodulation,[status(thm)],[c_732,c_726]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_737,plain,
% 2.41/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_721,c_733]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1283,plain,
% 2.41/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 2.41/0.99      inference(demodulation,[status(thm)],[c_5,c_737]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1581,plain,
% 2.41/0.99      ( sK0(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
% 2.41/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1575,c_1283]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1585,plain,
% 2.41/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) = k1_xboole_0
% 2.41/0.99      | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1581,c_365]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_6,plain,
% 2.41/0.99      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = X1 ),
% 2.41/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_450,plain,
% 2.41/0.99      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0))
% 2.41/0.99      | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X0,X0,X0,X0,X0) ),
% 2.41/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_451,plain,
% 2.41/0.99      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X0,X0,X0,X0,X0)
% 2.41/0.99      | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_2621,plain,
% 2.41/0.99      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 2.41/0.99      inference(global_propositional_subsumption,
% 2.41/0.99                [status(thm)],
% 2.41/0.99                [c_1585,c_5,c_451]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_14,negated_conjecture,
% 2.41/0.99      ( k1_mcart_1(sK1) = sK1 | k2_mcart_1(sK1) = sK1 ),
% 2.41/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_15,negated_conjecture,
% 2.41/0.99      ( k4_tarski(sK2,sK3) = sK1 ),
% 2.41/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_10,plain,
% 2.41/0.99      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 2.41/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_457,plain,
% 2.41/0.99      ( k1_mcart_1(sK1) = sK2 ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_15,c_10]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_500,plain,
% 2.41/0.99      ( k2_mcart_1(sK1) = sK1 | sK2 = sK1 ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_14,c_457]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_9,plain,
% 2.41/0.99      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 2.41/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_436,plain,
% 2.41/0.99      ( k2_mcart_1(sK1) = sK3 ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_15,c_9]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_502,plain,
% 2.41/0.99      ( sK3 = sK1 | sK2 = sK1 ),
% 2.41/0.99      inference(demodulation,[status(thm)],[c_500,c_436]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_505,plain,
% 2.41/0.99      ( k4_tarski(sK2,sK1) = sK1 | sK2 = sK1 ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_502,c_15]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_11,plain,
% 2.41/0.99      ( ~ r2_hidden(X0,X1) | k4_tarski(X2,X0) != sK0(X1) | k1_xboole_0 = X1 ),
% 2.41/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_367,plain,
% 2.41/0.99      ( k4_tarski(X0,X1) != sK0(X2)
% 2.41/0.99      | k1_xboole_0 = X2
% 2.41/0.99      | r2_hidden(X1,X2) != iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_906,plain,
% 2.41/0.99      ( sK0(X0) != sK1
% 2.41/0.99      | sK2 = sK1
% 2.41/0.99      | k1_xboole_0 = X0
% 2.41/0.99      | r2_hidden(sK1,X0) != iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_505,c_367]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1586,plain,
% 2.41/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) = k1_xboole_0
% 2.41/0.99      | sK2 = sK1
% 2.41/0.99      | sK1 != X0
% 2.41/0.99      | r2_hidden(sK1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1581,c_906]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_2270,plain,
% 2.41/0.99      ( sK2 = sK1
% 2.41/0.99      | sK1 != X0
% 2.41/0.99      | r2_hidden(sK1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.41/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1586,c_1283]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_2279,plain,
% 2.41/0.99      ( sK2 = sK1 | r2_hidden(sK1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.41/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2270,c_1450]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_2629,plain,
% 2.41/0.99      ( sK2 = sK1 ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_2621,c_2279]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_12,plain,
% 2.41/0.99      ( ~ r2_hidden(X0,X1) | k4_tarski(X0,X2) != sK0(X1) | k1_xboole_0 = X1 ),
% 2.41/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_366,plain,
% 2.41/0.99      ( k4_tarski(X0,X1) != sK0(X2)
% 2.41/0.99      | k1_xboole_0 = X2
% 2.41/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_561,plain,
% 2.41/0.99      ( sK0(X0) != sK1 | k1_xboole_0 = X0 | r2_hidden(sK2,X0) != iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_15,c_366]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1588,plain,
% 2.41/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) = k1_xboole_0
% 2.41/0.99      | sK1 != X0
% 2.41/0.99      | r2_hidden(sK2,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1581,c_561]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1912,plain,
% 2.41/0.99      ( sK1 != X0 | r2_hidden(sK2,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.41/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1588,c_1283]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_2757,plain,
% 2.41/0.99      ( sK1 != X0 | r2_hidden(sK1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.41/0.99      inference(demodulation,[status(thm)],[c_2629,c_1912]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3096,plain,
% 2.41/0.99      ( r2_hidden(sK1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.41/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2757,c_1450]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3101,plain,
% 2.41/0.99      ( $false ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_2621,c_3096]) ).
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/0.99  
% 2.41/0.99  ------                               Statistics
% 2.41/0.99  
% 2.41/0.99  ------ General
% 2.41/0.99  
% 2.41/0.99  abstr_ref_over_cycles:                  0
% 2.41/0.99  abstr_ref_under_cycles:                 0
% 2.41/0.99  gc_basic_clause_elim:                   0
% 2.41/0.99  forced_gc_time:                         0
% 2.41/0.99  parsing_time:                           0.01
% 2.41/0.99  unif_index_cands_time:                  0.
% 2.41/0.99  unif_index_add_time:                    0.
% 2.41/0.99  orderings_time:                         0.
% 2.41/0.99  out_proof_time:                         0.007
% 2.41/0.99  total_time:                             0.155
% 2.41/0.99  num_of_symbols:                         44
% 2.41/0.99  num_of_terms:                           4949
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing
% 2.41/0.99  
% 2.41/0.99  num_of_splits:                          0
% 2.41/0.99  num_of_split_atoms:                     0
% 2.41/0.99  num_of_reused_defs:                     0
% 2.41/0.99  num_eq_ax_congr_red:                    16
% 2.41/0.99  num_of_sem_filtered_clauses:            1
% 2.41/0.99  num_of_subtypes:                        0
% 2.41/0.99  monotx_restored_types:                  0
% 2.41/0.99  sat_num_of_epr_types:                   0
% 2.41/0.99  sat_num_of_non_cyclic_types:            0
% 2.41/0.99  sat_guarded_non_collapsed_types:        0
% 2.41/0.99  num_pure_diseq_elim:                    0
% 2.41/0.99  simp_replaced_by:                       0
% 2.41/0.99  res_preprocessed:                       67
% 2.41/0.99  prep_upred:                             0
% 2.41/0.99  prep_unflattend:                        6
% 2.41/0.99  smt_new_axioms:                         0
% 2.41/0.99  pred_elim_cands:                        1
% 2.41/0.99  pred_elim:                              0
% 2.41/0.99  pred_elim_cl:                           0
% 2.41/0.99  pred_elim_cycles:                       1
% 2.41/0.99  merged_defs:                            6
% 2.41/0.99  merged_defs_ncl:                        0
% 2.41/0.99  bin_hyper_res:                          6
% 2.41/0.99  prep_cycles:                            3
% 2.41/0.99  pred_elim_time:                         0.001
% 2.41/0.99  splitting_time:                         0.
% 2.41/0.99  sem_filter_time:                        0.
% 2.41/0.99  monotx_time:                            0.
% 2.41/0.99  subtype_inf_time:                       0.
% 2.41/0.99  
% 2.41/0.99  ------ Problem properties
% 2.41/0.99  
% 2.41/0.99  clauses:                                16
% 2.41/0.99  conjectures:                            2
% 2.41/0.99  epr:                                    0
% 2.41/0.99  horn:                                   12
% 2.41/0.99  ground:                                 2
% 2.41/0.99  unary:                                  9
% 2.41/0.99  binary:                                 5
% 2.41/0.99  lits:                                   25
% 2.41/0.99  lits_eq:                                20
% 2.41/0.99  fd_pure:                                0
% 2.41/0.99  fd_pseudo:                              0
% 2.41/0.99  fd_cond:                                3
% 2.41/0.99  fd_pseudo_cond:                         1
% 2.41/0.99  ac_symbols:                             0
% 2.41/0.99  
% 2.41/0.99  ------ Propositional Solver
% 2.41/0.99  
% 2.41/0.99  prop_solver_calls:                      23
% 2.41/0.99  prop_fast_solver_calls:                 342
% 2.41/0.99  smt_solver_calls:                       0
% 2.41/0.99  smt_fast_solver_calls:                  0
% 2.41/0.99  prop_num_of_clauses:                    1059
% 2.41/0.99  prop_preprocess_simplified:             3594
% 2.41/0.99  prop_fo_subsumed:                       6
% 2.41/0.99  prop_solver_time:                       0.
% 2.41/0.99  smt_solver_time:                        0.
% 2.41/0.99  smt_fast_solver_time:                   0.
% 2.41/0.99  prop_fast_solver_time:                  0.
% 2.41/0.99  prop_unsat_core_time:                   0.
% 2.41/0.99  
% 2.41/0.99  ------ QBF
% 2.41/0.99  
% 2.41/0.99  qbf_q_res:                              0
% 2.41/0.99  qbf_num_tautologies:                    0
% 2.41/0.99  qbf_prep_cycles:                        0
% 2.41/0.99  
% 2.41/0.99  ------ BMC1
% 2.41/0.99  
% 2.41/0.99  bmc1_current_bound:                     -1
% 2.41/0.99  bmc1_last_solved_bound:                 -1
% 2.41/0.99  bmc1_unsat_core_size:                   -1
% 2.41/0.99  bmc1_unsat_core_parents_size:           -1
% 2.41/0.99  bmc1_merge_next_fun:                    0
% 2.41/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.41/0.99  
% 2.41/0.99  ------ Instantiation
% 2.41/0.99  
% 2.41/0.99  inst_num_of_clauses:                    539
% 2.41/0.99  inst_num_in_passive:                    288
% 2.41/0.99  inst_num_in_active:                     160
% 2.41/0.99  inst_num_in_unprocessed:                91
% 2.41/0.99  inst_num_of_loops:                      220
% 2.41/0.99  inst_num_of_learning_restarts:          0
% 2.41/0.99  inst_num_moves_active_passive:          57
% 2.41/0.99  inst_lit_activity:                      0
% 2.41/0.99  inst_lit_activity_moves:                0
% 2.41/0.99  inst_num_tautologies:                   0
% 2.41/0.99  inst_num_prop_implied:                  0
% 2.41/0.99  inst_num_existing_simplified:           0
% 2.41/0.99  inst_num_eq_res_simplified:             0
% 2.41/0.99  inst_num_child_elim:                    0
% 2.41/0.99  inst_num_of_dismatching_blockings:      408
% 2.41/0.99  inst_num_of_non_proper_insts:           590
% 2.41/0.99  inst_num_of_duplicates:                 0
% 2.41/0.99  inst_inst_num_from_inst_to_res:         0
% 2.41/0.99  inst_dismatching_checking_time:         0.
% 2.41/0.99  
% 2.41/0.99  ------ Resolution
% 2.41/0.99  
% 2.41/0.99  res_num_of_clauses:                     0
% 2.41/0.99  res_num_in_passive:                     0
% 2.41/0.99  res_num_in_active:                      0
% 2.41/0.99  res_num_of_loops:                       70
% 2.41/0.99  res_forward_subset_subsumed:            58
% 2.41/0.99  res_backward_subset_subsumed:           0
% 2.41/0.99  res_forward_subsumed:                   0
% 2.41/0.99  res_backward_subsumed:                  0
% 2.41/0.99  res_forward_subsumption_resolution:     0
% 2.41/0.99  res_backward_subsumption_resolution:    0
% 2.41/0.99  res_clause_to_clause_subsumption:       96
% 2.41/0.99  res_orphan_elimination:                 0
% 2.41/0.99  res_tautology_del:                      74
% 2.41/0.99  res_num_eq_res_simplified:              0
% 2.41/0.99  res_num_sel_changes:                    0
% 2.41/0.99  res_moves_from_active_to_pass:          0
% 2.41/0.99  
% 2.41/0.99  ------ Superposition
% 2.41/0.99  
% 2.41/0.99  sup_time_total:                         0.
% 2.41/0.99  sup_time_generating:                    0.
% 2.41/0.99  sup_time_sim_full:                      0.
% 2.41/0.99  sup_time_sim_immed:                     0.
% 2.41/0.99  
% 2.41/0.99  sup_num_of_clauses:                     36
% 2.41/0.99  sup_num_in_active:                      31
% 2.41/0.99  sup_num_in_passive:                     5
% 2.41/0.99  sup_num_of_loops:                       43
% 2.41/0.99  sup_fw_superposition:                   31
% 2.41/0.99  sup_bw_superposition:                   31
% 2.41/0.99  sup_immediate_simplified:               23
% 2.41/0.99  sup_given_eliminated:                   0
% 2.41/0.99  comparisons_done:                       0
% 2.41/0.99  comparisons_avoided:                    3
% 2.41/0.99  
% 2.41/0.99  ------ Simplifications
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  sim_fw_subset_subsumed:                 4
% 2.41/0.99  sim_bw_subset_subsumed:                 4
% 2.41/0.99  sim_fw_subsumed:                        2
% 2.41/0.99  sim_bw_subsumed:                        0
% 2.41/0.99  sim_fw_subsumption_res:                 2
% 2.41/0.99  sim_bw_subsumption_res:                 0
% 2.41/0.99  sim_tautology_del:                      0
% 2.41/0.99  sim_eq_tautology_del:                   10
% 2.41/0.99  sim_eq_res_simp:                        0
% 2.41/0.99  sim_fw_demodulated:                     7
% 2.41/0.99  sim_bw_demodulated:                     13
% 2.41/0.99  sim_light_normalised:                   8
% 2.41/0.99  sim_joinable_taut:                      0
% 2.41/0.99  sim_joinable_simp:                      0
% 2.41/0.99  sim_ac_normalised:                      0
% 2.41/0.99  sim_smt_subsumption:                    0
% 2.41/0.99  
%------------------------------------------------------------------------------
