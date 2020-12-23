%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:19 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  115 (1235 expanded)
%              Number of clauses        :   60 ( 325 expanded)
%              Number of leaves         :   17 ( 351 expanded)
%              Depth                    :   19
%              Number of atoms          :  162 (1931 expanded)
%              Number of equality atoms :  117 (1254 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k1_enumset1(X0,X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26])).

fof(f48,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) ),
    inference(definition_unfolding,[],[f42,f41,f41,f41])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f41,f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f44,f44])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f29,f50])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f41])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),k1_enumset1(sK0,sK0,sK1)) != sK2 ),
    inference(definition_unfolding,[],[f49,f41,f44,f44])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(X1,k1_enumset1(X0,X0,X2)) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_429,plain,
    ( k4_xboole_0(X0,k1_enumset1(X1,X1,X2)) = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_428,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_763,plain,
    ( k4_xboole_0(sK2,k1_enumset1(X0,X0,sK1)) = sK2
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_429,c_428])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_427,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_903,plain,
    ( k4_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_763,c_427])).

cnf(c_764,plain,
    ( k4_xboole_0(sK2,k1_enumset1(X0,X0,sK0)) = sK2
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_429,c_427])).

cnf(c_998,plain,
    ( k4_xboole_0(sK2,k1_enumset1(sK1,sK1,sK0)) = sK2 ),
    inference(superposition,[status(thm)],[c_764,c_428])).

cnf(c_12,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_435,plain,
    ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_8,c_14])).

cnf(c_437,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_12,c_14,c_435])).

cnf(c_2834,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2),X0),k4_xboole_0(k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2),X0),k4_xboole_0(sK2,X0))) = k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2),X0) ),
    inference(superposition,[status(thm)],[c_998,c_437])).

cnf(c_13,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1002,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK1,sK1,sK0),sK2)) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) ),
    inference(superposition,[status(thm)],[c_998,c_14])).

cnf(c_1761,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) ),
    inference(superposition,[status(thm)],[c_13,c_1002])).

cnf(c_942,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_903,c_14])).

cnf(c_1765,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(light_normalisation,[status(thm)],[c_1761,c_942])).

cnf(c_2847,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2),X0),k4_xboole_0(k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2),X0),k4_xboole_0(sK2,X0))) = k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_2834,c_1765])).

cnf(c_2833,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0),k4_xboole_0(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0),k4_xboole_0(sK2,X0))) = k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0) ),
    inference(superposition,[status(thm)],[c_903,c_437])).

cnf(c_3865,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0))) = k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0) ),
    inference(superposition,[status(thm)],[c_13,c_2833])).

cnf(c_2816,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0))) = k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0) ),
    inference(superposition,[status(thm)],[c_903,c_437])).

cnf(c_3893,plain,
    ( k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0) = k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_3865,c_2816])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_434,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1,c_0,c_11])).

cnf(c_896,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_434])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_893,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_14,c_7])).

cnf(c_1413,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_893])).

cnf(c_1820,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_896,c_1413])).

cnf(c_4557,plain,
    ( k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),k1_xboole_0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_3893,c_1820])).

cnf(c_4567,plain,
    ( k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(demodulation,[status(thm)],[c_4557,c_1820])).

cnf(c_1759,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK1,sK1,sK0))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) ),
    inference(superposition,[status(thm)],[c_13,c_1002])).

cnf(c_1770,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK1,sK1,sK0))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(light_normalisation,[status(thm)],[c_1759,c_1765])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_821,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_11,c_10])).

cnf(c_831,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_821,c_434])).

cnf(c_5993,plain,
    ( k5_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_14,c_831])).

cnf(c_7778,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) = k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) ),
    inference(superposition,[status(thm)],[c_1770,c_5993])).

cnf(c_7838,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1))) = k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) ),
    inference(light_normalisation,[status(thm)],[c_7778,c_4567])).

cnf(c_7839,plain,
    ( k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) = k1_enumset1(sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_7838,c_831])).

cnf(c_11431,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),k4_xboole_0(sK2,X0))) = k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_2847,c_2847,c_4567,c_7839])).

cnf(c_11445,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1)),sK2)) = k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_903,c_11431])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_432,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_431,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1782,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_432,c_431])).

cnf(c_11460,plain,
    ( k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_11445,c_1413,c_1782])).

cnf(c_1735,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_13,c_942])).

cnf(c_16,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),k1_enumset1(sK0,sK0,sK1)) != sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_436,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))),k1_enumset1(sK0,sK0,sK1)) != sK2 ),
    inference(demodulation,[status(thm)],[c_16,c_14])).

cnf(c_1949,plain,
    ( k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1)) != sK2 ),
    inference(demodulation,[status(thm)],[c_1735,c_436])).

cnf(c_4535,plain,
    ( k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) != sK2 ),
    inference(demodulation,[status(thm)],[c_3893,c_1949])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11460,c_4535])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:00:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.85/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.98  
% 3.85/0.98  ------  iProver source info
% 3.85/0.98  
% 3.85/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.98  git: non_committed_changes: false
% 3.85/0.98  git: last_make_outside_of_git: false
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options
% 3.85/0.98  
% 3.85/0.98  --out_options                           all
% 3.85/0.98  --tptp_safe_out                         true
% 3.85/0.98  --problem_path                          ""
% 3.85/0.98  --include_path                          ""
% 3.85/0.98  --clausifier                            res/vclausify_rel
% 3.85/0.98  --clausifier_options                    ""
% 3.85/0.98  --stdin                                 false
% 3.85/0.98  --stats_out                             all
% 3.85/0.98  
% 3.85/0.98  ------ General Options
% 3.85/0.98  
% 3.85/0.98  --fof                                   false
% 3.85/0.98  --time_out_real                         305.
% 3.85/0.98  --time_out_virtual                      -1.
% 3.85/0.98  --symbol_type_check                     false
% 3.85/0.98  --clausify_out                          false
% 3.85/0.98  --sig_cnt_out                           false
% 3.85/0.98  --trig_cnt_out                          false
% 3.85/0.98  --trig_cnt_out_tolerance                1.
% 3.85/0.98  --trig_cnt_out_sk_spl                   false
% 3.85/0.98  --abstr_cl_out                          false
% 3.85/0.98  
% 3.85/0.98  ------ Global Options
% 3.85/0.98  
% 3.85/0.98  --schedule                              default
% 3.85/0.98  --add_important_lit                     false
% 3.85/0.98  --prop_solver_per_cl                    1000
% 3.85/0.98  --min_unsat_core                        false
% 3.85/0.98  --soft_assumptions                      false
% 3.85/0.98  --soft_lemma_size                       3
% 3.85/0.98  --prop_impl_unit_size                   0
% 3.85/0.98  --prop_impl_unit                        []
% 3.85/0.98  --share_sel_clauses                     true
% 3.85/0.98  --reset_solvers                         false
% 3.85/0.98  --bc_imp_inh                            [conj_cone]
% 3.85/0.98  --conj_cone_tolerance                   3.
% 3.85/0.98  --extra_neg_conj                        none
% 3.85/0.98  --large_theory_mode                     true
% 3.85/0.98  --prolific_symb_bound                   200
% 3.85/0.98  --lt_threshold                          2000
% 3.85/0.98  --clause_weak_htbl                      true
% 3.85/0.98  --gc_record_bc_elim                     false
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing Options
% 3.85/0.98  
% 3.85/0.98  --preprocessing_flag                    true
% 3.85/0.98  --time_out_prep_mult                    0.1
% 3.85/0.98  --splitting_mode                        input
% 3.85/0.98  --splitting_grd                         true
% 3.85/0.98  --splitting_cvd                         false
% 3.85/0.98  --splitting_cvd_svl                     false
% 3.85/0.98  --splitting_nvd                         32
% 3.85/0.98  --sub_typing                            true
% 3.85/0.98  --prep_gs_sim                           true
% 3.85/0.98  --prep_unflatten                        true
% 3.85/0.98  --prep_res_sim                          true
% 3.85/0.98  --prep_upred                            true
% 3.85/0.98  --prep_sem_filter                       exhaustive
% 3.85/0.98  --prep_sem_filter_out                   false
% 3.85/0.98  --pred_elim                             true
% 3.85/0.98  --res_sim_input                         true
% 3.85/0.98  --eq_ax_congr_red                       true
% 3.85/0.98  --pure_diseq_elim                       true
% 3.85/0.98  --brand_transform                       false
% 3.85/0.98  --non_eq_to_eq                          false
% 3.85/0.98  --prep_def_merge                        true
% 3.85/0.98  --prep_def_merge_prop_impl              false
% 3.85/0.98  --prep_def_merge_mbd                    true
% 3.85/0.98  --prep_def_merge_tr_red                 false
% 3.85/0.98  --prep_def_merge_tr_cl                  false
% 3.85/0.98  --smt_preprocessing                     true
% 3.85/0.98  --smt_ac_axioms                         fast
% 3.85/0.98  --preprocessed_out                      false
% 3.85/0.98  --preprocessed_stats                    false
% 3.85/0.98  
% 3.85/0.98  ------ Abstraction refinement Options
% 3.85/0.98  
% 3.85/0.98  --abstr_ref                             []
% 3.85/0.98  --abstr_ref_prep                        false
% 3.85/0.98  --abstr_ref_until_sat                   false
% 3.85/0.98  --abstr_ref_sig_restrict                funpre
% 3.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.98  --abstr_ref_under                       []
% 3.85/0.98  
% 3.85/0.98  ------ SAT Options
% 3.85/0.98  
% 3.85/0.98  --sat_mode                              false
% 3.85/0.98  --sat_fm_restart_options                ""
% 3.85/0.98  --sat_gr_def                            false
% 3.85/0.98  --sat_epr_types                         true
% 3.85/0.98  --sat_non_cyclic_types                  false
% 3.85/0.98  --sat_finite_models                     false
% 3.85/0.98  --sat_fm_lemmas                         false
% 3.85/0.98  --sat_fm_prep                           false
% 3.85/0.98  --sat_fm_uc_incr                        true
% 3.85/0.98  --sat_out_model                         small
% 3.85/0.98  --sat_out_clauses                       false
% 3.85/0.98  
% 3.85/0.98  ------ QBF Options
% 3.85/0.98  
% 3.85/0.98  --qbf_mode                              false
% 3.85/0.98  --qbf_elim_univ                         false
% 3.85/0.98  --qbf_dom_inst                          none
% 3.85/0.98  --qbf_dom_pre_inst                      false
% 3.85/0.98  --qbf_sk_in                             false
% 3.85/0.98  --qbf_pred_elim                         true
% 3.85/0.98  --qbf_split                             512
% 3.85/0.98  
% 3.85/0.98  ------ BMC1 Options
% 3.85/0.98  
% 3.85/0.98  --bmc1_incremental                      false
% 3.85/0.98  --bmc1_axioms                           reachable_all
% 3.85/0.98  --bmc1_min_bound                        0
% 3.85/0.98  --bmc1_max_bound                        -1
% 3.85/0.98  --bmc1_max_bound_default                -1
% 3.85/0.98  --bmc1_symbol_reachability              true
% 3.85/0.98  --bmc1_property_lemmas                  false
% 3.85/0.98  --bmc1_k_induction                      false
% 3.85/0.98  --bmc1_non_equiv_states                 false
% 3.85/0.98  --bmc1_deadlock                         false
% 3.85/0.98  --bmc1_ucm                              false
% 3.85/0.98  --bmc1_add_unsat_core                   none
% 3.85/0.98  --bmc1_unsat_core_children              false
% 3.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.98  --bmc1_out_stat                         full
% 3.85/0.98  --bmc1_ground_init                      false
% 3.85/0.98  --bmc1_pre_inst_next_state              false
% 3.85/0.98  --bmc1_pre_inst_state                   false
% 3.85/0.98  --bmc1_pre_inst_reach_state             false
% 3.85/0.98  --bmc1_out_unsat_core                   false
% 3.85/0.98  --bmc1_aig_witness_out                  false
% 3.85/0.98  --bmc1_verbose                          false
% 3.85/0.98  --bmc1_dump_clauses_tptp                false
% 3.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.98  --bmc1_dump_file                        -
% 3.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.98  --bmc1_ucm_extend_mode                  1
% 3.85/0.98  --bmc1_ucm_init_mode                    2
% 3.85/0.98  --bmc1_ucm_cone_mode                    none
% 3.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.98  --bmc1_ucm_relax_model                  4
% 3.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.98  --bmc1_ucm_layered_model                none
% 3.85/0.98  --bmc1_ucm_max_lemma_size               10
% 3.85/0.98  
% 3.85/0.98  ------ AIG Options
% 3.85/0.98  
% 3.85/0.98  --aig_mode                              false
% 3.85/0.98  
% 3.85/0.98  ------ Instantiation Options
% 3.85/0.98  
% 3.85/0.98  --instantiation_flag                    true
% 3.85/0.98  --inst_sos_flag                         true
% 3.85/0.98  --inst_sos_phase                        true
% 3.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel_side                     num_symb
% 3.85/0.98  --inst_solver_per_active                1400
% 3.85/0.98  --inst_solver_calls_frac                1.
% 3.85/0.98  --inst_passive_queue_type               priority_queues
% 3.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.98  --inst_passive_queues_freq              [25;2]
% 3.85/0.98  --inst_dismatching                      true
% 3.85/0.98  --inst_eager_unprocessed_to_passive     true
% 3.85/0.98  --inst_prop_sim_given                   true
% 3.85/0.98  --inst_prop_sim_new                     false
% 3.85/0.98  --inst_subs_new                         false
% 3.85/0.98  --inst_eq_res_simp                      false
% 3.85/0.98  --inst_subs_given                       false
% 3.85/0.98  --inst_orphan_elimination               true
% 3.85/0.98  --inst_learning_loop_flag               true
% 3.85/0.98  --inst_learning_start                   3000
% 3.85/0.98  --inst_learning_factor                  2
% 3.85/0.98  --inst_start_prop_sim_after_learn       3
% 3.85/0.98  --inst_sel_renew                        solver
% 3.85/0.98  --inst_lit_activity_flag                true
% 3.85/0.98  --inst_restr_to_given                   false
% 3.85/0.98  --inst_activity_threshold               500
% 3.85/0.98  --inst_out_proof                        true
% 3.85/0.98  
% 3.85/0.98  ------ Resolution Options
% 3.85/0.98  
% 3.85/0.98  --resolution_flag                       true
% 3.85/0.98  --res_lit_sel                           adaptive
% 3.85/0.98  --res_lit_sel_side                      none
% 3.85/0.98  --res_ordering                          kbo
% 3.85/0.98  --res_to_prop_solver                    active
% 3.85/0.98  --res_prop_simpl_new                    false
% 3.85/0.98  --res_prop_simpl_given                  true
% 3.85/0.98  --res_passive_queue_type                priority_queues
% 3.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.98  --res_passive_queues_freq               [15;5]
% 3.85/0.98  --res_forward_subs                      full
% 3.85/0.98  --res_backward_subs                     full
% 3.85/0.98  --res_forward_subs_resolution           true
% 3.85/0.98  --res_backward_subs_resolution          true
% 3.85/0.98  --res_orphan_elimination                true
% 3.85/0.98  --res_time_limit                        2.
% 3.85/0.98  --res_out_proof                         true
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Options
% 3.85/0.98  
% 3.85/0.98  --superposition_flag                    true
% 3.85/0.98  --sup_passive_queue_type                priority_queues
% 3.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.85/0.98  --demod_completeness_check              fast
% 3.85/0.98  --demod_use_ground                      true
% 3.85/0.98  --sup_to_prop_solver                    passive
% 3.85/0.98  --sup_prop_simpl_new                    true
% 3.85/0.98  --sup_prop_simpl_given                  true
% 3.85/0.98  --sup_fun_splitting                     true
% 3.85/0.98  --sup_smt_interval                      50000
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Simplification Setup
% 3.85/0.98  
% 3.85/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_immed_triv                        [TrivRules]
% 3.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_bw_main                     []
% 3.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_input_bw                          []
% 3.85/0.98  
% 3.85/0.98  ------ Combination Options
% 3.85/0.98  
% 3.85/0.98  --comb_res_mult                         3
% 3.85/0.98  --comb_sup_mult                         2
% 3.85/0.98  --comb_inst_mult                        10
% 3.85/0.98  
% 3.85/0.98  ------ Debug Options
% 3.85/0.98  
% 3.85/0.98  --dbg_backtrace                         false
% 3.85/0.98  --dbg_dump_prop_clauses                 false
% 3.85/0.98  --dbg_dump_prop_clauses_file            -
% 3.85/0.98  --dbg_out_stat                          false
% 3.85/0.98  ------ Parsing...
% 3.85/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  ------ Proving...
% 3.85/0.98  ------ Problem Properties 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  clauses                                 18
% 3.85/0.98  conjectures                             3
% 3.85/0.98  EPR                                     4
% 3.85/0.98  Horn                                    17
% 3.85/0.98  unary                                   14
% 3.85/0.98  binary                                  2
% 3.85/0.98  lits                                    24
% 3.85/0.98  lits eq                                 15
% 3.85/0.98  fd_pure                                 0
% 3.85/0.98  fd_pseudo                               0
% 3.85/0.98  fd_cond                                 0
% 3.85/0.98  fd_pseudo_cond                          1
% 3.85/0.98  AC symbols                              0
% 3.85/0.98  
% 3.85/0.98  ------ Schedule dynamic 5 is on 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  Current options:
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options
% 3.85/0.98  
% 3.85/0.98  --out_options                           all
% 3.85/0.98  --tptp_safe_out                         true
% 3.85/0.98  --problem_path                          ""
% 3.85/0.98  --include_path                          ""
% 3.85/0.98  --clausifier                            res/vclausify_rel
% 3.85/0.98  --clausifier_options                    ""
% 3.85/0.98  --stdin                                 false
% 3.85/0.98  --stats_out                             all
% 3.85/0.98  
% 3.85/0.98  ------ General Options
% 3.85/0.98  
% 3.85/0.98  --fof                                   false
% 3.85/0.98  --time_out_real                         305.
% 3.85/0.98  --time_out_virtual                      -1.
% 3.85/0.98  --symbol_type_check                     false
% 3.85/0.98  --clausify_out                          false
% 3.85/0.98  --sig_cnt_out                           false
% 3.85/0.98  --trig_cnt_out                          false
% 3.85/0.98  --trig_cnt_out_tolerance                1.
% 3.85/0.98  --trig_cnt_out_sk_spl                   false
% 3.85/0.98  --abstr_cl_out                          false
% 3.85/0.98  
% 3.85/0.98  ------ Global Options
% 3.85/0.98  
% 3.85/0.98  --schedule                              default
% 3.85/0.98  --add_important_lit                     false
% 3.85/0.98  --prop_solver_per_cl                    1000
% 3.85/0.98  --min_unsat_core                        false
% 3.85/0.98  --soft_assumptions                      false
% 3.85/0.98  --soft_lemma_size                       3
% 3.85/0.98  --prop_impl_unit_size                   0
% 3.85/0.98  --prop_impl_unit                        []
% 3.85/0.98  --share_sel_clauses                     true
% 3.85/0.98  --reset_solvers                         false
% 3.85/0.98  --bc_imp_inh                            [conj_cone]
% 3.85/0.98  --conj_cone_tolerance                   3.
% 3.85/0.98  --extra_neg_conj                        none
% 3.85/0.98  --large_theory_mode                     true
% 3.85/0.98  --prolific_symb_bound                   200
% 3.85/0.98  --lt_threshold                          2000
% 3.85/0.98  --clause_weak_htbl                      true
% 3.85/0.98  --gc_record_bc_elim                     false
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing Options
% 3.85/0.98  
% 3.85/0.98  --preprocessing_flag                    true
% 3.85/0.98  --time_out_prep_mult                    0.1
% 3.85/0.98  --splitting_mode                        input
% 3.85/0.98  --splitting_grd                         true
% 3.85/0.98  --splitting_cvd                         false
% 3.85/0.98  --splitting_cvd_svl                     false
% 3.85/0.98  --splitting_nvd                         32
% 3.85/0.98  --sub_typing                            true
% 3.85/0.98  --prep_gs_sim                           true
% 3.85/0.98  --prep_unflatten                        true
% 3.85/0.98  --prep_res_sim                          true
% 3.85/0.98  --prep_upred                            true
% 3.85/0.98  --prep_sem_filter                       exhaustive
% 3.85/0.98  --prep_sem_filter_out                   false
% 3.85/0.98  --pred_elim                             true
% 3.85/0.98  --res_sim_input                         true
% 3.85/0.98  --eq_ax_congr_red                       true
% 3.85/0.98  --pure_diseq_elim                       true
% 3.85/0.98  --brand_transform                       false
% 3.85/0.98  --non_eq_to_eq                          false
% 3.85/0.98  --prep_def_merge                        true
% 3.85/0.98  --prep_def_merge_prop_impl              false
% 3.85/0.98  --prep_def_merge_mbd                    true
% 3.85/0.98  --prep_def_merge_tr_red                 false
% 3.85/0.98  --prep_def_merge_tr_cl                  false
% 3.85/0.98  --smt_preprocessing                     true
% 3.85/0.98  --smt_ac_axioms                         fast
% 3.85/0.98  --preprocessed_out                      false
% 3.85/0.98  --preprocessed_stats                    false
% 3.85/0.98  
% 3.85/0.98  ------ Abstraction refinement Options
% 3.85/0.98  
% 3.85/0.98  --abstr_ref                             []
% 3.85/0.98  --abstr_ref_prep                        false
% 3.85/0.98  --abstr_ref_until_sat                   false
% 3.85/0.98  --abstr_ref_sig_restrict                funpre
% 3.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.98  --abstr_ref_under                       []
% 3.85/0.98  
% 3.85/0.98  ------ SAT Options
% 3.85/0.98  
% 3.85/0.98  --sat_mode                              false
% 3.85/0.98  --sat_fm_restart_options                ""
% 3.85/0.98  --sat_gr_def                            false
% 3.85/0.98  --sat_epr_types                         true
% 3.85/0.98  --sat_non_cyclic_types                  false
% 3.85/0.98  --sat_finite_models                     false
% 3.85/0.98  --sat_fm_lemmas                         false
% 3.85/0.98  --sat_fm_prep                           false
% 3.85/0.98  --sat_fm_uc_incr                        true
% 3.85/0.98  --sat_out_model                         small
% 3.85/0.98  --sat_out_clauses                       false
% 3.85/0.98  
% 3.85/0.98  ------ QBF Options
% 3.85/0.98  
% 3.85/0.98  --qbf_mode                              false
% 3.85/0.98  --qbf_elim_univ                         false
% 3.85/0.98  --qbf_dom_inst                          none
% 3.85/0.98  --qbf_dom_pre_inst                      false
% 3.85/0.98  --qbf_sk_in                             false
% 3.85/0.98  --qbf_pred_elim                         true
% 3.85/0.98  --qbf_split                             512
% 3.85/0.98  
% 3.85/0.98  ------ BMC1 Options
% 3.85/0.98  
% 3.85/0.98  --bmc1_incremental                      false
% 3.85/0.98  --bmc1_axioms                           reachable_all
% 3.85/0.98  --bmc1_min_bound                        0
% 3.85/0.98  --bmc1_max_bound                        -1
% 3.85/0.98  --bmc1_max_bound_default                -1
% 3.85/0.98  --bmc1_symbol_reachability              true
% 3.85/0.98  --bmc1_property_lemmas                  false
% 3.85/0.98  --bmc1_k_induction                      false
% 3.85/0.98  --bmc1_non_equiv_states                 false
% 3.85/0.98  --bmc1_deadlock                         false
% 3.85/0.98  --bmc1_ucm                              false
% 3.85/0.98  --bmc1_add_unsat_core                   none
% 3.85/0.98  --bmc1_unsat_core_children              false
% 3.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.98  --bmc1_out_stat                         full
% 3.85/0.98  --bmc1_ground_init                      false
% 3.85/0.98  --bmc1_pre_inst_next_state              false
% 3.85/0.98  --bmc1_pre_inst_state                   false
% 3.85/0.98  --bmc1_pre_inst_reach_state             false
% 3.85/0.98  --bmc1_out_unsat_core                   false
% 3.85/0.98  --bmc1_aig_witness_out                  false
% 3.85/0.98  --bmc1_verbose                          false
% 3.85/0.98  --bmc1_dump_clauses_tptp                false
% 3.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.98  --bmc1_dump_file                        -
% 3.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.98  --bmc1_ucm_extend_mode                  1
% 3.85/0.98  --bmc1_ucm_init_mode                    2
% 3.85/0.98  --bmc1_ucm_cone_mode                    none
% 3.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.98  --bmc1_ucm_relax_model                  4
% 3.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.98  --bmc1_ucm_layered_model                none
% 3.85/0.98  --bmc1_ucm_max_lemma_size               10
% 3.85/0.98  
% 3.85/0.98  ------ AIG Options
% 3.85/0.98  
% 3.85/0.98  --aig_mode                              false
% 3.85/0.98  
% 3.85/0.98  ------ Instantiation Options
% 3.85/0.98  
% 3.85/0.98  --instantiation_flag                    true
% 3.85/0.98  --inst_sos_flag                         true
% 3.85/0.98  --inst_sos_phase                        true
% 3.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel_side                     none
% 3.85/0.98  --inst_solver_per_active                1400
% 3.85/0.98  --inst_solver_calls_frac                1.
% 3.85/0.98  --inst_passive_queue_type               priority_queues
% 3.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.98  --inst_passive_queues_freq              [25;2]
% 3.85/0.98  --inst_dismatching                      true
% 3.85/0.98  --inst_eager_unprocessed_to_passive     true
% 3.85/0.98  --inst_prop_sim_given                   true
% 3.85/0.98  --inst_prop_sim_new                     false
% 3.85/0.98  --inst_subs_new                         false
% 3.85/0.98  --inst_eq_res_simp                      false
% 3.85/0.98  --inst_subs_given                       false
% 3.85/0.98  --inst_orphan_elimination               true
% 3.85/0.98  --inst_learning_loop_flag               true
% 3.85/0.98  --inst_learning_start                   3000
% 3.85/0.98  --inst_learning_factor                  2
% 3.85/0.98  --inst_start_prop_sim_after_learn       3
% 3.85/0.98  --inst_sel_renew                        solver
% 3.85/0.98  --inst_lit_activity_flag                true
% 3.85/0.98  --inst_restr_to_given                   false
% 3.85/0.98  --inst_activity_threshold               500
% 3.85/0.98  --inst_out_proof                        true
% 3.85/0.98  
% 3.85/0.98  ------ Resolution Options
% 3.85/0.98  
% 3.85/0.98  --resolution_flag                       false
% 3.85/0.98  --res_lit_sel                           adaptive
% 3.85/0.98  --res_lit_sel_side                      none
% 3.85/0.98  --res_ordering                          kbo
% 3.85/0.98  --res_to_prop_solver                    active
% 3.85/0.98  --res_prop_simpl_new                    false
% 3.85/0.98  --res_prop_simpl_given                  true
% 3.85/0.98  --res_passive_queue_type                priority_queues
% 3.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.98  --res_passive_queues_freq               [15;5]
% 3.85/0.98  --res_forward_subs                      full
% 3.85/0.98  --res_backward_subs                     full
% 3.85/0.98  --res_forward_subs_resolution           true
% 3.85/0.98  --res_backward_subs_resolution          true
% 3.85/0.98  --res_orphan_elimination                true
% 3.85/0.98  --res_time_limit                        2.
% 3.85/0.98  --res_out_proof                         true
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Options
% 3.85/0.98  
% 3.85/0.98  --superposition_flag                    true
% 3.85/0.98  --sup_passive_queue_type                priority_queues
% 3.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.85/0.98  --demod_completeness_check              fast
% 3.85/0.98  --demod_use_ground                      true
% 3.85/0.98  --sup_to_prop_solver                    passive
% 3.85/0.98  --sup_prop_simpl_new                    true
% 3.85/0.98  --sup_prop_simpl_given                  true
% 3.85/0.98  --sup_fun_splitting                     true
% 3.85/0.98  --sup_smt_interval                      50000
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Simplification Setup
% 3.85/0.98  
% 3.85/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_immed_triv                        [TrivRules]
% 3.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_bw_main                     []
% 3.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_input_bw                          []
% 3.85/0.98  
% 3.85/0.98  ------ Combination Options
% 3.85/0.98  
% 3.85/0.98  --comb_res_mult                         3
% 3.85/0.98  --comb_sup_mult                         2
% 3.85/0.98  --comb_inst_mult                        10
% 3.85/0.98  
% 3.85/0.98  ------ Debug Options
% 3.85/0.98  
% 3.85/0.98  --dbg_backtrace                         false
% 3.85/0.98  --dbg_dump_prop_clauses                 false
% 3.85/0.98  --dbg_dump_prop_clauses_file            -
% 3.85/0.98  --dbg_out_stat                          false
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS status Theorem for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  fof(f16,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f21,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 3.85/0.98    inference(ennf_transformation,[],[f16])).
% 3.85/0.98  
% 3.85/0.98  fof(f46,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f21])).
% 3.85/0.98  
% 3.85/0.98  fof(f14,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f44,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f14])).
% 3.85/0.98  
% 3.85/0.98  fof(f58,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k1_enumset1(X0,X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f46,f44])).
% 3.85/0.98  
% 3.85/0.98  fof(f17,conjecture,(
% 3.85/0.98    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f18,negated_conjecture,(
% 3.85/0.98    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 3.85/0.98    inference(negated_conjecture,[],[f17])).
% 3.85/0.98  
% 3.85/0.98  fof(f22,plain,(
% 3.85/0.98    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 3.85/0.98    inference(ennf_transformation,[],[f18])).
% 3.85/0.98  
% 3.85/0.98  fof(f26,plain,(
% 3.85/0.98    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f27,plain,(
% 3.85/0.98    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26])).
% 3.85/0.98  
% 3.85/0.98  fof(f48,plain,(
% 3.85/0.98    ~r2_hidden(sK1,sK2)),
% 3.85/0.98    inference(cnf_transformation,[],[f27])).
% 3.85/0.98  
% 3.85/0.98  fof(f47,plain,(
% 3.85/0.98    ~r2_hidden(sK0,sK2)),
% 3.85/0.98    inference(cnf_transformation,[],[f27])).
% 3.85/0.98  
% 3.85/0.98  fof(f12,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f42,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f12])).
% 3.85/0.98  
% 3.85/0.98  fof(f11,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f41,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f11])).
% 3.85/0.98  
% 3.85/0.98  fof(f55,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f42,f41,f41,f41])).
% 3.85/0.98  
% 3.85/0.98  fof(f15,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f45,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f57,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f45,f41,f44])).
% 3.85/0.98  
% 3.85/0.98  fof(f6,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f36,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f6])).
% 3.85/0.98  
% 3.85/0.98  fof(f54,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f36,f41])).
% 3.85/0.98  
% 3.85/0.98  fof(f13,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f43,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f13])).
% 3.85/0.98  
% 3.85/0.98  fof(f56,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f43,f44,f44])).
% 3.85/0.98  
% 3.85/0.98  fof(f2,axiom,(
% 3.85/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f20,plain,(
% 3.85/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.85/0.98    inference(rectify,[],[f2])).
% 3.85/0.98  
% 3.85/0.98  fof(f29,plain,(
% 3.85/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.85/0.98    inference(cnf_transformation,[],[f20])).
% 3.85/0.98  
% 3.85/0.98  fof(f10,axiom,(
% 3.85/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f40,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f10])).
% 3.85/0.98  
% 3.85/0.98  fof(f50,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f40,f41])).
% 3.85/0.98  
% 3.85/0.98  fof(f52,plain,(
% 3.85/0.98    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))) = X0) )),
% 3.85/0.98    inference(definition_unfolding,[],[f29,f50])).
% 3.85/0.98  
% 3.85/0.98  fof(f1,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f19,plain,(
% 3.85/0.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.85/0.98    inference(rectify,[],[f1])).
% 3.85/0.98  
% 3.85/0.98  fof(f28,plain,(
% 3.85/0.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.85/0.98    inference(cnf_transformation,[],[f19])).
% 3.85/0.98  
% 3.85/0.98  fof(f51,plain,(
% 3.85/0.98    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.85/0.98    inference(definition_unfolding,[],[f28,f41])).
% 3.85/0.98  
% 3.85/0.98  fof(f9,axiom,(
% 3.85/0.98    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f39,plain,(
% 3.85/0.98    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f9])).
% 3.85/0.98  
% 3.85/0.98  fof(f5,axiom,(
% 3.85/0.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f35,plain,(
% 3.85/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.85/0.98    inference(cnf_transformation,[],[f5])).
% 3.85/0.98  
% 3.85/0.98  fof(f53,plain,(
% 3.85/0.98    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 3.85/0.98    inference(definition_unfolding,[],[f35,f41])).
% 3.85/0.98  
% 3.85/0.98  fof(f8,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f38,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f8])).
% 3.85/0.98  
% 3.85/0.98  fof(f3,axiom,(
% 3.85/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f23,plain,(
% 3.85/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.85/0.98    inference(nnf_transformation,[],[f3])).
% 3.85/0.98  
% 3.85/0.98  fof(f24,plain,(
% 3.85/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.85/0.98    inference(flattening,[],[f23])).
% 3.85/0.98  
% 3.85/0.98  fof(f30,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.85/0.98    inference(cnf_transformation,[],[f24])).
% 3.85/0.98  
% 3.85/0.98  fof(f61,plain,(
% 3.85/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.85/0.98    inference(equality_resolution,[],[f30])).
% 3.85/0.98  
% 3.85/0.98  fof(f4,axiom,(
% 3.85/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f25,plain,(
% 3.85/0.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.85/0.98    inference(nnf_transformation,[],[f4])).
% 3.85/0.98  
% 3.85/0.98  fof(f34,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f25])).
% 3.85/0.98  
% 3.85/0.98  fof(f49,plain,(
% 3.85/0.98    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2),
% 3.85/0.98    inference(cnf_transformation,[],[f27])).
% 3.85/0.98  
% 3.85/0.98  fof(f59,plain,(
% 3.85/0.98    k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),k1_enumset1(sK0,sK0,sK1)) != sK2),
% 3.85/0.98    inference(definition_unfolding,[],[f49,f41,f44,f44])).
% 3.85/0.98  
% 3.85/0.98  cnf(c_15,plain,
% 3.85/0.98      ( r2_hidden(X0,X1)
% 3.85/0.98      | r2_hidden(X2,X1)
% 3.85/0.98      | k4_xboole_0(X1,k1_enumset1(X0,X0,X2)) = X1 ),
% 3.85/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_429,plain,
% 3.85/0.98      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X2)) = X0
% 3.85/0.98      | r2_hidden(X1,X0) = iProver_top
% 3.85/0.98      | r2_hidden(X2,X0) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_17,negated_conjecture,
% 3.85/0.98      ( ~ r2_hidden(sK1,sK2) ),
% 3.85/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_428,plain,
% 3.85/0.98      ( r2_hidden(sK1,sK2) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_763,plain,
% 3.85/0.98      ( k4_xboole_0(sK2,k1_enumset1(X0,X0,sK1)) = sK2
% 3.85/0.98      | r2_hidden(X0,sK2) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_429,c_428]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_18,negated_conjecture,
% 3.85/0.98      ( ~ r2_hidden(sK0,sK2) ),
% 3.85/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_427,plain,
% 3.85/0.98      ( r2_hidden(sK0,sK2) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_903,plain,
% 3.85/0.98      ( k4_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) = sK2 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_763,c_427]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_764,plain,
% 3.85/0.98      ( k4_xboole_0(sK2,k1_enumset1(X0,X0,sK0)) = sK2
% 3.85/0.98      | r2_hidden(X0,sK2) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_429,c_427]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_998,plain,
% 3.85/0.98      ( k4_xboole_0(sK2,k1_enumset1(sK1,sK1,sK0)) = sK2 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_764,c_428]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_12,plain,
% 3.85/0.98      ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 3.85/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_14,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_8,plain,
% 3.85/0.98      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.85/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_435,plain,
% 3.85/0.98      ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_8,c_14]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_437,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_12,c_14,c_435]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2834,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2),X0),k4_xboole_0(k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2),X0),k4_xboole_0(sK2,X0))) = k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2),X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_998,c_437]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_13,plain,
% 3.85/0.98      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1002,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK1,sK1,sK0),sK2)) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_998,c_14]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1761,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_13,c_1002]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_942,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_903,c_14]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1765,plain,
% 3.85/0.98      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_1761,c_942]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2847,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2),X0),k4_xboole_0(k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2),X0),k4_xboole_0(sK2,X0))) = k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0) ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_2834,c_1765]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2833,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0),k4_xboole_0(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0),k4_xboole_0(sK2,X0))) = k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_903,c_437]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3865,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0))) = k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_13,c_2833]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2816,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0))) = k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_903,c_437]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3893,plain,
% 3.85/0.98      ( k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0) = k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0) ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_3865,c_2816]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1,plain,
% 3.85/0.98      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_0,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_11,plain,
% 3.85/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_434,plain,
% 3.85/0.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_1,c_0,c_11]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_896,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_14,c_434]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_893,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_14,c_7]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1413,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_13,c_893]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1820,plain,
% 3.85/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_896,c_1413]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4557,plain,
% 3.85/0.98      ( k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),k1_xboole_0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_3893,c_1820]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4567,plain,
% 3.85/0.98      ( k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_4557,c_1820]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1759,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK1,sK1,sK0))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_13,c_1002]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1770,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK1,sK1,sK0))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_1759,c_1765]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_10,plain,
% 3.85/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_821,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_11,c_10]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_831,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_821,c_434]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5993,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(X1,X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_14,c_831]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7778,plain,
% 3.85/0.98      ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) = k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1770,c_5993]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7838,plain,
% 3.85/0.98      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1))) = k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_7778,c_4567]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7839,plain,
% 3.85/0.98      ( k4_xboole_0(k1_enumset1(sK1,sK1,sK0),sK2) = k1_enumset1(sK0,sK0,sK1) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_7838,c_831]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_11431,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),k4_xboole_0(sK2,X0))) = k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0) ),
% 3.85/0.98      inference(light_normalisation,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_2847,c_2847,c_4567,c_7839]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_11445,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1)),sK2)) = k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_903,c_11431]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4,plain,
% 3.85/0.98      ( r1_tarski(X0,X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_432,plain,
% 3.85/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_431,plain,
% 3.85/0.98      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.85/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1782,plain,
% 3.85/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_432,c_431]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_11460,plain,
% 3.85/0.98      ( k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) = sK2 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_11445,c_1413,c_1782]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1735,plain,
% 3.85/0.98      ( k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_13,c_942]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_16,negated_conjecture,
% 3.85/0.98      ( k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),k1_enumset1(sK0,sK0,sK1)) != sK2 ),
% 3.85/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_436,plain,
% 3.85/0.98      ( k4_xboole_0(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))),k1_enumset1(sK0,sK0,sK1)) != sK2 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_16,c_14]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1949,plain,
% 3.85/0.98      ( k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1)) != sK2 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_1735,c_436]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4535,plain,
% 3.85/0.98      ( k4_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) != sK2 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_3893,c_1949]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(contradiction,plain,
% 3.85/0.98      ( $false ),
% 3.85/0.98      inference(minisat,[status(thm)],[c_11460,c_4535]) ).
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  ------                               Statistics
% 3.85/0.98  
% 3.85/0.98  ------ General
% 3.85/0.98  
% 3.85/0.98  abstr_ref_over_cycles:                  0
% 3.85/0.98  abstr_ref_under_cycles:                 0
% 3.85/0.98  gc_basic_clause_elim:                   0
% 3.85/0.98  forced_gc_time:                         0
% 3.85/0.98  parsing_time:                           0.009
% 3.85/0.98  unif_index_cands_time:                  0.
% 3.85/0.98  unif_index_add_time:                    0.
% 3.85/0.98  orderings_time:                         0.
% 3.85/0.98  out_proof_time:                         0.008
% 3.85/0.98  total_time:                             0.441
% 3.85/0.98  num_of_symbols:                         41
% 3.85/0.98  num_of_terms:                           19234
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing
% 3.85/0.98  
% 3.85/0.98  num_of_splits:                          0
% 3.85/0.98  num_of_split_atoms:                     0
% 3.85/0.98  num_of_reused_defs:                     0
% 3.85/0.98  num_eq_ax_congr_red:                    6
% 3.85/0.98  num_of_sem_filtered_clauses:            1
% 3.85/0.98  num_of_subtypes:                        0
% 3.85/0.98  monotx_restored_types:                  0
% 3.85/0.98  sat_num_of_epr_types:                   0
% 3.85/0.98  sat_num_of_non_cyclic_types:            0
% 3.85/0.98  sat_guarded_non_collapsed_types:        0
% 3.85/0.98  num_pure_diseq_elim:                    0
% 3.85/0.98  simp_replaced_by:                       0
% 3.85/0.98  res_preprocessed:                       87
% 3.85/0.98  prep_upred:                             0
% 3.85/0.98  prep_unflattend:                        0
% 3.85/0.98  smt_new_axioms:                         0
% 3.85/0.98  pred_elim_cands:                        2
% 3.85/0.98  pred_elim:                              0
% 3.85/0.98  pred_elim_cl:                           0
% 3.85/0.98  pred_elim_cycles:                       2
% 3.85/0.98  merged_defs:                            8
% 3.85/0.98  merged_defs_ncl:                        0
% 3.85/0.98  bin_hyper_res:                          8
% 3.85/0.98  prep_cycles:                            4
% 3.85/0.98  pred_elim_time:                         0.
% 3.85/0.98  splitting_time:                         0.
% 3.85/0.98  sem_filter_time:                        0.
% 3.85/0.98  monotx_time:                            0.
% 3.85/0.98  subtype_inf_time:                       0.
% 3.85/0.98  
% 3.85/0.98  ------ Problem properties
% 3.85/0.98  
% 3.85/0.98  clauses:                                18
% 3.85/0.98  conjectures:                            3
% 3.85/0.98  epr:                                    4
% 3.85/0.98  horn:                                   17
% 3.85/0.98  ground:                                 3
% 3.85/0.98  unary:                                  14
% 3.85/0.98  binary:                                 2
% 3.85/0.98  lits:                                   24
% 3.85/0.98  lits_eq:                                15
% 3.85/0.98  fd_pure:                                0
% 3.85/0.98  fd_pseudo:                              0
% 3.85/0.98  fd_cond:                                0
% 3.85/0.98  fd_pseudo_cond:                         1
% 3.85/0.98  ac_symbols:                             1
% 3.85/0.98  
% 3.85/0.98  ------ Propositional Solver
% 3.85/0.98  
% 3.85/0.98  prop_solver_calls:                      33
% 3.85/0.98  prop_fast_solver_calls:                 440
% 3.85/0.98  smt_solver_calls:                       0
% 3.85/0.98  smt_fast_solver_calls:                  0
% 3.85/0.98  prop_num_of_clauses:                    4707
% 3.85/0.98  prop_preprocess_simplified:             7499
% 3.85/0.98  prop_fo_subsumed:                       0
% 3.85/0.98  prop_solver_time:                       0.
% 3.85/0.98  smt_solver_time:                        0.
% 3.85/0.98  smt_fast_solver_time:                   0.
% 3.85/0.98  prop_fast_solver_time:                  0.
% 3.85/0.98  prop_unsat_core_time:                   0.
% 3.85/0.98  
% 3.85/0.98  ------ QBF
% 3.85/0.98  
% 3.85/0.98  qbf_q_res:                              0
% 3.85/0.98  qbf_num_tautologies:                    0
% 3.85/0.98  qbf_prep_cycles:                        0
% 3.85/0.98  
% 3.85/0.98  ------ BMC1
% 3.85/0.98  
% 3.85/0.98  bmc1_current_bound:                     -1
% 3.85/0.98  bmc1_last_solved_bound:                 -1
% 3.85/0.98  bmc1_unsat_core_size:                   -1
% 3.85/0.98  bmc1_unsat_core_parents_size:           -1
% 3.85/0.98  bmc1_merge_next_fun:                    0
% 3.85/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.85/0.98  
% 3.85/0.98  ------ Instantiation
% 3.85/0.98  
% 3.85/0.98  inst_num_of_clauses:                    1462
% 3.85/0.98  inst_num_in_passive:                    858
% 3.85/0.98  inst_num_in_active:                     541
% 3.85/0.98  inst_num_in_unprocessed:                63
% 3.85/0.98  inst_num_of_loops:                      630
% 3.85/0.98  inst_num_of_learning_restarts:          0
% 3.85/0.98  inst_num_moves_active_passive:          85
% 3.85/0.98  inst_lit_activity:                      0
% 3.85/0.98  inst_lit_activity_moves:                0
% 3.85/0.98  inst_num_tautologies:                   0
% 3.85/0.98  inst_num_prop_implied:                  0
% 3.85/0.98  inst_num_existing_simplified:           0
% 3.85/0.98  inst_num_eq_res_simplified:             0
% 3.85/0.98  inst_num_child_elim:                    0
% 3.85/0.98  inst_num_of_dismatching_blockings:      315
% 3.85/0.98  inst_num_of_non_proper_insts:           1657
% 3.85/0.98  inst_num_of_duplicates:                 0
% 3.85/0.98  inst_inst_num_from_inst_to_res:         0
% 3.85/0.98  inst_dismatching_checking_time:         0.
% 3.85/0.98  
% 3.85/0.98  ------ Resolution
% 3.85/0.98  
% 3.85/0.98  res_num_of_clauses:                     0
% 3.85/0.98  res_num_in_passive:                     0
% 3.85/0.98  res_num_in_active:                      0
% 3.85/0.98  res_num_of_loops:                       91
% 3.85/0.98  res_forward_subset_subsumed:            280
% 3.85/0.98  res_backward_subset_subsumed:           0
% 3.85/0.98  res_forward_subsumed:                   0
% 3.85/0.98  res_backward_subsumed:                  0
% 3.85/0.98  res_forward_subsumption_resolution:     0
% 3.85/0.98  res_backward_subsumption_resolution:    0
% 3.85/0.98  res_clause_to_clause_subsumption:       6987
% 3.85/0.98  res_orphan_elimination:                 0
% 3.85/0.98  res_tautology_del:                      92
% 3.85/0.98  res_num_eq_res_simplified:              0
% 3.85/0.98  res_num_sel_changes:                    0
% 3.85/0.98  res_moves_from_active_to_pass:          0
% 3.85/0.98  
% 3.85/0.98  ------ Superposition
% 3.85/0.98  
% 3.85/0.98  sup_time_total:                         0.
% 3.85/0.98  sup_time_generating:                    0.
% 3.85/0.98  sup_time_sim_full:                      0.
% 3.85/0.98  sup_time_sim_immed:                     0.
% 3.85/0.98  
% 3.85/0.98  sup_num_of_clauses:                     895
% 3.85/0.98  sup_num_in_active:                      97
% 3.85/0.98  sup_num_in_passive:                     798
% 3.85/0.98  sup_num_of_loops:                       124
% 3.85/0.98  sup_fw_superposition:                   1699
% 3.85/0.98  sup_bw_superposition:                   983
% 3.85/0.98  sup_immediate_simplified:               1383
% 3.85/0.98  sup_given_eliminated:                   17
% 3.85/0.98  comparisons_done:                       0
% 3.85/0.98  comparisons_avoided:                    0
% 3.85/0.98  
% 3.85/0.98  ------ Simplifications
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  sim_fw_subset_subsumed:                 0
% 3.85/0.98  sim_bw_subset_subsumed:                 0
% 3.85/0.98  sim_fw_subsumed:                        155
% 3.85/0.98  sim_bw_subsumed:                        8
% 3.85/0.98  sim_fw_subsumption_res:                 0
% 3.85/0.98  sim_bw_subsumption_res:                 0
% 3.85/0.98  sim_tautology_del:                      0
% 3.85/0.98  sim_eq_tautology_del:                   495
% 3.85/0.98  sim_eq_res_simp:                        1
% 3.85/0.98  sim_fw_demodulated:                     1006
% 3.85/0.98  sim_bw_demodulated:                     97
% 3.85/0.98  sim_light_normalised:                   725
% 3.85/0.98  sim_joinable_taut:                      14
% 3.85/0.98  sim_joinable_simp:                      0
% 3.85/0.98  sim_ac_normalised:                      0
% 3.85/0.98  sim_smt_subsumption:                    0
% 3.85/0.98  
%------------------------------------------------------------------------------
