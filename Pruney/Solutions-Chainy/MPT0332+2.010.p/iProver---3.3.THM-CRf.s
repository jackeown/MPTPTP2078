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
% DateTime   : Thu Dec  3 11:38:19 EST 2020

% Result     : Theorem 11.80s
% Output     : CNFRefutation 11.80s
% Verified   : 
% Statistics : Number of formulae       :  242 (707069 expanded)
%              Number of clauses        :  197 (167600 expanded)
%              Number of leaves         :   15 (214162 expanded)
%              Depth                    :   53
%              Number of atoms          :  269 (714375 expanded)
%              Number of equality atoms :  242 (707256 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X0,X0,X0,X1))) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f32,f21,f37])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f34,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f27,f21])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f36,f36])).

fof(f35,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k2_enumset1(sK0,sK0,sK0,sK1))) != sK2 ),
    inference(definition_unfolding,[],[f35,f21,f36,f37,f37])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f23,f36])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f22,f36])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) ),
    inference(definition_unfolding,[],[f28,f36,f21,f36,f21,f36,f21])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f36,f37])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X2))) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_124,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X2))) = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_123,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_344,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(X0,X0,X0,sK1))) = sK2
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_124,c_123])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_122,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_695,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_344,c_122])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_764,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_695,c_1])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k2_enumset1(sK0,sK0,sK0,sK1))) != sK2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_360,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k2_enumset1(sK0,sK0,sK0,sK1)))) != sK2 ),
    inference(demodulation,[status(thm)],[c_5,c_9])).

cnf(c_2690,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1)))) != sK2 ),
    inference(demodulation,[status(thm)],[c_764,c_360])).

cnf(c_2693,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),X0)) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),X0) ),
    inference(superposition,[status(thm)],[c_764,c_5])).

cnf(c_2708,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1))) != sK2 ),
    inference(demodulation,[status(thm)],[c_2690,c_2693])).

cnf(c_2709,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1)))) != sK2 ),
    inference(superposition,[status(thm)],[c_5,c_2708])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_762,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_695,c_0])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_365,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,X1)))))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_3])).

cnf(c_6987,plain,
    ( k3_xboole_0(k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)))))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_762,c_365])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_427,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_439,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_427,c_4])).

cnf(c_1090,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_439,c_5])).

cnf(c_1764,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1090,c_5])).

cnf(c_4823,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_764,c_1764])).

cnf(c_574,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_2])).

cnf(c_576,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_574,c_4])).

cnf(c_1168,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_576,c_5])).

cnf(c_4778,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_439,c_1168])).

cnf(c_289,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_3,c_3])).

cnf(c_570,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X2)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X2) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_1539,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_289,c_570])).

cnf(c_4783,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)),k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k5_xboole_0(k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_1168,c_1539])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_997,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),k5_xboole_0(X0,X0)))) = k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_3,c_6])).

cnf(c_1032,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)))) = k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_997,c_3])).

cnf(c_286,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_3])).

cnf(c_1033,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) ),
    inference(demodulation,[status(thm)],[c_1032,c_286])).

cnf(c_1010,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)))),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))))))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(superposition,[status(thm)],[c_4,c_6])).

cnf(c_288,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_842,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_288,c_288,c_576])).

cnf(c_1026,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(demodulation,[status(thm)],[c_1010,c_576,c_842])).

cnf(c_1035,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(demodulation,[status(thm)],[c_1033,c_1026])).

cnf(c_844,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_842,c_2])).

cnf(c_1036,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1035,c_844])).

cnf(c_1166,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_576])).

cnf(c_4794,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1168,c_1166])).

cnf(c_4907,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_4783,c_4,c_1036,c_4794])).

cnf(c_4908,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4907,c_4,c_576])).

cnf(c_1089,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_439,c_5])).

cnf(c_3760,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_439,c_1089])).

cnf(c_1167,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_576,c_0])).

cnf(c_1169,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_1167,c_1168])).

cnf(c_1170,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1169,c_4,c_842])).

cnf(c_3774,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1170,c_1089])).

cnf(c_3815,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3774,c_576])).

cnf(c_3823,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3760,c_3815])).

cnf(c_1086,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_439])).

cnf(c_3772,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1086,c_1089])).

cnf(c_3832,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_3823,c_3772])).

cnf(c_3833,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3832,c_1166])).

cnf(c_4909,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k5_xboole_0(k1_xboole_0,k1_xboole_0))))) = X0 ),
    inference(demodulation,[status(thm)],[c_4908,c_3833])).

cnf(c_4910,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k1_xboole_0))) = X0 ),
    inference(demodulation,[status(thm)],[c_4909,c_1166])).

cnf(c_3781,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1089,c_5])).

cnf(c_3812,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_3781,c_5])).

cnf(c_3813,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_3812,c_1089])).

cnf(c_4911,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),k1_xboole_0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_4910,c_3813])).

cnf(c_4912,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_4911,c_576])).

cnf(c_4913,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_4912,c_286,c_842])).

cnf(c_4846,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1166,c_1764])).

cnf(c_4917,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4913,c_4846])).

cnf(c_4918,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4917,c_1090])).

cnf(c_4937,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_4778,c_4918])).

cnf(c_3771,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1090,c_1089])).

cnf(c_3817,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_3771,c_3815])).

cnf(c_4938,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4937,c_3817])).

cnf(c_5316,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4823,c_2693,c_4938])).

cnf(c_7091,plain,
    ( k3_xboole_0(k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6987,c_5316])).

cnf(c_2490,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),X0)) = k5_xboole_0(k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),X0) ),
    inference(superposition,[status(thm)],[c_762,c_5])).

cnf(c_7092,plain,
    ( k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7091,c_3,c_2490])).

cnf(c_7199,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(demodulation,[status(thm)],[c_7092,c_764])).

cnf(c_4843,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1090,c_1764])).

cnf(c_5288,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4843,c_844,c_4938])).

cnf(c_5342,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)),k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_4783,c_5288])).

cnf(c_5343,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k1_xboole_0),k1_xboole_0))) = X0 ),
    inference(demodulation,[status(thm)],[c_5342,c_4,c_3815,c_4794,c_4938])).

cnf(c_5344,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))))) = X0 ),
    inference(demodulation,[status(thm)],[c_5343,c_3815])).

cnf(c_5345,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_5344,c_4938])).

cnf(c_5346,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_5345,c_286,c_842])).

cnf(c_7205,plain,
    ( k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(demodulation,[status(thm)],[c_7199,c_5346])).

cnf(c_763,plain,
    ( k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_695,c_3])).

cnf(c_4782,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1168,c_5])).

cnf(c_5357,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_4782,c_5346])).

cnf(c_5358,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_5357,c_5])).

cnf(c_7814,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_5358])).

cnf(c_8451,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7814,c_0])).

cnf(c_9724,plain,
    ( k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_763,c_8451])).

cnf(c_9843,plain,
    ( k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_9724,c_763])).

cnf(c_694,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_344,c_123])).

cnf(c_7858,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_694,c_5358])).

cnf(c_8339,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,sK2)) = k5_xboole_0(X0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_7858,c_694])).

cnf(c_8586,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,sK2),k3_xboole_0(k5_xboole_0(X0,sK2),k1_xboole_0)))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_8339,c_0])).

cnf(c_8587,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,sK2),X1)) = k5_xboole_0(k5_xboole_0(X0,sK2),X1) ),
    inference(superposition,[status(thm)],[c_8339,c_5])).

cnf(c_8596,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k5_xboole_0(X0,sK2),k3_xboole_0(k5_xboole_0(X0,sK2),k1_xboole_0))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_8586,c_8587])).

cnf(c_7850,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(superposition,[status(thm)],[c_5,c_5358])).

cnf(c_7836,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1166,c_5358])).

cnf(c_8016,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7836,c_1166])).

cnf(c_8351,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_7850,c_8016])).

cnf(c_7817,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_6,c_5358])).

cnf(c_8440,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2)))) ),
    inference(demodulation,[status(thm)],[c_7817,c_8351])).

cnf(c_1018,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_8441,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2)))) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X1,X0),X2)) ),
    inference(light_normalisation,[status(thm)],[c_8440,c_1018])).

cnf(c_8442,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,X0),X2))) ),
    inference(demodulation,[status(thm)],[c_8441,c_8016])).

cnf(c_8597,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK2,X0),k1_xboole_0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8596,c_842,c_8351,c_8442])).

cnf(c_8598,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8597,c_4,c_5346])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_412,plain,
    ( k3_tarski(k2_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_7,c_5])).

cnf(c_11334,plain,
    ( k3_tarski(k2_enumset1(k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,X0)),k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,X0)),k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,X0)),X1)) = k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k5_xboole_0(sK2,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_8598,c_412])).

cnf(c_11413,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k5_xboole_0(sK2,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_11334,c_8598])).

cnf(c_4785,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1168,c_7])).

cnf(c_407,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_4,c_7])).

cnf(c_5339,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4785,c_4,c_407])).

cnf(c_5347,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_5346,c_5339])).

cnf(c_10006,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k5_xboole_0(sK2,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_8598,c_5])).

cnf(c_10034,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k5_xboole_0(sK2,X0),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_10006,c_4938,c_8351])).

cnf(c_697,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_694,c_5])).

cnf(c_1271,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),X0),X1)) = k5_xboole_0(k5_xboole_0(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_697,c_5])).

cnf(c_699,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_694,c_0])).

cnf(c_6985,plain,
    ( k3_xboole_0(k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_699,c_365])).

cnf(c_701,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_694,c_1])).

cnf(c_4831,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_701,c_1764])).

cnf(c_2473,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)),X0)) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0) ),
    inference(superposition,[status(thm)],[c_701,c_5])).

cnf(c_5309,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4831,c_2473,c_4938])).

cnf(c_7095,plain,
    ( k3_xboole_0(k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6985,c_5309])).

cnf(c_2338,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0)) = k5_xboole_0(k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0) ),
    inference(superposition,[status(thm)],[c_699,c_5])).

cnf(c_7096,plain,
    ( k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7095,c_3,c_2338])).

cnf(c_7254,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0))) = k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_7096,c_0])).

cnf(c_1993,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_1170])).

cnf(c_7266,plain,
    ( k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7254,c_1993])).

cnf(c_10793,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(sK2,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1271,c_1271,c_4938,c_7266])).

cnf(c_11414,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))))) = X1 ),
    inference(demodulation,[status(thm)],[c_11413,c_5347,c_10034,c_10793])).

cnf(c_11415,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,k5_xboole_0(X0,X1))) = X1 ),
    inference(demodulation,[status(thm)],[c_11414,c_4,c_5346])).

cnf(c_13485,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_9843,c_11415])).

cnf(c_345,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(X0,X0,X0,sK0))) = sK2
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_124,c_122])).

cnf(c_769,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) = sK2 ),
    inference(superposition,[status(thm)],[c_345,c_122])).

cnf(c_1175,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_769,c_5])).

cnf(c_7838,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_1175,c_5358])).

cnf(c_8391,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,X0)) = k5_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_7838,c_1175])).

cnf(c_8735,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1))) = k5_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_694,c_8391])).

cnf(c_8853,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_8735,c_694])).

cnf(c_13579,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_13485,c_8853])).

cnf(c_14607,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)))) = k3_xboole_0(sK2,k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_13579,c_0])).

cnf(c_7214,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0))) = sK2 ),
    inference(superposition,[status(thm)],[c_7092,c_3])).

cnf(c_7221,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_7214,c_5346])).

cnf(c_14641,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_14607,c_7221])).

cnf(c_406,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_5,c_7])).

cnf(c_7545,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))) ),
    inference(superposition,[status(thm)],[c_406,c_7])).

cnf(c_14642,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2))))) = sK2 ),
    inference(demodulation,[status(thm)],[c_14641,c_7545])).

cnf(c_988,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))))))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0),k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0),sK2)) ),
    inference(superposition,[status(thm)],[c_695,c_6])).

cnf(c_10918,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))))),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))))))))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_10793,c_988])).

cnf(c_10924,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_10793,c_1089])).

cnf(c_10968,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10924,c_4938,c_8391])).

cnf(c_10981,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,sK2))))))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)) ),
    inference(demodulation,[status(thm)],[c_10918,c_10968])).

cnf(c_2697,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_764,c_3])).

cnf(c_10982,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,sK2))))))) = k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)) ),
    inference(light_normalisation,[status(thm)],[c_10981,c_2697,c_7205])).

cnf(c_4853,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1764,c_1089])).

cnf(c_5271,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_4853,c_3815,c_4938])).

cnf(c_4856,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1764,c_5])).

cnf(c_5267,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),X2)) = X2 ),
    inference(demodulation,[status(thm)],[c_4856,c_4938])).

cnf(c_5273,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_5271,c_5267])).

cnf(c_409,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X2)) = k5_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_7,c_5])).

cnf(c_9295,plain,
    ( k5_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1))),X0) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0),X0)) ),
    inference(superposition,[status(thm)],[c_7092,c_409])).

cnf(c_2696,plain,
    ( k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_764,c_7])).

cnf(c_7426,plain,
    ( k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_2696,c_2696,c_7205])).

cnf(c_9598,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0),X0)) = k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_9295,c_7426])).

cnf(c_9599,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),X0) ),
    inference(demodulation,[status(thm)],[c_9598,c_4794,c_8351])).

cnf(c_9600,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0)) = k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_9599,c_5346])).

cnf(c_10983,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2))) ),
    inference(demodulation,[status(thm)],[c_10982,c_286,c_5273,c_5346,c_7092,c_9600])).

cnf(c_10984,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2))) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_10983,c_286,c_842,c_5288,c_5346,c_7092])).

cnf(c_14643,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_14642,c_10984])).

cnf(c_424,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,X1))))) = k3_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_15237,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1)))) = k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_763,c_424])).

cnf(c_10665,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9843,c_1090])).

cnf(c_15516,plain,
    ( k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_15237,c_7205,c_10665,c_14643])).

cnf(c_8759,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(k5_xboole_0(k1_xboole_0,X0),sK2)) ),
    inference(superposition,[status(thm)],[c_8391,c_6])).

cnf(c_8820,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))))))) = k5_xboole_0(X0,k3_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_8759,c_4938])).

cnf(c_8821,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))),k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))),X0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))))))) = k5_xboole_0(X0,k3_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_8820,c_3813,c_8442,c_8451])).

cnf(c_8822,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK2),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK2),X0),k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))))) = k5_xboole_0(X0,k3_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_8821,c_4,c_842,c_5346,c_8016,c_8451])).

cnf(c_8823,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK2),X0) = k5_xboole_0(X0,k3_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_8822,c_4,c_842,c_5346])).

cnf(c_11699,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_7092,c_8823])).

cnf(c_11763,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_11699,c_7092,c_9843])).

cnf(c_15517,plain,
    ( k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_15516,c_8351,c_11763,c_13579])).

cnf(c_22075,plain,
    ( sK2 != sK2 ),
    inference(light_normalisation,[status(thm)],[c_2709,c_7205,c_14643,c_15517])).

cnf(c_22076,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_22075])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:05:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.80/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.80/1.98  
% 11.80/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.80/1.98  
% 11.80/1.98  ------  iProver source info
% 11.80/1.98  
% 11.80/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.80/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.80/1.98  git: non_committed_changes: false
% 11.80/1.98  git: last_make_outside_of_git: false
% 11.80/1.98  
% 11.80/1.98  ------ 
% 11.80/1.98  
% 11.80/1.98  ------ Input Options
% 11.80/1.98  
% 11.80/1.98  --out_options                           all
% 11.80/1.98  --tptp_safe_out                         true
% 11.80/1.98  --problem_path                          ""
% 11.80/1.98  --include_path                          ""
% 11.80/1.98  --clausifier                            res/vclausify_rel
% 11.80/1.98  --clausifier_options                    ""
% 11.80/1.98  --stdin                                 false
% 11.80/1.98  --stats_out                             all
% 11.80/1.98  
% 11.80/1.98  ------ General Options
% 11.80/1.98  
% 11.80/1.98  --fof                                   false
% 11.80/1.98  --time_out_real                         305.
% 11.80/1.98  --time_out_virtual                      -1.
% 11.80/1.98  --symbol_type_check                     false
% 11.80/1.98  --clausify_out                          false
% 11.80/1.98  --sig_cnt_out                           false
% 11.80/1.98  --trig_cnt_out                          false
% 11.80/1.98  --trig_cnt_out_tolerance                1.
% 11.80/1.98  --trig_cnt_out_sk_spl                   false
% 11.80/1.98  --abstr_cl_out                          false
% 11.80/1.98  
% 11.80/1.98  ------ Global Options
% 11.80/1.98  
% 11.80/1.98  --schedule                              default
% 11.80/1.98  --add_important_lit                     false
% 11.80/1.98  --prop_solver_per_cl                    1000
% 11.80/1.98  --min_unsat_core                        false
% 11.80/1.98  --soft_assumptions                      false
% 11.80/1.98  --soft_lemma_size                       3
% 11.80/1.98  --prop_impl_unit_size                   0
% 11.80/1.98  --prop_impl_unit                        []
% 11.80/1.98  --share_sel_clauses                     true
% 11.80/1.98  --reset_solvers                         false
% 11.80/1.98  --bc_imp_inh                            [conj_cone]
% 11.80/1.98  --conj_cone_tolerance                   3.
% 11.80/1.98  --extra_neg_conj                        none
% 11.80/1.98  --large_theory_mode                     true
% 11.80/1.98  --prolific_symb_bound                   200
% 11.80/1.98  --lt_threshold                          2000
% 11.80/1.98  --clause_weak_htbl                      true
% 11.80/1.98  --gc_record_bc_elim                     false
% 11.80/1.98  
% 11.80/1.98  ------ Preprocessing Options
% 11.80/1.98  
% 11.80/1.98  --preprocessing_flag                    true
% 11.80/1.98  --time_out_prep_mult                    0.1
% 11.80/1.98  --splitting_mode                        input
% 11.80/1.98  --splitting_grd                         true
% 11.80/1.98  --splitting_cvd                         false
% 11.80/1.98  --splitting_cvd_svl                     false
% 11.80/1.98  --splitting_nvd                         32
% 11.80/1.98  --sub_typing                            true
% 11.80/1.98  --prep_gs_sim                           true
% 11.80/1.98  --prep_unflatten                        true
% 11.80/1.98  --prep_res_sim                          true
% 11.80/1.98  --prep_upred                            true
% 11.80/1.98  --prep_sem_filter                       exhaustive
% 11.80/1.98  --prep_sem_filter_out                   false
% 11.80/1.98  --pred_elim                             true
% 11.80/1.98  --res_sim_input                         true
% 11.80/1.98  --eq_ax_congr_red                       true
% 11.80/1.98  --pure_diseq_elim                       true
% 11.80/1.98  --brand_transform                       false
% 11.80/1.98  --non_eq_to_eq                          false
% 11.80/1.98  --prep_def_merge                        true
% 11.80/1.98  --prep_def_merge_prop_impl              false
% 11.80/1.98  --prep_def_merge_mbd                    true
% 11.80/1.98  --prep_def_merge_tr_red                 false
% 11.80/1.98  --prep_def_merge_tr_cl                  false
% 11.80/1.98  --smt_preprocessing                     true
% 11.80/1.98  --smt_ac_axioms                         fast
% 11.80/1.98  --preprocessed_out                      false
% 11.80/1.98  --preprocessed_stats                    false
% 11.80/1.98  
% 11.80/1.98  ------ Abstraction refinement Options
% 11.80/1.98  
% 11.80/1.98  --abstr_ref                             []
% 11.80/1.98  --abstr_ref_prep                        false
% 11.80/1.98  --abstr_ref_until_sat                   false
% 11.80/1.98  --abstr_ref_sig_restrict                funpre
% 11.80/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.80/1.98  --abstr_ref_under                       []
% 11.80/1.98  
% 11.80/1.98  ------ SAT Options
% 11.80/1.98  
% 11.80/1.98  --sat_mode                              false
% 11.80/1.98  --sat_fm_restart_options                ""
% 11.80/1.98  --sat_gr_def                            false
% 11.80/1.98  --sat_epr_types                         true
% 11.80/1.98  --sat_non_cyclic_types                  false
% 11.80/1.98  --sat_finite_models                     false
% 11.80/1.98  --sat_fm_lemmas                         false
% 11.80/1.98  --sat_fm_prep                           false
% 11.80/1.98  --sat_fm_uc_incr                        true
% 11.80/1.98  --sat_out_model                         small
% 11.80/1.98  --sat_out_clauses                       false
% 11.80/1.98  
% 11.80/1.98  ------ QBF Options
% 11.80/1.98  
% 11.80/1.98  --qbf_mode                              false
% 11.80/1.98  --qbf_elim_univ                         false
% 11.80/1.98  --qbf_dom_inst                          none
% 11.80/1.98  --qbf_dom_pre_inst                      false
% 11.80/1.98  --qbf_sk_in                             false
% 11.80/1.98  --qbf_pred_elim                         true
% 11.80/1.98  --qbf_split                             512
% 11.80/1.98  
% 11.80/1.98  ------ BMC1 Options
% 11.80/1.98  
% 11.80/1.98  --bmc1_incremental                      false
% 11.80/1.98  --bmc1_axioms                           reachable_all
% 11.80/1.98  --bmc1_min_bound                        0
% 11.80/1.98  --bmc1_max_bound                        -1
% 11.80/1.98  --bmc1_max_bound_default                -1
% 11.80/1.98  --bmc1_symbol_reachability              true
% 11.80/1.98  --bmc1_property_lemmas                  false
% 11.80/1.98  --bmc1_k_induction                      false
% 11.80/1.98  --bmc1_non_equiv_states                 false
% 11.80/1.98  --bmc1_deadlock                         false
% 11.80/1.98  --bmc1_ucm                              false
% 11.80/1.98  --bmc1_add_unsat_core                   none
% 11.80/1.98  --bmc1_unsat_core_children              false
% 11.80/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.80/1.98  --bmc1_out_stat                         full
% 11.80/1.98  --bmc1_ground_init                      false
% 11.80/1.98  --bmc1_pre_inst_next_state              false
% 11.80/1.98  --bmc1_pre_inst_state                   false
% 11.80/1.98  --bmc1_pre_inst_reach_state             false
% 11.80/1.98  --bmc1_out_unsat_core                   false
% 11.80/1.98  --bmc1_aig_witness_out                  false
% 11.80/1.98  --bmc1_verbose                          false
% 11.80/1.98  --bmc1_dump_clauses_tptp                false
% 11.80/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.80/1.98  --bmc1_dump_file                        -
% 11.80/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.80/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.80/1.98  --bmc1_ucm_extend_mode                  1
% 11.80/1.98  --bmc1_ucm_init_mode                    2
% 11.80/1.98  --bmc1_ucm_cone_mode                    none
% 11.80/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.80/1.98  --bmc1_ucm_relax_model                  4
% 11.80/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.80/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.80/1.98  --bmc1_ucm_layered_model                none
% 11.80/1.98  --bmc1_ucm_max_lemma_size               10
% 11.80/1.98  
% 11.80/1.98  ------ AIG Options
% 11.80/1.98  
% 11.80/1.98  --aig_mode                              false
% 11.80/1.98  
% 11.80/1.98  ------ Instantiation Options
% 11.80/1.98  
% 11.80/1.98  --instantiation_flag                    true
% 11.80/1.98  --inst_sos_flag                         true
% 11.80/1.98  --inst_sos_phase                        true
% 11.80/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.80/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.80/1.98  --inst_lit_sel_side                     num_symb
% 11.80/1.98  --inst_solver_per_active                1400
% 11.80/1.98  --inst_solver_calls_frac                1.
% 11.80/1.98  --inst_passive_queue_type               priority_queues
% 11.80/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.80/1.98  --inst_passive_queues_freq              [25;2]
% 11.80/1.98  --inst_dismatching                      true
% 11.80/1.98  --inst_eager_unprocessed_to_passive     true
% 11.80/1.98  --inst_prop_sim_given                   true
% 11.80/1.98  --inst_prop_sim_new                     false
% 11.80/1.98  --inst_subs_new                         false
% 11.80/1.98  --inst_eq_res_simp                      false
% 11.80/1.98  --inst_subs_given                       false
% 11.80/1.98  --inst_orphan_elimination               true
% 11.80/1.98  --inst_learning_loop_flag               true
% 11.80/1.98  --inst_learning_start                   3000
% 11.80/1.98  --inst_learning_factor                  2
% 11.80/1.98  --inst_start_prop_sim_after_learn       3
% 11.80/1.98  --inst_sel_renew                        solver
% 11.80/1.98  --inst_lit_activity_flag                true
% 11.80/1.98  --inst_restr_to_given                   false
% 11.80/1.98  --inst_activity_threshold               500
% 11.80/1.98  --inst_out_proof                        true
% 11.80/1.98  
% 11.80/1.98  ------ Resolution Options
% 11.80/1.98  
% 11.80/1.98  --resolution_flag                       true
% 11.80/1.98  --res_lit_sel                           adaptive
% 11.80/1.98  --res_lit_sel_side                      none
% 11.80/1.98  --res_ordering                          kbo
% 11.80/1.98  --res_to_prop_solver                    active
% 11.80/1.98  --res_prop_simpl_new                    false
% 11.80/1.98  --res_prop_simpl_given                  true
% 11.80/1.98  --res_passive_queue_type                priority_queues
% 11.80/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.80/1.98  --res_passive_queues_freq               [15;5]
% 11.80/1.98  --res_forward_subs                      full
% 11.80/1.98  --res_backward_subs                     full
% 11.80/1.98  --res_forward_subs_resolution           true
% 11.80/1.98  --res_backward_subs_resolution          true
% 11.80/1.98  --res_orphan_elimination                true
% 11.80/1.98  --res_time_limit                        2.
% 11.80/1.98  --res_out_proof                         true
% 11.80/1.98  
% 11.80/1.98  ------ Superposition Options
% 11.80/1.98  
% 11.80/1.98  --superposition_flag                    true
% 11.80/1.98  --sup_passive_queue_type                priority_queues
% 11.80/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.80/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.80/1.98  --demod_completeness_check              fast
% 11.80/1.98  --demod_use_ground                      true
% 11.80/1.98  --sup_to_prop_solver                    passive
% 11.80/1.98  --sup_prop_simpl_new                    true
% 11.80/1.98  --sup_prop_simpl_given                  true
% 11.80/1.98  --sup_fun_splitting                     true
% 11.80/1.98  --sup_smt_interval                      50000
% 11.80/1.98  
% 11.80/1.98  ------ Superposition Simplification Setup
% 11.80/1.98  
% 11.80/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.80/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.80/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.80/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.80/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.80/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.80/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.80/1.98  --sup_immed_triv                        [TrivRules]
% 11.80/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.98  --sup_immed_bw_main                     []
% 11.80/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.80/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.80/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.98  --sup_input_bw                          []
% 11.80/1.98  
% 11.80/1.98  ------ Combination Options
% 11.80/1.98  
% 11.80/1.98  --comb_res_mult                         3
% 11.80/1.98  --comb_sup_mult                         2
% 11.80/1.98  --comb_inst_mult                        10
% 11.80/1.98  
% 11.80/1.98  ------ Debug Options
% 11.80/1.98  
% 11.80/1.98  --dbg_backtrace                         false
% 11.80/1.98  --dbg_dump_prop_clauses                 false
% 11.80/1.98  --dbg_dump_prop_clauses_file            -
% 11.80/1.98  --dbg_out_stat                          false
% 11.80/1.98  ------ Parsing...
% 11.80/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.80/1.98  
% 11.80/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.80/1.98  
% 11.80/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.80/1.98  
% 11.80/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.98  ------ Proving...
% 11.80/1.98  ------ Problem Properties 
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  clauses                                 12
% 11.80/1.98  conjectures                             3
% 11.80/1.98  EPR                                     2
% 11.80/1.98  Horn                                    11
% 11.80/1.98  unary                                   11
% 11.80/1.98  binary                                  0
% 11.80/1.98  lits                                    14
% 11.80/1.98  lits eq                                 10
% 11.80/1.98  fd_pure                                 0
% 11.80/1.98  fd_pseudo                               0
% 11.80/1.98  fd_cond                                 0
% 11.80/1.98  fd_pseudo_cond                          0
% 11.80/1.98  AC symbols                              0
% 11.80/1.98  
% 11.80/1.98  ------ Schedule dynamic 5 is on 
% 11.80/1.98  
% 11.80/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  ------ 
% 11.80/1.98  Current options:
% 11.80/1.98  ------ 
% 11.80/1.98  
% 11.80/1.98  ------ Input Options
% 11.80/1.98  
% 11.80/1.98  --out_options                           all
% 11.80/1.98  --tptp_safe_out                         true
% 11.80/1.98  --problem_path                          ""
% 11.80/1.98  --include_path                          ""
% 11.80/1.98  --clausifier                            res/vclausify_rel
% 11.80/1.98  --clausifier_options                    ""
% 11.80/1.98  --stdin                                 false
% 11.80/1.98  --stats_out                             all
% 11.80/1.98  
% 11.80/1.98  ------ General Options
% 11.80/1.98  
% 11.80/1.98  --fof                                   false
% 11.80/1.98  --time_out_real                         305.
% 11.80/1.98  --time_out_virtual                      -1.
% 11.80/1.98  --symbol_type_check                     false
% 11.80/1.98  --clausify_out                          false
% 11.80/1.98  --sig_cnt_out                           false
% 11.80/1.98  --trig_cnt_out                          false
% 11.80/1.98  --trig_cnt_out_tolerance                1.
% 11.80/1.98  --trig_cnt_out_sk_spl                   false
% 11.80/1.98  --abstr_cl_out                          false
% 11.80/1.98  
% 11.80/1.98  ------ Global Options
% 11.80/1.98  
% 11.80/1.98  --schedule                              default
% 11.80/1.98  --add_important_lit                     false
% 11.80/1.98  --prop_solver_per_cl                    1000
% 11.80/1.98  --min_unsat_core                        false
% 11.80/1.98  --soft_assumptions                      false
% 11.80/1.98  --soft_lemma_size                       3
% 11.80/1.98  --prop_impl_unit_size                   0
% 11.80/1.98  --prop_impl_unit                        []
% 11.80/1.98  --share_sel_clauses                     true
% 11.80/1.98  --reset_solvers                         false
% 11.80/1.98  --bc_imp_inh                            [conj_cone]
% 11.80/1.98  --conj_cone_tolerance                   3.
% 11.80/1.98  --extra_neg_conj                        none
% 11.80/1.98  --large_theory_mode                     true
% 11.80/1.98  --prolific_symb_bound                   200
% 11.80/1.98  --lt_threshold                          2000
% 11.80/1.98  --clause_weak_htbl                      true
% 11.80/1.98  --gc_record_bc_elim                     false
% 11.80/1.98  
% 11.80/1.98  ------ Preprocessing Options
% 11.80/1.98  
% 11.80/1.98  --preprocessing_flag                    true
% 11.80/1.98  --time_out_prep_mult                    0.1
% 11.80/1.98  --splitting_mode                        input
% 11.80/1.98  --splitting_grd                         true
% 11.80/1.98  --splitting_cvd                         false
% 11.80/1.98  --splitting_cvd_svl                     false
% 11.80/1.98  --splitting_nvd                         32
% 11.80/1.98  --sub_typing                            true
% 11.80/1.98  --prep_gs_sim                           true
% 11.80/1.98  --prep_unflatten                        true
% 11.80/1.98  --prep_res_sim                          true
% 11.80/1.98  --prep_upred                            true
% 11.80/1.98  --prep_sem_filter                       exhaustive
% 11.80/1.98  --prep_sem_filter_out                   false
% 11.80/1.98  --pred_elim                             true
% 11.80/1.98  --res_sim_input                         true
% 11.80/1.98  --eq_ax_congr_red                       true
% 11.80/1.98  --pure_diseq_elim                       true
% 11.80/1.98  --brand_transform                       false
% 11.80/1.98  --non_eq_to_eq                          false
% 11.80/1.98  --prep_def_merge                        true
% 11.80/1.98  --prep_def_merge_prop_impl              false
% 11.80/1.98  --prep_def_merge_mbd                    true
% 11.80/1.98  --prep_def_merge_tr_red                 false
% 11.80/1.98  --prep_def_merge_tr_cl                  false
% 11.80/1.98  --smt_preprocessing                     true
% 11.80/1.98  --smt_ac_axioms                         fast
% 11.80/1.98  --preprocessed_out                      false
% 11.80/1.98  --preprocessed_stats                    false
% 11.80/1.98  
% 11.80/1.98  ------ Abstraction refinement Options
% 11.80/1.98  
% 11.80/1.98  --abstr_ref                             []
% 11.80/1.98  --abstr_ref_prep                        false
% 11.80/1.98  --abstr_ref_until_sat                   false
% 11.80/1.98  --abstr_ref_sig_restrict                funpre
% 11.80/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.80/1.98  --abstr_ref_under                       []
% 11.80/1.98  
% 11.80/1.98  ------ SAT Options
% 11.80/1.98  
% 11.80/1.98  --sat_mode                              false
% 11.80/1.98  --sat_fm_restart_options                ""
% 11.80/1.98  --sat_gr_def                            false
% 11.80/1.98  --sat_epr_types                         true
% 11.80/1.98  --sat_non_cyclic_types                  false
% 11.80/1.98  --sat_finite_models                     false
% 11.80/1.98  --sat_fm_lemmas                         false
% 11.80/1.98  --sat_fm_prep                           false
% 11.80/1.98  --sat_fm_uc_incr                        true
% 11.80/1.98  --sat_out_model                         small
% 11.80/1.98  --sat_out_clauses                       false
% 11.80/1.98  
% 11.80/1.98  ------ QBF Options
% 11.80/1.98  
% 11.80/1.98  --qbf_mode                              false
% 11.80/1.98  --qbf_elim_univ                         false
% 11.80/1.98  --qbf_dom_inst                          none
% 11.80/1.98  --qbf_dom_pre_inst                      false
% 11.80/1.98  --qbf_sk_in                             false
% 11.80/1.98  --qbf_pred_elim                         true
% 11.80/1.98  --qbf_split                             512
% 11.80/1.98  
% 11.80/1.98  ------ BMC1 Options
% 11.80/1.98  
% 11.80/1.98  --bmc1_incremental                      false
% 11.80/1.98  --bmc1_axioms                           reachable_all
% 11.80/1.98  --bmc1_min_bound                        0
% 11.80/1.98  --bmc1_max_bound                        -1
% 11.80/1.98  --bmc1_max_bound_default                -1
% 11.80/1.98  --bmc1_symbol_reachability              true
% 11.80/1.98  --bmc1_property_lemmas                  false
% 11.80/1.98  --bmc1_k_induction                      false
% 11.80/1.98  --bmc1_non_equiv_states                 false
% 11.80/1.98  --bmc1_deadlock                         false
% 11.80/1.98  --bmc1_ucm                              false
% 11.80/1.98  --bmc1_add_unsat_core                   none
% 11.80/1.98  --bmc1_unsat_core_children              false
% 11.80/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.80/1.98  --bmc1_out_stat                         full
% 11.80/1.98  --bmc1_ground_init                      false
% 11.80/1.98  --bmc1_pre_inst_next_state              false
% 11.80/1.98  --bmc1_pre_inst_state                   false
% 11.80/1.98  --bmc1_pre_inst_reach_state             false
% 11.80/1.98  --bmc1_out_unsat_core                   false
% 11.80/1.98  --bmc1_aig_witness_out                  false
% 11.80/1.98  --bmc1_verbose                          false
% 11.80/1.98  --bmc1_dump_clauses_tptp                false
% 11.80/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.80/1.98  --bmc1_dump_file                        -
% 11.80/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.80/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.80/1.98  --bmc1_ucm_extend_mode                  1
% 11.80/1.98  --bmc1_ucm_init_mode                    2
% 11.80/1.98  --bmc1_ucm_cone_mode                    none
% 11.80/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.80/1.98  --bmc1_ucm_relax_model                  4
% 11.80/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.80/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.80/1.98  --bmc1_ucm_layered_model                none
% 11.80/1.98  --bmc1_ucm_max_lemma_size               10
% 11.80/1.98  
% 11.80/1.98  ------ AIG Options
% 11.80/1.98  
% 11.80/1.98  --aig_mode                              false
% 11.80/1.98  
% 11.80/1.98  ------ Instantiation Options
% 11.80/1.98  
% 11.80/1.98  --instantiation_flag                    true
% 11.80/1.98  --inst_sos_flag                         true
% 11.80/1.98  --inst_sos_phase                        true
% 11.80/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.80/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.80/1.98  --inst_lit_sel_side                     none
% 11.80/1.98  --inst_solver_per_active                1400
% 11.80/1.98  --inst_solver_calls_frac                1.
% 11.80/1.98  --inst_passive_queue_type               priority_queues
% 11.80/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.80/1.98  --inst_passive_queues_freq              [25;2]
% 11.80/1.98  --inst_dismatching                      true
% 11.80/1.98  --inst_eager_unprocessed_to_passive     true
% 11.80/1.98  --inst_prop_sim_given                   true
% 11.80/1.98  --inst_prop_sim_new                     false
% 11.80/1.98  --inst_subs_new                         false
% 11.80/1.98  --inst_eq_res_simp                      false
% 11.80/1.98  --inst_subs_given                       false
% 11.80/1.98  --inst_orphan_elimination               true
% 11.80/1.98  --inst_learning_loop_flag               true
% 11.80/1.98  --inst_learning_start                   3000
% 11.80/1.98  --inst_learning_factor                  2
% 11.80/1.98  --inst_start_prop_sim_after_learn       3
% 11.80/1.98  --inst_sel_renew                        solver
% 11.80/1.98  --inst_lit_activity_flag                true
% 11.80/1.98  --inst_restr_to_given                   false
% 11.80/1.98  --inst_activity_threshold               500
% 11.80/1.98  --inst_out_proof                        true
% 11.80/1.98  
% 11.80/1.98  ------ Resolution Options
% 11.80/1.98  
% 11.80/1.98  --resolution_flag                       false
% 11.80/1.98  --res_lit_sel                           adaptive
% 11.80/1.98  --res_lit_sel_side                      none
% 11.80/1.98  --res_ordering                          kbo
% 11.80/1.98  --res_to_prop_solver                    active
% 11.80/1.98  --res_prop_simpl_new                    false
% 11.80/1.98  --res_prop_simpl_given                  true
% 11.80/1.98  --res_passive_queue_type                priority_queues
% 11.80/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.80/1.98  --res_passive_queues_freq               [15;5]
% 11.80/1.98  --res_forward_subs                      full
% 11.80/1.98  --res_backward_subs                     full
% 11.80/1.98  --res_forward_subs_resolution           true
% 11.80/1.98  --res_backward_subs_resolution          true
% 11.80/1.98  --res_orphan_elimination                true
% 11.80/1.98  --res_time_limit                        2.
% 11.80/1.98  --res_out_proof                         true
% 11.80/1.98  
% 11.80/1.98  ------ Superposition Options
% 11.80/1.98  
% 11.80/1.98  --superposition_flag                    true
% 11.80/1.98  --sup_passive_queue_type                priority_queues
% 11.80/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.80/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.80/1.98  --demod_completeness_check              fast
% 11.80/1.98  --demod_use_ground                      true
% 11.80/1.98  --sup_to_prop_solver                    passive
% 11.80/1.98  --sup_prop_simpl_new                    true
% 11.80/1.98  --sup_prop_simpl_given                  true
% 11.80/1.98  --sup_fun_splitting                     true
% 11.80/1.98  --sup_smt_interval                      50000
% 11.80/1.98  
% 11.80/1.98  ------ Superposition Simplification Setup
% 11.80/1.98  
% 11.80/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.80/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.80/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.80/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.80/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.80/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.80/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.80/1.98  --sup_immed_triv                        [TrivRules]
% 11.80/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.98  --sup_immed_bw_main                     []
% 11.80/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.80/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.80/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.98  --sup_input_bw                          []
% 11.80/1.98  
% 11.80/1.98  ------ Combination Options
% 11.80/1.98  
% 11.80/1.98  --comb_res_mult                         3
% 11.80/1.98  --comb_sup_mult                         2
% 11.80/1.98  --comb_inst_mult                        10
% 11.80/1.98  
% 11.80/1.98  ------ Debug Options
% 11.80/1.98  
% 11.80/1.98  --dbg_backtrace                         false
% 11.80/1.98  --dbg_dump_prop_clauses                 false
% 11.80/1.98  --dbg_dump_prop_clauses_file            -
% 11.80/1.98  --dbg_out_stat                          false
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  ------ Proving...
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  % SZS status Theorem for theBenchmark.p
% 11.80/1.98  
% 11.80/1.98   Resolution empty clause
% 11.80/1.98  
% 11.80/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.80/1.98  
% 11.80/1.98  fof(f6,axiom,(
% 11.80/1.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f25,plain,(
% 11.80/1.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f6])).
% 11.80/1.98  
% 11.80/1.98  fof(f13,axiom,(
% 11.80/1.98    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f16,plain,(
% 11.80/1.98    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 11.80/1.98    inference(ennf_transformation,[],[f13])).
% 11.80/1.98  
% 11.80/1.98  fof(f32,plain,(
% 11.80/1.98    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f16])).
% 11.80/1.98  
% 11.80/1.98  fof(f2,axiom,(
% 11.80/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f21,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.80/1.98    inference(cnf_transformation,[],[f2])).
% 11.80/1.98  
% 11.80/1.98  fof(f10,axiom,(
% 11.80/1.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f29,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f10])).
% 11.80/1.98  
% 11.80/1.98  fof(f11,axiom,(
% 11.80/1.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f30,plain,(
% 11.80/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f11])).
% 11.80/1.98  
% 11.80/1.98  fof(f37,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.80/1.98    inference(definition_unfolding,[],[f29,f30])).
% 11.80/1.98  
% 11.80/1.98  fof(f44,plain,(
% 11.80/1.98    ( ! [X2,X0,X1] : (k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X0,X0,X0,X1))) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 11.80/1.98    inference(definition_unfolding,[],[f32,f21,f37])).
% 11.80/1.98  
% 11.80/1.98  fof(f14,conjecture,(
% 11.80/1.98    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f15,negated_conjecture,(
% 11.80/1.98    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 11.80/1.98    inference(negated_conjecture,[],[f14])).
% 11.80/1.98  
% 11.80/1.98  fof(f17,plain,(
% 11.80/1.98    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 11.80/1.98    inference(ennf_transformation,[],[f15])).
% 11.80/1.98  
% 11.80/1.98  fof(f18,plain,(
% 11.80/1.98    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 11.80/1.98    introduced(choice_axiom,[])).
% 11.80/1.98  
% 11.80/1.98  fof(f19,plain,(
% 11.80/1.98    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 11.80/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 11.80/1.98  
% 11.80/1.98  fof(f34,plain,(
% 11.80/1.98    ~r2_hidden(sK1,sK2)),
% 11.80/1.98    inference(cnf_transformation,[],[f19])).
% 11.80/1.98  
% 11.80/1.98  fof(f33,plain,(
% 11.80/1.98    ~r2_hidden(sK0,sK2)),
% 11.80/1.98    inference(cnf_transformation,[],[f19])).
% 11.80/1.98  
% 11.80/1.98  fof(f1,axiom,(
% 11.80/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f20,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f1])).
% 11.80/1.98  
% 11.80/1.98  fof(f8,axiom,(
% 11.80/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f27,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.80/1.98    inference(cnf_transformation,[],[f8])).
% 11.80/1.98  
% 11.80/1.98  fof(f36,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 11.80/1.98    inference(definition_unfolding,[],[f27,f21])).
% 11.80/1.98  
% 11.80/1.98  fof(f39,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 11.80/1.98    inference(definition_unfolding,[],[f20,f36,f36])).
% 11.80/1.98  
% 11.80/1.98  fof(f35,plain,(
% 11.80/1.98    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2),
% 11.80/1.98    inference(cnf_transformation,[],[f19])).
% 11.80/1.98  
% 11.80/1.98  fof(f45,plain,(
% 11.80/1.98    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k2_enumset1(sK0,sK0,sK0,sK1))) != sK2),
% 11.80/1.98    inference(definition_unfolding,[],[f35,f21,f36,f37,f37])).
% 11.80/1.98  
% 11.80/1.98  fof(f7,axiom,(
% 11.80/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f26,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 11.80/1.98    inference(cnf_transformation,[],[f7])).
% 11.80/1.98  
% 11.80/1.98  fof(f38,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 11.80/1.98    inference(definition_unfolding,[],[f26,f36])).
% 11.80/1.98  
% 11.80/1.98  fof(f4,axiom,(
% 11.80/1.98    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f23,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 11.80/1.98    inference(cnf_transformation,[],[f4])).
% 11.80/1.98  
% 11.80/1.98  fof(f41,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 11.80/1.98    inference(definition_unfolding,[],[f23,f36])).
% 11.80/1.98  
% 11.80/1.98  fof(f3,axiom,(
% 11.80/1.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f22,plain,(
% 11.80/1.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.80/1.98    inference(cnf_transformation,[],[f3])).
% 11.80/1.98  
% 11.80/1.98  fof(f40,plain,(
% 11.80/1.98    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 11.80/1.98    inference(definition_unfolding,[],[f22,f36])).
% 11.80/1.98  
% 11.80/1.98  fof(f5,axiom,(
% 11.80/1.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f24,plain,(
% 11.80/1.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.80/1.98    inference(cnf_transformation,[],[f5])).
% 11.80/1.98  
% 11.80/1.98  fof(f9,axiom,(
% 11.80/1.98    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f28,plain,(
% 11.80/1.98    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f9])).
% 11.80/1.98  
% 11.80/1.98  fof(f42,plain,(
% 11.80/1.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))) )),
% 11.80/1.98    inference(definition_unfolding,[],[f28,f36,f21,f36,f21,f36,f21])).
% 11.80/1.98  
% 11.80/1.98  fof(f12,axiom,(
% 11.80/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f31,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.80/1.98    inference(cnf_transformation,[],[f12])).
% 11.80/1.98  
% 11.80/1.98  fof(f43,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 11.80/1.98    inference(definition_unfolding,[],[f31,f36,f37])).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.80/1.98      inference(cnf_transformation,[],[f25]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8,plain,
% 11.80/1.98      ( r2_hidden(X0,X1)
% 11.80/1.98      | r2_hidden(X2,X1)
% 11.80/1.98      | k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X2))) = X1 ),
% 11.80/1.98      inference(cnf_transformation,[],[f44]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_124,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X2))) = X0
% 11.80/1.98      | r2_hidden(X1,X0) = iProver_top
% 11.80/1.98      | r2_hidden(X2,X0) = iProver_top ),
% 11.80/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10,negated_conjecture,
% 11.80/1.98      ( ~ r2_hidden(sK1,sK2) ),
% 11.80/1.98      inference(cnf_transformation,[],[f34]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_123,plain,
% 11.80/1.98      ( r2_hidden(sK1,sK2) != iProver_top ),
% 11.80/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_344,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(X0,X0,X0,sK1))) = sK2
% 11.80/1.98      | r2_hidden(X0,sK2) = iProver_top ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_124,c_123]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_11,negated_conjecture,
% 11.80/1.98      ( ~ r2_hidden(sK0,sK2) ),
% 11.80/1.98      inference(cnf_transformation,[],[f33]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_122,plain,
% 11.80/1.98      ( r2_hidden(sK0,sK2) != iProver_top ),
% 11.80/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_695,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = sK2 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_344,c_122]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 11.80/1.98      inference(cnf_transformation,[],[f39]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_764,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_695,c_1]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_9,negated_conjecture,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k2_enumset1(sK0,sK0,sK0,sK1))) != sK2 ),
% 11.80/1.98      inference(cnf_transformation,[],[f45]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_360,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k2_enumset1(sK0,sK0,sK0,sK1)))) != sK2 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_5,c_9]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_2690,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1)))) != sK2 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_764,c_360]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_2693,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),X0)) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),X0) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_764,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_2708,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1))) != sK2 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_2690,c_2693]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_2709,plain,
% 11.80/1.98      ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1)))) != sK2 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_5,c_2708]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_0,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
% 11.80/1.98      inference(cnf_transformation,[],[f38]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_762,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_695,c_0]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3,plain,
% 11.80/1.98      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 11.80/1.98      inference(cnf_transformation,[],[f41]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_365,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,X1)))))) = k5_xboole_0(X0,X1) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_5,c_3]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_6987,plain,
% 11.80/1.98      ( k3_xboole_0(k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)))))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_762,c_365]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_2,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 11.80/1.98      inference(cnf_transformation,[],[f40]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_427,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k3_xboole_0(X0,k1_xboole_0) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4,plain,
% 11.80/1.98      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.80/1.98      inference(cnf_transformation,[],[f24]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_439,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k1_xboole_0 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_427,c_4]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1090,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_439,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1764,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1090,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4823,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)))) = k1_xboole_0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_764,c_1764]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_574,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1,c_2]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_576,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_574,c_4]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1168,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(X0,X1) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_576,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4778,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_439,c_1168]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_289,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_3,c_3]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_570,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X2)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1539,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_289,c_570]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4783,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)),k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k5_xboole_0(k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0))) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1168,c_1539]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_6,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
% 11.80/1.98      inference(cnf_transformation,[],[f42]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_997,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),k5_xboole_0(X0,X0)))) = k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_3,c_6]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1032,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)))) = k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_997,c_3]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_286,plain,
% 11.80/1.98      ( k3_xboole_0(X0,X0) = X0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_2,c_3]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1033,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_1032,c_286]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1010,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)))),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))))))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_4,c_6]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_288,plain,
% 11.80/1.98      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_842,plain,
% 11.80/1.98      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_288,c_288,c_576]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1026,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_1010,c_576,c_842]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1035,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_1033,c_1026]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_844,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_842,c_2]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1036,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_1035,c_844]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1166,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(X0,X1) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_5,c_576]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4794,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1168,c_1166]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4907,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4783,c_4,c_1036,c_4794]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4908,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0))) = X0 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_4907,c_4,c_576]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1089,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_439,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3760,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_439,c_1089]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1167,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_576,c_0]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1169,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_1167,c_1168]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1170,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_1169,c_4,c_842]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3774,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1170,c_1089]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3815,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_3774,c_576]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3823,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_3760,c_3815]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1086,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_5,c_439]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3772,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1086,c_1089]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3832,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_3823,c_3772]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3833,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_3832,c_1166]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4909,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k5_xboole_0(k1_xboole_0,k1_xboole_0))))) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4908,c_3833]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4910,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k1_xboole_0))) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4909,c_1166]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3781,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1089,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3812,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_3781,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3813,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_3812,c_1089]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4911,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),k1_xboole_0)))) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4910,c_3813]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4912,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)))) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4911,c_576]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4913,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4912,c_286,c_842]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4846,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1166,c_1764]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4917,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4913,c_4846]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4918,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4917,c_1090]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4937,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4778,c_4918]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3771,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1090,c_1089]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3817,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_3771,c_3815]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4938,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_4937,c_3817]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5316,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k1_xboole_0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4823,c_2693,c_4938]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7091,plain,
% 11.80/1.98      ( k3_xboole_0(k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)))))) = k1_xboole_0 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_6987,c_5316]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_2490,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),X0)) = k5_xboole_0(k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),X0) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_762,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7092,plain,
% 11.80/1.98      ( k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) = k1_xboole_0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_7091,c_3,c_2490]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7199,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_7092,c_764]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4843,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1090,c_1764]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5288,plain,
% 11.80/1.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_4843,c_844,c_4938]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5342,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)),k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0))) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4783,c_5288]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5343,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))),k1_xboole_0),k1_xboole_0))) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_5342,c_4,c_3815,c_4794,c_4938]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5344,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))))) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_5343,c_3815]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5345,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)))) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_5344,c_4938]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5346,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_5345,c_286,c_842]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7205,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_7199,c_5346]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_763,plain,
% 11.80/1.98      ( k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK0,sK0,sK0,sK1) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_695,c_3]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4782,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1168,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5357,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4782,c_5346]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5358,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_5357,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7814,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_0,c_5358]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8451,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_7814,c_0]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_9724,plain,
% 11.80/1.98      ( k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_763,c_8451]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_9843,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK0,sK0,sK0,sK1) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_9724,c_763]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_694,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1))) = sK2 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_344,c_123]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7858,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,sK2)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_694,c_5358]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8339,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,sK2)) = k5_xboole_0(X0,sK2) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_7858,c_694]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8586,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,sK2),k3_xboole_0(k5_xboole_0(X0,sK2),k1_xboole_0)))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,sK2)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_8339,c_0]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8587,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,sK2),X1)) = k5_xboole_0(k5_xboole_0(X0,sK2),X1) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_8339,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8596,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k5_xboole_0(X0,sK2),k3_xboole_0(k5_xboole_0(X0,sK2),k1_xboole_0))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,sK2)) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_8586,c_8587]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7850,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_5,c_5358]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7836,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1166,c_5358]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8016,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_7836,c_1166]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8351,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_7850,c_8016]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7817,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2))) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_6,c_5358]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8440,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2)))) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_7817,c_8351]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1018,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X1,X0),X2)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8441,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2)))) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X1,X0),X2)) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_8440,c_1018]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8442,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,X0),X2))) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_8441,c_8016]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8597,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK2,X0),k1_xboole_0)))) = k1_xboole_0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_8596,c_842,c_8351,c_8442]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8598,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,X0)) = k1_xboole_0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_8597,c_4,c_5346]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 11.80/1.98      inference(cnf_transformation,[],[f43]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_412,plain,
% 11.80/1.98      ( k3_tarski(k2_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,X1))))) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_7,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_11334,plain,
% 11.80/1.98      ( k3_tarski(k2_enumset1(k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,X0)),k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,X0)),k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,X0)),X1)) = k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k5_xboole_0(sK2,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_8598,c_412]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_11413,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k5_xboole_0(sK2,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_11334,c_8598]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4785,plain,
% 11.80/1.98      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1168,c_7]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_407,plain,
% 11.80/1.98      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_4,c_7]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5339,plain,
% 11.80/1.98      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k1_xboole_0) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4785,c_4,c_407]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5347,plain,
% 11.80/1.98      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_5346,c_5339]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10006,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k5_xboole_0(sK2,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_8598,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10034,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(k5_xboole_0(sK2,X0),X1)) = X1 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_10006,c_4938,c_8351]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_697,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(sK2,X0) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_694,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1271,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),X0),X1)) = k5_xboole_0(k5_xboole_0(sK2,X0),X1) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_697,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_699,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_694,c_0]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_6985,plain,
% 11.80/1.98      ( k3_xboole_0(k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_699,c_365]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_701,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_694,c_1]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4831,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))) = k1_xboole_0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_701,c_1764]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_2473,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)),X0)) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_701,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5309,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_xboole_0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4831,c_2473,c_4938]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7095,plain,
% 11.80/1.98      ( k3_xboole_0(k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))))) = k1_xboole_0 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_6985,c_5309]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_2338,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k5_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0)) = k5_xboole_0(k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_699,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7096,plain,
% 11.80/1.98      ( k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k1_xboole_0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_7095,c_3,c_2338]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7254,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0))) = k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_7096,c_0]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1993,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k1_xboole_0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_5,c_1170]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7266,plain,
% 11.80/1.98      ( k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_7254,c_1993]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10793,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(sK2,X0),X1) ),
% 11.80/1.98      inference(light_normalisation,
% 11.80/1.98                [status(thm)],
% 11.80/1.98                [c_1271,c_1271,c_4938,c_7266]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_11414,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))))) = X1 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_11413,c_5347,c_10034,c_10793]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_11415,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(sK2,k5_xboole_0(X0,X1))) = X1 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_11414,c_4,c_5346]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_13485,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = k2_enumset1(sK0,sK0,sK0,sK1) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_9843,c_11415]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_345,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(X0,X0,X0,sK0))) = sK2
% 11.80/1.98      | r2_hidden(X0,sK2) = iProver_top ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_124,c_122]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_769,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) = sK2 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_345,c_122]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1175,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(sK2,X0) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_769,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7838,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,X0)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1175,c_5358]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8391,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,X0)) = k5_xboole_0(sK2,X0) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_7838,c_1175]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8735,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1))) = k5_xboole_0(k1_xboole_0,sK2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_694,c_8391]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8853,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,sK2) = sK2 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_8735,c_694]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_13579,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = k2_enumset1(sK0,sK0,sK0,sK1) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_13485,c_8853]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_14607,plain,
% 11.80/1.98      ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)))) = k3_xboole_0(sK2,k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_13579,c_0]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7214,plain,
% 11.80/1.98      ( k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0))) = sK2 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_7092,c_3]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7221,plain,
% 11.80/1.98      ( k3_xboole_0(sK2,k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = sK2 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_7214,c_5346]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_14641,plain,
% 11.80/1.98      ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)))) = sK2 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_14607,c_7221]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_406,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,X2))) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_5,c_7]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7545,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_406,c_7]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_14642,plain,
% 11.80/1.98      ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2))))) = sK2 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_14641,c_7545]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_988,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))))))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0),k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0),sK2)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_695,c_6]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10918,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))))),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))))))))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_10793,c_988]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10924,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_10793,c_1089]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10968,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = X0 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_10924,c_4938,c_8391]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10981,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,sK2))))))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_10918,c_10968]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_2697,plain,
% 11.80/1.98      ( k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = sK2 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_764,c_3]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10982,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,sK2))))))) = k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_10981,c_2697,c_7205]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4853,plain,
% 11.80/1.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k1_xboole_0) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1764,c_1089]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5271,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4853,c_3815,c_4938]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4856,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_1764,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5267,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),X2)) = X2 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_4856,c_4938]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5273,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_5271,c_5267]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_409,plain,
% 11.80/1.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X2)) = k5_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_7,c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_9295,plain,
% 11.80/1.98      ( k5_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1))),X0) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0),X0)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_7092,c_409]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_2696,plain,
% 11.80/1.98      ( k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_764,c_7]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7426,plain,
% 11.80/1.98      ( k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_2696,c_2696,c_7205]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_9598,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0),X0)) = k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),X0) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_9295,c_7426]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_9599,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),X0) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_9598,c_4794,c_8351]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_9600,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0)) = k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),X0) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_9599,c_5346]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10983,plain,
% 11.80/1.98      ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2))) ),
% 11.80/1.98      inference(demodulation,
% 11.80/1.98                [status(thm)],
% 11.80/1.98                [c_10982,c_286,c_5273,c_5346,c_7092,c_9600]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10984,plain,
% 11.80/1.98      ( k5_xboole_0(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2))) = k2_enumset1(sK0,sK0,sK0,sK1) ),
% 11.80/1.98      inference(demodulation,
% 11.80/1.98                [status(thm)],
% 11.80/1.98                [c_10983,c_286,c_842,c_5288,c_5346,c_7092]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_14643,plain,
% 11.80/1.98      ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) = sK2 ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_14642,c_10984]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_424,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,X1))))) = k3_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_15237,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1)))) = k3_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_763,c_424]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10665,plain,
% 11.80/1.98      ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1)) = k1_xboole_0 ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_9843,c_1090]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_15516,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k1_xboole_0)) ),
% 11.80/1.98      inference(light_normalisation,
% 11.80/1.98                [status(thm)],
% 11.80/1.98                [c_15237,c_7205,c_10665,c_14643]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8759,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(k5_xboole_0(k1_xboole_0,X0),sK2)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_8391,c_6]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8820,plain,
% 11.80/1.98      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))))))) = k5_xboole_0(X0,k3_xboole_0(X0,sK2)) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_8759,c_4938]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8821,plain,
% 11.80/1.98      ( k5_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))),k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))),X0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))))))) = k5_xboole_0(X0,k3_xboole_0(X0,sK2)) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_8820,c_3813,c_8442,c_8451]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8822,plain,
% 11.80/1.98      ( k5_xboole_0(k3_xboole_0(X0,sK2),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK2),X0),k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))))) = k5_xboole_0(X0,k3_xboole_0(X0,sK2)) ),
% 11.80/1.98      inference(demodulation,
% 11.80/1.98                [status(thm)],
% 11.80/1.98                [c_8821,c_4,c_842,c_5346,c_8016,c_8451]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8823,plain,
% 11.80/1.98      ( k5_xboole_0(k3_xboole_0(X0,sK2),X0) = k5_xboole_0(X0,k3_xboole_0(X0,sK2)) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_8822,c_4,c_842,c_5346]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_11699,plain,
% 11.80/1.98      ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)) ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_7092,c_8823]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_11763,plain,
% 11.80/1.98      ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0) = k2_enumset1(sK0,sK0,sK0,sK1) ),
% 11.80/1.98      inference(light_normalisation,[status(thm)],[c_11699,c_7092,c_9843]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_15517,plain,
% 11.80/1.98      ( k3_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK0,sK0,sK0,sK1) ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_15516,c_8351,c_11763,c_13579]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_22075,plain,
% 11.80/1.98      ( sK2 != sK2 ),
% 11.80/1.98      inference(light_normalisation,
% 11.80/1.98                [status(thm)],
% 11.80/1.98                [c_2709,c_7205,c_14643,c_15517]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_22076,plain,
% 11.80/1.98      ( $false ),
% 11.80/1.98      inference(equality_resolution_simp,[status(thm)],[c_22075]) ).
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.80/1.98  
% 11.80/1.98  ------                               Statistics
% 11.80/1.98  
% 11.80/1.98  ------ General
% 11.80/1.98  
% 11.80/1.98  abstr_ref_over_cycles:                  0
% 11.80/1.98  abstr_ref_under_cycles:                 0
% 11.80/1.98  gc_basic_clause_elim:                   0
% 11.80/1.98  forced_gc_time:                         0
% 11.80/1.98  parsing_time:                           0.008
% 11.80/1.98  unif_index_cands_time:                  0.
% 11.80/1.98  unif_index_add_time:                    0.
% 11.80/1.98  orderings_time:                         0.
% 11.80/1.98  out_proof_time:                         0.015
% 11.80/1.98  total_time:                             1.356
% 11.80/1.98  num_of_symbols:                         40
% 11.80/1.98  num_of_terms:                           59018
% 11.80/1.98  
% 11.80/1.98  ------ Preprocessing
% 11.80/1.98  
% 11.80/1.98  num_of_splits:                          0
% 11.80/1.98  num_of_split_atoms:                     0
% 11.80/1.98  num_of_reused_defs:                     0
% 11.80/1.98  num_eq_ax_congr_red:                    0
% 11.80/1.98  num_of_sem_filtered_clauses:            1
% 11.80/1.98  num_of_subtypes:                        0
% 11.80/1.98  monotx_restored_types:                  0
% 11.80/1.98  sat_num_of_epr_types:                   0
% 11.80/1.98  sat_num_of_non_cyclic_types:            0
% 11.80/1.98  sat_guarded_non_collapsed_types:        0
% 11.80/1.98  num_pure_diseq_elim:                    0
% 11.80/1.98  simp_replaced_by:                       0
% 11.80/1.98  res_preprocessed:                       51
% 11.80/1.98  prep_upred:                             0
% 11.80/1.98  prep_unflattend:                        0
% 11.80/1.98  smt_new_axioms:                         0
% 11.80/1.98  pred_elim_cands:                        1
% 11.80/1.98  pred_elim:                              0
% 11.80/1.98  pred_elim_cl:                           0
% 11.80/1.98  pred_elim_cycles:                       1
% 11.80/1.98  merged_defs:                            0
% 11.80/1.98  merged_defs_ncl:                        0
% 11.80/1.98  bin_hyper_res:                          0
% 11.80/1.98  prep_cycles:                            3
% 11.80/1.98  pred_elim_time:                         0.
% 11.80/1.98  splitting_time:                         0.
% 11.80/1.98  sem_filter_time:                        0.
% 11.80/1.98  monotx_time:                            0.
% 11.80/1.98  subtype_inf_time:                       0.
% 11.80/1.98  
% 11.80/1.98  ------ Problem properties
% 11.80/1.98  
% 11.80/1.98  clauses:                                12
% 11.80/1.98  conjectures:                            3
% 11.80/1.98  epr:                                    2
% 11.80/1.98  horn:                                   11
% 11.80/1.98  ground:                                 3
% 11.80/1.98  unary:                                  11
% 11.80/1.98  binary:                                 0
% 11.80/1.98  lits:                                   14
% 11.80/1.98  lits_eq:                                10
% 11.80/1.98  fd_pure:                                0
% 11.80/1.98  fd_pseudo:                              0
% 11.80/1.98  fd_cond:                                0
% 11.80/1.98  fd_pseudo_cond:                         0
% 11.80/1.98  ac_symbols:                             0
% 11.80/1.98  
% 11.80/1.98  ------ Propositional Solver
% 11.80/1.98  
% 11.80/1.98  prop_solver_calls:                      28
% 11.80/1.98  prop_fast_solver_calls:                 405
% 11.80/1.98  smt_solver_calls:                       0
% 11.80/1.98  smt_fast_solver_calls:                  0
% 11.80/1.98  prop_num_of_clauses:                    7788
% 11.80/1.98  prop_preprocess_simplified:             7299
% 11.80/1.98  prop_fo_subsumed:                       0
% 11.80/1.98  prop_solver_time:                       0.
% 11.80/1.98  smt_solver_time:                        0.
% 11.80/1.98  smt_fast_solver_time:                   0.
% 11.80/1.98  prop_fast_solver_time:                  0.
% 11.80/1.98  prop_unsat_core_time:                   0.
% 11.80/1.98  
% 11.80/1.98  ------ QBF
% 11.80/1.98  
% 11.80/1.98  qbf_q_res:                              0
% 11.80/1.98  qbf_num_tautologies:                    0
% 11.80/1.98  qbf_prep_cycles:                        0
% 11.80/1.98  
% 11.80/1.98  ------ BMC1
% 11.80/1.98  
% 11.80/1.98  bmc1_current_bound:                     -1
% 11.80/1.98  bmc1_last_solved_bound:                 -1
% 11.80/1.98  bmc1_unsat_core_size:                   -1
% 11.80/1.98  bmc1_unsat_core_parents_size:           -1
% 11.80/1.98  bmc1_merge_next_fun:                    0
% 11.80/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.80/1.98  
% 11.80/1.98  ------ Instantiation
% 11.80/1.98  
% 11.80/1.98  inst_num_of_clauses:                    1585
% 11.80/1.98  inst_num_in_passive:                    147
% 11.80/1.98  inst_num_in_active:                     674
% 11.80/1.98  inst_num_in_unprocessed:                764
% 11.80/1.98  inst_num_of_loops:                      750
% 11.80/1.98  inst_num_of_learning_restarts:          0
% 11.80/1.98  inst_num_moves_active_passive:          72
% 11.80/1.98  inst_lit_activity:                      0
% 11.80/1.98  inst_lit_activity_moves:                0
% 11.80/1.98  inst_num_tautologies:                   0
% 11.80/1.98  inst_num_prop_implied:                  0
% 11.80/1.98  inst_num_existing_simplified:           0
% 11.80/1.98  inst_num_eq_res_simplified:             0
% 11.80/1.98  inst_num_child_elim:                    0
% 11.80/1.98  inst_num_of_dismatching_blockings:      455
% 11.80/1.98  inst_num_of_non_proper_insts:           1526
% 11.80/1.98  inst_num_of_duplicates:                 0
% 11.80/1.98  inst_inst_num_from_inst_to_res:         0
% 11.80/1.98  inst_dismatching_checking_time:         0.
% 11.80/1.98  
% 11.80/1.98  ------ Resolution
% 11.80/1.98  
% 11.80/1.98  res_num_of_clauses:                     0
% 11.80/1.98  res_num_in_passive:                     0
% 11.80/1.98  res_num_in_active:                      0
% 11.80/1.98  res_num_of_loops:                       54
% 11.80/1.98  res_forward_subset_subsumed:            316
% 11.80/1.98  res_backward_subset_subsumed:           0
% 11.80/1.98  res_forward_subsumed:                   0
% 11.80/1.98  res_backward_subsumed:                  0
% 11.80/1.98  res_forward_subsumption_resolution:     0
% 11.80/1.98  res_backward_subsumption_resolution:    0
% 11.80/1.98  res_clause_to_clause_subsumption:       14160
% 11.80/1.98  res_orphan_elimination:                 0
% 11.80/1.98  res_tautology_del:                      96
% 11.80/1.98  res_num_eq_res_simplified:              0
% 11.80/1.98  res_num_sel_changes:                    0
% 11.80/1.98  res_moves_from_active_to_pass:          0
% 11.80/1.98  
% 11.80/1.98  ------ Superposition
% 11.80/1.98  
% 11.80/1.98  sup_time_total:                         0.
% 11.80/1.98  sup_time_generating:                    0.
% 11.80/1.98  sup_time_sim_full:                      0.
% 11.80/1.98  sup_time_sim_immed:                     0.
% 11.80/1.98  
% 11.80/1.98  sup_num_of_clauses:                     2075
% 11.80/1.98  sup_num_in_active:                      103
% 11.80/1.98  sup_num_in_passive:                     1972
% 11.80/1.98  sup_num_of_loops:                       149
% 11.80/1.98  sup_fw_superposition:                   3587
% 11.80/1.98  sup_bw_superposition:                   2469
% 11.80/1.98  sup_immediate_simplified:               4281
% 11.80/1.98  sup_given_eliminated:                   11
% 11.80/1.98  comparisons_done:                       0
% 11.80/1.98  comparisons_avoided:                    0
% 11.80/1.98  
% 11.80/1.98  ------ Simplifications
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  sim_fw_subset_subsumed:                 0
% 11.80/1.98  sim_bw_subset_subsumed:                 0
% 11.80/1.98  sim_fw_subsumed:                        358
% 11.80/1.98  sim_bw_subsumed:                        84
% 11.80/1.98  sim_fw_subsumption_res:                 0
% 11.80/1.98  sim_bw_subsumption_res:                 0
% 11.80/1.98  sim_tautology_del:                      0
% 11.80/1.98  sim_eq_tautology_del:                   1418
% 11.80/1.98  sim_eq_res_simp:                        1
% 11.80/1.98  sim_fw_demodulated:                     4572
% 11.80/1.98  sim_bw_demodulated:                     270
% 11.80/1.98  sim_light_normalised:                   2199
% 11.80/1.98  sim_joinable_taut:                      0
% 11.80/1.98  sim_joinable_simp:                      0
% 11.80/1.98  sim_ac_normalised:                      0
% 11.80/1.98  sim_smt_subsumption:                    0
% 11.80/1.98  
%------------------------------------------------------------------------------
