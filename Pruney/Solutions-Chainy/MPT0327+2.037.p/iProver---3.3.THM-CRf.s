%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:03 EST 2020

% Result     : Theorem 7.89s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  150 (4856 expanded)
%              Number of clauses        :   88 (1322 expanded)
%              Number of leaves         :   20 (1264 expanded)
%              Depth                    :   31
%              Number of atoms          :  191 (7072 expanded)
%              Number of equality atoms :  142 (4633 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f41,f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f42,f41,f41])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f40,f55,f55])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f55,f57])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).

fof(f53,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(definition_unfolding,[],[f54,f55,f58,f58])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_10,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_968,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_10])).

cnf(c_5576,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_968,c_10])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1010,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_14,c_12])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_793,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_1012,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_1010,c_793])).

cnf(c_1013,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_1012,c_14])).

cnf(c_1082,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_9,c_9,c_1013])).

cnf(c_17786,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1))))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5576,c_1082])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_481,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_478,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_861,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_481,c_478])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_480,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2305,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_481,c_480])).

cnf(c_4189,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_861,c_861,c_2305])).

cnf(c_981,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_12589,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_4189,c_981])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_871,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11,c_12])).

cnf(c_1723,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_871])).

cnf(c_2504,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1723,c_0])).

cnf(c_2533,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2504,c_1723])).

cnf(c_2534,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_2533,c_2504])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_158,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_159,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_475,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_2308,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_480])).

cnf(c_864,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_475,c_478])).

cnf(c_1209,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_864,c_1])).

cnf(c_1218,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0) ),
    inference(superposition,[status(thm)],[c_1209,c_10])).

cnf(c_2688,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2308,c_1218])).

cnf(c_2691,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2688,c_2308])).

cnf(c_2809,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2691,c_10])).

cnf(c_791,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_3562,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK1)) ),
    inference(superposition,[status(thm)],[c_2809,c_791])).

cnf(c_3564,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK1) ),
    inference(superposition,[status(thm)],[c_2809,c_793])).

cnf(c_1000,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_11,c_14])).

cnf(c_1112,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1000,c_0,c_1012])).

cnf(c_2511,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1723,c_1112])).

cnf(c_8,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_477,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2306,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_477,c_480])).

cnf(c_2512,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2511,c_2306])).

cnf(c_3571,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3564,c_2512])).

cnf(c_3574,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3562,c_3571])).

cnf(c_3575,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3574,c_11,c_2305,c_2306])).

cnf(c_13112,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12589,c_10,c_2534,c_3575])).

cnf(c_13532,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_13112])).

cnf(c_971,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2) ),
    inference(superposition,[status(thm)],[c_1,c_10])).

cnf(c_10106,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(superposition,[status(thm)],[c_3575,c_971])).

cnf(c_10371,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_10106,c_4189])).

cnf(c_10372,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_10371,c_3575,c_4189])).

cnf(c_10234,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_971,c_4189])).

cnf(c_10298,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_10234,c_4189])).

cnf(c_10374,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_10372,c_10298])).

cnf(c_13709,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13532,c_10374])).

cnf(c_17953,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1))))) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_17786,c_13709])).

cnf(c_5531,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) ),
    inference(superposition,[status(thm)],[c_968,c_1])).

cnf(c_5634,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_5531,c_10])).

cnf(c_5530,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_968,c_793])).

cnf(c_5636,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_5530,c_10])).

cnf(c_10456,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_10374,c_971])).

cnf(c_17954,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_17953,c_11,c_5634,c_5636,c_10456])).

cnf(c_20656,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_17954,c_793])).

cnf(c_20759,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_20656,c_11,c_13709])).

cnf(c_16,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_787,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_1,c_16])).

cnf(c_1002,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_14])).

cnf(c_1110,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1002,c_1012])).

cnf(c_1130,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_787,c_1110])).

cnf(c_20913,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != sK1 ),
    inference(demodulation,[status(thm)],[c_20759,c_1130])).

cnf(c_7517,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_1209,c_1013])).

cnf(c_1219,plain,
    ( k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_1209,c_0])).

cnf(c_7585,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7517,c_1219,c_2308])).

cnf(c_1567,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0) ),
    inference(superposition,[status(thm)],[c_1219,c_12])).

cnf(c_7586,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_7585,c_11,c_1567])).

cnf(c_20914,plain,
    ( sK1 != sK1 ),
    inference(light_normalisation,[status(thm)],[c_20913,c_7586])).

cnf(c_20915,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_20914])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.89/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.89/1.49  
% 7.89/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.89/1.49  
% 7.89/1.49  ------  iProver source info
% 7.89/1.49  
% 7.89/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.89/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.89/1.49  git: non_committed_changes: false
% 7.89/1.49  git: last_make_outside_of_git: false
% 7.89/1.49  
% 7.89/1.49  ------ 
% 7.89/1.49  
% 7.89/1.49  ------ Input Options
% 7.89/1.49  
% 7.89/1.49  --out_options                           all
% 7.89/1.49  --tptp_safe_out                         true
% 7.89/1.49  --problem_path                          ""
% 7.89/1.49  --include_path                          ""
% 7.89/1.49  --clausifier                            res/vclausify_rel
% 7.89/1.49  --clausifier_options                    ""
% 7.89/1.49  --stdin                                 false
% 7.89/1.49  --stats_out                             all
% 7.89/1.49  
% 7.89/1.49  ------ General Options
% 7.89/1.49  
% 7.89/1.49  --fof                                   false
% 7.89/1.49  --time_out_real                         305.
% 7.89/1.49  --time_out_virtual                      -1.
% 7.89/1.49  --symbol_type_check                     false
% 7.89/1.49  --clausify_out                          false
% 7.89/1.49  --sig_cnt_out                           false
% 7.89/1.49  --trig_cnt_out                          false
% 7.89/1.49  --trig_cnt_out_tolerance                1.
% 7.89/1.49  --trig_cnt_out_sk_spl                   false
% 7.89/1.49  --abstr_cl_out                          false
% 7.89/1.49  
% 7.89/1.49  ------ Global Options
% 7.89/1.49  
% 7.89/1.49  --schedule                              default
% 7.89/1.49  --add_important_lit                     false
% 7.89/1.49  --prop_solver_per_cl                    1000
% 7.89/1.49  --min_unsat_core                        false
% 7.89/1.49  --soft_assumptions                      false
% 7.89/1.49  --soft_lemma_size                       3
% 7.89/1.49  --prop_impl_unit_size                   0
% 7.89/1.49  --prop_impl_unit                        []
% 7.89/1.49  --share_sel_clauses                     true
% 7.89/1.49  --reset_solvers                         false
% 7.89/1.49  --bc_imp_inh                            [conj_cone]
% 7.89/1.49  --conj_cone_tolerance                   3.
% 7.89/1.49  --extra_neg_conj                        none
% 7.89/1.49  --large_theory_mode                     true
% 7.89/1.49  --prolific_symb_bound                   200
% 7.89/1.49  --lt_threshold                          2000
% 7.89/1.49  --clause_weak_htbl                      true
% 7.89/1.49  --gc_record_bc_elim                     false
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing Options
% 7.89/1.49  
% 7.89/1.49  --preprocessing_flag                    true
% 7.89/1.49  --time_out_prep_mult                    0.1
% 7.89/1.49  --splitting_mode                        input
% 7.89/1.49  --splitting_grd                         true
% 7.89/1.49  --splitting_cvd                         false
% 7.89/1.49  --splitting_cvd_svl                     false
% 7.89/1.49  --splitting_nvd                         32
% 7.89/1.49  --sub_typing                            true
% 7.89/1.49  --prep_gs_sim                           true
% 7.89/1.49  --prep_unflatten                        true
% 7.89/1.49  --prep_res_sim                          true
% 7.89/1.49  --prep_upred                            true
% 7.89/1.49  --prep_sem_filter                       exhaustive
% 7.89/1.49  --prep_sem_filter_out                   false
% 7.89/1.49  --pred_elim                             true
% 7.89/1.49  --res_sim_input                         true
% 7.89/1.49  --eq_ax_congr_red                       true
% 7.89/1.49  --pure_diseq_elim                       true
% 7.89/1.49  --brand_transform                       false
% 7.89/1.49  --non_eq_to_eq                          false
% 7.89/1.49  --prep_def_merge                        true
% 7.89/1.49  --prep_def_merge_prop_impl              false
% 7.89/1.49  --prep_def_merge_mbd                    true
% 7.89/1.49  --prep_def_merge_tr_red                 false
% 7.89/1.49  --prep_def_merge_tr_cl                  false
% 7.89/1.49  --smt_preprocessing                     true
% 7.89/1.49  --smt_ac_axioms                         fast
% 7.89/1.49  --preprocessed_out                      false
% 7.89/1.49  --preprocessed_stats                    false
% 7.89/1.49  
% 7.89/1.49  ------ Abstraction refinement Options
% 7.89/1.49  
% 7.89/1.49  --abstr_ref                             []
% 7.89/1.49  --abstr_ref_prep                        false
% 7.89/1.49  --abstr_ref_until_sat                   false
% 7.89/1.49  --abstr_ref_sig_restrict                funpre
% 7.89/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.89/1.49  --abstr_ref_under                       []
% 7.89/1.49  
% 7.89/1.49  ------ SAT Options
% 7.89/1.49  
% 7.89/1.49  --sat_mode                              false
% 7.89/1.49  --sat_fm_restart_options                ""
% 7.89/1.49  --sat_gr_def                            false
% 7.89/1.49  --sat_epr_types                         true
% 7.89/1.49  --sat_non_cyclic_types                  false
% 7.89/1.49  --sat_finite_models                     false
% 7.89/1.49  --sat_fm_lemmas                         false
% 7.89/1.49  --sat_fm_prep                           false
% 7.89/1.49  --sat_fm_uc_incr                        true
% 7.89/1.49  --sat_out_model                         small
% 7.89/1.49  --sat_out_clauses                       false
% 7.89/1.49  
% 7.89/1.49  ------ QBF Options
% 7.89/1.49  
% 7.89/1.49  --qbf_mode                              false
% 7.89/1.49  --qbf_elim_univ                         false
% 7.89/1.49  --qbf_dom_inst                          none
% 7.89/1.49  --qbf_dom_pre_inst                      false
% 7.89/1.49  --qbf_sk_in                             false
% 7.89/1.49  --qbf_pred_elim                         true
% 7.89/1.49  --qbf_split                             512
% 7.89/1.49  
% 7.89/1.49  ------ BMC1 Options
% 7.89/1.49  
% 7.89/1.49  --bmc1_incremental                      false
% 7.89/1.49  --bmc1_axioms                           reachable_all
% 7.89/1.49  --bmc1_min_bound                        0
% 7.89/1.49  --bmc1_max_bound                        -1
% 7.89/1.49  --bmc1_max_bound_default                -1
% 7.89/1.49  --bmc1_symbol_reachability              true
% 7.89/1.49  --bmc1_property_lemmas                  false
% 7.89/1.49  --bmc1_k_induction                      false
% 7.89/1.49  --bmc1_non_equiv_states                 false
% 7.89/1.49  --bmc1_deadlock                         false
% 7.89/1.49  --bmc1_ucm                              false
% 7.89/1.49  --bmc1_add_unsat_core                   none
% 7.89/1.49  --bmc1_unsat_core_children              false
% 7.89/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.89/1.49  --bmc1_out_stat                         full
% 7.89/1.49  --bmc1_ground_init                      false
% 7.89/1.49  --bmc1_pre_inst_next_state              false
% 7.89/1.49  --bmc1_pre_inst_state                   false
% 7.89/1.49  --bmc1_pre_inst_reach_state             false
% 7.89/1.49  --bmc1_out_unsat_core                   false
% 7.89/1.49  --bmc1_aig_witness_out                  false
% 7.89/1.49  --bmc1_verbose                          false
% 7.89/1.49  --bmc1_dump_clauses_tptp                false
% 7.89/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.89/1.49  --bmc1_dump_file                        -
% 7.89/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.89/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.89/1.49  --bmc1_ucm_extend_mode                  1
% 7.89/1.49  --bmc1_ucm_init_mode                    2
% 7.89/1.49  --bmc1_ucm_cone_mode                    none
% 7.89/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.89/1.49  --bmc1_ucm_relax_model                  4
% 7.89/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.89/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.89/1.49  --bmc1_ucm_layered_model                none
% 7.89/1.49  --bmc1_ucm_max_lemma_size               10
% 7.89/1.49  
% 7.89/1.49  ------ AIG Options
% 7.89/1.49  
% 7.89/1.49  --aig_mode                              false
% 7.89/1.49  
% 7.89/1.49  ------ Instantiation Options
% 7.89/1.49  
% 7.89/1.49  --instantiation_flag                    true
% 7.89/1.49  --inst_sos_flag                         true
% 7.89/1.49  --inst_sos_phase                        true
% 7.89/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.89/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.89/1.49  --inst_lit_sel_side                     num_symb
% 7.89/1.49  --inst_solver_per_active                1400
% 7.89/1.49  --inst_solver_calls_frac                1.
% 7.89/1.49  --inst_passive_queue_type               priority_queues
% 7.89/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.89/1.49  --inst_passive_queues_freq              [25;2]
% 7.89/1.49  --inst_dismatching                      true
% 7.89/1.49  --inst_eager_unprocessed_to_passive     true
% 7.89/1.49  --inst_prop_sim_given                   true
% 7.89/1.49  --inst_prop_sim_new                     false
% 7.89/1.49  --inst_subs_new                         false
% 7.89/1.49  --inst_eq_res_simp                      false
% 7.89/1.49  --inst_subs_given                       false
% 7.89/1.49  --inst_orphan_elimination               true
% 7.89/1.49  --inst_learning_loop_flag               true
% 7.89/1.49  --inst_learning_start                   3000
% 7.89/1.49  --inst_learning_factor                  2
% 7.89/1.49  --inst_start_prop_sim_after_learn       3
% 7.89/1.49  --inst_sel_renew                        solver
% 7.89/1.49  --inst_lit_activity_flag                true
% 7.89/1.49  --inst_restr_to_given                   false
% 7.89/1.49  --inst_activity_threshold               500
% 7.89/1.49  --inst_out_proof                        true
% 7.89/1.49  
% 7.89/1.49  ------ Resolution Options
% 7.89/1.49  
% 7.89/1.49  --resolution_flag                       true
% 7.89/1.49  --res_lit_sel                           adaptive
% 7.89/1.49  --res_lit_sel_side                      none
% 7.89/1.49  --res_ordering                          kbo
% 7.89/1.49  --res_to_prop_solver                    active
% 7.89/1.49  --res_prop_simpl_new                    false
% 7.89/1.49  --res_prop_simpl_given                  true
% 7.89/1.49  --res_passive_queue_type                priority_queues
% 7.89/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.89/1.49  --res_passive_queues_freq               [15;5]
% 7.89/1.49  --res_forward_subs                      full
% 7.89/1.49  --res_backward_subs                     full
% 7.89/1.49  --res_forward_subs_resolution           true
% 7.89/1.49  --res_backward_subs_resolution          true
% 7.89/1.49  --res_orphan_elimination                true
% 7.89/1.49  --res_time_limit                        2.
% 7.89/1.49  --res_out_proof                         true
% 7.89/1.49  
% 7.89/1.49  ------ Superposition Options
% 7.89/1.49  
% 7.89/1.49  --superposition_flag                    true
% 7.89/1.49  --sup_passive_queue_type                priority_queues
% 7.89/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.89/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.89/1.49  --demod_completeness_check              fast
% 7.89/1.49  --demod_use_ground                      true
% 7.89/1.49  --sup_to_prop_solver                    passive
% 7.89/1.49  --sup_prop_simpl_new                    true
% 7.89/1.49  --sup_prop_simpl_given                  true
% 7.89/1.49  --sup_fun_splitting                     true
% 7.89/1.49  --sup_smt_interval                      50000
% 7.89/1.49  
% 7.89/1.49  ------ Superposition Simplification Setup
% 7.89/1.49  
% 7.89/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.89/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.89/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.89/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.89/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.89/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.89/1.49  --sup_immed_triv                        [TrivRules]
% 7.89/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.49  --sup_immed_bw_main                     []
% 7.89/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.89/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.89/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.49  --sup_input_bw                          []
% 7.89/1.49  
% 7.89/1.49  ------ Combination Options
% 7.89/1.49  
% 7.89/1.49  --comb_res_mult                         3
% 7.89/1.49  --comb_sup_mult                         2
% 7.89/1.49  --comb_inst_mult                        10
% 7.89/1.49  
% 7.89/1.49  ------ Debug Options
% 7.89/1.49  
% 7.89/1.49  --dbg_backtrace                         false
% 7.89/1.49  --dbg_dump_prop_clauses                 false
% 7.89/1.49  --dbg_dump_prop_clauses_file            -
% 7.89/1.49  --dbg_out_stat                          false
% 7.89/1.49  ------ Parsing...
% 7.89/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.49  ------ Proving...
% 7.89/1.49  ------ Problem Properties 
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  clauses                                 16
% 7.89/1.49  conjectures                             1
% 7.89/1.49  EPR                                     2
% 7.89/1.49  Horn                                    16
% 7.89/1.49  unary                                   12
% 7.89/1.49  binary                                  3
% 7.89/1.49  lits                                    21
% 7.89/1.49  lits eq                                 12
% 7.89/1.49  fd_pure                                 0
% 7.89/1.49  fd_pseudo                               0
% 7.89/1.49  fd_cond                                 0
% 7.89/1.49  fd_pseudo_cond                          1
% 7.89/1.49  AC symbols                              0
% 7.89/1.49  
% 7.89/1.49  ------ Schedule dynamic 5 is on 
% 7.89/1.49  
% 7.89/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  ------ 
% 7.89/1.49  Current options:
% 7.89/1.49  ------ 
% 7.89/1.49  
% 7.89/1.49  ------ Input Options
% 7.89/1.49  
% 7.89/1.49  --out_options                           all
% 7.89/1.49  --tptp_safe_out                         true
% 7.89/1.49  --problem_path                          ""
% 7.89/1.49  --include_path                          ""
% 7.89/1.49  --clausifier                            res/vclausify_rel
% 7.89/1.49  --clausifier_options                    ""
% 7.89/1.49  --stdin                                 false
% 7.89/1.49  --stats_out                             all
% 7.89/1.49  
% 7.89/1.49  ------ General Options
% 7.89/1.49  
% 7.89/1.49  --fof                                   false
% 7.89/1.49  --time_out_real                         305.
% 7.89/1.49  --time_out_virtual                      -1.
% 7.89/1.49  --symbol_type_check                     false
% 7.89/1.49  --clausify_out                          false
% 7.89/1.49  --sig_cnt_out                           false
% 7.89/1.49  --trig_cnt_out                          false
% 7.89/1.49  --trig_cnt_out_tolerance                1.
% 7.89/1.49  --trig_cnt_out_sk_spl                   false
% 7.89/1.49  --abstr_cl_out                          false
% 7.89/1.49  
% 7.89/1.49  ------ Global Options
% 7.89/1.49  
% 7.89/1.49  --schedule                              default
% 7.89/1.49  --add_important_lit                     false
% 7.89/1.49  --prop_solver_per_cl                    1000
% 7.89/1.49  --min_unsat_core                        false
% 7.89/1.49  --soft_assumptions                      false
% 7.89/1.49  --soft_lemma_size                       3
% 7.89/1.49  --prop_impl_unit_size                   0
% 7.89/1.49  --prop_impl_unit                        []
% 7.89/1.49  --share_sel_clauses                     true
% 7.89/1.49  --reset_solvers                         false
% 7.89/1.49  --bc_imp_inh                            [conj_cone]
% 7.89/1.49  --conj_cone_tolerance                   3.
% 7.89/1.49  --extra_neg_conj                        none
% 7.89/1.49  --large_theory_mode                     true
% 7.89/1.49  --prolific_symb_bound                   200
% 7.89/1.49  --lt_threshold                          2000
% 7.89/1.49  --clause_weak_htbl                      true
% 7.89/1.49  --gc_record_bc_elim                     false
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing Options
% 7.89/1.49  
% 7.89/1.49  --preprocessing_flag                    true
% 7.89/1.49  --time_out_prep_mult                    0.1
% 7.89/1.49  --splitting_mode                        input
% 7.89/1.49  --splitting_grd                         true
% 7.89/1.49  --splitting_cvd                         false
% 7.89/1.49  --splitting_cvd_svl                     false
% 7.89/1.49  --splitting_nvd                         32
% 7.89/1.49  --sub_typing                            true
% 7.89/1.49  --prep_gs_sim                           true
% 7.89/1.49  --prep_unflatten                        true
% 7.89/1.49  --prep_res_sim                          true
% 7.89/1.49  --prep_upred                            true
% 7.89/1.49  --prep_sem_filter                       exhaustive
% 7.89/1.49  --prep_sem_filter_out                   false
% 7.89/1.49  --pred_elim                             true
% 7.89/1.49  --res_sim_input                         true
% 7.89/1.49  --eq_ax_congr_red                       true
% 7.89/1.49  --pure_diseq_elim                       true
% 7.89/1.49  --brand_transform                       false
% 7.89/1.49  --non_eq_to_eq                          false
% 7.89/1.49  --prep_def_merge                        true
% 7.89/1.49  --prep_def_merge_prop_impl              false
% 7.89/1.49  --prep_def_merge_mbd                    true
% 7.89/1.49  --prep_def_merge_tr_red                 false
% 7.89/1.49  --prep_def_merge_tr_cl                  false
% 7.89/1.49  --smt_preprocessing                     true
% 7.89/1.49  --smt_ac_axioms                         fast
% 7.89/1.49  --preprocessed_out                      false
% 7.89/1.49  --preprocessed_stats                    false
% 7.89/1.49  
% 7.89/1.49  ------ Abstraction refinement Options
% 7.89/1.49  
% 7.89/1.49  --abstr_ref                             []
% 7.89/1.49  --abstr_ref_prep                        false
% 7.89/1.49  --abstr_ref_until_sat                   false
% 7.89/1.49  --abstr_ref_sig_restrict                funpre
% 7.89/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.89/1.49  --abstr_ref_under                       []
% 7.89/1.49  
% 7.89/1.49  ------ SAT Options
% 7.89/1.49  
% 7.89/1.49  --sat_mode                              false
% 7.89/1.49  --sat_fm_restart_options                ""
% 7.89/1.49  --sat_gr_def                            false
% 7.89/1.49  --sat_epr_types                         true
% 7.89/1.49  --sat_non_cyclic_types                  false
% 7.89/1.49  --sat_finite_models                     false
% 7.89/1.49  --sat_fm_lemmas                         false
% 7.89/1.49  --sat_fm_prep                           false
% 7.89/1.49  --sat_fm_uc_incr                        true
% 7.89/1.49  --sat_out_model                         small
% 7.89/1.49  --sat_out_clauses                       false
% 7.89/1.49  
% 7.89/1.49  ------ QBF Options
% 7.89/1.49  
% 7.89/1.49  --qbf_mode                              false
% 7.89/1.49  --qbf_elim_univ                         false
% 7.89/1.49  --qbf_dom_inst                          none
% 7.89/1.49  --qbf_dom_pre_inst                      false
% 7.89/1.49  --qbf_sk_in                             false
% 7.89/1.49  --qbf_pred_elim                         true
% 7.89/1.49  --qbf_split                             512
% 7.89/1.49  
% 7.89/1.49  ------ BMC1 Options
% 7.89/1.49  
% 7.89/1.49  --bmc1_incremental                      false
% 7.89/1.49  --bmc1_axioms                           reachable_all
% 7.89/1.49  --bmc1_min_bound                        0
% 7.89/1.49  --bmc1_max_bound                        -1
% 7.89/1.49  --bmc1_max_bound_default                -1
% 7.89/1.49  --bmc1_symbol_reachability              true
% 7.89/1.49  --bmc1_property_lemmas                  false
% 7.89/1.49  --bmc1_k_induction                      false
% 7.89/1.49  --bmc1_non_equiv_states                 false
% 7.89/1.49  --bmc1_deadlock                         false
% 7.89/1.49  --bmc1_ucm                              false
% 7.89/1.49  --bmc1_add_unsat_core                   none
% 7.89/1.49  --bmc1_unsat_core_children              false
% 7.89/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.89/1.49  --bmc1_out_stat                         full
% 7.89/1.49  --bmc1_ground_init                      false
% 7.89/1.49  --bmc1_pre_inst_next_state              false
% 7.89/1.49  --bmc1_pre_inst_state                   false
% 7.89/1.49  --bmc1_pre_inst_reach_state             false
% 7.89/1.49  --bmc1_out_unsat_core                   false
% 7.89/1.49  --bmc1_aig_witness_out                  false
% 7.89/1.49  --bmc1_verbose                          false
% 7.89/1.49  --bmc1_dump_clauses_tptp                false
% 7.89/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.89/1.49  --bmc1_dump_file                        -
% 7.89/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.89/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.89/1.49  --bmc1_ucm_extend_mode                  1
% 7.89/1.49  --bmc1_ucm_init_mode                    2
% 7.89/1.49  --bmc1_ucm_cone_mode                    none
% 7.89/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.89/1.49  --bmc1_ucm_relax_model                  4
% 7.89/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.89/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.89/1.49  --bmc1_ucm_layered_model                none
% 7.89/1.49  --bmc1_ucm_max_lemma_size               10
% 7.89/1.49  
% 7.89/1.49  ------ AIG Options
% 7.89/1.49  
% 7.89/1.49  --aig_mode                              false
% 7.89/1.49  
% 7.89/1.49  ------ Instantiation Options
% 7.89/1.49  
% 7.89/1.49  --instantiation_flag                    true
% 7.89/1.49  --inst_sos_flag                         true
% 7.89/1.49  --inst_sos_phase                        true
% 7.89/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.89/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.89/1.49  --inst_lit_sel_side                     none
% 7.89/1.49  --inst_solver_per_active                1400
% 7.89/1.49  --inst_solver_calls_frac                1.
% 7.89/1.49  --inst_passive_queue_type               priority_queues
% 7.89/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.89/1.49  --inst_passive_queues_freq              [25;2]
% 7.89/1.49  --inst_dismatching                      true
% 7.89/1.49  --inst_eager_unprocessed_to_passive     true
% 7.89/1.49  --inst_prop_sim_given                   true
% 7.89/1.49  --inst_prop_sim_new                     false
% 7.89/1.49  --inst_subs_new                         false
% 7.89/1.49  --inst_eq_res_simp                      false
% 7.89/1.49  --inst_subs_given                       false
% 7.89/1.49  --inst_orphan_elimination               true
% 7.89/1.49  --inst_learning_loop_flag               true
% 7.89/1.49  --inst_learning_start                   3000
% 7.89/1.49  --inst_learning_factor                  2
% 7.89/1.49  --inst_start_prop_sim_after_learn       3
% 7.89/1.49  --inst_sel_renew                        solver
% 7.89/1.49  --inst_lit_activity_flag                true
% 7.89/1.49  --inst_restr_to_given                   false
% 7.89/1.49  --inst_activity_threshold               500
% 7.89/1.49  --inst_out_proof                        true
% 7.89/1.49  
% 7.89/1.49  ------ Resolution Options
% 7.89/1.49  
% 7.89/1.49  --resolution_flag                       false
% 7.89/1.49  --res_lit_sel                           adaptive
% 7.89/1.49  --res_lit_sel_side                      none
% 7.89/1.49  --res_ordering                          kbo
% 7.89/1.49  --res_to_prop_solver                    active
% 7.89/1.49  --res_prop_simpl_new                    false
% 7.89/1.49  --res_prop_simpl_given                  true
% 7.89/1.49  --res_passive_queue_type                priority_queues
% 7.89/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.89/1.49  --res_passive_queues_freq               [15;5]
% 7.89/1.49  --res_forward_subs                      full
% 7.89/1.49  --res_backward_subs                     full
% 7.89/1.49  --res_forward_subs_resolution           true
% 7.89/1.49  --res_backward_subs_resolution          true
% 7.89/1.49  --res_orphan_elimination                true
% 7.89/1.49  --res_time_limit                        2.
% 7.89/1.49  --res_out_proof                         true
% 7.89/1.49  
% 7.89/1.49  ------ Superposition Options
% 7.89/1.49  
% 7.89/1.49  --superposition_flag                    true
% 7.89/1.49  --sup_passive_queue_type                priority_queues
% 7.89/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.89/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.89/1.49  --demod_completeness_check              fast
% 7.89/1.49  --demod_use_ground                      true
% 7.89/1.49  --sup_to_prop_solver                    passive
% 7.89/1.49  --sup_prop_simpl_new                    true
% 7.89/1.49  --sup_prop_simpl_given                  true
% 7.89/1.49  --sup_fun_splitting                     true
% 7.89/1.49  --sup_smt_interval                      50000
% 7.89/1.49  
% 7.89/1.49  ------ Superposition Simplification Setup
% 7.89/1.49  
% 7.89/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.89/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.89/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.89/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.89/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.89/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.89/1.49  --sup_immed_triv                        [TrivRules]
% 7.89/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.49  --sup_immed_bw_main                     []
% 7.89/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.89/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.89/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.49  --sup_input_bw                          []
% 7.89/1.49  
% 7.89/1.49  ------ Combination Options
% 7.89/1.49  
% 7.89/1.49  --comb_res_mult                         3
% 7.89/1.49  --comb_sup_mult                         2
% 7.89/1.49  --comb_inst_mult                        10
% 7.89/1.49  
% 7.89/1.49  ------ Debug Options
% 7.89/1.49  
% 7.89/1.49  --dbg_backtrace                         false
% 7.89/1.49  --dbg_dump_prop_clauses                 false
% 7.89/1.49  --dbg_dump_prop_clauses_file            -
% 7.89/1.49  --dbg_out_stat                          false
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  ------ Proving...
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  % SZS status Theorem for theBenchmark.p
% 7.89/1.49  
% 7.89/1.49   Resolution empty clause
% 7.89/1.49  
% 7.89/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.89/1.49  
% 7.89/1.49  fof(f1,axiom,(
% 7.89/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f31,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f1])).
% 7.89/1.49  
% 7.89/1.49  fof(f8,axiom,(
% 7.89/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f41,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.89/1.49    inference(cnf_transformation,[],[f8])).
% 7.89/1.49  
% 7.89/1.49  fof(f60,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.89/1.49    inference(definition_unfolding,[],[f31,f41,f41])).
% 7.89/1.49  
% 7.89/1.49  fof(f9,axiom,(
% 7.89/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f42,plain,(
% 7.89/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f9])).
% 7.89/1.49  
% 7.89/1.49  fof(f63,plain,(
% 7.89/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.89/1.49    inference(definition_unfolding,[],[f42,f41,f41])).
% 7.89/1.49  
% 7.89/1.49  fof(f7,axiom,(
% 7.89/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f40,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.89/1.49    inference(cnf_transformation,[],[f7])).
% 7.89/1.49  
% 7.89/1.49  fof(f12,axiom,(
% 7.89/1.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f45,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f12])).
% 7.89/1.49  
% 7.89/1.49  fof(f55,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1)) )),
% 7.89/1.49    inference(definition_unfolding,[],[f45,f41])).
% 7.89/1.49  
% 7.89/1.49  fof(f62,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 7.89/1.49    inference(definition_unfolding,[],[f40,f55,f55])).
% 7.89/1.49  
% 7.89/1.49  fof(f18,axiom,(
% 7.89/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f51,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.89/1.49    inference(cnf_transformation,[],[f18])).
% 7.89/1.49  
% 7.89/1.49  fof(f14,axiom,(
% 7.89/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f47,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f14])).
% 7.89/1.49  
% 7.89/1.49  fof(f15,axiom,(
% 7.89/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f48,plain,(
% 7.89/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f15])).
% 7.89/1.49  
% 7.89/1.49  fof(f16,axiom,(
% 7.89/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f49,plain,(
% 7.89/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f16])).
% 7.89/1.49  
% 7.89/1.49  fof(f56,plain,(
% 7.89/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.89/1.49    inference(definition_unfolding,[],[f48,f49])).
% 7.89/1.49  
% 7.89/1.49  fof(f57,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.89/1.49    inference(definition_unfolding,[],[f47,f56])).
% 7.89/1.49  
% 7.89/1.49  fof(f65,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 7.89/1.49    inference(definition_unfolding,[],[f51,f55,f57])).
% 7.89/1.49  
% 7.89/1.49  fof(f11,axiom,(
% 7.89/1.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f44,plain,(
% 7.89/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f11])).
% 7.89/1.49  
% 7.89/1.49  fof(f4,axiom,(
% 7.89/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f37,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.89/1.49    inference(cnf_transformation,[],[f4])).
% 7.89/1.49  
% 7.89/1.49  fof(f59,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.89/1.49    inference(definition_unfolding,[],[f37,f41])).
% 7.89/1.49  
% 7.89/1.49  fof(f2,axiom,(
% 7.89/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f26,plain,(
% 7.89/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.89/1.49    inference(nnf_transformation,[],[f2])).
% 7.89/1.49  
% 7.89/1.49  fof(f27,plain,(
% 7.89/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.89/1.49    inference(flattening,[],[f26])).
% 7.89/1.49  
% 7.89/1.49  fof(f32,plain,(
% 7.89/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.89/1.49    inference(cnf_transformation,[],[f27])).
% 7.89/1.49  
% 7.89/1.49  fof(f68,plain,(
% 7.89/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.89/1.49    inference(equality_resolution,[],[f32])).
% 7.89/1.49  
% 7.89/1.49  fof(f5,axiom,(
% 7.89/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f23,plain,(
% 7.89/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.89/1.49    inference(ennf_transformation,[],[f5])).
% 7.89/1.49  
% 7.89/1.49  fof(f38,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f23])).
% 7.89/1.49  
% 7.89/1.49  fof(f61,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.89/1.49    inference(definition_unfolding,[],[f38,f41])).
% 7.89/1.49  
% 7.89/1.49  fof(f3,axiom,(
% 7.89/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f28,plain,(
% 7.89/1.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.89/1.49    inference(nnf_transformation,[],[f3])).
% 7.89/1.49  
% 7.89/1.49  fof(f36,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f28])).
% 7.89/1.49  
% 7.89/1.49  fof(f10,axiom,(
% 7.89/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f43,plain,(
% 7.89/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.89/1.49    inference(cnf_transformation,[],[f10])).
% 7.89/1.49  
% 7.89/1.49  fof(f17,axiom,(
% 7.89/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f22,plain,(
% 7.89/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 7.89/1.49    inference(unused_predicate_definition_removal,[],[f17])).
% 7.89/1.49  
% 7.89/1.49  fof(f24,plain,(
% 7.89/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 7.89/1.49    inference(ennf_transformation,[],[f22])).
% 7.89/1.49  
% 7.89/1.49  fof(f50,plain,(
% 7.89/1.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f24])).
% 7.89/1.49  
% 7.89/1.49  fof(f13,axiom,(
% 7.89/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f46,plain,(
% 7.89/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f13])).
% 7.89/1.49  
% 7.89/1.49  fof(f58,plain,(
% 7.89/1.49    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.89/1.49    inference(definition_unfolding,[],[f46,f57])).
% 7.89/1.49  
% 7.89/1.49  fof(f64,plain,(
% 7.89/1.49    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.89/1.49    inference(definition_unfolding,[],[f50,f58])).
% 7.89/1.49  
% 7.89/1.49  fof(f20,conjecture,(
% 7.89/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f21,negated_conjecture,(
% 7.89/1.49    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 7.89/1.49    inference(negated_conjecture,[],[f20])).
% 7.89/1.49  
% 7.89/1.49  fof(f25,plain,(
% 7.89/1.49    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 7.89/1.49    inference(ennf_transformation,[],[f21])).
% 7.89/1.49  
% 7.89/1.49  fof(f29,plain,(
% 7.89/1.49    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1))),
% 7.89/1.49    introduced(choice_axiom,[])).
% 7.89/1.49  
% 7.89/1.49  fof(f30,plain,(
% 7.89/1.49    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1)),
% 7.89/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).
% 7.89/1.49  
% 7.89/1.49  fof(f53,plain,(
% 7.89/1.49    r2_hidden(sK0,sK1)),
% 7.89/1.49    inference(cnf_transformation,[],[f30])).
% 7.89/1.49  
% 7.89/1.49  fof(f6,axiom,(
% 7.89/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f39,plain,(
% 7.89/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f6])).
% 7.89/1.49  
% 7.89/1.49  fof(f54,plain,(
% 7.89/1.49    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1),
% 7.89/1.49    inference(cnf_transformation,[],[f30])).
% 7.89/1.49  
% 7.89/1.49  fof(f66,plain,(
% 7.89/1.49    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1),
% 7.89/1.49    inference(definition_unfolding,[],[f54,f55,f58,f58])).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.89/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_10,plain,
% 7.89/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.89/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_968,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1,c_10]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5576,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_968,c_10]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_9,plain,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.89/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_14,plain,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 7.89/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_12,plain,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.89/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1010,plain,
% 7.89/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_14,c_12]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_0,plain,
% 7.89/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.89/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_793,plain,
% 7.89/1.49      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1012,plain,
% 7.89/1.49      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_1010,c_793]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1013,plain,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_1012,c_14]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1082,plain,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.89/1.49      inference(light_normalisation,[status(thm)],[c_9,c_9,c_1013]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_17786,plain,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1))))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_5576,c_1082]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f68]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_481,plain,
% 7.89/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7,plain,
% 7.89/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.89/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_478,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.89/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_861,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_481,c_478]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5,plain,
% 7.89/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.89/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_480,plain,
% 7.89/1.49      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2305,plain,
% 7.89/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_481,c_480]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4189,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.89/1.49      inference(light_normalisation,[status(thm)],[c_861,c_861,c_2305]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_981,plain,
% 7.89/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_12589,plain,
% 7.89/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_4189,c_981]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_11,plain,
% 7.89/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.89/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_871,plain,
% 7.89/1.49      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_11,c_12]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1723,plain,
% 7.89/1.49      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_0,c_871]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2504,plain,
% 7.89/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1723,c_0]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2533,plain,
% 7.89/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_2504,c_1723]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2534,plain,
% 7.89/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_2533,c_2504]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_13,plain,
% 7.89/1.49      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 7.89/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_17,negated_conjecture,
% 7.89/1.49      ( r2_hidden(sK0,sK1) ),
% 7.89/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_158,plain,
% 7.89/1.49      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | sK0 != X0 | sK1 != X1 ),
% 7.89/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_159,plain,
% 7.89/1.49      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
% 7.89/1.49      inference(unflattening,[status(thm)],[c_158]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_475,plain,
% 7.89/1.49      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_159]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2308,plain,
% 7.89/1.49      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k1_xboole_0 ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_475,c_480]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_864,plain,
% 7.89/1.49      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_475,c_478]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1209,plain,
% 7.89/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_864,c_1]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1218,plain,
% 7.89/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1209,c_10]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2688,plain,
% 7.89/1.49      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_2308,c_1218]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2691,plain,
% 7.89/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_2688,c_2308]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2809,plain,
% 7.89/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_2691,c_10]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_791,plain,
% 7.89/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3562,plain,
% 7.89/1.49      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK1)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_2809,c_791]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3564,plain,
% 7.89/1.49      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK1) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_2809,c_793]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1000,plain,
% 7.89/1.49      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_11,c_14]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1112,plain,
% 7.89/1.49      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_1000,c_0,c_1012]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2511,plain,
% 7.89/1.49      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1723,c_1112]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8,plain,
% 7.89/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_477,plain,
% 7.89/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2306,plain,
% 7.89/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_477,c_480]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2512,plain,
% 7.89/1.49      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_2511,c_2306]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3571,plain,
% 7.89/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK1) = k1_xboole_0 ),
% 7.89/1.49      inference(light_normalisation,[status(thm)],[c_3564,c_2512]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3574,plain,
% 7.89/1.49      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_3562,c_3571]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3575,plain,
% 7.89/1.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_3574,c_11,c_2305,c_2306]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_13112,plain,
% 7.89/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_12589,c_10,c_2534,c_3575]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_13532,plain,
% 7.89/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1,c_13112]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_971,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1,c_10]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_10106,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)),X1) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_3575,c_971]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_10371,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)),X1) ),
% 7.89/1.49      inference(light_normalisation,[status(thm)],[c_10106,c_4189]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_10372,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_10371,c_3575,c_4189]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_10234,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_971,c_4189]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_10298,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_10234,c_4189]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_10374,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_10372,c_10298]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_13709,plain,
% 7.89/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.89/1.49      inference(light_normalisation,[status(thm)],[c_13532,c_10374]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_17953,plain,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1))))) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 7.89/1.49      inference(light_normalisation,[status(thm)],[c_17786,c_13709]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5531,plain,
% 7.89/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_968,c_1]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5634,plain,
% 7.89/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_5531,c_10]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5530,plain,
% 7.89/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_968,c_793]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5636,plain,
% 7.89/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_5530,c_10]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_10456,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_10374,c_971]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_17954,plain,
% 7.89/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.89/1.49      inference(demodulation,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_17953,c_11,c_5634,c_5636,c_10456]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20656,plain,
% 7.89/1.49      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_17954,c_793]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20759,plain,
% 7.89/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_20656,c_11,c_13709]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_16,negated_conjecture,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 7.89/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_787,plain,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_1,c_16]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1002,plain,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1,c_14]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1110,plain,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.89/1.49      inference(light_normalisation,[status(thm)],[c_1002,c_1012]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1130,plain,
% 7.89/1.49      ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_787,c_1110]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20913,plain,
% 7.89/1.49      ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != sK1 ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_20759,c_1130]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7517,plain,
% 7.89/1.49      ( k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1209,c_1013]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1219,plain,
% 7.89/1.49      ( k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1209,c_0]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7585,plain,
% 7.89/1.49      ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k1_xboole_0) ),
% 7.89/1.49      inference(light_normalisation,[status(thm)],[c_7517,c_1219,c_2308]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1567,plain,
% 7.89/1.49      ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1219,c_12]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7586,plain,
% 7.89/1.49      ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = sK1 ),
% 7.89/1.49      inference(demodulation,[status(thm)],[c_7585,c_11,c_1567]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20914,plain,
% 7.89/1.49      ( sK1 != sK1 ),
% 7.89/1.49      inference(light_normalisation,[status(thm)],[c_20913,c_7586]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20915,plain,
% 7.89/1.49      ( $false ),
% 7.89/1.49      inference(equality_resolution_simp,[status(thm)],[c_20914]) ).
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.89/1.49  
% 7.89/1.49  ------                               Statistics
% 7.89/1.49  
% 7.89/1.49  ------ General
% 7.89/1.49  
% 7.89/1.49  abstr_ref_over_cycles:                  0
% 7.89/1.49  abstr_ref_under_cycles:                 0
% 7.89/1.49  gc_basic_clause_elim:                   0
% 7.89/1.49  forced_gc_time:                         0
% 7.89/1.49  parsing_time:                           0.011
% 7.89/1.49  unif_index_cands_time:                  0.
% 7.89/1.49  unif_index_add_time:                    0.
% 7.89/1.49  orderings_time:                         0.
% 7.89/1.49  out_proof_time:                         0.007
% 7.89/1.49  total_time:                             0.915
% 7.89/1.49  num_of_symbols:                         41
% 7.89/1.49  num_of_terms:                           42284
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing
% 7.89/1.49  
% 7.89/1.49  num_of_splits:                          0
% 7.89/1.49  num_of_split_atoms:                     0
% 7.89/1.49  num_of_reused_defs:                     0
% 7.89/1.49  num_eq_ax_congr_red:                    0
% 7.89/1.49  num_of_sem_filtered_clauses:            1
% 7.89/1.49  num_of_subtypes:                        0
% 7.89/1.49  monotx_restored_types:                  0
% 7.89/1.49  sat_num_of_epr_types:                   0
% 7.89/1.49  sat_num_of_non_cyclic_types:            0
% 7.89/1.49  sat_guarded_non_collapsed_types:        0
% 7.89/1.49  num_pure_diseq_elim:                    0
% 7.89/1.49  simp_replaced_by:                       0
% 7.89/1.49  res_preprocessed:                       82
% 7.89/1.49  prep_upred:                             0
% 7.89/1.49  prep_unflattend:                        2
% 7.89/1.49  smt_new_axioms:                         0
% 7.89/1.49  pred_elim_cands:                        1
% 7.89/1.49  pred_elim:                              1
% 7.89/1.49  pred_elim_cl:                           1
% 7.89/1.49  pred_elim_cycles:                       3
% 7.89/1.49  merged_defs:                            8
% 7.89/1.49  merged_defs_ncl:                        0
% 7.89/1.49  bin_hyper_res:                          8
% 7.89/1.49  prep_cycles:                            4
% 7.89/1.49  pred_elim_time:                         0.
% 7.89/1.49  splitting_time:                         0.
% 7.89/1.49  sem_filter_time:                        0.
% 7.89/1.49  monotx_time:                            0.
% 7.89/1.49  subtype_inf_time:                       0.
% 7.89/1.49  
% 7.89/1.49  ------ Problem properties
% 7.89/1.49  
% 7.89/1.49  clauses:                                16
% 7.89/1.49  conjectures:                            1
% 7.89/1.49  epr:                                    2
% 7.89/1.49  horn:                                   16
% 7.89/1.49  ground:                                 2
% 7.89/1.49  unary:                                  12
% 7.89/1.49  binary:                                 3
% 7.89/1.49  lits:                                   21
% 7.89/1.49  lits_eq:                                12
% 7.89/1.49  fd_pure:                                0
% 7.89/1.49  fd_pseudo:                              0
% 7.89/1.49  fd_cond:                                0
% 7.89/1.49  fd_pseudo_cond:                         1
% 7.89/1.49  ac_symbols:                             0
% 7.89/1.49  
% 7.89/1.49  ------ Propositional Solver
% 7.89/1.49  
% 7.89/1.49  prop_solver_calls:                      36
% 7.89/1.49  prop_fast_solver_calls:                 439
% 7.89/1.49  smt_solver_calls:                       0
% 7.89/1.49  smt_fast_solver_calls:                  0
% 7.89/1.49  prop_num_of_clauses:                    7373
% 7.89/1.49  prop_preprocess_simplified:             8879
% 7.89/1.49  prop_fo_subsumed:                       0
% 7.89/1.49  prop_solver_time:                       0.
% 7.89/1.49  smt_solver_time:                        0.
% 7.89/1.49  smt_fast_solver_time:                   0.
% 7.89/1.49  prop_fast_solver_time:                  0.
% 7.89/1.49  prop_unsat_core_time:                   0.
% 7.89/1.49  
% 7.89/1.49  ------ QBF
% 7.89/1.49  
% 7.89/1.49  qbf_q_res:                              0
% 7.89/1.49  qbf_num_tautologies:                    0
% 7.89/1.49  qbf_prep_cycles:                        0
% 7.89/1.49  
% 7.89/1.49  ------ BMC1
% 7.89/1.49  
% 7.89/1.49  bmc1_current_bound:                     -1
% 7.89/1.49  bmc1_last_solved_bound:                 -1
% 7.89/1.49  bmc1_unsat_core_size:                   -1
% 7.89/1.49  bmc1_unsat_core_parents_size:           -1
% 7.89/1.49  bmc1_merge_next_fun:                    0
% 7.89/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.89/1.49  
% 7.89/1.49  ------ Instantiation
% 7.89/1.49  
% 7.89/1.49  inst_num_of_clauses:                    1460
% 7.89/1.49  inst_num_in_passive:                    725
% 7.89/1.49  inst_num_in_active:                     608
% 7.89/1.49  inst_num_in_unprocessed:                128
% 7.89/1.49  inst_num_of_loops:                      640
% 7.89/1.49  inst_num_of_learning_restarts:          0
% 7.89/1.49  inst_num_moves_active_passive:          24
% 7.89/1.49  inst_lit_activity:                      0
% 7.89/1.49  inst_lit_activity_moves:                0
% 7.89/1.49  inst_num_tautologies:                   0
% 7.89/1.49  inst_num_prop_implied:                  0
% 7.89/1.49  inst_num_existing_simplified:           0
% 7.89/1.49  inst_num_eq_res_simplified:             0
% 7.89/1.49  inst_num_child_elim:                    0
% 7.89/1.49  inst_num_of_dismatching_blockings:      747
% 7.89/1.49  inst_num_of_non_proper_insts:           1945
% 7.89/1.49  inst_num_of_duplicates:                 0
% 7.89/1.49  inst_inst_num_from_inst_to_res:         0
% 7.89/1.49  inst_dismatching_checking_time:         0.
% 7.89/1.49  
% 7.89/1.49  ------ Resolution
% 7.89/1.49  
% 7.89/1.49  res_num_of_clauses:                     0
% 7.89/1.49  res_num_in_passive:                     0
% 7.89/1.49  res_num_in_active:                      0
% 7.89/1.49  res_num_of_loops:                       86
% 7.89/1.49  res_forward_subset_subsumed:            232
% 7.89/1.49  res_backward_subset_subsumed:           6
% 7.89/1.49  res_forward_subsumed:                   0
% 7.89/1.49  res_backward_subsumed:                  0
% 7.89/1.49  res_forward_subsumption_resolution:     0
% 7.89/1.49  res_backward_subsumption_resolution:    0
% 7.89/1.49  res_clause_to_clause_subsumption:       22211
% 7.89/1.49  res_orphan_elimination:                 0
% 7.89/1.49  res_tautology_del:                      133
% 7.89/1.49  res_num_eq_res_simplified:              0
% 7.89/1.49  res_num_sel_changes:                    0
% 7.89/1.49  res_moves_from_active_to_pass:          0
% 7.89/1.49  
% 7.89/1.49  ------ Superposition
% 7.89/1.49  
% 7.89/1.49  sup_time_total:                         0.
% 7.89/1.49  sup_time_generating:                    0.
% 7.89/1.49  sup_time_sim_full:                      0.
% 7.89/1.49  sup_time_sim_immed:                     0.
% 7.89/1.49  
% 7.89/1.49  sup_num_of_clauses:                     1567
% 7.89/1.49  sup_num_in_active:                      95
% 7.89/1.49  sup_num_in_passive:                     1472
% 7.89/1.49  sup_num_of_loops:                       126
% 7.89/1.49  sup_fw_superposition:                   2454
% 7.89/1.49  sup_bw_superposition:                   2384
% 7.89/1.49  sup_immediate_simplified:               3696
% 7.89/1.49  sup_given_eliminated:                   11
% 7.89/1.49  comparisons_done:                       0
% 7.89/1.49  comparisons_avoided:                    0
% 7.89/1.49  
% 7.89/1.49  ------ Simplifications
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  sim_fw_subset_subsumed:                 0
% 7.89/1.49  sim_bw_subset_subsumed:                 0
% 7.89/1.49  sim_fw_subsumed:                        512
% 7.89/1.49  sim_bw_subsumed:                        41
% 7.89/1.49  sim_fw_subsumption_res:                 0
% 7.89/1.49  sim_bw_subsumption_res:                 0
% 7.89/1.49  sim_tautology_del:                      0
% 7.89/1.49  sim_eq_tautology_del:                   720
% 7.89/1.49  sim_eq_res_simp:                        1
% 7.89/1.49  sim_fw_demodulated:                     3869
% 7.89/1.49  sim_bw_demodulated:                     310
% 7.89/1.49  sim_light_normalised:                   2018
% 7.89/1.49  sim_joinable_taut:                      0
% 7.89/1.49  sim_joinable_simp:                      0
% 7.89/1.49  sim_ac_normalised:                      0
% 7.89/1.49  sim_smt_subsumption:                    0
% 7.89/1.49  
%------------------------------------------------------------------------------
