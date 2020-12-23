%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:29 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 339 expanded)
%              Number of clauses        :   36 (  96 expanded)
%              Number of leaves         :   18 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  117 ( 513 expanded)
%              Number of equality atoms :   89 ( 347 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f52,f51])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f17])).

fof(f21,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f25])).

fof(f46,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f57,plain,(
    k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f46,f47,f52,f51,f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f29,f47])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_10,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_363,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_364,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_851,plain,
    ( k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_363,c_364])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_446,plain,
    ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_11])).

cnf(c_14924,plain,
    ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_851,c_446])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_367,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_366,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3437,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_367,c_366])).

cnf(c_850,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_367,c_364])).

cnf(c_3442,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3437,c_850])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4299,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_3442,c_9])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_589,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_9])).

cnf(c_1028,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_850,c_589])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_408,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_1160,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1028,c_408])).

cnf(c_1134,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_1028])).

cnf(c_2810,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k5_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_1160,c_1134])).

cnf(c_1029,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_850,c_2])).

cnf(c_409,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_1100,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1029,c_409])).

cnf(c_1101,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1029,c_408])).

cnf(c_2818,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_2810,c_1029,c_1100,c_1101])).

cnf(c_4249,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_3442,c_2818])).

cnf(c_5006,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_4299,c_4249])).

cnf(c_5042,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_5006,c_409])).

cnf(c_14925,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_14924,c_5042])).

cnf(c_14926,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_14925])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.72/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.07  
% 3.72/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/1.07  
% 3.72/1.07  ------  iProver source info
% 3.72/1.07  
% 3.72/1.07  git: date: 2020-06-30 10:37:57 +0100
% 3.72/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/1.07  git: non_committed_changes: false
% 3.72/1.07  git: last_make_outside_of_git: false
% 3.72/1.07  
% 3.72/1.07  ------ 
% 3.72/1.07  
% 3.72/1.07  ------ Input Options
% 3.72/1.07  
% 3.72/1.07  --out_options                           all
% 3.72/1.07  --tptp_safe_out                         true
% 3.72/1.07  --problem_path                          ""
% 3.72/1.07  --include_path                          ""
% 3.72/1.07  --clausifier                            res/vclausify_rel
% 3.72/1.07  --clausifier_options                    --mode clausify
% 3.72/1.07  --stdin                                 false
% 3.72/1.07  --stats_out                             all
% 3.72/1.07  
% 3.72/1.07  ------ General Options
% 3.72/1.07  
% 3.72/1.07  --fof                                   false
% 3.72/1.07  --time_out_real                         305.
% 3.72/1.07  --time_out_virtual                      -1.
% 3.72/1.07  --symbol_type_check                     false
% 3.72/1.07  --clausify_out                          false
% 3.72/1.07  --sig_cnt_out                           false
% 3.72/1.07  --trig_cnt_out                          false
% 3.72/1.07  --trig_cnt_out_tolerance                1.
% 3.72/1.07  --trig_cnt_out_sk_spl                   false
% 3.72/1.07  --abstr_cl_out                          false
% 3.72/1.07  
% 3.72/1.07  ------ Global Options
% 3.72/1.07  
% 3.72/1.07  --schedule                              default
% 3.72/1.07  --add_important_lit                     false
% 3.72/1.07  --prop_solver_per_cl                    1000
% 3.72/1.07  --min_unsat_core                        false
% 3.72/1.07  --soft_assumptions                      false
% 3.72/1.07  --soft_lemma_size                       3
% 3.72/1.07  --prop_impl_unit_size                   0
% 3.72/1.07  --prop_impl_unit                        []
% 3.72/1.07  --share_sel_clauses                     true
% 3.72/1.07  --reset_solvers                         false
% 3.72/1.07  --bc_imp_inh                            [conj_cone]
% 3.72/1.07  --conj_cone_tolerance                   3.
% 3.72/1.07  --extra_neg_conj                        none
% 3.72/1.07  --large_theory_mode                     true
% 3.72/1.07  --prolific_symb_bound                   200
% 3.72/1.07  --lt_threshold                          2000
% 3.72/1.07  --clause_weak_htbl                      true
% 3.72/1.07  --gc_record_bc_elim                     false
% 3.72/1.07  
% 3.72/1.07  ------ Preprocessing Options
% 3.72/1.07  
% 3.72/1.07  --preprocessing_flag                    true
% 3.72/1.07  --time_out_prep_mult                    0.1
% 3.72/1.07  --splitting_mode                        input
% 3.72/1.07  --splitting_grd                         true
% 3.72/1.07  --splitting_cvd                         false
% 3.72/1.07  --splitting_cvd_svl                     false
% 3.72/1.07  --splitting_nvd                         32
% 3.72/1.07  --sub_typing                            true
% 3.72/1.07  --prep_gs_sim                           true
% 3.72/1.07  --prep_unflatten                        true
% 3.72/1.07  --prep_res_sim                          true
% 3.72/1.07  --prep_upred                            true
% 3.72/1.07  --prep_sem_filter                       exhaustive
% 3.72/1.07  --prep_sem_filter_out                   false
% 3.72/1.07  --pred_elim                             true
% 3.72/1.07  --res_sim_input                         true
% 3.72/1.07  --eq_ax_congr_red                       true
% 3.72/1.07  --pure_diseq_elim                       true
% 3.72/1.07  --brand_transform                       false
% 3.72/1.07  --non_eq_to_eq                          false
% 3.72/1.07  --prep_def_merge                        true
% 3.72/1.07  --prep_def_merge_prop_impl              false
% 3.72/1.07  --prep_def_merge_mbd                    true
% 3.72/1.07  --prep_def_merge_tr_red                 false
% 3.72/1.07  --prep_def_merge_tr_cl                  false
% 3.72/1.07  --smt_preprocessing                     true
% 3.72/1.07  --smt_ac_axioms                         fast
% 3.72/1.07  --preprocessed_out                      false
% 3.72/1.07  --preprocessed_stats                    false
% 3.72/1.07  
% 3.72/1.07  ------ Abstraction refinement Options
% 3.72/1.07  
% 3.72/1.07  --abstr_ref                             []
% 3.72/1.07  --abstr_ref_prep                        false
% 3.72/1.07  --abstr_ref_until_sat                   false
% 3.72/1.07  --abstr_ref_sig_restrict                funpre
% 3.72/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/1.07  --abstr_ref_under                       []
% 3.72/1.07  
% 3.72/1.07  ------ SAT Options
% 3.72/1.07  
% 3.72/1.07  --sat_mode                              false
% 3.72/1.07  --sat_fm_restart_options                ""
% 3.72/1.07  --sat_gr_def                            false
% 3.72/1.07  --sat_epr_types                         true
% 3.72/1.07  --sat_non_cyclic_types                  false
% 3.72/1.07  --sat_finite_models                     false
% 3.72/1.07  --sat_fm_lemmas                         false
% 3.72/1.07  --sat_fm_prep                           false
% 3.72/1.07  --sat_fm_uc_incr                        true
% 3.72/1.07  --sat_out_model                         small
% 3.72/1.07  --sat_out_clauses                       false
% 3.72/1.07  
% 3.72/1.07  ------ QBF Options
% 3.72/1.07  
% 3.72/1.07  --qbf_mode                              false
% 3.72/1.07  --qbf_elim_univ                         false
% 3.72/1.07  --qbf_dom_inst                          none
% 3.72/1.07  --qbf_dom_pre_inst                      false
% 3.72/1.07  --qbf_sk_in                             false
% 3.72/1.07  --qbf_pred_elim                         true
% 3.72/1.07  --qbf_split                             512
% 3.72/1.07  
% 3.72/1.07  ------ BMC1 Options
% 3.72/1.07  
% 3.72/1.07  --bmc1_incremental                      false
% 3.72/1.07  --bmc1_axioms                           reachable_all
% 3.72/1.07  --bmc1_min_bound                        0
% 3.72/1.07  --bmc1_max_bound                        -1
% 3.72/1.07  --bmc1_max_bound_default                -1
% 3.72/1.07  --bmc1_symbol_reachability              true
% 3.72/1.07  --bmc1_property_lemmas                  false
% 3.72/1.07  --bmc1_k_induction                      false
% 3.72/1.07  --bmc1_non_equiv_states                 false
% 3.72/1.07  --bmc1_deadlock                         false
% 3.72/1.07  --bmc1_ucm                              false
% 3.72/1.07  --bmc1_add_unsat_core                   none
% 3.72/1.07  --bmc1_unsat_core_children              false
% 3.72/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/1.07  --bmc1_out_stat                         full
% 3.72/1.07  --bmc1_ground_init                      false
% 3.72/1.07  --bmc1_pre_inst_next_state              false
% 3.72/1.07  --bmc1_pre_inst_state                   false
% 3.72/1.07  --bmc1_pre_inst_reach_state             false
% 3.72/1.07  --bmc1_out_unsat_core                   false
% 3.72/1.07  --bmc1_aig_witness_out                  false
% 3.72/1.07  --bmc1_verbose                          false
% 3.72/1.07  --bmc1_dump_clauses_tptp                false
% 3.72/1.07  --bmc1_dump_unsat_core_tptp             false
% 3.72/1.07  --bmc1_dump_file                        -
% 3.72/1.07  --bmc1_ucm_expand_uc_limit              128
% 3.72/1.07  --bmc1_ucm_n_expand_iterations          6
% 3.72/1.07  --bmc1_ucm_extend_mode                  1
% 3.72/1.07  --bmc1_ucm_init_mode                    2
% 3.72/1.07  --bmc1_ucm_cone_mode                    none
% 3.72/1.07  --bmc1_ucm_reduced_relation_type        0
% 3.72/1.07  --bmc1_ucm_relax_model                  4
% 3.72/1.07  --bmc1_ucm_full_tr_after_sat            true
% 3.72/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/1.07  --bmc1_ucm_layered_model                none
% 3.72/1.07  --bmc1_ucm_max_lemma_size               10
% 3.72/1.07  
% 3.72/1.07  ------ AIG Options
% 3.72/1.07  
% 3.72/1.07  --aig_mode                              false
% 3.72/1.07  
% 3.72/1.07  ------ Instantiation Options
% 3.72/1.07  
% 3.72/1.07  --instantiation_flag                    true
% 3.72/1.07  --inst_sos_flag                         false
% 3.72/1.07  --inst_sos_phase                        true
% 3.72/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/1.07  --inst_lit_sel_side                     num_symb
% 3.72/1.07  --inst_solver_per_active                1400
% 3.72/1.07  --inst_solver_calls_frac                1.
% 3.72/1.07  --inst_passive_queue_type               priority_queues
% 3.72/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/1.07  --inst_passive_queues_freq              [25;2]
% 3.72/1.07  --inst_dismatching                      true
% 3.72/1.07  --inst_eager_unprocessed_to_passive     true
% 3.72/1.07  --inst_prop_sim_given                   true
% 3.72/1.07  --inst_prop_sim_new                     false
% 3.72/1.07  --inst_subs_new                         false
% 3.72/1.07  --inst_eq_res_simp                      false
% 3.72/1.07  --inst_subs_given                       false
% 3.72/1.07  --inst_orphan_elimination               true
% 3.72/1.07  --inst_learning_loop_flag               true
% 3.72/1.07  --inst_learning_start                   3000
% 3.72/1.07  --inst_learning_factor                  2
% 3.72/1.07  --inst_start_prop_sim_after_learn       3
% 3.72/1.07  --inst_sel_renew                        solver
% 3.72/1.07  --inst_lit_activity_flag                true
% 3.72/1.07  --inst_restr_to_given                   false
% 3.72/1.07  --inst_activity_threshold               500
% 3.72/1.07  --inst_out_proof                        true
% 3.72/1.07  
% 3.72/1.07  ------ Resolution Options
% 3.72/1.07  
% 3.72/1.07  --resolution_flag                       true
% 3.72/1.07  --res_lit_sel                           adaptive
% 3.72/1.07  --res_lit_sel_side                      none
% 3.72/1.07  --res_ordering                          kbo
% 3.72/1.07  --res_to_prop_solver                    active
% 3.72/1.07  --res_prop_simpl_new                    false
% 3.72/1.07  --res_prop_simpl_given                  true
% 3.72/1.07  --res_passive_queue_type                priority_queues
% 3.72/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/1.07  --res_passive_queues_freq               [15;5]
% 3.72/1.07  --res_forward_subs                      full
% 3.72/1.07  --res_backward_subs                     full
% 3.72/1.07  --res_forward_subs_resolution           true
% 3.72/1.07  --res_backward_subs_resolution          true
% 3.72/1.07  --res_orphan_elimination                true
% 3.72/1.07  --res_time_limit                        2.
% 3.72/1.07  --res_out_proof                         true
% 3.72/1.07  
% 3.72/1.07  ------ Superposition Options
% 3.72/1.07  
% 3.72/1.07  --superposition_flag                    true
% 3.72/1.07  --sup_passive_queue_type                priority_queues
% 3.72/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/1.07  --sup_passive_queues_freq               [8;1;4]
% 3.72/1.07  --demod_completeness_check              fast
% 3.72/1.07  --demod_use_ground                      true
% 3.72/1.07  --sup_to_prop_solver                    passive
% 3.72/1.07  --sup_prop_simpl_new                    true
% 3.72/1.07  --sup_prop_simpl_given                  true
% 3.72/1.07  --sup_fun_splitting                     false
% 3.72/1.07  --sup_smt_interval                      50000
% 3.72/1.07  
% 3.72/1.07  ------ Superposition Simplification Setup
% 3.72/1.07  
% 3.72/1.07  --sup_indices_passive                   []
% 3.72/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.07  --sup_full_bw                           [BwDemod]
% 3.72/1.07  --sup_immed_triv                        [TrivRules]
% 3.72/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.07  --sup_immed_bw_main                     []
% 3.72/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.07  
% 3.72/1.07  ------ Combination Options
% 3.72/1.07  
% 3.72/1.07  --comb_res_mult                         3
% 3.72/1.07  --comb_sup_mult                         2
% 3.72/1.07  --comb_inst_mult                        10
% 3.72/1.07  
% 3.72/1.07  ------ Debug Options
% 3.72/1.07  
% 3.72/1.07  --dbg_backtrace                         false
% 3.72/1.07  --dbg_dump_prop_clauses                 false
% 3.72/1.07  --dbg_dump_prop_clauses_file            -
% 3.72/1.07  --dbg_out_stat                          false
% 3.72/1.07  ------ Parsing...
% 3.72/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/1.07  
% 3.72/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.72/1.07  
% 3.72/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/1.07  
% 3.72/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/1.07  ------ Proving...
% 3.72/1.07  ------ Problem Properties 
% 3.72/1.07  
% 3.72/1.07  
% 3.72/1.07  clauses                                 11
% 3.72/1.07  conjectures                             1
% 3.72/1.07  EPR                                     2
% 3.72/1.07  Horn                                    11
% 3.72/1.07  unary                                   7
% 3.72/1.07  binary                                  3
% 3.72/1.07  lits                                    16
% 3.72/1.07  lits eq                                 9
% 3.72/1.07  fd_pure                                 0
% 3.72/1.07  fd_pseudo                               0
% 3.72/1.07  fd_cond                                 0
% 3.72/1.07  fd_pseudo_cond                          1
% 3.72/1.07  AC symbols                              1
% 3.72/1.07  
% 3.72/1.07  ------ Schedule dynamic 5 is on 
% 3.72/1.07  
% 3.72/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.72/1.07  
% 3.72/1.07  
% 3.72/1.07  ------ 
% 3.72/1.07  Current options:
% 3.72/1.07  ------ 
% 3.72/1.07  
% 3.72/1.07  ------ Input Options
% 3.72/1.07  
% 3.72/1.07  --out_options                           all
% 3.72/1.07  --tptp_safe_out                         true
% 3.72/1.07  --problem_path                          ""
% 3.72/1.07  --include_path                          ""
% 3.72/1.07  --clausifier                            res/vclausify_rel
% 3.72/1.07  --clausifier_options                    --mode clausify
% 3.72/1.07  --stdin                                 false
% 3.72/1.07  --stats_out                             all
% 3.72/1.07  
% 3.72/1.07  ------ General Options
% 3.72/1.07  
% 3.72/1.07  --fof                                   false
% 3.72/1.07  --time_out_real                         305.
% 3.72/1.07  --time_out_virtual                      -1.
% 3.72/1.07  --symbol_type_check                     false
% 3.72/1.07  --clausify_out                          false
% 3.72/1.07  --sig_cnt_out                           false
% 3.72/1.07  --trig_cnt_out                          false
% 3.72/1.07  --trig_cnt_out_tolerance                1.
% 3.72/1.07  --trig_cnt_out_sk_spl                   false
% 3.72/1.07  --abstr_cl_out                          false
% 3.72/1.07  
% 3.72/1.07  ------ Global Options
% 3.72/1.07  
% 3.72/1.07  --schedule                              default
% 3.72/1.07  --add_important_lit                     false
% 3.72/1.07  --prop_solver_per_cl                    1000
% 3.72/1.07  --min_unsat_core                        false
% 3.72/1.07  --soft_assumptions                      false
% 3.72/1.07  --soft_lemma_size                       3
% 3.72/1.07  --prop_impl_unit_size                   0
% 3.72/1.07  --prop_impl_unit                        []
% 3.72/1.07  --share_sel_clauses                     true
% 3.72/1.07  --reset_solvers                         false
% 3.72/1.07  --bc_imp_inh                            [conj_cone]
% 3.72/1.07  --conj_cone_tolerance                   3.
% 3.72/1.07  --extra_neg_conj                        none
% 3.72/1.07  --large_theory_mode                     true
% 3.72/1.07  --prolific_symb_bound                   200
% 3.72/1.07  --lt_threshold                          2000
% 3.72/1.07  --clause_weak_htbl                      true
% 3.72/1.07  --gc_record_bc_elim                     false
% 3.72/1.07  
% 3.72/1.07  ------ Preprocessing Options
% 3.72/1.07  
% 3.72/1.07  --preprocessing_flag                    true
% 3.72/1.07  --time_out_prep_mult                    0.1
% 3.72/1.07  --splitting_mode                        input
% 3.72/1.07  --splitting_grd                         true
% 3.72/1.07  --splitting_cvd                         false
% 3.72/1.07  --splitting_cvd_svl                     false
% 3.72/1.07  --splitting_nvd                         32
% 3.72/1.07  --sub_typing                            true
% 3.72/1.07  --prep_gs_sim                           true
% 3.72/1.07  --prep_unflatten                        true
% 3.72/1.07  --prep_res_sim                          true
% 3.72/1.07  --prep_upred                            true
% 3.72/1.07  --prep_sem_filter                       exhaustive
% 3.72/1.07  --prep_sem_filter_out                   false
% 3.72/1.07  --pred_elim                             true
% 3.72/1.07  --res_sim_input                         true
% 3.72/1.07  --eq_ax_congr_red                       true
% 3.72/1.07  --pure_diseq_elim                       true
% 3.72/1.07  --brand_transform                       false
% 3.72/1.07  --non_eq_to_eq                          false
% 3.72/1.07  --prep_def_merge                        true
% 3.72/1.07  --prep_def_merge_prop_impl              false
% 3.72/1.07  --prep_def_merge_mbd                    true
% 3.72/1.07  --prep_def_merge_tr_red                 false
% 3.72/1.07  --prep_def_merge_tr_cl                  false
% 3.72/1.07  --smt_preprocessing                     true
% 3.72/1.07  --smt_ac_axioms                         fast
% 3.72/1.07  --preprocessed_out                      false
% 3.72/1.07  --preprocessed_stats                    false
% 3.72/1.07  
% 3.72/1.07  ------ Abstraction refinement Options
% 3.72/1.07  
% 3.72/1.07  --abstr_ref                             []
% 3.72/1.07  --abstr_ref_prep                        false
% 3.72/1.07  --abstr_ref_until_sat                   false
% 3.72/1.07  --abstr_ref_sig_restrict                funpre
% 3.72/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/1.07  --abstr_ref_under                       []
% 3.72/1.07  
% 3.72/1.07  ------ SAT Options
% 3.72/1.07  
% 3.72/1.07  --sat_mode                              false
% 3.72/1.07  --sat_fm_restart_options                ""
% 3.72/1.07  --sat_gr_def                            false
% 3.72/1.07  --sat_epr_types                         true
% 3.72/1.07  --sat_non_cyclic_types                  false
% 3.72/1.07  --sat_finite_models                     false
% 3.72/1.07  --sat_fm_lemmas                         false
% 3.72/1.07  --sat_fm_prep                           false
% 3.72/1.07  --sat_fm_uc_incr                        true
% 3.72/1.07  --sat_out_model                         small
% 3.72/1.07  --sat_out_clauses                       false
% 3.72/1.07  
% 3.72/1.07  ------ QBF Options
% 3.72/1.07  
% 3.72/1.07  --qbf_mode                              false
% 3.72/1.07  --qbf_elim_univ                         false
% 3.72/1.07  --qbf_dom_inst                          none
% 3.72/1.07  --qbf_dom_pre_inst                      false
% 3.72/1.07  --qbf_sk_in                             false
% 3.72/1.07  --qbf_pred_elim                         true
% 3.72/1.07  --qbf_split                             512
% 3.72/1.07  
% 3.72/1.07  ------ BMC1 Options
% 3.72/1.07  
% 3.72/1.07  --bmc1_incremental                      false
% 3.72/1.07  --bmc1_axioms                           reachable_all
% 3.72/1.07  --bmc1_min_bound                        0
% 3.72/1.07  --bmc1_max_bound                        -1
% 3.72/1.07  --bmc1_max_bound_default                -1
% 3.72/1.07  --bmc1_symbol_reachability              true
% 3.72/1.07  --bmc1_property_lemmas                  false
% 3.72/1.07  --bmc1_k_induction                      false
% 3.72/1.07  --bmc1_non_equiv_states                 false
% 3.72/1.07  --bmc1_deadlock                         false
% 3.72/1.07  --bmc1_ucm                              false
% 3.72/1.07  --bmc1_add_unsat_core                   none
% 3.72/1.07  --bmc1_unsat_core_children              false
% 3.72/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/1.07  --bmc1_out_stat                         full
% 3.72/1.07  --bmc1_ground_init                      false
% 3.72/1.07  --bmc1_pre_inst_next_state              false
% 3.72/1.07  --bmc1_pre_inst_state                   false
% 3.72/1.07  --bmc1_pre_inst_reach_state             false
% 3.72/1.07  --bmc1_out_unsat_core                   false
% 3.72/1.07  --bmc1_aig_witness_out                  false
% 3.72/1.07  --bmc1_verbose                          false
% 3.72/1.07  --bmc1_dump_clauses_tptp                false
% 3.72/1.07  --bmc1_dump_unsat_core_tptp             false
% 3.72/1.07  --bmc1_dump_file                        -
% 3.72/1.07  --bmc1_ucm_expand_uc_limit              128
% 3.72/1.07  --bmc1_ucm_n_expand_iterations          6
% 3.72/1.07  --bmc1_ucm_extend_mode                  1
% 3.72/1.07  --bmc1_ucm_init_mode                    2
% 3.72/1.07  --bmc1_ucm_cone_mode                    none
% 3.72/1.07  --bmc1_ucm_reduced_relation_type        0
% 3.72/1.07  --bmc1_ucm_relax_model                  4
% 3.72/1.07  --bmc1_ucm_full_tr_after_sat            true
% 3.72/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/1.07  --bmc1_ucm_layered_model                none
% 3.72/1.07  --bmc1_ucm_max_lemma_size               10
% 3.72/1.07  
% 3.72/1.07  ------ AIG Options
% 3.72/1.07  
% 3.72/1.07  --aig_mode                              false
% 3.72/1.07  
% 3.72/1.07  ------ Instantiation Options
% 3.72/1.07  
% 3.72/1.07  --instantiation_flag                    true
% 3.72/1.07  --inst_sos_flag                         false
% 3.72/1.07  --inst_sos_phase                        true
% 3.72/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/1.07  --inst_lit_sel_side                     none
% 3.72/1.07  --inst_solver_per_active                1400
% 3.72/1.07  --inst_solver_calls_frac                1.
% 3.72/1.07  --inst_passive_queue_type               priority_queues
% 3.72/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/1.07  --inst_passive_queues_freq              [25;2]
% 3.72/1.07  --inst_dismatching                      true
% 3.72/1.07  --inst_eager_unprocessed_to_passive     true
% 3.72/1.07  --inst_prop_sim_given                   true
% 3.72/1.07  --inst_prop_sim_new                     false
% 3.72/1.07  --inst_subs_new                         false
% 3.72/1.07  --inst_eq_res_simp                      false
% 3.72/1.07  --inst_subs_given                       false
% 3.72/1.07  --inst_orphan_elimination               true
% 3.72/1.07  --inst_learning_loop_flag               true
% 3.72/1.07  --inst_learning_start                   3000
% 3.72/1.07  --inst_learning_factor                  2
% 3.72/1.07  --inst_start_prop_sim_after_learn       3
% 3.72/1.07  --inst_sel_renew                        solver
% 3.72/1.07  --inst_lit_activity_flag                true
% 3.72/1.07  --inst_restr_to_given                   false
% 3.72/1.07  --inst_activity_threshold               500
% 3.72/1.07  --inst_out_proof                        true
% 3.72/1.07  
% 3.72/1.07  ------ Resolution Options
% 3.72/1.07  
% 3.72/1.07  --resolution_flag                       false
% 3.72/1.07  --res_lit_sel                           adaptive
% 3.72/1.07  --res_lit_sel_side                      none
% 3.72/1.07  --res_ordering                          kbo
% 3.72/1.07  --res_to_prop_solver                    active
% 3.72/1.07  --res_prop_simpl_new                    false
% 3.72/1.07  --res_prop_simpl_given                  true
% 3.72/1.07  --res_passive_queue_type                priority_queues
% 3.72/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/1.07  --res_passive_queues_freq               [15;5]
% 3.72/1.07  --res_forward_subs                      full
% 3.72/1.07  --res_backward_subs                     full
% 3.72/1.07  --res_forward_subs_resolution           true
% 3.72/1.07  --res_backward_subs_resolution          true
% 3.72/1.07  --res_orphan_elimination                true
% 3.72/1.07  --res_time_limit                        2.
% 3.72/1.07  --res_out_proof                         true
% 3.72/1.07  
% 3.72/1.07  ------ Superposition Options
% 3.72/1.07  
% 3.72/1.07  --superposition_flag                    true
% 3.72/1.07  --sup_passive_queue_type                priority_queues
% 3.72/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/1.07  --sup_passive_queues_freq               [8;1;4]
% 3.72/1.07  --demod_completeness_check              fast
% 3.72/1.07  --demod_use_ground                      true
% 3.72/1.07  --sup_to_prop_solver                    passive
% 3.72/1.07  --sup_prop_simpl_new                    true
% 3.72/1.07  --sup_prop_simpl_given                  true
% 3.72/1.07  --sup_fun_splitting                     false
% 3.72/1.07  --sup_smt_interval                      50000
% 3.72/1.07  
% 3.72/1.07  ------ Superposition Simplification Setup
% 3.72/1.07  
% 3.72/1.07  --sup_indices_passive                   []
% 3.72/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.07  --sup_full_bw                           [BwDemod]
% 3.72/1.07  --sup_immed_triv                        [TrivRules]
% 3.72/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.07  --sup_immed_bw_main                     []
% 3.72/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.07  
% 3.72/1.07  ------ Combination Options
% 3.72/1.07  
% 3.72/1.07  --comb_res_mult                         3
% 3.72/1.07  --comb_sup_mult                         2
% 3.72/1.07  --comb_inst_mult                        10
% 3.72/1.07  
% 3.72/1.07  ------ Debug Options
% 3.72/1.07  
% 3.72/1.07  --dbg_backtrace                         false
% 3.72/1.07  --dbg_dump_prop_clauses                 false
% 3.72/1.07  --dbg_dump_prop_clauses_file            -
% 3.72/1.07  --dbg_out_stat                          false
% 3.72/1.07  
% 3.72/1.07  
% 3.72/1.07  
% 3.72/1.07  
% 3.72/1.07  ------ Proving...
% 3.72/1.07  
% 3.72/1.07  
% 3.72/1.07  % SZS status Theorem for theBenchmark.p
% 3.72/1.07  
% 3.72/1.07   Resolution empty clause
% 3.72/1.07  
% 3.72/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/1.07  
% 3.72/1.07  fof(f16,axiom,(
% 3.72/1.07    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f45,plain,(
% 3.72/1.07    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 3.72/1.07    inference(cnf_transformation,[],[f16])).
% 3.72/1.07  
% 3.72/1.07  fof(f10,axiom,(
% 3.72/1.07    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f39,plain,(
% 3.72/1.07    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f10])).
% 3.72/1.07  
% 3.72/1.07  fof(f52,plain,(
% 3.72/1.07    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.72/1.07    inference(definition_unfolding,[],[f39,f51])).
% 3.72/1.07  
% 3.72/1.07  fof(f11,axiom,(
% 3.72/1.07    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f40,plain,(
% 3.72/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f11])).
% 3.72/1.07  
% 3.72/1.07  fof(f12,axiom,(
% 3.72/1.07    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f41,plain,(
% 3.72/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f12])).
% 3.72/1.07  
% 3.72/1.07  fof(f13,axiom,(
% 3.72/1.07    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f42,plain,(
% 3.72/1.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f13])).
% 3.72/1.07  
% 3.72/1.07  fof(f14,axiom,(
% 3.72/1.07    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f43,plain,(
% 3.72/1.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f14])).
% 3.72/1.07  
% 3.72/1.07  fof(f15,axiom,(
% 3.72/1.07    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f44,plain,(
% 3.72/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f15])).
% 3.72/1.07  
% 3.72/1.07  fof(f48,plain,(
% 3.72/1.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.72/1.07    inference(definition_unfolding,[],[f43,f44])).
% 3.72/1.07  
% 3.72/1.07  fof(f49,plain,(
% 3.72/1.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.72/1.07    inference(definition_unfolding,[],[f42,f48])).
% 3.72/1.07  
% 3.72/1.07  fof(f50,plain,(
% 3.72/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.72/1.07    inference(definition_unfolding,[],[f41,f49])).
% 3.72/1.07  
% 3.72/1.07  fof(f51,plain,(
% 3.72/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.72/1.07    inference(definition_unfolding,[],[f40,f50])).
% 3.72/1.07  
% 3.72/1.07  fof(f56,plain,(
% 3.72/1.07    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.72/1.07    inference(definition_unfolding,[],[f45,f52,f51])).
% 3.72/1.07  
% 3.72/1.07  fof(f7,axiom,(
% 3.72/1.07    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f20,plain,(
% 3.72/1.07    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.72/1.07    inference(ennf_transformation,[],[f7])).
% 3.72/1.07  
% 3.72/1.07  fof(f36,plain,(
% 3.72/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f20])).
% 3.72/1.07  
% 3.72/1.07  fof(f1,axiom,(
% 3.72/1.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f27,plain,(
% 3.72/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f1])).
% 3.72/1.07  
% 3.72/1.07  fof(f17,conjecture,(
% 3.72/1.07    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f18,negated_conjecture,(
% 3.72/1.07    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 3.72/1.07    inference(negated_conjecture,[],[f17])).
% 3.72/1.07  
% 3.72/1.07  fof(f21,plain,(
% 3.72/1.07    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)),
% 3.72/1.07    inference(ennf_transformation,[],[f18])).
% 3.72/1.07  
% 3.72/1.07  fof(f25,plain,(
% 3.72/1.07    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 3.72/1.07    introduced(choice_axiom,[])).
% 3.72/1.07  
% 3.72/1.07  fof(f26,plain,(
% 3.72/1.07    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 3.72/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f25])).
% 3.72/1.07  
% 3.72/1.07  fof(f46,plain,(
% 3.72/1.07    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 3.72/1.07    inference(cnf_transformation,[],[f26])).
% 3.72/1.07  
% 3.72/1.07  fof(f9,axiom,(
% 3.72/1.07    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f38,plain,(
% 3.72/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f9])).
% 3.72/1.07  
% 3.72/1.07  fof(f6,axiom,(
% 3.72/1.07    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f35,plain,(
% 3.72/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f6])).
% 3.72/1.07  
% 3.72/1.07  fof(f47,plain,(
% 3.72/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.72/1.07    inference(definition_unfolding,[],[f38,f35])).
% 3.72/1.07  
% 3.72/1.07  fof(f57,plain,(
% 3.72/1.07    k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 3.72/1.07    inference(definition_unfolding,[],[f46,f47,f52,f51,f51])).
% 3.72/1.07  
% 3.72/1.07  fof(f4,axiom,(
% 3.72/1.07    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f22,plain,(
% 3.72/1.07    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.72/1.07    inference(nnf_transformation,[],[f4])).
% 3.72/1.07  
% 3.72/1.07  fof(f23,plain,(
% 3.72/1.07    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.72/1.07    inference(flattening,[],[f22])).
% 3.72/1.07  
% 3.72/1.07  fof(f31,plain,(
% 3.72/1.07    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.72/1.07    inference(cnf_transformation,[],[f23])).
% 3.72/1.07  
% 3.72/1.07  fof(f58,plain,(
% 3.72/1.07    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.72/1.07    inference(equality_resolution,[],[f31])).
% 3.72/1.07  
% 3.72/1.07  fof(f5,axiom,(
% 3.72/1.07    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f24,plain,(
% 3.72/1.07    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.72/1.07    inference(nnf_transformation,[],[f5])).
% 3.72/1.07  
% 3.72/1.07  fof(f34,plain,(
% 3.72/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f24])).
% 3.72/1.07  
% 3.72/1.07  fof(f54,plain,(
% 3.72/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.72/1.07    inference(definition_unfolding,[],[f34,f35])).
% 3.72/1.07  
% 3.72/1.07  fof(f8,axiom,(
% 3.72/1.07    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f37,plain,(
% 3.72/1.07    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f8])).
% 3.72/1.07  
% 3.72/1.07  fof(f3,axiom,(
% 3.72/1.07    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f19,plain,(
% 3.72/1.07    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.72/1.07    inference(rectify,[],[f3])).
% 3.72/1.07  
% 3.72/1.07  fof(f29,plain,(
% 3.72/1.07    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.72/1.07    inference(cnf_transformation,[],[f19])).
% 3.72/1.07  
% 3.72/1.07  fof(f53,plain,(
% 3.72/1.07    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 3.72/1.07    inference(definition_unfolding,[],[f29,f47])).
% 3.72/1.07  
% 3.72/1.07  fof(f2,axiom,(
% 3.72/1.07    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.72/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.07  
% 3.72/1.07  fof(f28,plain,(
% 3.72/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.72/1.07    inference(cnf_transformation,[],[f2])).
% 3.72/1.07  
% 3.72/1.07  cnf(c_10,plain,
% 3.72/1.07      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 3.72/1.07      inference(cnf_transformation,[],[f56]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_363,plain,
% 3.72/1.07      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 3.72/1.07      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_8,plain,
% 3.72/1.07      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.72/1.07      inference(cnf_transformation,[],[f36]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_364,plain,
% 3.72/1.07      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.72/1.07      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_851,plain,
% 3.72/1.07      ( k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_363,c_364]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_0,plain,
% 3.72/1.07      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.72/1.07      inference(cnf_transformation,[],[f27]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_11,negated_conjecture,
% 3.72/1.07      ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 3.72/1.07      inference(cnf_transformation,[],[f57]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_446,plain,
% 3.72/1.07      ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 3.72/1.07      inference(demodulation,[status(thm)],[c_0,c_11]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_14924,plain,
% 3.72/1.07      ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 3.72/1.07      inference(demodulation,[status(thm)],[c_851,c_446]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f58]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_367,plain,
% 3.72/1.07      ( r1_tarski(X0,X0) = iProver_top ),
% 3.72/1.07      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_6,plain,
% 3.72/1.07      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.72/1.07      inference(cnf_transformation,[],[f54]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_366,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.72/1.07      | r1_tarski(X0,X1) != iProver_top ),
% 3.72/1.07      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_3437,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_367,c_366]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_850,plain,
% 3.72/1.07      ( k3_xboole_0(X0,X0) = X0 ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_367,c_364]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_3442,plain,
% 3.72/1.07      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.72/1.07      inference(light_normalisation,[status(thm)],[c_3437,c_850]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_9,plain,
% 3.72/1.07      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.72/1.07      inference(cnf_transformation,[],[f37]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_4299,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_3442,c_9]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_2,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 3.72/1.07      inference(cnf_transformation,[],[f53]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_589,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X1)) = k5_xboole_0(X0,X1) ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_2,c_9]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_1028,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X0,X1) ),
% 3.72/1.07      inference(demodulation,[status(thm)],[c_850,c_589]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_1,plain,
% 3.72/1.07      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.72/1.07      inference(cnf_transformation,[],[f28]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_408,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_1160,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),X1)) = k5_xboole_0(X1,X0) ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_1028,c_408]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_1134,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X1) ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_1,c_1028]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_2810,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k5_xboole_0(k5_xboole_0(X0,X0),X0) ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_1160,c_1134]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_1029,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 3.72/1.07      inference(demodulation,[status(thm)],[c_850,c_2]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_409,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_1100,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X1,X0) ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_1029,c_409]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_1101,plain,
% 3.72/1.07      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_1029,c_408]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_2818,plain,
% 3.72/1.07      ( k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
% 3.72/1.07      inference(demodulation,[status(thm)],[c_2810,c_1029,c_1100,c_1101]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_4249,plain,
% 3.72/1.07      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.72/1.07      inference(demodulation,[status(thm)],[c_3442,c_2818]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_5006,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 3.72/1.07      inference(demodulation,[status(thm)],[c_4299,c_4249]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_5042,plain,
% 3.72/1.07      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 3.72/1.07      inference(superposition,[status(thm)],[c_5006,c_409]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_14925,plain,
% 3.72/1.07      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 3.72/1.07      inference(demodulation,[status(thm)],[c_14924,c_5042]) ).
% 3.72/1.07  
% 3.72/1.07  cnf(c_14926,plain,
% 3.72/1.07      ( $false ),
% 3.72/1.07      inference(equality_resolution_simp,[status(thm)],[c_14925]) ).
% 3.72/1.07  
% 3.72/1.07  
% 3.72/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/1.07  
% 3.72/1.07  ------                               Statistics
% 3.72/1.07  
% 3.72/1.07  ------ General
% 3.72/1.07  
% 3.72/1.07  abstr_ref_over_cycles:                  0
% 3.72/1.07  abstr_ref_under_cycles:                 0
% 3.72/1.07  gc_basic_clause_elim:                   0
% 3.72/1.07  forced_gc_time:                         0
% 3.72/1.07  parsing_time:                           0.011
% 3.72/1.07  unif_index_cands_time:                  0.
% 3.72/1.07  unif_index_add_time:                    0.
% 3.72/1.07  orderings_time:                         0.
% 3.72/1.07  out_proof_time:                         0.008
% 3.72/1.07  total_time:                             0.511
% 3.72/1.07  num_of_symbols:                         38
% 3.72/1.07  num_of_terms:                           14900
% 3.72/1.07  
% 3.72/1.07  ------ Preprocessing
% 3.72/1.07  
% 3.72/1.07  num_of_splits:                          0
% 3.72/1.07  num_of_split_atoms:                     0
% 3.72/1.07  num_of_reused_defs:                     0
% 3.72/1.07  num_eq_ax_congr_red:                    0
% 3.72/1.07  num_of_sem_filtered_clauses:            1
% 3.72/1.07  num_of_subtypes:                        0
% 3.72/1.07  monotx_restored_types:                  0
% 3.72/1.07  sat_num_of_epr_types:                   0
% 3.72/1.07  sat_num_of_non_cyclic_types:            0
% 3.72/1.07  sat_guarded_non_collapsed_types:        0
% 3.72/1.07  num_pure_diseq_elim:                    0
% 3.72/1.07  simp_replaced_by:                       0
% 3.72/1.07  res_preprocessed:                       57
% 3.72/1.07  prep_upred:                             0
% 3.72/1.07  prep_unflattend:                        0
% 3.72/1.07  smt_new_axioms:                         0
% 3.72/1.07  pred_elim_cands:                        1
% 3.72/1.07  pred_elim:                              0
% 3.72/1.07  pred_elim_cl:                           0
% 3.72/1.07  pred_elim_cycles:                       2
% 3.72/1.07  merged_defs:                            8
% 3.72/1.07  merged_defs_ncl:                        0
% 3.72/1.07  bin_hyper_res:                          8
% 3.72/1.07  prep_cycles:                            4
% 3.72/1.07  pred_elim_time:                         0.
% 3.72/1.07  splitting_time:                         0.
% 3.72/1.07  sem_filter_time:                        0.
% 3.72/1.07  monotx_time:                            0.001
% 3.72/1.07  subtype_inf_time:                       0.
% 3.72/1.07  
% 3.72/1.07  ------ Problem properties
% 3.72/1.07  
% 3.72/1.07  clauses:                                11
% 3.72/1.07  conjectures:                            1
% 3.72/1.07  epr:                                    2
% 3.72/1.07  horn:                                   11
% 3.72/1.07  ground:                                 1
% 3.72/1.07  unary:                                  7
% 3.72/1.07  binary:                                 3
% 3.72/1.07  lits:                                   16
% 3.72/1.07  lits_eq:                                9
% 3.72/1.07  fd_pure:                                0
% 3.72/1.07  fd_pseudo:                              0
% 3.72/1.07  fd_cond:                                0
% 3.72/1.07  fd_pseudo_cond:                         1
% 3.72/1.07  ac_symbols:                             1
% 3.72/1.07  
% 3.72/1.07  ------ Propositional Solver
% 3.72/1.07  
% 3.72/1.07  prop_solver_calls:                      32
% 3.72/1.07  prop_fast_solver_calls:                 323
% 3.72/1.07  smt_solver_calls:                       0
% 3.72/1.07  smt_fast_solver_calls:                  0
% 3.72/1.07  prop_num_of_clauses:                    3506
% 3.72/1.07  prop_preprocess_simplified:             5857
% 3.72/1.07  prop_fo_subsumed:                       0
% 3.72/1.07  prop_solver_time:                       0.
% 3.72/1.07  smt_solver_time:                        0.
% 3.72/1.07  smt_fast_solver_time:                   0.
% 3.72/1.07  prop_fast_solver_time:                  0.
% 3.72/1.07  prop_unsat_core_time:                   0.
% 3.72/1.07  
% 3.72/1.07  ------ QBF
% 3.72/1.07  
% 3.72/1.07  qbf_q_res:                              0
% 3.72/1.07  qbf_num_tautologies:                    0
% 3.72/1.07  qbf_prep_cycles:                        0
% 3.72/1.07  
% 3.72/1.07  ------ BMC1
% 3.72/1.07  
% 3.72/1.07  bmc1_current_bound:                     -1
% 3.72/1.07  bmc1_last_solved_bound:                 -1
% 3.72/1.07  bmc1_unsat_core_size:                   -1
% 3.72/1.07  bmc1_unsat_core_parents_size:           -1
% 3.72/1.07  bmc1_merge_next_fun:                    0
% 3.72/1.07  bmc1_unsat_core_clauses_time:           0.
% 3.72/1.07  
% 3.72/1.07  ------ Instantiation
% 3.72/1.07  
% 3.72/1.07  inst_num_of_clauses:                    878
% 3.72/1.07  inst_num_in_passive:                    259
% 3.72/1.07  inst_num_in_active:                     355
% 3.72/1.07  inst_num_in_unprocessed:                264
% 3.72/1.07  inst_num_of_loops:                      360
% 3.72/1.07  inst_num_of_learning_restarts:          0
% 3.72/1.07  inst_num_moves_active_passive:          0
% 3.72/1.07  inst_lit_activity:                      0
% 3.72/1.07  inst_lit_activity_moves:                0
% 3.72/1.07  inst_num_tautologies:                   0
% 3.72/1.07  inst_num_prop_implied:                  0
% 3.72/1.07  inst_num_existing_simplified:           0
% 3.72/1.07  inst_num_eq_res_simplified:             0
% 3.72/1.07  inst_num_child_elim:                    0
% 3.72/1.07  inst_num_of_dismatching_blockings:      157
% 3.72/1.07  inst_num_of_non_proper_insts:           942
% 3.72/1.07  inst_num_of_duplicates:                 0
% 3.72/1.07  inst_inst_num_from_inst_to_res:         0
% 3.72/1.07  inst_dismatching_checking_time:         0.
% 3.72/1.07  
% 3.72/1.07  ------ Resolution
% 3.72/1.07  
% 3.72/1.07  res_num_of_clauses:                     0
% 3.72/1.07  res_num_in_passive:                     0
% 3.72/1.07  res_num_in_active:                      0
% 3.72/1.07  res_num_of_loops:                       61
% 3.72/1.07  res_forward_subset_subsumed:            142
% 3.72/1.07  res_backward_subset_subsumed:           0
% 3.72/1.07  res_forward_subsumed:                   0
% 3.72/1.07  res_backward_subsumed:                  0
% 3.72/1.07  res_forward_subsumption_resolution:     0
% 3.72/1.07  res_backward_subsumption_resolution:    0
% 3.72/1.07  res_clause_to_clause_subsumption:       31441
% 3.72/1.07  res_orphan_elimination:                 0
% 3.72/1.07  res_tautology_del:                      94
% 3.72/1.07  res_num_eq_res_simplified:              0
% 3.72/1.07  res_num_sel_changes:                    0
% 3.72/1.07  res_moves_from_active_to_pass:          0
% 3.72/1.07  
% 3.72/1.07  ------ Superposition
% 3.72/1.07  
% 3.72/1.07  sup_time_total:                         0.
% 3.72/1.07  sup_time_generating:                    0.
% 3.72/1.07  sup_time_sim_full:                      0.
% 3.72/1.07  sup_time_sim_immed:                     0.
% 3.72/1.07  
% 3.72/1.07  sup_num_of_clauses:                     1212
% 3.72/1.07  sup_num_in_active:                      45
% 3.72/1.07  sup_num_in_passive:                     1167
% 3.72/1.07  sup_num_of_loops:                       71
% 3.72/1.07  sup_fw_superposition:                   3064
% 3.72/1.07  sup_bw_superposition:                   2225
% 3.72/1.07  sup_immediate_simplified:               1388
% 3.72/1.07  sup_given_eliminated:                   1
% 3.72/1.07  comparisons_done:                       0
% 3.72/1.07  comparisons_avoided:                    0
% 3.72/1.07  
% 3.72/1.07  ------ Simplifications
% 3.72/1.07  
% 3.72/1.07  
% 3.72/1.07  sim_fw_subset_subsumed:                 1
% 3.72/1.07  sim_bw_subset_subsumed:                 0
% 3.72/1.07  sim_fw_subsumed:                        133
% 3.72/1.07  sim_bw_subsumed:                        5
% 3.72/1.07  sim_fw_subsumption_res:                 0
% 3.72/1.07  sim_bw_subsumption_res:                 0
% 3.72/1.07  sim_tautology_del:                      0
% 3.72/1.07  sim_eq_tautology_del:                   161
% 3.72/1.07  sim_eq_res_simp:                        0
% 3.72/1.07  sim_fw_demodulated:                     476
% 3.72/1.07  sim_bw_demodulated:                     75
% 3.72/1.07  sim_light_normalised:                   647
% 3.72/1.07  sim_joinable_taut:                      182
% 3.72/1.07  sim_joinable_simp:                      0
% 3.72/1.07  sim_ac_normalised:                      0
% 3.72/1.07  sim_smt_subsumption:                    0
% 3.72/1.07  
%------------------------------------------------------------------------------
