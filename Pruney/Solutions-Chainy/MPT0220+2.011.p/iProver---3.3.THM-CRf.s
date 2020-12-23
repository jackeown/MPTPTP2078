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
% DateTime   : Thu Dec  3 11:29:29 EST 2020

% Result     : Theorem 11.35s
% Output     : CNFRefutation 11.35s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 291 expanded)
%              Number of clauses        :   36 (  78 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  119 ( 393 expanded)
%              Number of equality atoms :   91 ( 295 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f54,f53])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f18])).

fof(f21,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f19])).

fof(f25,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f25])).

fof(f47,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f59,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f47,f48,f54,f53,f53])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f35,f48])).

cnf(c_10,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_358,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_359,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1285,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_358,c_359])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_541,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_11])).

cnf(c_36633,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1285,c_541])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_362,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_361,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2445,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_362,c_361])).

cnf(c_1284,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_362,c_359])).

cnf(c_2448,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2445,c_1284])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_372,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_2987,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2448,c_372])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_617,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_932,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_372,c_617])).

cnf(c_370,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_790,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_370,c_7])).

cnf(c_933,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_372,c_790])).

cnf(c_1288,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1284,c_933])).

cnf(c_1368,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1288,c_9])).

cnf(c_1471,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_9,c_1368])).

cnf(c_1664,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_932,c_1471])).

cnf(c_1680,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1664,c_932])).

cnf(c_1927,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_1680,c_372])).

cnf(c_2965,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_2448,c_1927])).

cnf(c_3007,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_2987,c_2965])).

cnf(c_36634,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_36633,c_3007])).

cnf(c_36635,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_36634])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n017.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 09:39:01 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 11.35/2.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.35/2.05  
% 11.35/2.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.35/2.05  
% 11.35/2.05  ------  iProver source info
% 11.35/2.05  
% 11.35/2.05  git: date: 2020-06-30 10:37:57 +0100
% 11.35/2.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.35/2.05  git: non_committed_changes: false
% 11.35/2.05  git: last_make_outside_of_git: false
% 11.35/2.05  
% 11.35/2.05  ------ 
% 11.35/2.05  
% 11.35/2.05  ------ Input Options
% 11.35/2.05  
% 11.35/2.05  --out_options                           all
% 11.35/2.05  --tptp_safe_out                         true
% 11.35/2.05  --problem_path                          ""
% 11.35/2.05  --include_path                          ""
% 11.35/2.05  --clausifier                            res/vclausify_rel
% 11.35/2.05  --clausifier_options                    ""
% 11.35/2.05  --stdin                                 false
% 11.35/2.05  --stats_out                             all
% 11.35/2.05  
% 11.35/2.05  ------ General Options
% 11.35/2.05  
% 11.35/2.05  --fof                                   false
% 11.35/2.05  --time_out_real                         305.
% 11.35/2.05  --time_out_virtual                      -1.
% 11.35/2.05  --symbol_type_check                     false
% 11.35/2.05  --clausify_out                          false
% 11.35/2.05  --sig_cnt_out                           false
% 11.35/2.05  --trig_cnt_out                          false
% 11.35/2.05  --trig_cnt_out_tolerance                1.
% 11.35/2.05  --trig_cnt_out_sk_spl                   false
% 11.35/2.05  --abstr_cl_out                          false
% 11.35/2.05  
% 11.35/2.05  ------ Global Options
% 11.35/2.05  
% 11.35/2.05  --schedule                              default
% 11.35/2.05  --add_important_lit                     false
% 11.35/2.05  --prop_solver_per_cl                    1000
% 11.35/2.05  --min_unsat_core                        false
% 11.35/2.05  --soft_assumptions                      false
% 11.35/2.05  --soft_lemma_size                       3
% 11.35/2.05  --prop_impl_unit_size                   0
% 11.35/2.05  --prop_impl_unit                        []
% 11.35/2.05  --share_sel_clauses                     true
% 11.35/2.05  --reset_solvers                         false
% 11.35/2.05  --bc_imp_inh                            [conj_cone]
% 11.35/2.05  --conj_cone_tolerance                   3.
% 11.35/2.05  --extra_neg_conj                        none
% 11.35/2.05  --large_theory_mode                     true
% 11.35/2.05  --prolific_symb_bound                   200
% 11.35/2.05  --lt_threshold                          2000
% 11.35/2.05  --clause_weak_htbl                      true
% 11.35/2.05  --gc_record_bc_elim                     false
% 11.35/2.05  
% 11.35/2.05  ------ Preprocessing Options
% 11.35/2.05  
% 11.35/2.05  --preprocessing_flag                    true
% 11.35/2.05  --time_out_prep_mult                    0.1
% 11.35/2.05  --splitting_mode                        input
% 11.35/2.05  --splitting_grd                         true
% 11.35/2.05  --splitting_cvd                         false
% 11.35/2.05  --splitting_cvd_svl                     false
% 11.35/2.05  --splitting_nvd                         32
% 11.35/2.05  --sub_typing                            true
% 11.35/2.05  --prep_gs_sim                           true
% 11.35/2.05  --prep_unflatten                        true
% 11.35/2.05  --prep_res_sim                          true
% 11.35/2.05  --prep_upred                            true
% 11.35/2.05  --prep_sem_filter                       exhaustive
% 11.35/2.05  --prep_sem_filter_out                   false
% 11.35/2.05  --pred_elim                             true
% 11.35/2.05  --res_sim_input                         true
% 11.35/2.05  --eq_ax_congr_red                       true
% 11.35/2.05  --pure_diseq_elim                       true
% 11.35/2.05  --brand_transform                       false
% 11.35/2.05  --non_eq_to_eq                          false
% 11.35/2.05  --prep_def_merge                        true
% 11.35/2.05  --prep_def_merge_prop_impl              false
% 11.35/2.05  --prep_def_merge_mbd                    true
% 11.35/2.05  --prep_def_merge_tr_red                 false
% 11.35/2.05  --prep_def_merge_tr_cl                  false
% 11.35/2.05  --smt_preprocessing                     true
% 11.35/2.05  --smt_ac_axioms                         fast
% 11.35/2.05  --preprocessed_out                      false
% 11.35/2.05  --preprocessed_stats                    false
% 11.35/2.05  
% 11.35/2.05  ------ Abstraction refinement Options
% 11.35/2.05  
% 11.35/2.05  --abstr_ref                             []
% 11.35/2.05  --abstr_ref_prep                        false
% 11.35/2.05  --abstr_ref_until_sat                   false
% 11.35/2.05  --abstr_ref_sig_restrict                funpre
% 11.35/2.05  --abstr_ref_af_restrict_to_split_sk     false
% 11.35/2.05  --abstr_ref_under                       []
% 11.35/2.05  
% 11.35/2.05  ------ SAT Options
% 11.35/2.05  
% 11.35/2.05  --sat_mode                              false
% 11.35/2.05  --sat_fm_restart_options                ""
% 11.35/2.05  --sat_gr_def                            false
% 11.35/2.05  --sat_epr_types                         true
% 11.35/2.05  --sat_non_cyclic_types                  false
% 11.35/2.05  --sat_finite_models                     false
% 11.35/2.05  --sat_fm_lemmas                         false
% 11.35/2.05  --sat_fm_prep                           false
% 11.35/2.05  --sat_fm_uc_incr                        true
% 11.35/2.05  --sat_out_model                         small
% 11.35/2.05  --sat_out_clauses                       false
% 11.35/2.05  
% 11.35/2.05  ------ QBF Options
% 11.35/2.05  
% 11.35/2.05  --qbf_mode                              false
% 11.35/2.05  --qbf_elim_univ                         false
% 11.35/2.05  --qbf_dom_inst                          none
% 11.35/2.05  --qbf_dom_pre_inst                      false
% 11.35/2.05  --qbf_sk_in                             false
% 11.35/2.05  --qbf_pred_elim                         true
% 11.35/2.05  --qbf_split                             512
% 11.35/2.05  
% 11.35/2.05  ------ BMC1 Options
% 11.35/2.05  
% 11.35/2.05  --bmc1_incremental                      false
% 11.35/2.05  --bmc1_axioms                           reachable_all
% 11.35/2.05  --bmc1_min_bound                        0
% 11.35/2.05  --bmc1_max_bound                        -1
% 11.35/2.05  --bmc1_max_bound_default                -1
% 11.35/2.05  --bmc1_symbol_reachability              true
% 11.35/2.05  --bmc1_property_lemmas                  false
% 11.35/2.05  --bmc1_k_induction                      false
% 11.35/2.05  --bmc1_non_equiv_states                 false
% 11.35/2.05  --bmc1_deadlock                         false
% 11.35/2.05  --bmc1_ucm                              false
% 11.35/2.05  --bmc1_add_unsat_core                   none
% 11.35/2.05  --bmc1_unsat_core_children              false
% 11.35/2.05  --bmc1_unsat_core_extrapolate_axioms    false
% 11.35/2.05  --bmc1_out_stat                         full
% 11.35/2.05  --bmc1_ground_init                      false
% 11.35/2.05  --bmc1_pre_inst_next_state              false
% 11.35/2.05  --bmc1_pre_inst_state                   false
% 11.35/2.05  --bmc1_pre_inst_reach_state             false
% 11.35/2.05  --bmc1_out_unsat_core                   false
% 11.35/2.05  --bmc1_aig_witness_out                  false
% 11.35/2.05  --bmc1_verbose                          false
% 11.35/2.05  --bmc1_dump_clauses_tptp                false
% 11.35/2.05  --bmc1_dump_unsat_core_tptp             false
% 11.35/2.05  --bmc1_dump_file                        -
% 11.35/2.05  --bmc1_ucm_expand_uc_limit              128
% 11.35/2.05  --bmc1_ucm_n_expand_iterations          6
% 11.35/2.05  --bmc1_ucm_extend_mode                  1
% 11.35/2.05  --bmc1_ucm_init_mode                    2
% 11.35/2.05  --bmc1_ucm_cone_mode                    none
% 11.35/2.05  --bmc1_ucm_reduced_relation_type        0
% 11.35/2.05  --bmc1_ucm_relax_model                  4
% 11.35/2.05  --bmc1_ucm_full_tr_after_sat            true
% 11.35/2.05  --bmc1_ucm_expand_neg_assumptions       false
% 11.35/2.05  --bmc1_ucm_layered_model                none
% 11.35/2.05  --bmc1_ucm_max_lemma_size               10
% 11.35/2.05  
% 11.35/2.05  ------ AIG Options
% 11.35/2.05  
% 11.35/2.05  --aig_mode                              false
% 11.35/2.05  
% 11.35/2.05  ------ Instantiation Options
% 11.35/2.05  
% 11.35/2.05  --instantiation_flag                    true
% 11.35/2.05  --inst_sos_flag                         true
% 11.35/2.05  --inst_sos_phase                        true
% 11.35/2.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.35/2.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.35/2.05  --inst_lit_sel_side                     num_symb
% 11.35/2.05  --inst_solver_per_active                1400
% 11.35/2.05  --inst_solver_calls_frac                1.
% 11.35/2.05  --inst_passive_queue_type               priority_queues
% 11.35/2.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.35/2.05  --inst_passive_queues_freq              [25;2]
% 11.35/2.05  --inst_dismatching                      true
% 11.35/2.05  --inst_eager_unprocessed_to_passive     true
% 11.35/2.05  --inst_prop_sim_given                   true
% 11.35/2.05  --inst_prop_sim_new                     false
% 11.35/2.05  --inst_subs_new                         false
% 11.35/2.05  --inst_eq_res_simp                      false
% 11.35/2.05  --inst_subs_given                       false
% 11.35/2.05  --inst_orphan_elimination               true
% 11.35/2.05  --inst_learning_loop_flag               true
% 11.35/2.05  --inst_learning_start                   3000
% 11.35/2.05  --inst_learning_factor                  2
% 11.35/2.05  --inst_start_prop_sim_after_learn       3
% 11.35/2.05  --inst_sel_renew                        solver
% 11.35/2.05  --inst_lit_activity_flag                true
% 11.35/2.05  --inst_restr_to_given                   false
% 11.35/2.05  --inst_activity_threshold               500
% 11.35/2.05  --inst_out_proof                        true
% 11.35/2.05  
% 11.35/2.05  ------ Resolution Options
% 11.35/2.05  
% 11.35/2.05  --resolution_flag                       true
% 11.35/2.05  --res_lit_sel                           adaptive
% 11.35/2.05  --res_lit_sel_side                      none
% 11.35/2.05  --res_ordering                          kbo
% 11.35/2.05  --res_to_prop_solver                    active
% 11.35/2.05  --res_prop_simpl_new                    false
% 11.35/2.05  --res_prop_simpl_given                  true
% 11.35/2.05  --res_passive_queue_type                priority_queues
% 11.35/2.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.35/2.05  --res_passive_queues_freq               [15;5]
% 11.35/2.05  --res_forward_subs                      full
% 11.35/2.05  --res_backward_subs                     full
% 11.35/2.05  --res_forward_subs_resolution           true
% 11.35/2.05  --res_backward_subs_resolution          true
% 11.35/2.05  --res_orphan_elimination                true
% 11.35/2.05  --res_time_limit                        2.
% 11.35/2.05  --res_out_proof                         true
% 11.35/2.05  
% 11.35/2.05  ------ Superposition Options
% 11.35/2.05  
% 11.35/2.05  --superposition_flag                    true
% 11.35/2.05  --sup_passive_queue_type                priority_queues
% 11.35/2.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.35/2.05  --sup_passive_queues_freq               [8;1;4]
% 11.35/2.05  --demod_completeness_check              fast
% 11.35/2.05  --demod_use_ground                      true
% 11.35/2.05  --sup_to_prop_solver                    passive
% 11.35/2.05  --sup_prop_simpl_new                    true
% 11.35/2.05  --sup_prop_simpl_given                  true
% 11.35/2.05  --sup_fun_splitting                     true
% 11.35/2.05  --sup_smt_interval                      50000
% 11.35/2.05  
% 11.35/2.05  ------ Superposition Simplification Setup
% 11.35/2.05  
% 11.35/2.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.35/2.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.35/2.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.35/2.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.35/2.05  --sup_full_triv                         [TrivRules;PropSubs]
% 11.35/2.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.35/2.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.35/2.05  --sup_immed_triv                        [TrivRules]
% 11.35/2.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.35/2.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.35/2.05  --sup_immed_bw_main                     []
% 11.35/2.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.35/2.05  --sup_input_triv                        [Unflattening;TrivRules]
% 11.35/2.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.35/2.05  --sup_input_bw                          []
% 11.35/2.05  
% 11.35/2.05  ------ Combination Options
% 11.35/2.05  
% 11.35/2.05  --comb_res_mult                         3
% 11.35/2.05  --comb_sup_mult                         2
% 11.35/2.05  --comb_inst_mult                        10
% 11.35/2.05  
% 11.35/2.05  ------ Debug Options
% 11.35/2.05  
% 11.35/2.05  --dbg_backtrace                         false
% 11.35/2.05  --dbg_dump_prop_clauses                 false
% 11.35/2.05  --dbg_dump_prop_clauses_file            -
% 11.35/2.05  --dbg_out_stat                          false
% 11.35/2.05  ------ Parsing...
% 11.35/2.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.35/2.05  
% 11.35/2.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.35/2.05  
% 11.35/2.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.35/2.05  
% 11.35/2.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.35/2.05  ------ Proving...
% 11.35/2.05  ------ Problem Properties 
% 11.35/2.05  
% 11.35/2.05  
% 11.35/2.05  clauses                                 11
% 11.35/2.05  conjectures                             1
% 11.35/2.05  EPR                                     2
% 11.35/2.05  Horn                                    11
% 11.35/2.05  unary                                   7
% 11.35/2.05  binary                                  3
% 11.35/2.05  lits                                    16
% 11.35/2.05  lits eq                                 9
% 11.35/2.05  fd_pure                                 0
% 11.35/2.05  fd_pseudo                               0
% 11.35/2.05  fd_cond                                 0
% 11.35/2.05  fd_pseudo_cond                          1
% 11.35/2.05  AC symbols                              1
% 11.35/2.05  
% 11.35/2.05  ------ Schedule dynamic 5 is on 
% 11.35/2.05  
% 11.35/2.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.35/2.05  
% 11.35/2.05  
% 11.35/2.05  ------ 
% 11.35/2.05  Current options:
% 11.35/2.05  ------ 
% 11.35/2.05  
% 11.35/2.05  ------ Input Options
% 11.35/2.05  
% 11.35/2.05  --out_options                           all
% 11.35/2.05  --tptp_safe_out                         true
% 11.35/2.05  --problem_path                          ""
% 11.35/2.05  --include_path                          ""
% 11.35/2.05  --clausifier                            res/vclausify_rel
% 11.35/2.05  --clausifier_options                    ""
% 11.35/2.05  --stdin                                 false
% 11.35/2.05  --stats_out                             all
% 11.35/2.05  
% 11.35/2.05  ------ General Options
% 11.35/2.05  
% 11.35/2.05  --fof                                   false
% 11.35/2.05  --time_out_real                         305.
% 11.35/2.05  --time_out_virtual                      -1.
% 11.35/2.05  --symbol_type_check                     false
% 11.35/2.05  --clausify_out                          false
% 11.35/2.05  --sig_cnt_out                           false
% 11.35/2.05  --trig_cnt_out                          false
% 11.35/2.05  --trig_cnt_out_tolerance                1.
% 11.35/2.05  --trig_cnt_out_sk_spl                   false
% 11.35/2.05  --abstr_cl_out                          false
% 11.35/2.05  
% 11.35/2.05  ------ Global Options
% 11.35/2.05  
% 11.35/2.05  --schedule                              default
% 11.35/2.05  --add_important_lit                     false
% 11.35/2.05  --prop_solver_per_cl                    1000
% 11.35/2.05  --min_unsat_core                        false
% 11.35/2.05  --soft_assumptions                      false
% 11.35/2.05  --soft_lemma_size                       3
% 11.35/2.05  --prop_impl_unit_size                   0
% 11.35/2.05  --prop_impl_unit                        []
% 11.35/2.05  --share_sel_clauses                     true
% 11.35/2.05  --reset_solvers                         false
% 11.35/2.05  --bc_imp_inh                            [conj_cone]
% 11.35/2.05  --conj_cone_tolerance                   3.
% 11.35/2.05  --extra_neg_conj                        none
% 11.35/2.05  --large_theory_mode                     true
% 11.35/2.05  --prolific_symb_bound                   200
% 11.35/2.05  --lt_threshold                          2000
% 11.35/2.05  --clause_weak_htbl                      true
% 11.35/2.05  --gc_record_bc_elim                     false
% 11.35/2.05  
% 11.35/2.05  ------ Preprocessing Options
% 11.35/2.05  
% 11.35/2.05  --preprocessing_flag                    true
% 11.35/2.05  --time_out_prep_mult                    0.1
% 11.35/2.05  --splitting_mode                        input
% 11.35/2.05  --splitting_grd                         true
% 11.35/2.05  --splitting_cvd                         false
% 11.35/2.05  --splitting_cvd_svl                     false
% 11.35/2.05  --splitting_nvd                         32
% 11.35/2.05  --sub_typing                            true
% 11.35/2.05  --prep_gs_sim                           true
% 11.35/2.05  --prep_unflatten                        true
% 11.35/2.05  --prep_res_sim                          true
% 11.35/2.05  --prep_upred                            true
% 11.35/2.05  --prep_sem_filter                       exhaustive
% 11.35/2.05  --prep_sem_filter_out                   false
% 11.35/2.05  --pred_elim                             true
% 11.35/2.05  --res_sim_input                         true
% 11.35/2.05  --eq_ax_congr_red                       true
% 11.35/2.05  --pure_diseq_elim                       true
% 11.35/2.05  --brand_transform                       false
% 11.35/2.05  --non_eq_to_eq                          false
% 11.35/2.05  --prep_def_merge                        true
% 11.35/2.05  --prep_def_merge_prop_impl              false
% 11.35/2.05  --prep_def_merge_mbd                    true
% 11.35/2.05  --prep_def_merge_tr_red                 false
% 11.35/2.05  --prep_def_merge_tr_cl                  false
% 11.35/2.05  --smt_preprocessing                     true
% 11.35/2.05  --smt_ac_axioms                         fast
% 11.35/2.05  --preprocessed_out                      false
% 11.35/2.05  --preprocessed_stats                    false
% 11.35/2.05  
% 11.35/2.05  ------ Abstraction refinement Options
% 11.35/2.05  
% 11.35/2.05  --abstr_ref                             []
% 11.35/2.05  --abstr_ref_prep                        false
% 11.35/2.05  --abstr_ref_until_sat                   false
% 11.35/2.05  --abstr_ref_sig_restrict                funpre
% 11.35/2.05  --abstr_ref_af_restrict_to_split_sk     false
% 11.35/2.05  --abstr_ref_under                       []
% 11.35/2.05  
% 11.35/2.05  ------ SAT Options
% 11.35/2.05  
% 11.35/2.05  --sat_mode                              false
% 11.35/2.05  --sat_fm_restart_options                ""
% 11.35/2.05  --sat_gr_def                            false
% 11.35/2.05  --sat_epr_types                         true
% 11.35/2.05  --sat_non_cyclic_types                  false
% 11.35/2.05  --sat_finite_models                     false
% 11.35/2.05  --sat_fm_lemmas                         false
% 11.35/2.05  --sat_fm_prep                           false
% 11.35/2.05  --sat_fm_uc_incr                        true
% 11.35/2.05  --sat_out_model                         small
% 11.35/2.05  --sat_out_clauses                       false
% 11.35/2.05  
% 11.35/2.05  ------ QBF Options
% 11.35/2.05  
% 11.35/2.05  --qbf_mode                              false
% 11.35/2.05  --qbf_elim_univ                         false
% 11.35/2.05  --qbf_dom_inst                          none
% 11.35/2.05  --qbf_dom_pre_inst                      false
% 11.35/2.05  --qbf_sk_in                             false
% 11.35/2.05  --qbf_pred_elim                         true
% 11.35/2.05  --qbf_split                             512
% 11.35/2.05  
% 11.35/2.05  ------ BMC1 Options
% 11.35/2.05  
% 11.35/2.05  --bmc1_incremental                      false
% 11.35/2.05  --bmc1_axioms                           reachable_all
% 11.35/2.05  --bmc1_min_bound                        0
% 11.35/2.05  --bmc1_max_bound                        -1
% 11.35/2.05  --bmc1_max_bound_default                -1
% 11.35/2.05  --bmc1_symbol_reachability              true
% 11.35/2.05  --bmc1_property_lemmas                  false
% 11.35/2.05  --bmc1_k_induction                      false
% 11.35/2.05  --bmc1_non_equiv_states                 false
% 11.35/2.05  --bmc1_deadlock                         false
% 11.35/2.05  --bmc1_ucm                              false
% 11.35/2.05  --bmc1_add_unsat_core                   none
% 11.35/2.05  --bmc1_unsat_core_children              false
% 11.35/2.05  --bmc1_unsat_core_extrapolate_axioms    false
% 11.35/2.05  --bmc1_out_stat                         full
% 11.35/2.05  --bmc1_ground_init                      false
% 11.35/2.05  --bmc1_pre_inst_next_state              false
% 11.35/2.05  --bmc1_pre_inst_state                   false
% 11.35/2.05  --bmc1_pre_inst_reach_state             false
% 11.35/2.05  --bmc1_out_unsat_core                   false
% 11.35/2.05  --bmc1_aig_witness_out                  false
% 11.35/2.05  --bmc1_verbose                          false
% 11.35/2.05  --bmc1_dump_clauses_tptp                false
% 11.35/2.05  --bmc1_dump_unsat_core_tptp             false
% 11.35/2.05  --bmc1_dump_file                        -
% 11.35/2.05  --bmc1_ucm_expand_uc_limit              128
% 11.35/2.05  --bmc1_ucm_n_expand_iterations          6
% 11.35/2.05  --bmc1_ucm_extend_mode                  1
% 11.35/2.05  --bmc1_ucm_init_mode                    2
% 11.35/2.05  --bmc1_ucm_cone_mode                    none
% 11.35/2.05  --bmc1_ucm_reduced_relation_type        0
% 11.35/2.05  --bmc1_ucm_relax_model                  4
% 11.35/2.05  --bmc1_ucm_full_tr_after_sat            true
% 11.35/2.05  --bmc1_ucm_expand_neg_assumptions       false
% 11.35/2.05  --bmc1_ucm_layered_model                none
% 11.35/2.05  --bmc1_ucm_max_lemma_size               10
% 11.35/2.05  
% 11.35/2.05  ------ AIG Options
% 11.35/2.05  
% 11.35/2.05  --aig_mode                              false
% 11.35/2.05  
% 11.35/2.05  ------ Instantiation Options
% 11.35/2.05  
% 11.35/2.05  --instantiation_flag                    true
% 11.35/2.05  --inst_sos_flag                         true
% 11.35/2.05  --inst_sos_phase                        true
% 11.35/2.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.35/2.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.35/2.05  --inst_lit_sel_side                     none
% 11.35/2.05  --inst_solver_per_active                1400
% 11.35/2.05  --inst_solver_calls_frac                1.
% 11.35/2.05  --inst_passive_queue_type               priority_queues
% 11.35/2.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.35/2.05  --inst_passive_queues_freq              [25;2]
% 11.35/2.05  --inst_dismatching                      true
% 11.35/2.05  --inst_eager_unprocessed_to_passive     true
% 11.35/2.05  --inst_prop_sim_given                   true
% 11.35/2.05  --inst_prop_sim_new                     false
% 11.35/2.05  --inst_subs_new                         false
% 11.35/2.05  --inst_eq_res_simp                      false
% 11.35/2.05  --inst_subs_given                       false
% 11.35/2.05  --inst_orphan_elimination               true
% 11.35/2.05  --inst_learning_loop_flag               true
% 11.35/2.05  --inst_learning_start                   3000
% 11.35/2.05  --inst_learning_factor                  2
% 11.35/2.05  --inst_start_prop_sim_after_learn       3
% 11.35/2.05  --inst_sel_renew                        solver
% 11.35/2.05  --inst_lit_activity_flag                true
% 11.35/2.05  --inst_restr_to_given                   false
% 11.35/2.05  --inst_activity_threshold               500
% 11.35/2.05  --inst_out_proof                        true
% 11.35/2.05  
% 11.35/2.05  ------ Resolution Options
% 11.35/2.05  
% 11.35/2.05  --resolution_flag                       false
% 11.35/2.05  --res_lit_sel                           adaptive
% 11.35/2.05  --res_lit_sel_side                      none
% 11.35/2.05  --res_ordering                          kbo
% 11.35/2.05  --res_to_prop_solver                    active
% 11.35/2.05  --res_prop_simpl_new                    false
% 11.35/2.05  --res_prop_simpl_given                  true
% 11.35/2.06  --res_passive_queue_type                priority_queues
% 11.35/2.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.35/2.06  --res_passive_queues_freq               [15;5]
% 11.35/2.06  --res_forward_subs                      full
% 11.35/2.06  --res_backward_subs                     full
% 11.35/2.06  --res_forward_subs_resolution           true
% 11.35/2.06  --res_backward_subs_resolution          true
% 11.35/2.06  --res_orphan_elimination                true
% 11.35/2.06  --res_time_limit                        2.
% 11.35/2.06  --res_out_proof                         true
% 11.35/2.06  
% 11.35/2.06  ------ Superposition Options
% 11.35/2.06  
% 11.35/2.06  --superposition_flag                    true
% 11.35/2.06  --sup_passive_queue_type                priority_queues
% 11.35/2.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.35/2.06  --sup_passive_queues_freq               [8;1;4]
% 11.35/2.06  --demod_completeness_check              fast
% 11.35/2.06  --demod_use_ground                      true
% 11.35/2.06  --sup_to_prop_solver                    passive
% 11.35/2.06  --sup_prop_simpl_new                    true
% 11.35/2.06  --sup_prop_simpl_given                  true
% 11.35/2.06  --sup_fun_splitting                     true
% 11.35/2.06  --sup_smt_interval                      50000
% 11.35/2.06  
% 11.35/2.06  ------ Superposition Simplification Setup
% 11.35/2.06  
% 11.35/2.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.35/2.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.35/2.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.35/2.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.35/2.06  --sup_full_triv                         [TrivRules;PropSubs]
% 11.35/2.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.35/2.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.35/2.06  --sup_immed_triv                        [TrivRules]
% 11.35/2.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.35/2.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.35/2.06  --sup_immed_bw_main                     []
% 11.35/2.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.35/2.06  --sup_input_triv                        [Unflattening;TrivRules]
% 11.35/2.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.35/2.06  --sup_input_bw                          []
% 11.35/2.06  
% 11.35/2.06  ------ Combination Options
% 11.35/2.06  
% 11.35/2.06  --comb_res_mult                         3
% 11.35/2.06  --comb_sup_mult                         2
% 11.35/2.06  --comb_inst_mult                        10
% 11.35/2.06  
% 11.35/2.06  ------ Debug Options
% 11.35/2.06  
% 11.35/2.06  --dbg_backtrace                         false
% 11.35/2.06  --dbg_dump_prop_clauses                 false
% 11.35/2.06  --dbg_dump_prop_clauses_file            -
% 11.35/2.06  --dbg_out_stat                          false
% 11.35/2.06  
% 11.35/2.06  
% 11.35/2.06  
% 11.35/2.06  
% 11.35/2.06  ------ Proving...
% 11.35/2.06  
% 11.35/2.06  
% 11.35/2.06  % SZS status Theorem for theBenchmark.p
% 11.35/2.06  
% 11.35/2.06   Resolution empty clause
% 11.35/2.06  
% 11.35/2.06  % SZS output start CNFRefutation for theBenchmark.p
% 11.35/2.06  
% 11.35/2.06  fof(f17,axiom,(
% 11.35/2.06    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f46,plain,(
% 11.35/2.06    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 11.35/2.06    inference(cnf_transformation,[],[f17])).
% 11.35/2.06  
% 11.35/2.06  fof(f10,axiom,(
% 11.35/2.06    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f39,plain,(
% 11.35/2.06    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f10])).
% 11.35/2.06  
% 11.35/2.06  fof(f54,plain,(
% 11.35/2.06    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.35/2.06    inference(definition_unfolding,[],[f39,f53])).
% 11.35/2.06  
% 11.35/2.06  fof(f11,axiom,(
% 11.35/2.06    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f40,plain,(
% 11.35/2.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f11])).
% 11.35/2.06  
% 11.35/2.06  fof(f12,axiom,(
% 11.35/2.06    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f41,plain,(
% 11.35/2.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f12])).
% 11.35/2.06  
% 11.35/2.06  fof(f13,axiom,(
% 11.35/2.06    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f42,plain,(
% 11.35/2.06    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f13])).
% 11.35/2.06  
% 11.35/2.06  fof(f14,axiom,(
% 11.35/2.06    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f43,plain,(
% 11.35/2.06    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f14])).
% 11.35/2.06  
% 11.35/2.06  fof(f15,axiom,(
% 11.35/2.06    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f44,plain,(
% 11.35/2.06    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f15])).
% 11.35/2.06  
% 11.35/2.06  fof(f16,axiom,(
% 11.35/2.06    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f45,plain,(
% 11.35/2.06    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f16])).
% 11.35/2.06  
% 11.35/2.06  fof(f49,plain,(
% 11.35/2.06    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.35/2.06    inference(definition_unfolding,[],[f44,f45])).
% 11.35/2.06  
% 11.35/2.06  fof(f50,plain,(
% 11.35/2.06    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.35/2.06    inference(definition_unfolding,[],[f43,f49])).
% 11.35/2.06  
% 11.35/2.06  fof(f51,plain,(
% 11.35/2.06    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.35/2.06    inference(definition_unfolding,[],[f42,f50])).
% 11.35/2.06  
% 11.35/2.06  fof(f52,plain,(
% 11.35/2.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.35/2.06    inference(definition_unfolding,[],[f41,f51])).
% 11.35/2.06  
% 11.35/2.06  fof(f53,plain,(
% 11.35/2.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.35/2.06    inference(definition_unfolding,[],[f40,f52])).
% 11.35/2.06  
% 11.35/2.06  fof(f58,plain,(
% 11.35/2.06    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.35/2.06    inference(definition_unfolding,[],[f46,f54,f53])).
% 11.35/2.06  
% 11.35/2.06  fof(f7,axiom,(
% 11.35/2.06    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f20,plain,(
% 11.35/2.06    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.35/2.06    inference(ennf_transformation,[],[f7])).
% 11.35/2.06  
% 11.35/2.06  fof(f36,plain,(
% 11.35/2.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f20])).
% 11.35/2.06  
% 11.35/2.06  fof(f1,axiom,(
% 11.35/2.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f27,plain,(
% 11.35/2.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f1])).
% 11.35/2.06  
% 11.35/2.06  fof(f18,conjecture,(
% 11.35/2.06    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f19,negated_conjecture,(
% 11.35/2.06    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 11.35/2.06    inference(negated_conjecture,[],[f18])).
% 11.35/2.06  
% 11.35/2.06  fof(f21,plain,(
% 11.35/2.06    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)),
% 11.35/2.06    inference(ennf_transformation,[],[f19])).
% 11.35/2.06  
% 11.35/2.06  fof(f25,plain,(
% 11.35/2.06    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 11.35/2.06    introduced(choice_axiom,[])).
% 11.35/2.06  
% 11.35/2.06  fof(f26,plain,(
% 11.35/2.06    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 11.35/2.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f25])).
% 11.35/2.06  
% 11.35/2.06  fof(f47,plain,(
% 11.35/2.06    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 11.35/2.06    inference(cnf_transformation,[],[f26])).
% 11.35/2.06  
% 11.35/2.06  fof(f9,axiom,(
% 11.35/2.06    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f38,plain,(
% 11.35/2.06    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f9])).
% 11.35/2.06  
% 11.35/2.06  fof(f5,axiom,(
% 11.35/2.06    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f34,plain,(
% 11.35/2.06    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f5])).
% 11.35/2.06  
% 11.35/2.06  fof(f48,plain,(
% 11.35/2.06    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 11.35/2.06    inference(definition_unfolding,[],[f38,f34])).
% 11.35/2.06  
% 11.35/2.06  fof(f59,plain,(
% 11.35/2.06    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 11.35/2.06    inference(definition_unfolding,[],[f47,f48,f54,f53,f53])).
% 11.35/2.06  
% 11.35/2.06  fof(f3,axiom,(
% 11.35/2.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f22,plain,(
% 11.35/2.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.35/2.06    inference(nnf_transformation,[],[f3])).
% 11.35/2.06  
% 11.35/2.06  fof(f23,plain,(
% 11.35/2.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.35/2.06    inference(flattening,[],[f22])).
% 11.35/2.06  
% 11.35/2.06  fof(f29,plain,(
% 11.35/2.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.35/2.06    inference(cnf_transformation,[],[f23])).
% 11.35/2.06  
% 11.35/2.06  fof(f61,plain,(
% 11.35/2.06    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.35/2.06    inference(equality_resolution,[],[f29])).
% 11.35/2.06  
% 11.35/2.06  fof(f4,axiom,(
% 11.35/2.06    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f24,plain,(
% 11.35/2.06    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.35/2.06    inference(nnf_transformation,[],[f4])).
% 11.35/2.06  
% 11.35/2.06  fof(f33,plain,(
% 11.35/2.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f24])).
% 11.35/2.06  
% 11.35/2.06  fof(f55,plain,(
% 11.35/2.06    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.35/2.06    inference(definition_unfolding,[],[f33,f34])).
% 11.35/2.06  
% 11.35/2.06  fof(f8,axiom,(
% 11.35/2.06    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f37,plain,(
% 11.35/2.06    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f8])).
% 11.35/2.06  
% 11.35/2.06  fof(f2,axiom,(
% 11.35/2.06    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f28,plain,(
% 11.35/2.06    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.35/2.06    inference(cnf_transformation,[],[f2])).
% 11.35/2.06  
% 11.35/2.06  fof(f6,axiom,(
% 11.35/2.06    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.35/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.35/2.06  
% 11.35/2.06  fof(f35,plain,(
% 11.35/2.06    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.35/2.06    inference(cnf_transformation,[],[f6])).
% 11.35/2.06  
% 11.35/2.06  fof(f57,plain,(
% 11.35/2.06    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 11.35/2.06    inference(definition_unfolding,[],[f35,f48])).
% 11.35/2.06  
% 11.35/2.06  cnf(c_10,plain,
% 11.35/2.06      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 11.35/2.06      inference(cnf_transformation,[],[f58]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_358,plain,
% 11.35/2.06      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 11.35/2.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_8,plain,
% 11.35/2.06      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.35/2.06      inference(cnf_transformation,[],[f36]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_359,plain,
% 11.35/2.06      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.35/2.06      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_1285,plain,
% 11.35/2.06      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_358,c_359]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_0,plain,
% 11.35/2.06      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.35/2.06      inference(cnf_transformation,[],[f27]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_11,negated_conjecture,
% 11.35/2.06      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 11.35/2.06      inference(cnf_transformation,[],[f59]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_541,plain,
% 11.35/2.06      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 11.35/2.06      inference(demodulation,[status(thm)],[c_0,c_11]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_36633,plain,
% 11.35/2.06      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 11.35/2.06      inference(demodulation,[status(thm)],[c_1285,c_541]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f61]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_362,plain,
% 11.35/2.06      ( r1_tarski(X0,X0) = iProver_top ),
% 11.35/2.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_5,plain,
% 11.35/2.06      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.35/2.06      inference(cnf_transformation,[],[f55]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_361,plain,
% 11.35/2.06      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 11.35/2.06      | r1_tarski(X0,X1) != iProver_top ),
% 11.35/2.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_2445,plain,
% 11.35/2.06      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_362,c_361]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_1284,plain,
% 11.35/2.06      ( k3_xboole_0(X0,X0) = X0 ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_362,c_359]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_2448,plain,
% 11.35/2.06      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.35/2.06      inference(light_normalisation,[status(thm)],[c_2445,c_1284]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_9,plain,
% 11.35/2.06      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.35/2.06      inference(cnf_transformation,[],[f37]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_1,plain,
% 11.35/2.06      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.35/2.06      inference(cnf_transformation,[],[f28]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_372,plain,
% 11.35/2.06      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_2987,plain,
% 11.35/2.06      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_2448,c_372]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_7,plain,
% 11.35/2.06      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 11.35/2.06      inference(cnf_transformation,[],[f57]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_617,plain,
% 11.35/2.06      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_932,plain,
% 11.35/2.06      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) = X0 ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_372,c_617]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_370,plain,
% 11.35/2.06      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_790,plain,
% 11.35/2.06      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_370,c_7]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_933,plain,
% 11.35/2.06      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = X0 ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_372,c_790]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_1288,plain,
% 11.35/2.06      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_1284,c_933]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_1368,plain,
% 11.35/2.06      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_1288,c_9]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_1471,plain,
% 11.35/2.06      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_9,c_1368]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_1664,plain,
% 11.35/2.06      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_932,c_1471]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_1680,plain,
% 11.35/2.06      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.35/2.06      inference(light_normalisation,[status(thm)],[c_1664,c_932]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_1927,plain,
% 11.35/2.06      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
% 11.35/2.06      inference(superposition,[status(thm)],[c_1680,c_372]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_2965,plain,
% 11.35/2.06      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.35/2.06      inference(demodulation,[status(thm)],[c_2448,c_1927]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_3007,plain,
% 11.35/2.06      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 11.35/2.06      inference(demodulation,[status(thm)],[c_2987,c_2965]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_36634,plain,
% 11.35/2.06      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 11.35/2.06      inference(demodulation,[status(thm)],[c_36633,c_3007]) ).
% 11.35/2.06  
% 11.35/2.06  cnf(c_36635,plain,
% 11.35/2.06      ( $false ),
% 11.35/2.06      inference(equality_resolution_simp,[status(thm)],[c_36634]) ).
% 11.35/2.06  
% 11.35/2.06  
% 11.35/2.06  % SZS output end CNFRefutation for theBenchmark.p
% 11.35/2.06  
% 11.35/2.06  ------                               Statistics
% 11.35/2.06  
% 11.35/2.06  ------ General
% 11.35/2.06  
% 11.35/2.06  abstr_ref_over_cycles:                  0
% 11.35/2.06  abstr_ref_under_cycles:                 0
% 11.35/2.06  gc_basic_clause_elim:                   0
% 11.35/2.06  forced_gc_time:                         0
% 11.35/2.06  parsing_time:                           0.008
% 11.35/2.06  unif_index_cands_time:                  0.
% 11.35/2.06  unif_index_add_time:                    0.
% 11.35/2.06  orderings_time:                         0.
% 11.35/2.06  out_proof_time:                         0.007
% 11.35/2.06  total_time:                             1.041
% 11.35/2.06  num_of_symbols:                         38
% 11.35/2.06  num_of_terms:                           70018
% 11.35/2.06  
% 11.35/2.06  ------ Preprocessing
% 11.35/2.06  
% 11.35/2.06  num_of_splits:                          0
% 11.35/2.06  num_of_split_atoms:                     0
% 11.35/2.06  num_of_reused_defs:                     0
% 11.35/2.06  num_eq_ax_congr_red:                    0
% 11.35/2.06  num_of_sem_filtered_clauses:            1
% 11.35/2.06  num_of_subtypes:                        0
% 11.35/2.06  monotx_restored_types:                  0
% 11.35/2.06  sat_num_of_epr_types:                   0
% 11.35/2.06  sat_num_of_non_cyclic_types:            0
% 11.35/2.06  sat_guarded_non_collapsed_types:        0
% 11.35/2.06  num_pure_diseq_elim:                    0
% 11.35/2.06  simp_replaced_by:                       0
% 11.35/2.06  res_preprocessed:                       57
% 11.35/2.06  prep_upred:                             0
% 11.35/2.06  prep_unflattend:                        0
% 11.35/2.06  smt_new_axioms:                         0
% 11.35/2.06  pred_elim_cands:                        1
% 11.35/2.06  pred_elim:                              0
% 11.35/2.06  pred_elim_cl:                           0
% 11.35/2.06  pred_elim_cycles:                       2
% 11.35/2.06  merged_defs:                            8
% 11.35/2.06  merged_defs_ncl:                        0
% 11.35/2.06  bin_hyper_res:                          8
% 11.35/2.06  prep_cycles:                            4
% 11.35/2.06  pred_elim_time:                         0.
% 11.35/2.06  splitting_time:                         0.
% 11.35/2.06  sem_filter_time:                        0.
% 11.35/2.06  monotx_time:                            0.
% 11.35/2.06  subtype_inf_time:                       0.
% 11.35/2.06  
% 11.35/2.06  ------ Problem properties
% 11.35/2.06  
% 11.35/2.06  clauses:                                11
% 11.35/2.06  conjectures:                            1
% 11.35/2.06  epr:                                    2
% 11.35/2.06  horn:                                   11
% 11.35/2.06  ground:                                 1
% 11.35/2.06  unary:                                  7
% 11.35/2.06  binary:                                 3
% 11.35/2.06  lits:                                   16
% 11.35/2.06  lits_eq:                                9
% 11.35/2.06  fd_pure:                                0
% 11.35/2.06  fd_pseudo:                              0
% 11.35/2.06  fd_cond:                                0
% 11.35/2.06  fd_pseudo_cond:                         1
% 11.35/2.06  ac_symbols:                             1
% 11.35/2.06  
% 11.35/2.06  ------ Propositional Solver
% 11.35/2.06  
% 11.35/2.06  prop_solver_calls:                      32
% 11.35/2.06  prop_fast_solver_calls:                 516
% 11.35/2.06  smt_solver_calls:                       0
% 11.35/2.06  smt_fast_solver_calls:                  0
% 11.35/2.06  prop_num_of_clauses:                    4748
% 11.35/2.06  prop_preprocess_simplified:             8580
% 11.35/2.06  prop_fo_subsumed:                       1
% 11.35/2.06  prop_solver_time:                       0.
% 11.35/2.06  smt_solver_time:                        0.
% 11.35/2.06  smt_fast_solver_time:                   0.
% 11.35/2.06  prop_fast_solver_time:                  0.
% 11.35/2.06  prop_unsat_core_time:                   0.
% 11.35/2.06  
% 11.35/2.06  ------ QBF
% 11.35/2.06  
% 11.35/2.06  qbf_q_res:                              0
% 11.35/2.06  qbf_num_tautologies:                    0
% 11.35/2.06  qbf_prep_cycles:                        0
% 11.35/2.06  
% 11.35/2.06  ------ BMC1
% 11.35/2.06  
% 11.35/2.06  bmc1_current_bound:                     -1
% 11.35/2.06  bmc1_last_solved_bound:                 -1
% 11.35/2.06  bmc1_unsat_core_size:                   -1
% 11.35/2.06  bmc1_unsat_core_parents_size:           -1
% 11.35/2.06  bmc1_merge_next_fun:                    0
% 11.35/2.06  bmc1_unsat_core_clauses_time:           0.
% 11.35/2.06  
% 11.35/2.06  ------ Instantiation
% 11.35/2.06  
% 11.35/2.06  inst_num_of_clauses:                    1372
% 11.35/2.06  inst_num_in_passive:                    168
% 11.35/2.06  inst_num_in_active:                     555
% 11.35/2.06  inst_num_in_unprocessed:                649
% 11.35/2.06  inst_num_of_loops:                      590
% 11.35/2.06  inst_num_of_learning_restarts:          0
% 11.35/2.06  inst_num_moves_active_passive:          30
% 11.35/2.06  inst_lit_activity:                      0
% 11.35/2.06  inst_lit_activity_moves:                0
% 11.35/2.06  inst_num_tautologies:                   0
% 11.35/2.06  inst_num_prop_implied:                  0
% 11.35/2.06  inst_num_existing_simplified:           0
% 11.35/2.06  inst_num_eq_res_simplified:             0
% 11.35/2.06  inst_num_child_elim:                    0
% 11.35/2.06  inst_num_of_dismatching_blockings:      563
% 11.35/2.06  inst_num_of_non_proper_insts:           2016
% 11.35/2.06  inst_num_of_duplicates:                 0
% 11.35/2.06  inst_inst_num_from_inst_to_res:         0
% 11.35/2.06  inst_dismatching_checking_time:         0.
% 11.35/2.06  
% 11.35/2.06  ------ Resolution
% 11.35/2.06  
% 11.35/2.06  res_num_of_clauses:                     0
% 11.35/2.06  res_num_in_passive:                     0
% 11.35/2.06  res_num_in_active:                      0
% 11.35/2.06  res_num_of_loops:                       61
% 11.35/2.06  res_forward_subset_subsumed:            402
% 11.35/2.06  res_backward_subset_subsumed:           0
% 11.35/2.06  res_forward_subsumed:                   0
% 11.35/2.06  res_backward_subsumed:                  0
% 11.35/2.06  res_forward_subsumption_resolution:     0
% 11.35/2.06  res_backward_subsumption_resolution:    0
% 11.35/2.06  res_clause_to_clause_subsumption:       81385
% 11.35/2.06  res_orphan_elimination:                 0
% 11.35/2.06  res_tautology_del:                      185
% 11.35/2.06  res_num_eq_res_simplified:              0
% 11.35/2.06  res_num_sel_changes:                    0
% 11.35/2.06  res_moves_from_active_to_pass:          0
% 11.35/2.06  
% 11.35/2.06  ------ Superposition
% 11.35/2.06  
% 11.35/2.06  sup_time_total:                         0.
% 11.35/2.06  sup_time_generating:                    0.
% 11.35/2.06  sup_time_sim_full:                      0.
% 11.35/2.06  sup_time_sim_immed:                     0.
% 11.35/2.06  
% 11.35/2.06  sup_num_of_clauses:                     1401
% 11.35/2.06  sup_num_in_active:                      89
% 11.35/2.06  sup_num_in_passive:                     1312
% 11.35/2.06  sup_num_of_loops:                       116
% 11.35/2.06  sup_fw_superposition:                   10494
% 11.35/2.06  sup_bw_superposition:                   7294
% 11.35/2.06  sup_immediate_simplified:               9212
% 11.35/2.06  sup_given_eliminated:                   1
% 11.35/2.06  comparisons_done:                       0
% 11.35/2.06  comparisons_avoided:                    0
% 11.35/2.06  
% 11.35/2.06  ------ Simplifications
% 11.35/2.06  
% 11.35/2.06  
% 11.35/2.06  sim_fw_subset_subsumed:                 2
% 11.35/2.06  sim_bw_subset_subsumed:                 0
% 11.35/2.06  sim_fw_subsumed:                        242
% 11.35/2.06  sim_bw_subsumed:                        5
% 11.35/2.06  sim_fw_subsumption_res:                 0
% 11.35/2.06  sim_bw_subsumption_res:                 0
% 11.35/2.06  sim_tautology_del:                      0
% 11.35/2.06  sim_eq_tautology_del:                   1686
% 11.35/2.06  sim_eq_res_simp:                        2
% 11.35/2.06  sim_fw_demodulated:                     8439
% 11.35/2.06  sim_bw_demodulated:                     44
% 11.35/2.06  sim_light_normalised:                   2449
% 11.35/2.06  sim_joinable_taut:                      500
% 11.35/2.06  sim_joinable_simp:                      0
% 11.35/2.06  sim_ac_normalised:                      0
% 11.35/2.06  sim_smt_subsumption:                    0
% 11.35/2.06  
%------------------------------------------------------------------------------
