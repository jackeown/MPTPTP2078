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
% DateTime   : Thu Dec  3 11:24:59 EST 2020

% Result     : Theorem 19.37s
% Output     : CNFRefutation 19.37s
% Verified   : 
% Statistics : Number of formulae       :  177 (21225 expanded)
%              Number of clauses        :  129 (8897 expanded)
%              Number of leaves         :   20 (5656 expanded)
%              Depth                    :   37
%              Number of atoms          :  207 (22360 expanded)
%              Number of equality atoms :  179 (21213 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f44,f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f19,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f26,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f28,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28])).

fof(f51,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f51,f31,f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_13,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_242,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_13,c_9,c_0])).

cnf(c_8,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_520,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_242,c_8])).

cnf(c_17,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_819,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_520,c_17])).

cnf(c_821,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_819,c_520])).

cnf(c_1032,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_821,c_520])).

cnf(c_11,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1349,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1032,c_11])).

cnf(c_1030,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_821,c_0])).

cnf(c_1353,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1349,c_1030])).

cnf(c_1688,plain,
    ( k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1032,c_1353])).

cnf(c_1696,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1688,c_1032])).

cnf(c_7,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_510,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_883,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k3_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_510])).

cnf(c_5645,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k3_xboole_0(k4_xboole_0(X0,X1),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1696,c_883])).

cnf(c_5727,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5645,c_1353])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2073,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1696,c_10])).

cnf(c_5728,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5727,c_2073])).

cnf(c_1346,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_1032,c_11])).

cnf(c_1358,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1346,c_821])).

cnf(c_1290,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_1032,c_10])).

cnf(c_1297,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_1290,c_8,c_1032])).

cnf(c_817,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_17])).

cnf(c_18,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_511,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_688,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_511])).

cnf(c_1668,plain,
    ( r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_817,c_688])).

cnf(c_2422,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_1668])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_515,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5201,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X0),k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_2422,c_515])).

cnf(c_533,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_1661,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_17,c_817])).

cnf(c_1126,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1030,c_17])).

cnf(c_1132,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1126,c_1030])).

cnf(c_1674,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1661,c_1132])).

cnf(c_2456,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1674])).

cnf(c_2822,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X2)),X2)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_533,c_2456])).

cnf(c_1658,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_817])).

cnf(c_2590,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_2456])).

cnf(c_2824,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_2822,c_1658,c_2590])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_513,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2747,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_510,c_513])).

cnf(c_3060,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k3_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2747,c_11])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_514,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_518,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2581,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_514,c_518])).

cnf(c_3061,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3060,c_2581])).

cnf(c_5202,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_5201,c_2824,c_3061])).

cnf(c_5203,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5202,c_1030])).

cnf(c_5221,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1358,c_5203])).

cnf(c_5729,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5728,c_5221])).

cnf(c_6283,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5729,c_518])).

cnf(c_12,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3059,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2747,c_12])).

cnf(c_3062,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3059,c_1030])).

cnf(c_6470,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6283,c_3062])).

cnf(c_6536,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6470,c_1032,c_2073])).

cnf(c_6717,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k3_xboole_0(X0,k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6536,c_11])).

cnf(c_6739,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_6717,c_1358])).

cnf(c_20,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_241,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_20,c_9,c_0])).

cnf(c_521,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_241,c_7])).

cnf(c_81818,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_6739,c_521])).

cnf(c_3055,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2747,c_10])).

cnf(c_3066,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3055,c_821])).

cnf(c_6764,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3062,c_3066])).

cnf(c_6831,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_6764,c_3066])).

cnf(c_16659,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_6831,c_3062])).

cnf(c_3058,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2747,c_7])).

cnf(c_3063,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3058,c_3062])).

cnf(c_3235,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_3063])).

cnf(c_6731,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6536,c_3235])).

cnf(c_12982,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6731,c_1353])).

cnf(c_16667,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_16659,c_12982])).

cnf(c_5,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_954,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(X1,k4_xboole_0(X2,X0))
    | k3_xboole_0(X1,X2) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_5])).

cnf(c_24213,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | k3_xboole_0(X1,k4_xboole_0(X0,k3_xboole_0(X0,X1))) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16667,c_954])).

cnf(c_3053,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2747,c_12])).

cnf(c_3068,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3053,c_821])).

cnf(c_24245,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | k3_xboole_0(X0,k4_xboole_0(X1,X0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_24213,c_3068])).

cnf(c_24246,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24245,c_3063])).

cnf(c_24247,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_24246])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_517,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1282,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_517,c_515])).

cnf(c_15464,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1282,c_1282,c_3068])).

cnf(c_24468,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_24247,c_15464])).

cnf(c_1557,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1297,c_9])).

cnf(c_30142,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_24468,c_1557])).

cnf(c_3243,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3063,c_10])).

cnf(c_3246,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3243,c_1030])).

cnf(c_53989,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3246,c_3066])).

cnf(c_54123,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_53989,c_3066])).

cnf(c_81819,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_81818,c_30142,c_54123])).

cnf(c_535,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_15553,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_15464,c_535])).

cnf(c_13112,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_12982,c_11])).

cnf(c_13176,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_13112,c_7])).

cnf(c_1562,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1297,c_821])).

cnf(c_13177,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13176,c_7,c_1562])).

cnf(c_3244,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3063,c_11])).

cnf(c_6768,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3244,c_3066])).

cnf(c_6827,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6768,c_1032])).

cnf(c_24481,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
    inference(superposition,[status(thm)],[c_24247,c_5203])).

cnf(c_24713,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6827,c_24481])).

cnf(c_2210,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_1358,c_1297])).

cnf(c_2300,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_2210,c_9])).

cnf(c_19752,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(superposition,[status(thm)],[c_817,c_2300])).

cnf(c_19917,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_19752,c_2300])).

cnf(c_24822,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_24713,c_19917])).

cnf(c_35157,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13177,c_24822])).

cnf(c_24757,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_24481,c_535])).

cnf(c_35284,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_35157,c_24757])).

cnf(c_42076,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_30142,c_35284])).

cnf(c_42263,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_42076,c_35284])).

cnf(c_81820,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_81819,c_15553,c_42263])).

cnf(c_917,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_81820,c_917])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:23:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.37/3.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.37/3.07  
% 19.37/3.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.37/3.07  
% 19.37/3.07  ------  iProver source info
% 19.37/3.07  
% 19.37/3.07  git: date: 2020-06-30 10:37:57 +0100
% 19.37/3.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.37/3.07  git: non_committed_changes: false
% 19.37/3.07  git: last_make_outside_of_git: false
% 19.37/3.07  
% 19.37/3.07  ------ 
% 19.37/3.07  
% 19.37/3.07  ------ Input Options
% 19.37/3.07  
% 19.37/3.07  --out_options                           all
% 19.37/3.07  --tptp_safe_out                         true
% 19.37/3.07  --problem_path                          ""
% 19.37/3.07  --include_path                          ""
% 19.37/3.07  --clausifier                            res/vclausify_rel
% 19.37/3.07  --clausifier_options                    ""
% 19.37/3.07  --stdin                                 false
% 19.37/3.07  --stats_out                             all
% 19.37/3.07  
% 19.37/3.07  ------ General Options
% 19.37/3.07  
% 19.37/3.07  --fof                                   false
% 19.37/3.07  --time_out_real                         305.
% 19.37/3.07  --time_out_virtual                      -1.
% 19.37/3.07  --symbol_type_check                     false
% 19.37/3.07  --clausify_out                          false
% 19.37/3.07  --sig_cnt_out                           false
% 19.37/3.07  --trig_cnt_out                          false
% 19.37/3.07  --trig_cnt_out_tolerance                1.
% 19.37/3.07  --trig_cnt_out_sk_spl                   false
% 19.37/3.07  --abstr_cl_out                          false
% 19.37/3.07  
% 19.37/3.07  ------ Global Options
% 19.37/3.07  
% 19.37/3.07  --schedule                              default
% 19.37/3.07  --add_important_lit                     false
% 19.37/3.07  --prop_solver_per_cl                    1000
% 19.37/3.07  --min_unsat_core                        false
% 19.37/3.07  --soft_assumptions                      false
% 19.37/3.07  --soft_lemma_size                       3
% 19.37/3.07  --prop_impl_unit_size                   0
% 19.37/3.07  --prop_impl_unit                        []
% 19.37/3.07  --share_sel_clauses                     true
% 19.37/3.07  --reset_solvers                         false
% 19.37/3.07  --bc_imp_inh                            [conj_cone]
% 19.37/3.07  --conj_cone_tolerance                   3.
% 19.37/3.07  --extra_neg_conj                        none
% 19.37/3.07  --large_theory_mode                     true
% 19.37/3.07  --prolific_symb_bound                   200
% 19.37/3.07  --lt_threshold                          2000
% 19.37/3.07  --clause_weak_htbl                      true
% 19.37/3.07  --gc_record_bc_elim                     false
% 19.37/3.07  
% 19.37/3.07  ------ Preprocessing Options
% 19.37/3.07  
% 19.37/3.07  --preprocessing_flag                    true
% 19.37/3.07  --time_out_prep_mult                    0.1
% 19.37/3.07  --splitting_mode                        input
% 19.37/3.07  --splitting_grd                         true
% 19.37/3.07  --splitting_cvd                         false
% 19.37/3.07  --splitting_cvd_svl                     false
% 19.37/3.07  --splitting_nvd                         32
% 19.37/3.07  --sub_typing                            true
% 19.37/3.07  --prep_gs_sim                           true
% 19.37/3.07  --prep_unflatten                        true
% 19.37/3.07  --prep_res_sim                          true
% 19.37/3.07  --prep_upred                            true
% 19.37/3.07  --prep_sem_filter                       exhaustive
% 19.37/3.07  --prep_sem_filter_out                   false
% 19.37/3.07  --pred_elim                             true
% 19.37/3.07  --res_sim_input                         true
% 19.37/3.07  --eq_ax_congr_red                       true
% 19.37/3.07  --pure_diseq_elim                       true
% 19.37/3.07  --brand_transform                       false
% 19.37/3.07  --non_eq_to_eq                          false
% 19.37/3.07  --prep_def_merge                        true
% 19.37/3.07  --prep_def_merge_prop_impl              false
% 19.37/3.07  --prep_def_merge_mbd                    true
% 19.37/3.07  --prep_def_merge_tr_red                 false
% 19.37/3.07  --prep_def_merge_tr_cl                  false
% 19.37/3.07  --smt_preprocessing                     true
% 19.37/3.07  --smt_ac_axioms                         fast
% 19.37/3.07  --preprocessed_out                      false
% 19.37/3.07  --preprocessed_stats                    false
% 19.37/3.07  
% 19.37/3.07  ------ Abstraction refinement Options
% 19.37/3.07  
% 19.37/3.07  --abstr_ref                             []
% 19.37/3.07  --abstr_ref_prep                        false
% 19.37/3.07  --abstr_ref_until_sat                   false
% 19.37/3.07  --abstr_ref_sig_restrict                funpre
% 19.37/3.07  --abstr_ref_af_restrict_to_split_sk     false
% 19.37/3.07  --abstr_ref_under                       []
% 19.37/3.07  
% 19.37/3.07  ------ SAT Options
% 19.37/3.07  
% 19.37/3.07  --sat_mode                              false
% 19.37/3.07  --sat_fm_restart_options                ""
% 19.37/3.07  --sat_gr_def                            false
% 19.37/3.07  --sat_epr_types                         true
% 19.37/3.07  --sat_non_cyclic_types                  false
% 19.37/3.07  --sat_finite_models                     false
% 19.37/3.07  --sat_fm_lemmas                         false
% 19.37/3.07  --sat_fm_prep                           false
% 19.37/3.07  --sat_fm_uc_incr                        true
% 19.37/3.07  --sat_out_model                         small
% 19.37/3.07  --sat_out_clauses                       false
% 19.37/3.07  
% 19.37/3.07  ------ QBF Options
% 19.37/3.07  
% 19.37/3.07  --qbf_mode                              false
% 19.37/3.07  --qbf_elim_univ                         false
% 19.37/3.07  --qbf_dom_inst                          none
% 19.37/3.07  --qbf_dom_pre_inst                      false
% 19.37/3.07  --qbf_sk_in                             false
% 19.37/3.07  --qbf_pred_elim                         true
% 19.37/3.07  --qbf_split                             512
% 19.37/3.07  
% 19.37/3.07  ------ BMC1 Options
% 19.37/3.07  
% 19.37/3.07  --bmc1_incremental                      false
% 19.37/3.07  --bmc1_axioms                           reachable_all
% 19.37/3.07  --bmc1_min_bound                        0
% 19.37/3.07  --bmc1_max_bound                        -1
% 19.37/3.07  --bmc1_max_bound_default                -1
% 19.37/3.07  --bmc1_symbol_reachability              true
% 19.37/3.07  --bmc1_property_lemmas                  false
% 19.37/3.07  --bmc1_k_induction                      false
% 19.37/3.07  --bmc1_non_equiv_states                 false
% 19.37/3.07  --bmc1_deadlock                         false
% 19.37/3.07  --bmc1_ucm                              false
% 19.37/3.07  --bmc1_add_unsat_core                   none
% 19.37/3.07  --bmc1_unsat_core_children              false
% 19.37/3.07  --bmc1_unsat_core_extrapolate_axioms    false
% 19.37/3.07  --bmc1_out_stat                         full
% 19.37/3.07  --bmc1_ground_init                      false
% 19.37/3.07  --bmc1_pre_inst_next_state              false
% 19.37/3.07  --bmc1_pre_inst_state                   false
% 19.37/3.07  --bmc1_pre_inst_reach_state             false
% 19.37/3.07  --bmc1_out_unsat_core                   false
% 19.37/3.07  --bmc1_aig_witness_out                  false
% 19.37/3.07  --bmc1_verbose                          false
% 19.37/3.07  --bmc1_dump_clauses_tptp                false
% 19.37/3.07  --bmc1_dump_unsat_core_tptp             false
% 19.37/3.07  --bmc1_dump_file                        -
% 19.37/3.07  --bmc1_ucm_expand_uc_limit              128
% 19.37/3.07  --bmc1_ucm_n_expand_iterations          6
% 19.37/3.07  --bmc1_ucm_extend_mode                  1
% 19.37/3.07  --bmc1_ucm_init_mode                    2
% 19.37/3.07  --bmc1_ucm_cone_mode                    none
% 19.37/3.07  --bmc1_ucm_reduced_relation_type        0
% 19.37/3.07  --bmc1_ucm_relax_model                  4
% 19.37/3.07  --bmc1_ucm_full_tr_after_sat            true
% 19.37/3.07  --bmc1_ucm_expand_neg_assumptions       false
% 19.37/3.07  --bmc1_ucm_layered_model                none
% 19.37/3.07  --bmc1_ucm_max_lemma_size               10
% 19.37/3.07  
% 19.37/3.07  ------ AIG Options
% 19.37/3.07  
% 19.37/3.07  --aig_mode                              false
% 19.37/3.07  
% 19.37/3.07  ------ Instantiation Options
% 19.37/3.07  
% 19.37/3.07  --instantiation_flag                    true
% 19.37/3.07  --inst_sos_flag                         true
% 19.37/3.07  --inst_sos_phase                        true
% 19.37/3.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.37/3.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.37/3.07  --inst_lit_sel_side                     num_symb
% 19.37/3.07  --inst_solver_per_active                1400
% 19.37/3.07  --inst_solver_calls_frac                1.
% 19.37/3.07  --inst_passive_queue_type               priority_queues
% 19.37/3.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.37/3.07  --inst_passive_queues_freq              [25;2]
% 19.37/3.07  --inst_dismatching                      true
% 19.37/3.07  --inst_eager_unprocessed_to_passive     true
% 19.37/3.07  --inst_prop_sim_given                   true
% 19.37/3.07  --inst_prop_sim_new                     false
% 19.37/3.07  --inst_subs_new                         false
% 19.37/3.07  --inst_eq_res_simp                      false
% 19.37/3.07  --inst_subs_given                       false
% 19.37/3.07  --inst_orphan_elimination               true
% 19.37/3.07  --inst_learning_loop_flag               true
% 19.37/3.07  --inst_learning_start                   3000
% 19.37/3.07  --inst_learning_factor                  2
% 19.37/3.07  --inst_start_prop_sim_after_learn       3
% 19.37/3.07  --inst_sel_renew                        solver
% 19.37/3.07  --inst_lit_activity_flag                true
% 19.37/3.07  --inst_restr_to_given                   false
% 19.37/3.07  --inst_activity_threshold               500
% 19.37/3.07  --inst_out_proof                        true
% 19.37/3.07  
% 19.37/3.07  ------ Resolution Options
% 19.37/3.07  
% 19.37/3.07  --resolution_flag                       true
% 19.37/3.07  --res_lit_sel                           adaptive
% 19.37/3.07  --res_lit_sel_side                      none
% 19.37/3.07  --res_ordering                          kbo
% 19.37/3.07  --res_to_prop_solver                    active
% 19.37/3.07  --res_prop_simpl_new                    false
% 19.37/3.07  --res_prop_simpl_given                  true
% 19.37/3.07  --res_passive_queue_type                priority_queues
% 19.37/3.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.37/3.07  --res_passive_queues_freq               [15;5]
% 19.37/3.07  --res_forward_subs                      full
% 19.37/3.07  --res_backward_subs                     full
% 19.37/3.07  --res_forward_subs_resolution           true
% 19.37/3.07  --res_backward_subs_resolution          true
% 19.37/3.07  --res_orphan_elimination                true
% 19.37/3.07  --res_time_limit                        2.
% 19.37/3.07  --res_out_proof                         true
% 19.37/3.07  
% 19.37/3.07  ------ Superposition Options
% 19.37/3.07  
% 19.37/3.07  --superposition_flag                    true
% 19.37/3.07  --sup_passive_queue_type                priority_queues
% 19.37/3.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.37/3.07  --sup_passive_queues_freq               [8;1;4]
% 19.37/3.07  --demod_completeness_check              fast
% 19.37/3.07  --demod_use_ground                      true
% 19.37/3.07  --sup_to_prop_solver                    passive
% 19.37/3.07  --sup_prop_simpl_new                    true
% 19.37/3.07  --sup_prop_simpl_given                  true
% 19.37/3.07  --sup_fun_splitting                     true
% 19.37/3.07  --sup_smt_interval                      50000
% 19.37/3.07  
% 19.37/3.07  ------ Superposition Simplification Setup
% 19.37/3.07  
% 19.37/3.07  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.37/3.07  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.37/3.07  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.37/3.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.37/3.07  --sup_full_triv                         [TrivRules;PropSubs]
% 19.37/3.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.37/3.07  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.37/3.07  --sup_immed_triv                        [TrivRules]
% 19.37/3.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.37/3.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.37/3.07  --sup_immed_bw_main                     []
% 19.37/3.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.37/3.07  --sup_input_triv                        [Unflattening;TrivRules]
% 19.37/3.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.37/3.07  --sup_input_bw                          []
% 19.37/3.07  
% 19.37/3.07  ------ Combination Options
% 19.37/3.07  
% 19.37/3.07  --comb_res_mult                         3
% 19.37/3.07  --comb_sup_mult                         2
% 19.37/3.07  --comb_inst_mult                        10
% 19.37/3.07  
% 19.37/3.07  ------ Debug Options
% 19.37/3.07  
% 19.37/3.07  --dbg_backtrace                         false
% 19.37/3.07  --dbg_dump_prop_clauses                 false
% 19.37/3.07  --dbg_dump_prop_clauses_file            -
% 19.37/3.07  --dbg_out_stat                          false
% 19.37/3.07  ------ Parsing...
% 19.37/3.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.37/3.07  
% 19.37/3.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.37/3.07  
% 19.37/3.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.37/3.07  
% 19.37/3.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.37/3.07  ------ Proving...
% 19.37/3.07  ------ Problem Properties 
% 19.37/3.07  
% 19.37/3.07  
% 19.37/3.07  clauses                                 21
% 19.37/3.07  conjectures                             1
% 19.37/3.07  EPR                                     3
% 19.37/3.07  Horn                                    21
% 19.37/3.07  unary                                   15
% 19.37/3.07  binary                                  6
% 19.37/3.07  lits                                    27
% 19.37/3.07  lits eq                                 17
% 19.37/3.07  fd_pure                                 0
% 19.37/3.07  fd_pseudo                               0
% 19.37/3.07  fd_cond                                 1
% 19.37/3.07  fd_pseudo_cond                          1
% 19.37/3.07  AC symbols                              1
% 19.37/3.07  
% 19.37/3.07  ------ Schedule dynamic 5 is on 
% 19.37/3.07  
% 19.37/3.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.37/3.07  
% 19.37/3.07  
% 19.37/3.07  ------ 
% 19.37/3.07  Current options:
% 19.37/3.07  ------ 
% 19.37/3.07  
% 19.37/3.07  ------ Input Options
% 19.37/3.07  
% 19.37/3.07  --out_options                           all
% 19.37/3.07  --tptp_safe_out                         true
% 19.37/3.07  --problem_path                          ""
% 19.37/3.07  --include_path                          ""
% 19.37/3.07  --clausifier                            res/vclausify_rel
% 19.37/3.07  --clausifier_options                    ""
% 19.37/3.07  --stdin                                 false
% 19.37/3.07  --stats_out                             all
% 19.37/3.07  
% 19.37/3.07  ------ General Options
% 19.37/3.07  
% 19.37/3.07  --fof                                   false
% 19.37/3.07  --time_out_real                         305.
% 19.37/3.07  --time_out_virtual                      -1.
% 19.37/3.07  --symbol_type_check                     false
% 19.37/3.07  --clausify_out                          false
% 19.37/3.07  --sig_cnt_out                           false
% 19.37/3.07  --trig_cnt_out                          false
% 19.37/3.07  --trig_cnt_out_tolerance                1.
% 19.37/3.07  --trig_cnt_out_sk_spl                   false
% 19.37/3.07  --abstr_cl_out                          false
% 19.37/3.07  
% 19.37/3.07  ------ Global Options
% 19.37/3.07  
% 19.37/3.07  --schedule                              default
% 19.37/3.07  --add_important_lit                     false
% 19.37/3.07  --prop_solver_per_cl                    1000
% 19.37/3.07  --min_unsat_core                        false
% 19.37/3.07  --soft_assumptions                      false
% 19.37/3.07  --soft_lemma_size                       3
% 19.37/3.07  --prop_impl_unit_size                   0
% 19.37/3.07  --prop_impl_unit                        []
% 19.37/3.07  --share_sel_clauses                     true
% 19.37/3.07  --reset_solvers                         false
% 19.37/3.07  --bc_imp_inh                            [conj_cone]
% 19.37/3.07  --conj_cone_tolerance                   3.
% 19.37/3.07  --extra_neg_conj                        none
% 19.37/3.07  --large_theory_mode                     true
% 19.37/3.07  --prolific_symb_bound                   200
% 19.37/3.07  --lt_threshold                          2000
% 19.37/3.07  --clause_weak_htbl                      true
% 19.37/3.07  --gc_record_bc_elim                     false
% 19.37/3.07  
% 19.37/3.07  ------ Preprocessing Options
% 19.37/3.07  
% 19.37/3.07  --preprocessing_flag                    true
% 19.37/3.07  --time_out_prep_mult                    0.1
% 19.37/3.07  --splitting_mode                        input
% 19.37/3.07  --splitting_grd                         true
% 19.37/3.07  --splitting_cvd                         false
% 19.37/3.07  --splitting_cvd_svl                     false
% 19.37/3.07  --splitting_nvd                         32
% 19.37/3.07  --sub_typing                            true
% 19.37/3.07  --prep_gs_sim                           true
% 19.37/3.07  --prep_unflatten                        true
% 19.37/3.07  --prep_res_sim                          true
% 19.37/3.07  --prep_upred                            true
% 19.37/3.07  --prep_sem_filter                       exhaustive
% 19.37/3.07  --prep_sem_filter_out                   false
% 19.37/3.07  --pred_elim                             true
% 19.37/3.07  --res_sim_input                         true
% 19.37/3.07  --eq_ax_congr_red                       true
% 19.37/3.07  --pure_diseq_elim                       true
% 19.37/3.07  --brand_transform                       false
% 19.37/3.07  --non_eq_to_eq                          false
% 19.37/3.07  --prep_def_merge                        true
% 19.37/3.07  --prep_def_merge_prop_impl              false
% 19.37/3.07  --prep_def_merge_mbd                    true
% 19.37/3.07  --prep_def_merge_tr_red                 false
% 19.37/3.07  --prep_def_merge_tr_cl                  false
% 19.37/3.07  --smt_preprocessing                     true
% 19.37/3.07  --smt_ac_axioms                         fast
% 19.37/3.07  --preprocessed_out                      false
% 19.37/3.07  --preprocessed_stats                    false
% 19.37/3.07  
% 19.37/3.07  ------ Abstraction refinement Options
% 19.37/3.07  
% 19.37/3.07  --abstr_ref                             []
% 19.37/3.07  --abstr_ref_prep                        false
% 19.37/3.07  --abstr_ref_until_sat                   false
% 19.37/3.07  --abstr_ref_sig_restrict                funpre
% 19.37/3.07  --abstr_ref_af_restrict_to_split_sk     false
% 19.37/3.07  --abstr_ref_under                       []
% 19.37/3.07  
% 19.37/3.07  ------ SAT Options
% 19.37/3.07  
% 19.37/3.07  --sat_mode                              false
% 19.37/3.07  --sat_fm_restart_options                ""
% 19.37/3.07  --sat_gr_def                            false
% 19.37/3.07  --sat_epr_types                         true
% 19.37/3.07  --sat_non_cyclic_types                  false
% 19.37/3.07  --sat_finite_models                     false
% 19.37/3.07  --sat_fm_lemmas                         false
% 19.37/3.07  --sat_fm_prep                           false
% 19.37/3.07  --sat_fm_uc_incr                        true
% 19.37/3.07  --sat_out_model                         small
% 19.37/3.07  --sat_out_clauses                       false
% 19.37/3.07  
% 19.37/3.07  ------ QBF Options
% 19.37/3.07  
% 19.37/3.07  --qbf_mode                              false
% 19.37/3.07  --qbf_elim_univ                         false
% 19.37/3.07  --qbf_dom_inst                          none
% 19.37/3.07  --qbf_dom_pre_inst                      false
% 19.37/3.07  --qbf_sk_in                             false
% 19.37/3.07  --qbf_pred_elim                         true
% 19.37/3.07  --qbf_split                             512
% 19.37/3.07  
% 19.37/3.07  ------ BMC1 Options
% 19.37/3.07  
% 19.37/3.07  --bmc1_incremental                      false
% 19.37/3.07  --bmc1_axioms                           reachable_all
% 19.37/3.07  --bmc1_min_bound                        0
% 19.37/3.07  --bmc1_max_bound                        -1
% 19.37/3.07  --bmc1_max_bound_default                -1
% 19.37/3.07  --bmc1_symbol_reachability              true
% 19.37/3.07  --bmc1_property_lemmas                  false
% 19.37/3.07  --bmc1_k_induction                      false
% 19.37/3.07  --bmc1_non_equiv_states                 false
% 19.37/3.07  --bmc1_deadlock                         false
% 19.37/3.07  --bmc1_ucm                              false
% 19.37/3.07  --bmc1_add_unsat_core                   none
% 19.37/3.07  --bmc1_unsat_core_children              false
% 19.37/3.07  --bmc1_unsat_core_extrapolate_axioms    false
% 19.37/3.07  --bmc1_out_stat                         full
% 19.37/3.07  --bmc1_ground_init                      false
% 19.37/3.07  --bmc1_pre_inst_next_state              false
% 19.37/3.07  --bmc1_pre_inst_state                   false
% 19.37/3.07  --bmc1_pre_inst_reach_state             false
% 19.37/3.07  --bmc1_out_unsat_core                   false
% 19.37/3.07  --bmc1_aig_witness_out                  false
% 19.37/3.07  --bmc1_verbose                          false
% 19.37/3.07  --bmc1_dump_clauses_tptp                false
% 19.37/3.07  --bmc1_dump_unsat_core_tptp             false
% 19.37/3.07  --bmc1_dump_file                        -
% 19.37/3.07  --bmc1_ucm_expand_uc_limit              128
% 19.37/3.07  --bmc1_ucm_n_expand_iterations          6
% 19.37/3.07  --bmc1_ucm_extend_mode                  1
% 19.37/3.07  --bmc1_ucm_init_mode                    2
% 19.37/3.07  --bmc1_ucm_cone_mode                    none
% 19.37/3.07  --bmc1_ucm_reduced_relation_type        0
% 19.37/3.07  --bmc1_ucm_relax_model                  4
% 19.37/3.07  --bmc1_ucm_full_tr_after_sat            true
% 19.37/3.07  --bmc1_ucm_expand_neg_assumptions       false
% 19.37/3.07  --bmc1_ucm_layered_model                none
% 19.37/3.07  --bmc1_ucm_max_lemma_size               10
% 19.37/3.07  
% 19.37/3.07  ------ AIG Options
% 19.37/3.07  
% 19.37/3.07  --aig_mode                              false
% 19.37/3.07  
% 19.37/3.07  ------ Instantiation Options
% 19.37/3.07  
% 19.37/3.07  --instantiation_flag                    true
% 19.37/3.07  --inst_sos_flag                         true
% 19.37/3.07  --inst_sos_phase                        true
% 19.37/3.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.37/3.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.37/3.07  --inst_lit_sel_side                     none
% 19.37/3.07  --inst_solver_per_active                1400
% 19.37/3.07  --inst_solver_calls_frac                1.
% 19.37/3.07  --inst_passive_queue_type               priority_queues
% 19.37/3.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.37/3.07  --inst_passive_queues_freq              [25;2]
% 19.37/3.07  --inst_dismatching                      true
% 19.37/3.07  --inst_eager_unprocessed_to_passive     true
% 19.37/3.07  --inst_prop_sim_given                   true
% 19.37/3.07  --inst_prop_sim_new                     false
% 19.37/3.07  --inst_subs_new                         false
% 19.37/3.07  --inst_eq_res_simp                      false
% 19.37/3.07  --inst_subs_given                       false
% 19.37/3.07  --inst_orphan_elimination               true
% 19.37/3.07  --inst_learning_loop_flag               true
% 19.37/3.07  --inst_learning_start                   3000
% 19.37/3.07  --inst_learning_factor                  2
% 19.37/3.07  --inst_start_prop_sim_after_learn       3
% 19.37/3.07  --inst_sel_renew                        solver
% 19.37/3.07  --inst_lit_activity_flag                true
% 19.37/3.07  --inst_restr_to_given                   false
% 19.37/3.07  --inst_activity_threshold               500
% 19.37/3.07  --inst_out_proof                        true
% 19.37/3.07  
% 19.37/3.07  ------ Resolution Options
% 19.37/3.07  
% 19.37/3.07  --resolution_flag                       false
% 19.37/3.07  --res_lit_sel                           adaptive
% 19.37/3.07  --res_lit_sel_side                      none
% 19.37/3.07  --res_ordering                          kbo
% 19.37/3.07  --res_to_prop_solver                    active
% 19.37/3.07  --res_prop_simpl_new                    false
% 19.37/3.07  --res_prop_simpl_given                  true
% 19.37/3.07  --res_passive_queue_type                priority_queues
% 19.37/3.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.37/3.07  --res_passive_queues_freq               [15;5]
% 19.37/3.07  --res_forward_subs                      full
% 19.37/3.07  --res_backward_subs                     full
% 19.37/3.07  --res_forward_subs_resolution           true
% 19.37/3.07  --res_backward_subs_resolution          true
% 19.37/3.07  --res_orphan_elimination                true
% 19.37/3.07  --res_time_limit                        2.
% 19.37/3.07  --res_out_proof                         true
% 19.37/3.07  
% 19.37/3.07  ------ Superposition Options
% 19.37/3.07  
% 19.37/3.07  --superposition_flag                    true
% 19.37/3.07  --sup_passive_queue_type                priority_queues
% 19.37/3.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.37/3.07  --sup_passive_queues_freq               [8;1;4]
% 19.37/3.07  --demod_completeness_check              fast
% 19.37/3.07  --demod_use_ground                      true
% 19.37/3.07  --sup_to_prop_solver                    passive
% 19.37/3.07  --sup_prop_simpl_new                    true
% 19.37/3.07  --sup_prop_simpl_given                  true
% 19.37/3.07  --sup_fun_splitting                     true
% 19.37/3.07  --sup_smt_interval                      50000
% 19.37/3.07  
% 19.37/3.07  ------ Superposition Simplification Setup
% 19.37/3.07  
% 19.37/3.07  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.37/3.07  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.37/3.07  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.37/3.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.37/3.07  --sup_full_triv                         [TrivRules;PropSubs]
% 19.37/3.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.37/3.07  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.37/3.07  --sup_immed_triv                        [TrivRules]
% 19.37/3.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.37/3.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.37/3.07  --sup_immed_bw_main                     []
% 19.37/3.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.37/3.07  --sup_input_triv                        [Unflattening;TrivRules]
% 19.37/3.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.37/3.07  --sup_input_bw                          []
% 19.37/3.07  
% 19.37/3.07  ------ Combination Options
% 19.37/3.07  
% 19.37/3.07  --comb_res_mult                         3
% 19.37/3.07  --comb_sup_mult                         2
% 19.37/3.07  --comb_inst_mult                        10
% 19.37/3.07  
% 19.37/3.07  ------ Debug Options
% 19.37/3.07  
% 19.37/3.07  --dbg_backtrace                         false
% 19.37/3.07  --dbg_dump_prop_clauses                 false
% 19.37/3.07  --dbg_dump_prop_clauses_file            -
% 19.37/3.07  --dbg_out_stat                          false
% 19.37/3.07  
% 19.37/3.07  
% 19.37/3.07  
% 19.37/3.07  
% 19.37/3.07  ------ Proving...
% 19.37/3.07  
% 19.37/3.07  
% 19.37/3.07  % SZS status Theorem for theBenchmark.p
% 19.37/3.07  
% 19.37/3.07  % SZS output start CNFRefutation for theBenchmark.p
% 19.37/3.07  
% 19.37/3.07  fof(f14,axiom,(
% 19.37/3.07    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f44,plain,(
% 19.37/3.07    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.37/3.07    inference(cnf_transformation,[],[f14])).
% 19.37/3.07  
% 19.37/3.07  fof(f2,axiom,(
% 19.37/3.07    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f31,plain,(
% 19.37/3.07    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 19.37/3.07    inference(cnf_transformation,[],[f2])).
% 19.37/3.07  
% 19.37/3.07  fof(f52,plain,(
% 19.37/3.07    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 19.37/3.07    inference(definition_unfolding,[],[f44,f31])).
% 19.37/3.07  
% 19.37/3.07  fof(f10,axiom,(
% 19.37/3.07    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f40,plain,(
% 19.37/3.07    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 19.37/3.07    inference(cnf_transformation,[],[f10])).
% 19.37/3.07  
% 19.37/3.07  fof(f1,axiom,(
% 19.37/3.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f30,plain,(
% 19.37/3.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 19.37/3.07    inference(cnf_transformation,[],[f1])).
% 19.37/3.07  
% 19.37/3.07  fof(f9,axiom,(
% 19.37/3.07    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f39,plain,(
% 19.37/3.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 19.37/3.07    inference(cnf_transformation,[],[f9])).
% 19.37/3.07  
% 19.37/3.07  fof(f17,axiom,(
% 19.37/3.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f48,plain,(
% 19.37/3.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 19.37/3.07    inference(cnf_transformation,[],[f17])).
% 19.37/3.07  
% 19.37/3.07  fof(f12,axiom,(
% 19.37/3.07    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f42,plain,(
% 19.37/3.07    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 19.37/3.07    inference(cnf_transformation,[],[f12])).
% 19.37/3.07  
% 19.37/3.07  fof(f8,axiom,(
% 19.37/3.07    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f38,plain,(
% 19.37/3.07    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 19.37/3.07    inference(cnf_transformation,[],[f8])).
% 19.37/3.07  
% 19.37/3.07  fof(f19,axiom,(
% 19.37/3.07    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f50,plain,(
% 19.37/3.07    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 19.37/3.07    inference(cnf_transformation,[],[f19])).
% 19.37/3.07  
% 19.37/3.07  fof(f11,axiom,(
% 19.37/3.07    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f41,plain,(
% 19.37/3.07    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 19.37/3.07    inference(cnf_transformation,[],[f11])).
% 19.37/3.07  
% 19.37/3.07  fof(f18,axiom,(
% 19.37/3.07    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f49,plain,(
% 19.37/3.07    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 19.37/3.07    inference(cnf_transformation,[],[f18])).
% 19.37/3.07  
% 19.37/3.07  fof(f7,axiom,(
% 19.37/3.07    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f24,plain,(
% 19.37/3.07    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 19.37/3.07    inference(ennf_transformation,[],[f7])).
% 19.37/3.07  
% 19.37/3.07  fof(f37,plain,(
% 19.37/3.07    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 19.37/3.07    inference(cnf_transformation,[],[f24])).
% 19.37/3.07  
% 19.37/3.07  fof(f16,axiom,(
% 19.37/3.07    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f25,plain,(
% 19.37/3.07    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 19.37/3.07    inference(ennf_transformation,[],[f16])).
% 19.37/3.07  
% 19.37/3.07  fof(f47,plain,(
% 19.37/3.07    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 19.37/3.07    inference(cnf_transformation,[],[f25])).
% 19.37/3.07  
% 19.37/3.07  fof(f15,axiom,(
% 19.37/3.07    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f45,plain,(
% 19.37/3.07    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 19.37/3.07    inference(cnf_transformation,[],[f15])).
% 19.37/3.07  
% 19.37/3.07  fof(f3,axiom,(
% 19.37/3.07    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f27,plain,(
% 19.37/3.07    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 19.37/3.07    inference(nnf_transformation,[],[f3])).
% 19.37/3.07  
% 19.37/3.07  fof(f32,plain,(
% 19.37/3.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 19.37/3.07    inference(cnf_transformation,[],[f27])).
% 19.37/3.07  
% 19.37/3.07  fof(f13,axiom,(
% 19.37/3.07    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2))),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f43,plain,(
% 19.37/3.07    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 19.37/3.07    inference(cnf_transformation,[],[f13])).
% 19.37/3.07  
% 19.37/3.07  fof(f20,conjecture,(
% 19.37/3.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f21,negated_conjecture,(
% 19.37/3.07    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 19.37/3.07    inference(negated_conjecture,[],[f20])).
% 19.37/3.07  
% 19.37/3.07  fof(f26,plain,(
% 19.37/3.07    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 19.37/3.07    inference(ennf_transformation,[],[f21])).
% 19.37/3.07  
% 19.37/3.07  fof(f28,plain,(
% 19.37/3.07    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 19.37/3.07    introduced(choice_axiom,[])).
% 19.37/3.07  
% 19.37/3.07  fof(f29,plain,(
% 19.37/3.07    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 19.37/3.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28])).
% 19.37/3.07  
% 19.37/3.07  fof(f51,plain,(
% 19.37/3.07    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 19.37/3.07    inference(cnf_transformation,[],[f29])).
% 19.37/3.07  
% 19.37/3.07  fof(f53,plain,(
% 19.37/3.07    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 19.37/3.07    inference(definition_unfolding,[],[f51,f31,f31])).
% 19.37/3.07  
% 19.37/3.07  fof(f6,axiom,(
% 19.37/3.07    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f23,plain,(
% 19.37/3.07    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 19.37/3.07    inference(ennf_transformation,[],[f6])).
% 19.37/3.07  
% 19.37/3.07  fof(f36,plain,(
% 19.37/3.07    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 19.37/3.07    inference(cnf_transformation,[],[f23])).
% 19.37/3.07  
% 19.37/3.07  fof(f4,axiom,(
% 19.37/3.07    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 19.37/3.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.37/3.07  
% 19.37/3.07  fof(f34,plain,(
% 19.37/3.07    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 19.37/3.07    inference(cnf_transformation,[],[f4])).
% 19.37/3.07  
% 19.37/3.07  cnf(c_13,plain,
% 19.37/3.07      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 19.37/3.07      inference(cnf_transformation,[],[f52]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_9,plain,
% 19.37/3.07      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.37/3.07      inference(cnf_transformation,[],[f40]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_0,plain,
% 19.37/3.07      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 19.37/3.07      inference(cnf_transformation,[],[f30]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_242,plain,
% 19.37/3.07      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k1_xboole_0)) = X0 ),
% 19.37/3.07      inference(theory_normalisation,[status(thm)],[c_13,c_9,c_0]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_8,plain,
% 19.37/3.07      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.37/3.07      inference(cnf_transformation,[],[f39]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_520,plain,
% 19.37/3.07      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_242,c_8]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_17,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 19.37/3.07      inference(cnf_transformation,[],[f48]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_819,plain,
% 19.37/3.07      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_520,c_17]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_821,plain,
% 19.37/3.07      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_819,c_520]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1032,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_821,c_520]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_11,plain,
% 19.37/3.07      ( k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.37/3.07      inference(cnf_transformation,[],[f42]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1349,plain,
% 19.37/3.07      ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1032,c_11]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1030,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_821,c_0]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1353,plain,
% 19.37/3.07      ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_1349,c_1030]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1688,plain,
% 19.37/3.07      ( k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1032,c_1353]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1696,plain,
% 19.37/3.07      ( k3_xboole_0(X0,X0) = X0 ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_1688,c_1032]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_7,plain,
% 19.37/3.07      ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 19.37/3.07      inference(cnf_transformation,[],[f38]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_19,plain,
% 19.37/3.07      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 19.37/3.07      inference(cnf_transformation,[],[f50]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_510,plain,
% 19.37/3.07      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = iProver_top ),
% 19.37/3.07      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_883,plain,
% 19.37/3.07      ( r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k3_xboole_0(X0,X1))) = iProver_top ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_7,c_510]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_5645,plain,
% 19.37/3.07      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k3_xboole_0(k4_xboole_0(X0,X1),X0))) = iProver_top ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1696,c_883]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_5727,plain,
% 19.37/3.07      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_5645,c_1353]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_10,plain,
% 19.37/3.07      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 19.37/3.07      inference(cnf_transformation,[],[f41]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_2073,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1696,c_10]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_5728,plain,
% 19.37/3.07      ( r1_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X1)) = iProver_top ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_5727,c_2073]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1346,plain,
% 19.37/3.07      ( k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1032,c_11]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1358,plain,
% 19.37/3.07      ( k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_1346,c_821]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1290,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1032,c_10]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1297,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_1290,c_8,c_1032]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_817,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_0,c_17]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_18,plain,
% 19.37/3.07      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 19.37/3.07      inference(cnf_transformation,[],[f49]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_511,plain,
% 19.37/3.07      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 19.37/3.07      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_688,plain,
% 19.37/3.07      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_0,c_511]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1668,plain,
% 19.37/3.07      ( r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = iProver_top ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_817,c_688]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_2422,plain,
% 19.37/3.07      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X0),X0) = iProver_top ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1297,c_1668]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_6,plain,
% 19.37/3.07      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 19.37/3.07      inference(cnf_transformation,[],[f37]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_515,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
% 19.37/3.07      | r1_tarski(X0,X1) != iProver_top ),
% 19.37/3.07      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_5201,plain,
% 19.37/3.07      ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X0),k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_2422,c_515]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_533,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1661,plain,
% 19.37/3.07      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_17,c_817]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1126,plain,
% 19.37/3.07      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1030,c_17]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1132,plain,
% 19.37/3.07      ( k2_xboole_0(X0,X0) = X0 ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_1126,c_1030]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1674,plain,
% 19.37/3.07      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_1661,c_1132]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_2456,plain,
% 19.37/3.07      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_0,c_1674]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_2822,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X2)),X2)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_533,c_2456]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1658,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_9,c_817]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_2590,plain,
% 19.37/3.07      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_9,c_2456]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_2824,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_2822,c_1658,c_2590]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_15,plain,
% 19.37/3.07      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 19.37/3.07      inference(cnf_transformation,[],[f47]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_513,plain,
% 19.37/3.07      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 19.37/3.07      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_2747,plain,
% 19.37/3.07      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_510,c_513]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3060,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k3_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_2747,c_11]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_14,plain,
% 19.37/3.07      ( r1_xboole_0(X0,k1_xboole_0) ),
% 19.37/3.07      inference(cnf_transformation,[],[f45]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_514,plain,
% 19.37/3.07      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 19.37/3.07      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_2,plain,
% 19.37/3.07      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 19.37/3.07      inference(cnf_transformation,[],[f32]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_518,plain,
% 19.37/3.07      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 19.37/3.07      | r1_xboole_0(X0,X1) != iProver_top ),
% 19.37/3.07      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_2581,plain,
% 19.37/3.07      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_514,c_518]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3061,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_3060,c_2581]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_5202,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,k1_xboole_0)) = X0 ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_5201,c_2824,c_3061]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_5203,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_5202,c_1030]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_5221,plain,
% 19.37/3.07      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1358,c_5203]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_5729,plain,
% 19.37/3.07      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_5728,c_5221]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_6283,plain,
% 19.37/3.07      ( k3_xboole_0(k4_xboole_0(X0,X1),X1) = k1_xboole_0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_5729,c_518]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_12,plain,
% 19.37/3.07      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 19.37/3.07      inference(cnf_transformation,[],[f43]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3059,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_2747,c_12]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3062,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_3059,c_1030]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_6470,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_6283,c_3062]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_6536,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_6470,c_1032,c_2073]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_6717,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k3_xboole_0(X0,k4_xboole_0(X0,X2)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_6536,c_11]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_6739,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_6717,c_1358]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_20,negated_conjecture,
% 19.37/3.07      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
% 19.37/3.07      inference(cnf_transformation,[],[f53]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_241,negated_conjecture,
% 19.37/3.07      ( k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
% 19.37/3.07      inference(theory_normalisation,[status(thm)],[c_20,c_9,c_0]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_521,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_241,c_7]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_81818,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_6739,c_521]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3055,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_2747,c_10]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3066,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_3055,c_821]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_6764,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_3062,c_3066]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_6831,plain,
% 19.37/3.07      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_6764,c_3066]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_16659,plain,
% 19.37/3.07      ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_6831,c_3062]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3058,plain,
% 19.37/3.07      ( k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_2747,c_7]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3063,plain,
% 19.37/3.07      ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_3058,c_3062]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3235,plain,
% 19.37/3.07      ( k3_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,X0))) = k1_xboole_0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_7,c_3063]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_6731,plain,
% 19.37/3.07      ( k3_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k1_xboole_0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_6536,c_3235]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_12982,plain,
% 19.37/3.07      ( k4_xboole_0(k3_xboole_0(X0,X1),X1) = k1_xboole_0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_6731,c_1353]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_16667,plain,
% 19.37/3.07      ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_16659,c_12982]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_5,plain,
% 19.37/3.07      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 19.37/3.07      inference(cnf_transformation,[],[f36]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_954,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(X1,k4_xboole_0(X2,X0))
% 19.37/3.07      | k3_xboole_0(X1,X2) = X0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_7,c_5]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_24213,plain,
% 19.37/3.07      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
% 19.37/3.07      | k3_xboole_0(X1,k4_xboole_0(X0,k3_xboole_0(X0,X1))) != k1_xboole_0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_16667,c_954]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3053,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_2747,c_12]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3068,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_3053,c_821]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_24245,plain,
% 19.37/3.07      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
% 19.37/3.07      | k3_xboole_0(X0,k4_xboole_0(X1,X0)) != k1_xboole_0 ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_24213,c_3068]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_24246,plain,
% 19.37/3.07      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
% 19.37/3.07      | k1_xboole_0 != k1_xboole_0 ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_24245,c_3063]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_24247,plain,
% 19.37/3.07      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 19.37/3.07      inference(equality_resolution_simp,[status(thm)],[c_24246]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3,plain,
% 19.37/3.07      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 19.37/3.07      inference(cnf_transformation,[],[f34]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_517,plain,
% 19.37/3.07      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 19.37/3.07      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1282,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_517,c_515]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_15464,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_1282,c_1282,c_3068]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_24468,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X1 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_24247,c_15464]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1557,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1297,c_9]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_30142,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_24468,c_1557]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3243,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_3063,c_10]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3246,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_3243,c_1030]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_53989,plain,
% 19.37/3.07      ( k3_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_3246,c_3066]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_54123,plain,
% 19.37/3.07      ( k3_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k3_xboole_0(X0,X1) ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_53989,c_3066]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_81819,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_81818,c_30142,c_54123]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_535,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_15553,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,X0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_15464,c_535]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_13112,plain,
% 19.37/3.07      ( k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_12982,c_11]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_13176,plain,
% 19.37/3.07      ( k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_13112,c_7]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_1562,plain,
% 19.37/3.07      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1297,c_821]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_13177,plain,
% 19.37/3.07      ( k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_13176,c_7,c_1562]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_3244,plain,
% 19.37/3.07      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_3063,c_11]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_6768,plain,
% 19.37/3.07      ( k3_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_xboole_0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_3244,c_3066]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_6827,plain,
% 19.37/3.07      ( k3_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = X0 ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_6768,c_1032]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_24481,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_24247,c_5203]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_24713,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_6827,c_24481]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_2210,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_1358,c_1297]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_2300,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_2210,c_9]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_19752,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),X1)) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_817,c_2300]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_19917,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_19752,c_2300]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_24822,plain,
% 19.37/3.07      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_24713,c_19917]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_35157,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_13177,c_24822]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_24757,plain,
% 19.37/3.07      ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_24481,c_535]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_35284,plain,
% 19.37/3.07      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 19.37/3.07      inference(light_normalisation,[status(thm)],[c_35157,c_24757]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_42076,plain,
% 19.37/3.07      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 19.37/3.07      inference(superposition,[status(thm)],[c_30142,c_35284]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_42263,plain,
% 19.37/3.07      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_42076,c_35284]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_81820,plain,
% 19.37/3.07      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 19.37/3.07      inference(demodulation,[status(thm)],[c_81819,c_15553,c_42263]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(c_917,plain,
% 19.37/3.07      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1) ),
% 19.37/3.07      inference(instantiation,[status(thm)],[c_0]) ).
% 19.37/3.07  
% 19.37/3.07  cnf(contradiction,plain,
% 19.37/3.07      ( $false ),
% 19.37/3.07      inference(minisat,[status(thm)],[c_81820,c_917]) ).
% 19.37/3.07  
% 19.37/3.07  
% 19.37/3.07  % SZS output end CNFRefutation for theBenchmark.p
% 19.37/3.07  
% 19.37/3.07  ------                               Statistics
% 19.37/3.07  
% 19.37/3.07  ------ General
% 19.37/3.07  
% 19.37/3.07  abstr_ref_over_cycles:                  0
% 19.37/3.07  abstr_ref_under_cycles:                 0
% 19.37/3.07  gc_basic_clause_elim:                   0
% 19.37/3.07  forced_gc_time:                         0
% 19.37/3.07  parsing_time:                           0.011
% 19.37/3.07  unif_index_cands_time:                  0.
% 19.37/3.07  unif_index_add_time:                    0.
% 19.37/3.07  orderings_time:                         0.
% 19.37/3.07  out_proof_time:                         0.012
% 19.37/3.07  total_time:                             2.181
% 19.37/3.07  num_of_symbols:                         39
% 19.37/3.07  num_of_terms:                           101222
% 19.37/3.07  
% 19.37/3.07  ------ Preprocessing
% 19.37/3.07  
% 19.37/3.07  num_of_splits:                          0
% 19.37/3.07  num_of_split_atoms:                     0
% 19.37/3.07  num_of_reused_defs:                     0
% 19.37/3.07  num_eq_ax_congr_red:                    0
% 19.37/3.07  num_of_sem_filtered_clauses:            1
% 19.37/3.07  num_of_subtypes:                        0
% 19.37/3.07  monotx_restored_types:                  0
% 19.37/3.07  sat_num_of_epr_types:                   0
% 19.37/3.07  sat_num_of_non_cyclic_types:            0
% 19.37/3.07  sat_guarded_non_collapsed_types:        0
% 19.37/3.07  num_pure_diseq_elim:                    0
% 19.37/3.07  simp_replaced_by:                       0
% 19.37/3.07  res_preprocessed:                       78
% 19.37/3.07  prep_upred:                             0
% 19.37/3.07  prep_unflattend:                        20
% 19.37/3.07  smt_new_axioms:                         0
% 19.37/3.07  pred_elim_cands:                        2
% 19.37/3.07  pred_elim:                              0
% 19.37/3.07  pred_elim_cl:                           0
% 19.37/3.07  pred_elim_cycles:                       2
% 19.37/3.07  merged_defs:                            6
% 19.37/3.07  merged_defs_ncl:                        0
% 19.37/3.07  bin_hyper_res:                          6
% 19.37/3.07  prep_cycles:                            3
% 19.37/3.07  pred_elim_time:                         0.001
% 19.37/3.07  splitting_time:                         0.
% 19.37/3.07  sem_filter_time:                        0.
% 19.37/3.07  monotx_time:                            0.
% 19.37/3.07  subtype_inf_time:                       0.
% 19.37/3.07  
% 19.37/3.07  ------ Problem properties
% 19.37/3.07  
% 19.37/3.07  clauses:                                21
% 19.37/3.07  conjectures:                            1
% 19.37/3.07  epr:                                    3
% 19.37/3.07  horn:                                   21
% 19.37/3.07  ground:                                 2
% 19.37/3.07  unary:                                  15
% 19.37/3.07  binary:                                 6
% 19.37/3.07  lits:                                   27
% 19.37/3.07  lits_eq:                                17
% 19.37/3.07  fd_pure:                                0
% 19.37/3.07  fd_pseudo:                              0
% 19.37/3.07  fd_cond:                                1
% 19.37/3.07  fd_pseudo_cond:                         1
% 19.37/3.07  ac_symbols:                             1
% 19.37/3.07  
% 19.37/3.07  ------ Propositional Solver
% 19.37/3.07  
% 19.37/3.07  prop_solver_calls:                      26
% 19.37/3.07  prop_fast_solver_calls:                 627
% 19.37/3.07  smt_solver_calls:                       0
% 19.37/3.07  smt_fast_solver_calls:                  0
% 19.37/3.07  prop_num_of_clauses:                    17155
% 19.37/3.07  prop_preprocess_simplified:             16894
% 19.37/3.07  prop_fo_subsumed:                       0
% 19.37/3.07  prop_solver_time:                       0.
% 19.37/3.07  smt_solver_time:                        0.
% 19.37/3.07  smt_fast_solver_time:                   0.
% 19.37/3.07  prop_fast_solver_time:                  0.
% 19.37/3.07  prop_unsat_core_time:                   0.002
% 19.37/3.07  
% 19.37/3.07  ------ QBF
% 19.37/3.07  
% 19.37/3.07  qbf_q_res:                              0
% 19.37/3.07  qbf_num_tautologies:                    0
% 19.37/3.07  qbf_prep_cycles:                        0
% 19.37/3.07  
% 19.37/3.07  ------ BMC1
% 19.37/3.07  
% 19.37/3.07  bmc1_current_bound:                     -1
% 19.37/3.07  bmc1_last_solved_bound:                 -1
% 19.37/3.07  bmc1_unsat_core_size:                   -1
% 19.37/3.07  bmc1_unsat_core_parents_size:           -1
% 19.37/3.07  bmc1_merge_next_fun:                    0
% 19.37/3.07  bmc1_unsat_core_clauses_time:           0.
% 19.37/3.07  
% 19.37/3.07  ------ Instantiation
% 19.37/3.07  
% 19.37/3.07  inst_num_of_clauses:                    3887
% 19.37/3.07  inst_num_in_passive:                    587
% 19.37/3.07  inst_num_in_active:                     1512
% 19.37/3.07  inst_num_in_unprocessed:                1791
% 19.37/3.07  inst_num_of_loops:                      1580
% 19.37/3.07  inst_num_of_learning_restarts:          0
% 19.37/3.07  inst_num_moves_active_passive:          67
% 19.37/3.07  inst_lit_activity:                      0
% 19.37/3.07  inst_lit_activity_moves:                0
% 19.37/3.07  inst_num_tautologies:                   0
% 19.37/3.07  inst_num_prop_implied:                  0
% 19.37/3.07  inst_num_existing_simplified:           0
% 19.37/3.07  inst_num_eq_res_simplified:             0
% 19.37/3.07  inst_num_child_elim:                    0
% 19.37/3.07  inst_num_of_dismatching_blockings:      4383
% 19.37/3.07  inst_num_of_non_proper_insts:           6291
% 19.37/3.07  inst_num_of_duplicates:                 0
% 19.37/3.07  inst_inst_num_from_inst_to_res:         0
% 19.37/3.07  inst_dismatching_checking_time:         0.
% 19.37/3.07  
% 19.37/3.07  ------ Resolution
% 19.37/3.07  
% 19.37/3.07  res_num_of_clauses:                     0
% 19.37/3.07  res_num_in_passive:                     0
% 19.37/3.07  res_num_in_active:                      0
% 19.37/3.07  res_num_of_loops:                       81
% 19.37/3.07  res_forward_subset_subsumed:            829
% 19.37/3.07  res_backward_subset_subsumed:           10
% 19.37/3.07  res_forward_subsumed:                   1
% 19.37/3.07  res_backward_subsumed:                  0
% 19.37/3.07  res_forward_subsumption_resolution:     0
% 19.37/3.07  res_backward_subsumption_resolution:    0
% 19.37/3.07  res_clause_to_clause_subsumption:       89282
% 19.37/3.07  res_orphan_elimination:                 0
% 19.37/3.07  res_tautology_del:                      443
% 19.37/3.07  res_num_eq_res_simplified:              0
% 19.37/3.07  res_num_sel_changes:                    0
% 19.37/3.07  res_moves_from_active_to_pass:          0
% 19.37/3.07  
% 19.37/3.07  ------ Superposition
% 19.37/3.07  
% 19.37/3.07  sup_time_total:                         0.
% 19.37/3.07  sup_time_generating:                    0.
% 19.37/3.07  sup_time_sim_full:                      0.
% 19.37/3.07  sup_time_sim_immed:                     0.
% 19.37/3.07  
% 19.37/3.07  sup_num_of_clauses:                     5154
% 19.37/3.07  sup_num_in_active:                      292
% 19.37/3.07  sup_num_in_passive:                     4862
% 19.37/3.07  sup_num_of_loops:                       315
% 19.37/3.07  sup_fw_superposition:                   22240
% 19.37/3.07  sup_bw_superposition:                   17039
% 19.37/3.07  sup_immediate_simplified:               14261
% 19.37/3.07  sup_given_eliminated:                   3
% 19.37/3.07  comparisons_done:                       0
% 19.37/3.07  comparisons_avoided:                    0
% 19.37/3.07  
% 19.37/3.07  ------ Simplifications
% 19.37/3.07  
% 19.37/3.07  
% 19.37/3.07  sim_fw_subset_subsumed:                 1
% 19.37/3.07  sim_bw_subset_subsumed:                 0
% 19.37/3.07  sim_fw_subsumed:                        2855
% 19.37/3.07  sim_bw_subsumed:                        40
% 19.37/3.07  sim_fw_subsumption_res:                 0
% 19.37/3.07  sim_bw_subsumption_res:                 0
% 19.37/3.07  sim_tautology_del:                      46
% 19.37/3.07  sim_eq_tautology_del:                   2811
% 19.37/3.07  sim_eq_res_simp:                        3
% 19.37/3.07  sim_fw_demodulated:                     7771
% 19.37/3.07  sim_bw_demodulated:                     109
% 19.37/3.07  sim_light_normalised:                   6402
% 19.37/3.07  sim_joinable_taut:                      58
% 19.37/3.07  sim_joinable_simp:                      0
% 19.37/3.07  sim_ac_normalised:                      0
% 19.37/3.07  sim_smt_subsumption:                    0
% 19.37/3.07  
%------------------------------------------------------------------------------
