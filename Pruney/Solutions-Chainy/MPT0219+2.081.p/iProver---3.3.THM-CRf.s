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
% DateTime   : Thu Dec  3 11:29:22 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  112 (3583 expanded)
%              Number of clauses        :   56 ( 495 expanded)
%              Number of leaves         :   19 (1124 expanded)
%              Depth                    :   30
%              Number of atoms          :  131 (3913 expanded)
%              Number of equality atoms :  116 (3766 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f23,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK0 != sK1
      & k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( sK0 != sK1
    & k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f43,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f48])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f56,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f43,f34,f50,f50,f50])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f31,f31])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f42,f50,f50])).

fof(f44,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_552,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
    inference(superposition,[status(thm)],[c_9,c_6])).

cnf(c_646,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
    inference(superposition,[status(thm)],[c_552,c_6])).

cnf(c_739,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
    inference(superposition,[status(thm)],[c_6,c_646])).

cnf(c_749,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
    inference(demodulation,[status(thm)],[c_739,c_552])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_461,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_882,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k4_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(superposition,[status(thm)],[c_749,c_461])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_142,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_141,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_391,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_142,c_141])).

cnf(c_1139,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_391,c_0])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1143,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1139,c_5])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1232,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1143,c_1])).

cnf(c_1318,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1232,c_0])).

cnf(c_1325,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1318,c_5])).

cnf(c_1326,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1325,c_1232])).

cnf(c_1573,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_882,c_1326])).

cnf(c_1599,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1573,c_552])).

cnf(c_1608,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1599,c_9])).

cnf(c_1628,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1608,c_749])).

cnf(c_1588,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_552,c_1573])).

cnf(c_2247,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_552,c_1588])).

cnf(c_2324,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2247,c_2247])).

cnf(c_751,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),X1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_749,c_646])).

cnf(c_2333,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2324,c_5,c_552,c_751])).

cnf(c_2572,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))),k5_xboole_0(k1_xboole_0,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1628,c_2333])).

cnf(c_551,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_2598,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))),X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2572,c_551,c_552])).

cnf(c_2634,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_552,c_2598])).

cnf(c_2890,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2634,c_2247])).

cnf(c_2899,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2890,c_5,c_552,c_751])).

cnf(c_639,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_461,c_6])).

cnf(c_3083,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(light_normalisation,[status(thm)],[c_639,c_639,c_1326])).

cnf(c_3106,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_461,c_3083])).

cnf(c_462,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_463,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_462,c_2])).

cnf(c_3158,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3106,c_463])).

cnf(c_3160,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_3158,c_3083])).

cnf(c_3516,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2899,c_552,c_749,c_3160])).

cnf(c_3519,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_552,c_3516])).

cnf(c_3664,plain,
    ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3519,c_552,c_3160])).

cnf(c_542,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_142])).

cnf(c_3693,plain,
    ( r1_tarski(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3664,c_542])).

cnf(c_3713,plain,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3693,c_1325])).

cnf(c_7,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_146,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_147,plain,
    ( sK0 = sK1
    | r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146])).

cnf(c_8,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3713,c_147,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:10:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
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
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  ------ Proving...
% 3.85/0.98  ------ Problem Properties 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  clauses                                 10
% 3.85/0.98  conjectures                             2
% 3.85/0.98  EPR                                     2
% 3.85/0.98  Horn                                    10
% 3.85/0.98  unary                                   8
% 3.85/0.98  binary                                  2
% 3.85/0.98  lits                                    12
% 3.85/0.98  lits eq                                 9
% 3.85/0.98  fd_pure                                 0
% 3.85/0.98  fd_pseudo                               0
% 3.85/0.98  fd_cond                                 1
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
% 3.85/0.98  fof(f18,conjecture,(
% 3.85/0.98    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f19,negated_conjecture,(
% 3.85/0.98    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.85/0.98    inference(negated_conjecture,[],[f18])).
% 3.85/0.98  
% 3.85/0.98  fof(f23,plain,(
% 3.85/0.98    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f19])).
% 3.85/0.98  
% 3.85/0.98  fof(f24,plain,(
% 3.85/0.98    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK0 != sK1 & k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f25,plain,(
% 3.85/0.98    sK0 != sK1 & k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0)),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 3.85/0.98  
% 3.85/0.98  fof(f43,plain,(
% 3.85/0.98    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0)),
% 3.85/0.98    inference(cnf_transformation,[],[f25])).
% 3.85/0.98  
% 3.85/0.98  fof(f9,axiom,(
% 3.85/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f34,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f9])).
% 3.85/0.98  
% 3.85/0.98  fof(f10,axiom,(
% 3.85/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f35,plain,(
% 3.85/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f10])).
% 3.85/0.98  
% 3.85/0.98  fof(f11,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f36,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f11])).
% 3.85/0.98  
% 3.85/0.98  fof(f12,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f37,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f12])).
% 3.85/0.98  
% 3.85/0.98  fof(f13,axiom,(
% 3.85/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f38,plain,(
% 3.85/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f13])).
% 3.85/0.98  
% 3.85/0.98  fof(f14,axiom,(
% 3.85/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f39,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f14])).
% 3.85/0.98  
% 3.85/0.98  fof(f15,axiom,(
% 3.85/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f40,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f16,axiom,(
% 3.85/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f41,plain,(
% 3.85/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f16])).
% 3.85/0.98  
% 3.85/0.98  fof(f45,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f40,f41])).
% 3.85/0.98  
% 3.85/0.98  fof(f46,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f39,f45])).
% 3.85/0.98  
% 3.85/0.98  fof(f47,plain,(
% 3.85/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f38,f46])).
% 3.85/0.98  
% 3.85/0.98  fof(f48,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f37,f47])).
% 3.85/0.98  
% 3.85/0.98  fof(f49,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f36,f48])).
% 3.85/0.98  
% 3.85/0.98  fof(f50,plain,(
% 3.85/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f35,f49])).
% 3.85/0.98  
% 3.85/0.98  fof(f56,plain,(
% 3.85/0.98    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 3.85/0.98    inference(definition_unfolding,[],[f43,f34,f50,f50,f50])).
% 3.85/0.98  
% 3.85/0.98  fof(f8,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f33,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f8])).
% 3.85/0.98  
% 3.85/0.98  fof(f2,axiom,(
% 3.85/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f20,plain,(
% 3.85/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.85/0.98    inference(rectify,[],[f2])).
% 3.85/0.98  
% 3.85/0.98  fof(f27,plain,(
% 3.85/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.85/0.98    inference(cnf_transformation,[],[f20])).
% 3.85/0.98  
% 3.85/0.98  fof(f6,axiom,(
% 3.85/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f31,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f6])).
% 3.85/0.98  
% 3.85/0.98  fof(f53,plain,(
% 3.85/0.98    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.85/0.98    inference(definition_unfolding,[],[f27,f31])).
% 3.85/0.98  
% 3.85/0.98  fof(f3,axiom,(
% 3.85/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f28,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f3])).
% 3.85/0.98  
% 3.85/0.98  fof(f51,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f28,f31])).
% 3.85/0.98  
% 3.85/0.98  fof(f4,axiom,(
% 3.85/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f29,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f4])).
% 3.85/0.98  
% 3.85/0.98  fof(f54,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f29,f31])).
% 3.85/0.98  
% 3.85/0.98  fof(f5,axiom,(
% 3.85/0.98    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f21,plain,(
% 3.85/0.98    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.85/0.98    inference(ennf_transformation,[],[f5])).
% 3.85/0.98  
% 3.85/0.98  fof(f30,plain,(
% 3.85/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f21])).
% 3.85/0.98  
% 3.85/0.98  fof(f7,axiom,(
% 3.85/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f32,plain,(
% 3.85/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.85/0.98    inference(cnf_transformation,[],[f7])).
% 3.85/0.98  
% 3.85/0.98  fof(f1,axiom,(
% 3.85/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f26,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f1])).
% 3.85/0.98  
% 3.85/0.98  fof(f52,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f26,f31,f31])).
% 3.85/0.98  
% 3.85/0.98  fof(f17,axiom,(
% 3.85/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f22,plain,(
% 3.85/0.98    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 3.85/0.98    inference(ennf_transformation,[],[f17])).
% 3.85/0.98  
% 3.85/0.98  fof(f42,plain,(
% 3.85/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f22])).
% 3.85/0.98  
% 3.85/0.98  fof(f55,plain,(
% 3.85/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f42,f50,f50])).
% 3.85/0.98  
% 3.85/0.98  fof(f44,plain,(
% 3.85/0.98    sK0 != sK1),
% 3.85/0.98    inference(cnf_transformation,[],[f25])).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9,negated_conjecture,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_6,plain,
% 3.85/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_552,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_9,c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_646,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_552,c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_739,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_6,c_646]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_749,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_739,c_552]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2,plain,
% 3.85/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_0,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_461,plain,
% 3.85/0.98      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_882,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k4_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_749,c_461]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3,plain,
% 3.85/0.98      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_142,plain,
% 3.85/0.98      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_141,plain,
% 3.85/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_391,plain,
% 3.85/0.98      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_142,c_141]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1139,plain,
% 3.85/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_391,c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1143,plain,
% 3.85/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_1139,c_5]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1,plain,
% 3.85/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1232,plain,
% 3.85/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1143,c_1]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1318,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1232,c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1325,plain,
% 3.85/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_1318,c_5]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1326,plain,
% 3.85/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_1325,c_1232]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1573,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k1_xboole_0 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_882,c_1326]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1599,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1573,c_552]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1608,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_1599,c_9]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1628,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1608,c_749]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1588,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k1_xboole_0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_552,c_1573]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2247,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k1_xboole_0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_552,c_1588]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2324,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))),k1_xboole_0)) = k1_xboole_0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2247,c_2247]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_751,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),X1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,X1)) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_749,c_646]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2333,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))) = k1_xboole_0 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_2324,c_5,c_552,c_751]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2572,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))),k5_xboole_0(k1_xboole_0,X0)))) = k1_xboole_0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1628,c_2333]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_551,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2598,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))),X0)) = k1_xboole_0 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_2572,c_551,c_552]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2634,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) = k1_xboole_0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_552,c_2598]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2890,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))),k1_xboole_0)) = k1_xboole_0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2634,c_2247]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2899,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))) = k1_xboole_0 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_2890,c_5,c_552,c_751]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_639,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_461,c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3083,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_639,c_639,c_1326]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3106,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_461,c_3083]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_462,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_463,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_462,c_2]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3158,plain,
% 3.85/0.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_3106,c_463]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3160,plain,
% 3.85/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_3158,c_3083]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3516,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))) = k1_xboole_0 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_2899,c_552,c_749,c_3160]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3519,plain,
% 3.85/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k1_xboole_0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_552,c_3516]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3664,plain,
% 3.85/0.98      ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_3519,c_552,c_3160]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_542,plain,
% 3.85/0.98      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1,c_142]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3693,plain,
% 3.85/0.98      ( r1_tarski(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_3664,c_542]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3713,plain,
% 3.85/0.98      ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_3693,c_1325]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7,plain,
% 3.85/0.98      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.85/0.98      | X1 = X0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_146,plain,
% 3.85/0.98      ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 3.85/0.98      | sK0 = sK1 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_147,plain,
% 3.85/0.98      ( sK0 = sK1
% 3.85/0.98      | r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_146]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_8,negated_conjecture,
% 3.85/0.98      ( sK0 != sK1 ),
% 3.85/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(contradiction,plain,
% 3.85/0.98      ( $false ),
% 3.85/0.98      inference(minisat,[status(thm)],[c_3713,c_147,c_8]) ).
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
% 3.85/0.98  parsing_time:                           0.005
% 3.85/0.98  unif_index_cands_time:                  0.
% 3.85/0.98  unif_index_add_time:                    0.
% 3.85/0.98  orderings_time:                         0.
% 3.85/0.98  out_proof_time:                         0.008
% 3.85/0.98  total_time:                             0.227
% 3.85/0.98  num_of_symbols:                         38
% 3.85/0.98  num_of_terms:                           6373
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing
% 3.85/0.98  
% 3.85/0.98  num_of_splits:                          0
% 3.85/0.98  num_of_split_atoms:                     0
% 3.85/0.98  num_of_reused_defs:                     0
% 3.85/0.98  num_eq_ax_congr_red:                    0
% 3.85/0.98  num_of_sem_filtered_clauses:            1
% 3.85/0.98  num_of_subtypes:                        0
% 3.85/0.98  monotx_restored_types:                  0
% 3.85/0.98  sat_num_of_epr_types:                   0
% 3.85/0.98  sat_num_of_non_cyclic_types:            0
% 3.85/0.98  sat_guarded_non_collapsed_types:        0
% 3.85/0.98  num_pure_diseq_elim:                    0
% 3.85/0.98  simp_replaced_by:                       0
% 3.85/0.98  res_preprocessed:                       43
% 3.85/0.98  prep_upred:                             0
% 3.85/0.98  prep_unflattend:                        3
% 3.85/0.98  smt_new_axioms:                         0
% 3.85/0.98  pred_elim_cands:                        1
% 3.85/0.98  pred_elim:                              0
% 3.85/0.98  pred_elim_cl:                           0
% 3.85/0.98  pred_elim_cycles:                       1
% 3.85/0.98  merged_defs:                            0
% 3.85/0.98  merged_defs_ncl:                        0
% 3.85/0.98  bin_hyper_res:                          0
% 3.85/0.98  prep_cycles:                            3
% 3.85/0.98  pred_elim_time:                         0.
% 3.85/0.98  splitting_time:                         0.
% 3.85/0.98  sem_filter_time:                        0.
% 3.85/0.98  monotx_time:                            0.
% 3.85/0.98  subtype_inf_time:                       0.
% 3.85/0.98  
% 3.85/0.98  ------ Problem properties
% 3.85/0.98  
% 3.85/0.98  clauses:                                10
% 3.85/0.98  conjectures:                            2
% 3.85/0.98  epr:                                    2
% 3.85/0.98  horn:                                   10
% 3.85/0.98  ground:                                 2
% 3.85/0.98  unary:                                  8
% 3.85/0.98  binary:                                 2
% 3.85/0.98  lits:                                   12
% 3.85/0.98  lits_eq:                                9
% 3.85/0.98  fd_pure:                                0
% 3.85/0.98  fd_pseudo:                              0
% 3.85/0.98  fd_cond:                                1
% 3.85/0.98  fd_pseudo_cond:                         1
% 3.85/0.98  ac_symbols:                             0
% 3.85/0.98  
% 3.85/0.98  ------ Propositional Solver
% 3.85/0.98  
% 3.85/0.98  prop_solver_calls:                      27
% 3.85/0.98  prop_fast_solver_calls:                 234
% 3.85/0.98  smt_solver_calls:                       0
% 3.85/0.98  smt_fast_solver_calls:                  0
% 3.85/0.98  prop_num_of_clauses:                    1620
% 3.85/0.98  prop_preprocess_simplified:             3086
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
% 3.85/0.98  inst_num_of_clauses:                    582
% 3.85/0.98  inst_num_in_passive:                    87
% 3.85/0.98  inst_num_in_active:                     247
% 3.85/0.98  inst_num_in_unprocessed:                248
% 3.85/0.98  inst_num_of_loops:                      270
% 3.85/0.98  inst_num_of_learning_restarts:          0
% 3.85/0.98  inst_num_moves_active_passive:          19
% 3.85/0.98  inst_lit_activity:                      0
% 3.85/0.98  inst_lit_activity_moves:                0
% 3.85/0.98  inst_num_tautologies:                   0
% 3.85/0.98  inst_num_prop_implied:                  0
% 3.85/0.98  inst_num_existing_simplified:           0
% 3.85/0.98  inst_num_eq_res_simplified:             0
% 3.85/0.98  inst_num_child_elim:                    0
% 3.85/0.98  inst_num_of_dismatching_blockings:      137
% 3.85/0.98  inst_num_of_non_proper_insts:           724
% 3.85/0.98  inst_num_of_duplicates:                 0
% 3.85/0.98  inst_inst_num_from_inst_to_res:         0
% 3.85/0.98  inst_dismatching_checking_time:         0.
% 3.85/0.98  
% 3.85/0.98  ------ Resolution
% 3.85/0.98  
% 3.85/0.98  res_num_of_clauses:                     0
% 3.85/0.98  res_num_in_passive:                     0
% 3.85/0.98  res_num_in_active:                      0
% 3.85/0.98  res_num_of_loops:                       46
% 3.85/0.98  res_forward_subset_subsumed:            106
% 3.85/0.98  res_backward_subset_subsumed:           0
% 3.85/0.98  res_forward_subsumed:                   0
% 3.85/0.98  res_backward_subsumed:                  0
% 3.85/0.98  res_forward_subsumption_resolution:     0
% 3.85/0.98  res_backward_subsumption_resolution:    0
% 3.85/0.98  res_clause_to_clause_subsumption:       886
% 3.85/0.98  res_orphan_elimination:                 0
% 3.85/0.98  res_tautology_del:                      56
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
% 3.85/0.98  sup_num_of_clauses:                     194
% 3.85/0.98  sup_num_in_active:                      31
% 3.85/0.98  sup_num_in_passive:                     163
% 3.85/0.98  sup_num_of_loops:                       53
% 3.85/0.98  sup_fw_superposition:                   470
% 3.85/0.98  sup_bw_superposition:                   277
% 3.85/0.98  sup_immediate_simplified:               416
% 3.85/0.98  sup_given_eliminated:                   5
% 3.85/0.98  comparisons_done:                       0
% 3.85/0.98  comparisons_avoided:                    0
% 3.85/0.98  
% 3.85/0.98  ------ Simplifications
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  sim_fw_subset_subsumed:                 0
% 3.85/0.98  sim_bw_subset_subsumed:                 0
% 3.85/0.98  sim_fw_subsumed:                        35
% 3.85/0.98  sim_bw_subsumed:                        12
% 3.85/0.98  sim_fw_subsumption_res:                 0
% 3.85/0.98  sim_bw_subsumption_res:                 0
% 3.85/0.98  sim_tautology_del:                      0
% 3.85/0.98  sim_eq_tautology_del:                   178
% 3.85/0.98  sim_eq_res_simp:                        0
% 3.85/0.98  sim_fw_demodulated:                     292
% 3.85/0.98  sim_bw_demodulated:                     32
% 3.85/0.98  sim_light_normalised:                   189
% 3.85/0.98  sim_joinable_taut:                      0
% 3.85/0.98  sim_joinable_simp:                      0
% 3.85/0.98  sim_ac_normalised:                      0
% 3.85/0.98  sim_smt_subsumption:                    0
% 3.85/0.98  
%------------------------------------------------------------------------------
