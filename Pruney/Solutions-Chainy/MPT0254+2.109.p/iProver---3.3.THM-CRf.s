%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:05 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  141 (4244 expanded)
%              Number of clauses        :   83 (1162 expanded)
%              Number of leaves         :   21 (1232 expanded)
%              Depth                    :   30
%              Number of atoms          :  153 (4329 expanded)
%              Number of equality atoms :  144 (4304 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f20])).

fof(f24,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f21])).

fof(f26,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26])).

fof(f48,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f59,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f48,f37,f54])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f37,f53])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f46,f31,f54,f54,f54])).

fof(f60,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f58])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_57,negated_conjecture,
    ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_11,c_6,c_1])).

cnf(c_222,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_57])).

cnf(c_426,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_222,c_6])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_309,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_433,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_426,c_309])).

cnf(c_600,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_433])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_601,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_433])).

cnf(c_605,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_601,c_5])).

cnf(c_609,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_605,c_433])).

cnf(c_713,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_600,c_609])).

cnf(c_611,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,sK1)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_609])).

cnf(c_718,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_611])).

cnf(c_617,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_609,c_6])).

cnf(c_429,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_1339,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_617,c_429])).

cnf(c_2160,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(sK1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1339,c_1])).

cnf(c_2583,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),sK1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_609,c_2160])).

cnf(c_2985,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),sK1),k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_718,c_2583])).

cnf(c_121,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_120,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_3924,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(sK1,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_609,c_120])).

cnf(c_4499,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0)) = k5_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_7,c_3924])).

cnf(c_5702,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),sK1) ),
    inference(superposition,[status(thm)],[c_121,c_4499])).

cnf(c_119,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_4738,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,sK1)) ),
    inference(superposition,[status(thm)],[c_4499,c_119])).

cnf(c_5755,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sK1) = k5_xboole_0(X1,k5_xboole_0(X0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_5702,c_4738])).

cnf(c_8636,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK1)),k5_xboole_0(X1,k5_xboole_0(X0,sK1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2985,c_2985,c_5755])).

cnf(c_8661,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_713,c_8636])).

cnf(c_8700,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),k5_xboole_0(sK1,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_713,c_8636])).

cnf(c_785,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_617])).

cnf(c_805,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK1,X0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_785,c_5])).

cnf(c_1003,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1,c_805])).

cnf(c_1832,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1003,c_713])).

cnf(c_1838,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(demodulation,[status(thm)],[c_1832,c_611])).

cnf(c_1827,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_713])).

cnf(c_1841,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_1827,c_5])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_113,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_463,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_113])).

cnf(c_1396,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_463])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_114,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7632,plain,
    ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK1 ),
    inference(superposition,[status(thm)],[c_1396,c_114])).

cnf(c_8804,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8700,c_1838,c_1841,c_7632])).

cnf(c_2846,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_119])).

cnf(c_2930,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_2846,c_5])).

cnf(c_4215,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK1,X0))) = k5_xboole_0(sK1,X1) ),
    inference(superposition,[status(thm)],[c_2930,c_617])).

cnf(c_6813,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_4215,c_713])).

cnf(c_6854,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_6813,c_1841])).

cnf(c_8805,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8804,c_5,c_7,c_6854])).

cnf(c_8830,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k5_xboole_0(k1_xboole_0,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8661,c_8805])).

cnf(c_5623,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),X1),k5_xboole_0(X2,sK1)) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_617,c_121])).

cnf(c_781,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_617])).

cnf(c_3240,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,X1)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_781,c_6])).

cnf(c_2907,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_119,c_617])).

cnf(c_2923,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_2907,c_6])).

cnf(c_3261,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_3240,c_2923])).

cnf(c_5772,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X1,k5_xboole_0(X2,sK1))) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_5623,c_3261])).

cnf(c_8,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_58,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_8,c_6,c_1])).

cnf(c_415,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_58])).

cnf(c_3912,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_5,c_120])).

cnf(c_7886,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_415,c_3912])).

cnf(c_6339,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[status(thm)],[c_3912,c_58])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_465,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_113])).

cnf(c_466,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_465,c_7])).

cnf(c_897,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_466,c_114])).

cnf(c_6358,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6339,c_309,c_897])).

cnf(c_7909,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7886,c_6358])).

cnf(c_8831,plain,
    ( sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8830,c_7,c_309,c_5772,c_7909])).

cnf(c_8874,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8831,c_605])).

cnf(c_8882,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8874,c_5,c_897])).

cnf(c_10,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_115,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10,c_2,c_7])).

cnf(c_117,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8882,c_117])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:18:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.77/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/0.98  
% 3.77/0.98  ------  iProver source info
% 3.77/0.98  
% 3.77/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.77/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/0.98  git: non_committed_changes: false
% 3.77/0.98  git: last_make_outside_of_git: false
% 3.77/0.98  
% 3.77/0.98  ------ 
% 3.77/0.98  
% 3.77/0.98  ------ Input Options
% 3.77/0.98  
% 3.77/0.98  --out_options                           all
% 3.77/0.98  --tptp_safe_out                         true
% 3.77/0.98  --problem_path                          ""
% 3.77/0.98  --include_path                          ""
% 3.77/0.98  --clausifier                            res/vclausify_rel
% 3.77/0.98  --clausifier_options                    ""
% 3.77/0.98  --stdin                                 false
% 3.77/0.98  --stats_out                             all
% 3.77/0.98  
% 3.77/0.98  ------ General Options
% 3.77/0.98  
% 3.77/0.98  --fof                                   false
% 3.77/0.98  --time_out_real                         305.
% 3.77/0.98  --time_out_virtual                      -1.
% 3.77/0.98  --symbol_type_check                     false
% 3.77/0.98  --clausify_out                          false
% 3.77/0.98  --sig_cnt_out                           false
% 3.77/0.98  --trig_cnt_out                          false
% 3.77/0.98  --trig_cnt_out_tolerance                1.
% 3.77/0.98  --trig_cnt_out_sk_spl                   false
% 3.77/0.98  --abstr_cl_out                          false
% 3.77/0.98  
% 3.77/0.98  ------ Global Options
% 3.77/0.98  
% 3.77/0.98  --schedule                              default
% 3.77/0.98  --add_important_lit                     false
% 3.77/0.98  --prop_solver_per_cl                    1000
% 3.77/0.98  --min_unsat_core                        false
% 3.77/0.98  --soft_assumptions                      false
% 3.77/0.98  --soft_lemma_size                       3
% 3.77/0.98  --prop_impl_unit_size                   0
% 3.77/0.98  --prop_impl_unit                        []
% 3.77/0.98  --share_sel_clauses                     true
% 3.77/0.98  --reset_solvers                         false
% 3.77/0.98  --bc_imp_inh                            [conj_cone]
% 3.77/0.98  --conj_cone_tolerance                   3.
% 3.77/0.98  --extra_neg_conj                        none
% 3.77/0.98  --large_theory_mode                     true
% 3.77/0.98  --prolific_symb_bound                   200
% 3.77/0.98  --lt_threshold                          2000
% 3.77/0.98  --clause_weak_htbl                      true
% 3.77/0.98  --gc_record_bc_elim                     false
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing Options
% 3.77/0.98  
% 3.77/0.98  --preprocessing_flag                    true
% 3.77/0.98  --time_out_prep_mult                    0.1
% 3.77/0.98  --splitting_mode                        input
% 3.77/0.98  --splitting_grd                         true
% 3.77/0.98  --splitting_cvd                         false
% 3.77/0.98  --splitting_cvd_svl                     false
% 3.77/0.98  --splitting_nvd                         32
% 3.77/0.98  --sub_typing                            true
% 3.77/0.98  --prep_gs_sim                           true
% 3.77/0.98  --prep_unflatten                        true
% 3.77/0.98  --prep_res_sim                          true
% 3.77/0.98  --prep_upred                            true
% 3.77/0.98  --prep_sem_filter                       exhaustive
% 3.77/0.98  --prep_sem_filter_out                   false
% 3.77/0.98  --pred_elim                             true
% 3.77/0.98  --res_sim_input                         true
% 3.77/0.98  --eq_ax_congr_red                       true
% 3.77/0.98  --pure_diseq_elim                       true
% 3.77/0.98  --brand_transform                       false
% 3.77/0.98  --non_eq_to_eq                          false
% 3.77/0.98  --prep_def_merge                        true
% 3.77/0.98  --prep_def_merge_prop_impl              false
% 3.77/0.98  --prep_def_merge_mbd                    true
% 3.77/0.98  --prep_def_merge_tr_red                 false
% 3.77/0.98  --prep_def_merge_tr_cl                  false
% 3.77/0.98  --smt_preprocessing                     true
% 3.77/0.98  --smt_ac_axioms                         fast
% 3.77/0.98  --preprocessed_out                      false
% 3.77/0.98  --preprocessed_stats                    false
% 3.77/0.98  
% 3.77/0.98  ------ Abstraction refinement Options
% 3.77/0.98  
% 3.77/0.98  --abstr_ref                             []
% 3.77/0.98  --abstr_ref_prep                        false
% 3.77/0.98  --abstr_ref_until_sat                   false
% 3.77/0.98  --abstr_ref_sig_restrict                funpre
% 3.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.98  --abstr_ref_under                       []
% 3.77/0.98  
% 3.77/0.98  ------ SAT Options
% 3.77/0.98  
% 3.77/0.98  --sat_mode                              false
% 3.77/0.98  --sat_fm_restart_options                ""
% 3.77/0.98  --sat_gr_def                            false
% 3.77/0.98  --sat_epr_types                         true
% 3.77/0.98  --sat_non_cyclic_types                  false
% 3.77/0.98  --sat_finite_models                     false
% 3.77/0.98  --sat_fm_lemmas                         false
% 3.77/0.98  --sat_fm_prep                           false
% 3.77/0.98  --sat_fm_uc_incr                        true
% 3.77/0.98  --sat_out_model                         small
% 3.77/0.98  --sat_out_clauses                       false
% 3.77/0.98  
% 3.77/0.98  ------ QBF Options
% 3.77/0.98  
% 3.77/0.98  --qbf_mode                              false
% 3.77/0.98  --qbf_elim_univ                         false
% 3.77/0.98  --qbf_dom_inst                          none
% 3.77/0.98  --qbf_dom_pre_inst                      false
% 3.77/0.98  --qbf_sk_in                             false
% 3.77/0.98  --qbf_pred_elim                         true
% 3.77/0.98  --qbf_split                             512
% 3.77/0.98  
% 3.77/0.98  ------ BMC1 Options
% 3.77/0.98  
% 3.77/0.98  --bmc1_incremental                      false
% 3.77/0.98  --bmc1_axioms                           reachable_all
% 3.77/0.98  --bmc1_min_bound                        0
% 3.77/0.98  --bmc1_max_bound                        -1
% 3.77/0.98  --bmc1_max_bound_default                -1
% 3.77/0.98  --bmc1_symbol_reachability              true
% 3.77/0.98  --bmc1_property_lemmas                  false
% 3.77/0.98  --bmc1_k_induction                      false
% 3.77/0.98  --bmc1_non_equiv_states                 false
% 3.77/0.98  --bmc1_deadlock                         false
% 3.77/0.98  --bmc1_ucm                              false
% 3.77/0.98  --bmc1_add_unsat_core                   none
% 3.77/0.98  --bmc1_unsat_core_children              false
% 3.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.98  --bmc1_out_stat                         full
% 3.77/0.98  --bmc1_ground_init                      false
% 3.77/0.98  --bmc1_pre_inst_next_state              false
% 3.77/0.98  --bmc1_pre_inst_state                   false
% 3.77/0.98  --bmc1_pre_inst_reach_state             false
% 3.77/0.98  --bmc1_out_unsat_core                   false
% 3.77/0.98  --bmc1_aig_witness_out                  false
% 3.77/0.98  --bmc1_verbose                          false
% 3.77/0.98  --bmc1_dump_clauses_tptp                false
% 3.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.98  --bmc1_dump_file                        -
% 3.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.98  --bmc1_ucm_extend_mode                  1
% 3.77/0.98  --bmc1_ucm_init_mode                    2
% 3.77/0.98  --bmc1_ucm_cone_mode                    none
% 3.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.98  --bmc1_ucm_relax_model                  4
% 3.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.98  --bmc1_ucm_layered_model                none
% 3.77/0.98  --bmc1_ucm_max_lemma_size               10
% 3.77/0.98  
% 3.77/0.98  ------ AIG Options
% 3.77/0.98  
% 3.77/0.98  --aig_mode                              false
% 3.77/0.98  
% 3.77/0.98  ------ Instantiation Options
% 3.77/0.98  
% 3.77/0.98  --instantiation_flag                    true
% 3.77/0.98  --inst_sos_flag                         true
% 3.77/0.98  --inst_sos_phase                        true
% 3.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.98  --inst_lit_sel_side                     num_symb
% 3.77/0.98  --inst_solver_per_active                1400
% 3.77/0.98  --inst_solver_calls_frac                1.
% 3.77/0.98  --inst_passive_queue_type               priority_queues
% 3.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.98  --inst_passive_queues_freq              [25;2]
% 3.77/0.98  --inst_dismatching                      true
% 3.77/0.98  --inst_eager_unprocessed_to_passive     true
% 3.77/0.98  --inst_prop_sim_given                   true
% 3.77/0.98  --inst_prop_sim_new                     false
% 3.77/0.98  --inst_subs_new                         false
% 3.77/0.98  --inst_eq_res_simp                      false
% 3.77/0.98  --inst_subs_given                       false
% 3.77/0.98  --inst_orphan_elimination               true
% 3.77/0.98  --inst_learning_loop_flag               true
% 3.77/0.98  --inst_learning_start                   3000
% 3.77/0.98  --inst_learning_factor                  2
% 3.77/0.98  --inst_start_prop_sim_after_learn       3
% 3.77/0.98  --inst_sel_renew                        solver
% 3.77/0.98  --inst_lit_activity_flag                true
% 3.77/0.98  --inst_restr_to_given                   false
% 3.77/0.98  --inst_activity_threshold               500
% 3.77/0.98  --inst_out_proof                        true
% 3.77/0.98  
% 3.77/0.98  ------ Resolution Options
% 3.77/0.98  
% 3.77/0.98  --resolution_flag                       true
% 3.77/0.98  --res_lit_sel                           adaptive
% 3.77/0.98  --res_lit_sel_side                      none
% 3.77/0.98  --res_ordering                          kbo
% 3.77/0.98  --res_to_prop_solver                    active
% 3.77/0.98  --res_prop_simpl_new                    false
% 3.77/0.98  --res_prop_simpl_given                  true
% 3.77/0.98  --res_passive_queue_type                priority_queues
% 3.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.98  --res_passive_queues_freq               [15;5]
% 3.77/0.98  --res_forward_subs                      full
% 3.77/0.98  --res_backward_subs                     full
% 3.77/0.98  --res_forward_subs_resolution           true
% 3.77/0.98  --res_backward_subs_resolution          true
% 3.77/0.98  --res_orphan_elimination                true
% 3.77/0.98  --res_time_limit                        2.
% 3.77/0.98  --res_out_proof                         true
% 3.77/0.98  
% 3.77/0.98  ------ Superposition Options
% 3.77/0.98  
% 3.77/0.98  --superposition_flag                    true
% 3.77/0.98  --sup_passive_queue_type                priority_queues
% 3.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.98  --demod_completeness_check              fast
% 3.77/0.98  --demod_use_ground                      true
% 3.77/0.98  --sup_to_prop_solver                    passive
% 3.77/0.98  --sup_prop_simpl_new                    true
% 3.77/0.98  --sup_prop_simpl_given                  true
% 3.77/0.98  --sup_fun_splitting                     true
% 3.77/0.98  --sup_smt_interval                      50000
% 3.77/0.98  
% 3.77/0.98  ------ Superposition Simplification Setup
% 3.77/0.98  
% 3.77/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.77/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.77/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.77/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.77/0.98  --sup_immed_triv                        [TrivRules]
% 3.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.98  --sup_immed_bw_main                     []
% 3.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.98  --sup_input_bw                          []
% 3.77/0.98  
% 3.77/0.98  ------ Combination Options
% 3.77/0.98  
% 3.77/0.98  --comb_res_mult                         3
% 3.77/0.98  --comb_sup_mult                         2
% 3.77/0.98  --comb_inst_mult                        10
% 3.77/0.98  
% 3.77/0.98  ------ Debug Options
% 3.77/0.98  
% 3.77/0.98  --dbg_backtrace                         false
% 3.77/0.98  --dbg_dump_prop_clauses                 false
% 3.77/0.98  --dbg_dump_prop_clauses_file            -
% 3.77/0.98  --dbg_out_stat                          false
% 3.77/0.98  ------ Parsing...
% 3.77/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/0.98  ------ Proving...
% 3.77/0.98  ------ Problem Properties 
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  clauses                                 12
% 3.77/0.98  conjectures                             1
% 3.77/0.98  EPR                                     0
% 3.77/0.98  Horn                                    11
% 3.77/0.98  unary                                   10
% 3.77/0.98  binary                                  2
% 3.77/0.98  lits                                    14
% 3.77/0.98  lits eq                                 12
% 3.77/0.98  fd_pure                                 0
% 3.77/0.98  fd_pseudo                               0
% 3.77/0.98  fd_cond                                 0
% 3.77/0.98  fd_pseudo_cond                          1
% 3.77/0.98  AC symbols                              1
% 3.77/0.98  
% 3.77/0.98  ------ Schedule dynamic 5 is on 
% 3.77/0.98  
% 3.77/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  ------ 
% 3.77/0.98  Current options:
% 3.77/0.98  ------ 
% 3.77/0.98  
% 3.77/0.98  ------ Input Options
% 3.77/0.98  
% 3.77/0.98  --out_options                           all
% 3.77/0.98  --tptp_safe_out                         true
% 3.77/0.98  --problem_path                          ""
% 3.77/0.98  --include_path                          ""
% 3.77/0.98  --clausifier                            res/vclausify_rel
% 3.77/0.98  --clausifier_options                    ""
% 3.77/0.98  --stdin                                 false
% 3.77/0.98  --stats_out                             all
% 3.77/0.98  
% 3.77/0.98  ------ General Options
% 3.77/0.98  
% 3.77/0.98  --fof                                   false
% 3.77/0.98  --time_out_real                         305.
% 3.77/0.98  --time_out_virtual                      -1.
% 3.77/0.98  --symbol_type_check                     false
% 3.77/0.98  --clausify_out                          false
% 3.77/0.98  --sig_cnt_out                           false
% 3.77/0.98  --trig_cnt_out                          false
% 3.77/0.98  --trig_cnt_out_tolerance                1.
% 3.77/0.98  --trig_cnt_out_sk_spl                   false
% 3.77/0.98  --abstr_cl_out                          false
% 3.77/0.98  
% 3.77/0.98  ------ Global Options
% 3.77/0.98  
% 3.77/0.98  --schedule                              default
% 3.77/0.98  --add_important_lit                     false
% 3.77/0.98  --prop_solver_per_cl                    1000
% 3.77/0.98  --min_unsat_core                        false
% 3.77/0.98  --soft_assumptions                      false
% 3.77/0.98  --soft_lemma_size                       3
% 3.77/0.98  --prop_impl_unit_size                   0
% 3.77/0.98  --prop_impl_unit                        []
% 3.77/0.98  --share_sel_clauses                     true
% 3.77/0.98  --reset_solvers                         false
% 3.77/0.98  --bc_imp_inh                            [conj_cone]
% 3.77/0.98  --conj_cone_tolerance                   3.
% 3.77/0.98  --extra_neg_conj                        none
% 3.77/0.98  --large_theory_mode                     true
% 3.77/0.98  --prolific_symb_bound                   200
% 3.77/0.98  --lt_threshold                          2000
% 3.77/0.98  --clause_weak_htbl                      true
% 3.77/0.98  --gc_record_bc_elim                     false
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing Options
% 3.77/0.98  
% 3.77/0.98  --preprocessing_flag                    true
% 3.77/0.98  --time_out_prep_mult                    0.1
% 3.77/0.98  --splitting_mode                        input
% 3.77/0.98  --splitting_grd                         true
% 3.77/0.98  --splitting_cvd                         false
% 3.77/0.98  --splitting_cvd_svl                     false
% 3.77/0.98  --splitting_nvd                         32
% 3.77/0.98  --sub_typing                            true
% 3.77/0.98  --prep_gs_sim                           true
% 3.77/0.98  --prep_unflatten                        true
% 3.77/0.98  --prep_res_sim                          true
% 3.77/0.98  --prep_upred                            true
% 3.77/0.98  --prep_sem_filter                       exhaustive
% 3.77/0.98  --prep_sem_filter_out                   false
% 3.77/0.98  --pred_elim                             true
% 3.77/0.98  --res_sim_input                         true
% 3.77/0.98  --eq_ax_congr_red                       true
% 3.77/0.98  --pure_diseq_elim                       true
% 3.77/0.98  --brand_transform                       false
% 3.77/0.98  --non_eq_to_eq                          false
% 3.77/0.98  --prep_def_merge                        true
% 3.77/0.98  --prep_def_merge_prop_impl              false
% 3.77/0.98  --prep_def_merge_mbd                    true
% 3.77/0.98  --prep_def_merge_tr_red                 false
% 3.77/0.98  --prep_def_merge_tr_cl                  false
% 3.77/0.98  --smt_preprocessing                     true
% 3.77/0.98  --smt_ac_axioms                         fast
% 3.77/0.98  --preprocessed_out                      false
% 3.77/0.98  --preprocessed_stats                    false
% 3.77/0.98  
% 3.77/0.98  ------ Abstraction refinement Options
% 3.77/0.98  
% 3.77/0.98  --abstr_ref                             []
% 3.77/0.98  --abstr_ref_prep                        false
% 3.77/0.98  --abstr_ref_until_sat                   false
% 3.77/0.98  --abstr_ref_sig_restrict                funpre
% 3.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.98  --abstr_ref_under                       []
% 3.77/0.98  
% 3.77/0.98  ------ SAT Options
% 3.77/0.98  
% 3.77/0.98  --sat_mode                              false
% 3.77/0.98  --sat_fm_restart_options                ""
% 3.77/0.98  --sat_gr_def                            false
% 3.77/0.98  --sat_epr_types                         true
% 3.77/0.98  --sat_non_cyclic_types                  false
% 3.77/0.98  --sat_finite_models                     false
% 3.77/0.98  --sat_fm_lemmas                         false
% 3.77/0.98  --sat_fm_prep                           false
% 3.77/0.98  --sat_fm_uc_incr                        true
% 3.77/0.98  --sat_out_model                         small
% 3.77/0.98  --sat_out_clauses                       false
% 3.77/0.98  
% 3.77/0.98  ------ QBF Options
% 3.77/0.98  
% 3.77/0.98  --qbf_mode                              false
% 3.77/0.98  --qbf_elim_univ                         false
% 3.77/0.98  --qbf_dom_inst                          none
% 3.77/0.98  --qbf_dom_pre_inst                      false
% 3.77/0.98  --qbf_sk_in                             false
% 3.77/0.98  --qbf_pred_elim                         true
% 3.77/0.98  --qbf_split                             512
% 3.77/0.98  
% 3.77/0.98  ------ BMC1 Options
% 3.77/0.98  
% 3.77/0.98  --bmc1_incremental                      false
% 3.77/0.98  --bmc1_axioms                           reachable_all
% 3.77/0.98  --bmc1_min_bound                        0
% 3.77/0.98  --bmc1_max_bound                        -1
% 3.77/0.98  --bmc1_max_bound_default                -1
% 3.77/0.98  --bmc1_symbol_reachability              true
% 3.77/0.98  --bmc1_property_lemmas                  false
% 3.77/0.98  --bmc1_k_induction                      false
% 3.77/0.98  --bmc1_non_equiv_states                 false
% 3.77/0.98  --bmc1_deadlock                         false
% 3.77/0.98  --bmc1_ucm                              false
% 3.77/0.98  --bmc1_add_unsat_core                   none
% 3.77/0.98  --bmc1_unsat_core_children              false
% 3.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.98  --bmc1_out_stat                         full
% 3.77/0.98  --bmc1_ground_init                      false
% 3.77/0.98  --bmc1_pre_inst_next_state              false
% 3.77/0.98  --bmc1_pre_inst_state                   false
% 3.77/0.98  --bmc1_pre_inst_reach_state             false
% 3.77/0.98  --bmc1_out_unsat_core                   false
% 3.77/0.98  --bmc1_aig_witness_out                  false
% 3.77/0.98  --bmc1_verbose                          false
% 3.77/0.98  --bmc1_dump_clauses_tptp                false
% 3.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.98  --bmc1_dump_file                        -
% 3.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.98  --bmc1_ucm_extend_mode                  1
% 3.77/0.98  --bmc1_ucm_init_mode                    2
% 3.77/0.98  --bmc1_ucm_cone_mode                    none
% 3.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.98  --bmc1_ucm_relax_model                  4
% 3.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.98  --bmc1_ucm_layered_model                none
% 3.77/0.98  --bmc1_ucm_max_lemma_size               10
% 3.77/0.98  
% 3.77/0.98  ------ AIG Options
% 3.77/0.98  
% 3.77/0.98  --aig_mode                              false
% 3.77/0.98  
% 3.77/0.98  ------ Instantiation Options
% 3.77/0.98  
% 3.77/0.98  --instantiation_flag                    true
% 3.77/0.98  --inst_sos_flag                         true
% 3.77/0.98  --inst_sos_phase                        true
% 3.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.98  --inst_lit_sel_side                     none
% 3.77/0.98  --inst_solver_per_active                1400
% 3.77/0.98  --inst_solver_calls_frac                1.
% 3.77/0.98  --inst_passive_queue_type               priority_queues
% 3.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.98  --inst_passive_queues_freq              [25;2]
% 3.77/0.98  --inst_dismatching                      true
% 3.77/0.98  --inst_eager_unprocessed_to_passive     true
% 3.77/0.98  --inst_prop_sim_given                   true
% 3.77/0.98  --inst_prop_sim_new                     false
% 3.77/0.98  --inst_subs_new                         false
% 3.77/0.98  --inst_eq_res_simp                      false
% 3.77/0.98  --inst_subs_given                       false
% 3.77/0.98  --inst_orphan_elimination               true
% 3.77/0.98  --inst_learning_loop_flag               true
% 3.77/0.98  --inst_learning_start                   3000
% 3.77/0.98  --inst_learning_factor                  2
% 3.77/0.98  --inst_start_prop_sim_after_learn       3
% 3.77/0.98  --inst_sel_renew                        solver
% 3.77/0.98  --inst_lit_activity_flag                true
% 3.77/0.98  --inst_restr_to_given                   false
% 3.77/0.98  --inst_activity_threshold               500
% 3.77/0.98  --inst_out_proof                        true
% 3.77/0.98  
% 3.77/0.98  ------ Resolution Options
% 3.77/0.98  
% 3.77/0.98  --resolution_flag                       false
% 3.77/0.98  --res_lit_sel                           adaptive
% 3.77/0.98  --res_lit_sel_side                      none
% 3.77/0.98  --res_ordering                          kbo
% 3.77/0.98  --res_to_prop_solver                    active
% 3.77/0.98  --res_prop_simpl_new                    false
% 3.77/0.98  --res_prop_simpl_given                  true
% 3.77/0.98  --res_passive_queue_type                priority_queues
% 3.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.98  --res_passive_queues_freq               [15;5]
% 3.77/0.98  --res_forward_subs                      full
% 3.77/0.98  --res_backward_subs                     full
% 3.77/0.98  --res_forward_subs_resolution           true
% 3.77/0.98  --res_backward_subs_resolution          true
% 3.77/0.98  --res_orphan_elimination                true
% 3.77/0.98  --res_time_limit                        2.
% 3.77/0.98  --res_out_proof                         true
% 3.77/0.98  
% 3.77/0.98  ------ Superposition Options
% 3.77/0.98  
% 3.77/0.98  --superposition_flag                    true
% 3.77/0.98  --sup_passive_queue_type                priority_queues
% 3.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.98  --demod_completeness_check              fast
% 3.77/0.98  --demod_use_ground                      true
% 3.77/0.98  --sup_to_prop_solver                    passive
% 3.77/0.98  --sup_prop_simpl_new                    true
% 3.77/0.98  --sup_prop_simpl_given                  true
% 3.77/0.98  --sup_fun_splitting                     true
% 3.77/0.98  --sup_smt_interval                      50000
% 3.77/0.98  
% 3.77/0.98  ------ Superposition Simplification Setup
% 3.77/0.98  
% 3.77/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.77/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.77/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.77/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.77/0.98  --sup_immed_triv                        [TrivRules]
% 3.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.98  --sup_immed_bw_main                     []
% 3.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.98  --sup_input_bw                          []
% 3.77/0.98  
% 3.77/0.98  ------ Combination Options
% 3.77/0.98  
% 3.77/0.98  --comb_res_mult                         3
% 3.77/0.98  --comb_sup_mult                         2
% 3.77/0.98  --comb_inst_mult                        10
% 3.77/0.98  
% 3.77/0.98  ------ Debug Options
% 3.77/0.98  
% 3.77/0.98  --dbg_backtrace                         false
% 3.77/0.98  --dbg_dump_prop_clauses                 false
% 3.77/0.98  --dbg_dump_prop_clauses_file            -
% 3.77/0.98  --dbg_out_stat                          false
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  ------ Proving...
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  % SZS status Theorem for theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  fof(f8,axiom,(
% 3.77/0.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f35,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f8])).
% 3.77/0.98  
% 3.77/0.98  fof(f1,axiom,(
% 3.77/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f28,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f1])).
% 3.77/0.98  
% 3.77/0.98  fof(f20,conjecture,(
% 3.77/0.98    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f21,negated_conjecture,(
% 3.77/0.98    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.77/0.98    inference(negated_conjecture,[],[f20])).
% 3.77/0.98  
% 3.77/0.98  fof(f24,plain,(
% 3.77/0.98    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 3.77/0.98    inference(ennf_transformation,[],[f21])).
% 3.77/0.98  
% 3.77/0.98  fof(f26,plain,(
% 3.77/0.98    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 3.77/0.98    introduced(choice_axiom,[])).
% 3.77/0.98  
% 3.77/0.98  fof(f27,plain,(
% 3.77/0.98    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 3.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26])).
% 3.77/0.98  
% 3.77/0.98  fof(f48,plain,(
% 3.77/0.98    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 3.77/0.98    inference(cnf_transformation,[],[f27])).
% 3.77/0.98  
% 3.77/0.98  fof(f10,axiom,(
% 3.77/0.98    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f37,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f10])).
% 3.77/0.98  
% 3.77/0.98  fof(f11,axiom,(
% 3.77/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f38,plain,(
% 3.77/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f11])).
% 3.77/0.98  
% 3.77/0.98  fof(f12,axiom,(
% 3.77/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f39,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f12])).
% 3.77/0.98  
% 3.77/0.98  fof(f13,axiom,(
% 3.77/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f40,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f13])).
% 3.77/0.98  
% 3.77/0.98  fof(f14,axiom,(
% 3.77/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f41,plain,(
% 3.77/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f14])).
% 3.77/0.98  
% 3.77/0.98  fof(f15,axiom,(
% 3.77/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f42,plain,(
% 3.77/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f15])).
% 3.77/0.98  
% 3.77/0.98  fof(f16,axiom,(
% 3.77/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f43,plain,(
% 3.77/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f16])).
% 3.77/0.98  
% 3.77/0.98  fof(f17,axiom,(
% 3.77/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f44,plain,(
% 3.77/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f17])).
% 3.77/0.98  
% 3.77/0.98  fof(f49,plain,(
% 3.77/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f43,f44])).
% 3.77/0.98  
% 3.77/0.98  fof(f50,plain,(
% 3.77/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f42,f49])).
% 3.77/0.98  
% 3.77/0.98  fof(f51,plain,(
% 3.77/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f41,f50])).
% 3.77/0.98  
% 3.77/0.98  fof(f52,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f40,f51])).
% 3.77/0.98  
% 3.77/0.98  fof(f53,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f39,f52])).
% 3.77/0.98  
% 3.77/0.98  fof(f54,plain,(
% 3.77/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f38,f53])).
% 3.77/0.98  
% 3.77/0.98  fof(f59,plain,(
% 3.77/0.98    k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0),
% 3.77/0.98    inference(definition_unfolding,[],[f48,f37,f54])).
% 3.77/0.98  
% 3.77/0.98  fof(f2,axiom,(
% 3.77/0.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f29,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f2])).
% 3.77/0.98  
% 3.77/0.98  fof(f7,axiom,(
% 3.77/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f34,plain,(
% 3.77/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.77/0.98    inference(cnf_transformation,[],[f7])).
% 3.77/0.98  
% 3.77/0.98  fof(f9,axiom,(
% 3.77/0.98    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f36,plain,(
% 3.77/0.98    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.77/0.98    inference(cnf_transformation,[],[f9])).
% 3.77/0.98  
% 3.77/0.98  fof(f6,axiom,(
% 3.77/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f33,plain,(
% 3.77/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f6])).
% 3.77/0.98  
% 3.77/0.98  fof(f4,axiom,(
% 3.77/0.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f31,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f4])).
% 3.77/0.98  
% 3.77/0.98  fof(f55,plain,(
% 3.77/0.98    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f33,f31])).
% 3.77/0.98  
% 3.77/0.98  fof(f5,axiom,(
% 3.77/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f23,plain,(
% 3.77/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.77/0.98    inference(ennf_transformation,[],[f5])).
% 3.77/0.98  
% 3.77/0.98  fof(f32,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f23])).
% 3.77/0.98  
% 3.77/0.98  fof(f18,axiom,(
% 3.77/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f45,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.77/0.98    inference(cnf_transformation,[],[f18])).
% 3.77/0.98  
% 3.77/0.98  fof(f56,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.77/0.98    inference(definition_unfolding,[],[f45,f37,f53])).
% 3.77/0.98  
% 3.77/0.98  fof(f3,axiom,(
% 3.77/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f22,plain,(
% 3.77/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.77/0.98    inference(rectify,[],[f3])).
% 3.77/0.98  
% 3.77/0.98  fof(f30,plain,(
% 3.77/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.77/0.98    inference(cnf_transformation,[],[f22])).
% 3.77/0.98  
% 3.77/0.98  fof(f19,axiom,(
% 3.77/0.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f25,plain,(
% 3.77/0.98    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.77/0.98    inference(nnf_transformation,[],[f19])).
% 3.77/0.98  
% 3.77/0.98  fof(f46,plain,(
% 3.77/0.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f25])).
% 3.77/0.98  
% 3.77/0.98  fof(f58,plain,(
% 3.77/0.98    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f46,f31,f54,f54,f54])).
% 3.77/0.98  
% 3.77/0.98  fof(f60,plain,(
% 3.77/0.98    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.77/0.98    inference(equality_resolution,[],[f58])).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.77/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_0,plain,
% 3.77/0.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_11,negated_conjecture,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
% 3.77/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1,plain,
% 3.77/0.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_57,negated_conjecture,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k1_xboole_0 ),
% 3.77/0.98      inference(theory_normalisation,[status(thm)],[c_11,c_6,c_1]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_222,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_0,c_57]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_426,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_222,c_6]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_5,plain,
% 3.77/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.77/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_309,plain,
% 3.77/0.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_433,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = X0 ),
% 3.77/0.98      inference(light_normalisation,[status(thm)],[c_426,c_309]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_600,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) = X0 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_6,c_433]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_7,plain,
% 3.77/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.77/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_601,plain,
% 3.77/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_7,c_433]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_605,plain,
% 3.77/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_601,c_5]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_609,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = X0 ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_605,c_433]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_713,plain,
% 3.77/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(sK1,X0) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_600,c_609]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_611,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(X0,sK1)) = X0 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1,c_609]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_718,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(X0,X1) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_6,c_611]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_617,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,X0),X1)) = k5_xboole_0(X0,X1) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_609,c_6]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_429,plain,
% 3.77/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1339,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X0,sK1)) = k1_xboole_0 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_617,c_429]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2160,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(sK1,X0)) = k1_xboole_0 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1339,c_1]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2583,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),sK1),X0) = k1_xboole_0 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_609,c_2160]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2985,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),sK1),k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k1_xboole_0 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_718,c_2583]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_121,plain,
% 3.77/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_120,plain,
% 3.77/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3924,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(sK1,X1)) = k5_xboole_0(X1,X0) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_609,c_120]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4499,plain,
% 3.77/0.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0)) = k5_xboole_0(X0,sK1) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_7,c_3924]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_5702,plain,
% 3.77/0.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),sK1) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_121,c_4499]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_119,plain,
% 3.77/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4738,plain,
% 3.77/0.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,sK1)) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_4499,c_119]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_5755,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),sK1) = k5_xboole_0(X1,k5_xboole_0(X0,sK1)) ),
% 3.77/0.98      inference(light_normalisation,[status(thm)],[c_5702,c_4738]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8636,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK1)),k5_xboole_0(X1,k5_xboole_0(X0,sK1))) = k1_xboole_0 ),
% 3.77/0.98      inference(light_normalisation,[status(thm)],[c_2985,c_2985,c_5755]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8661,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k1_xboole_0 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_713,c_8636]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8700,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),k5_xboole_0(sK1,sK1)) = k1_xboole_0 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_713,c_8636]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_785,plain,
% 3.77/0.98      ( k5_xboole_0(X0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_7,c_617]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_805,plain,
% 3.77/0.98      ( k5_xboole_0(X0,k5_xboole_0(sK1,X0)) = sK1 ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_785,c_5]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1003,plain,
% 3.77/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,sK1)) = sK1 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1,c_805]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1832,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1003,c_713]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1838,plain,
% 3.77/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_1832,c_611]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1827,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_7,c_713]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1841,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_1827,c_5]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4,plain,
% 3.77/0.98      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_113,plain,
% 3.77/0.98      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_463,plain,
% 3.77/0.98      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_0,c_113]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1396,plain,
% 3.77/0.98      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_605,c_463]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3,plain,
% 3.77/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.77/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_114,plain,
% 3.77/0.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_7632,plain,
% 3.77/0.98      ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK1 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1396,c_114]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8804,plain,
% 3.77/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1)) = k1_xboole_0 ),
% 3.77/0.98      inference(light_normalisation,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_8700,c_1838,c_1841,c_7632]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2846,plain,
% 3.77/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_7,c_119]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2930,plain,
% 3.77/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_2846,c_5]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4215,plain,
% 3.77/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK1,X0))) = k5_xboole_0(sK1,X1) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_2930,c_617]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6813,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,X0)) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_4215,c_713]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6854,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,X0)) ),
% 3.77/0.98      inference(light_normalisation,[status(thm)],[c_6813,c_1841]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8805,plain,
% 3.77/0.98      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_8804,c_5,c_7,c_6854]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8830,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k5_xboole_0(k1_xboole_0,sK1))) = k1_xboole_0 ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_8661,c_8805]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_5623,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),X1),k5_xboole_0(X2,sK1)) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_617,c_121]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_781,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(X1,X0) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1,c_617]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3240,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,X1)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_781,c_6]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2907,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_119,c_617]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2923,plain,
% 3.77/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.77/0.98      inference(light_normalisation,[status(thm)],[c_2907,c_6]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3261,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 3.77/0.98      inference(light_normalisation,[status(thm)],[c_3240,c_2923]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_5772,plain,
% 3.77/0.98      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X1,k5_xboole_0(X2,sK1))) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_5623,c_3261]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8,plain,
% 3.77/0.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 3.77/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_58,plain,
% 3.77/0.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 3.77/0.98      inference(theory_normalisation,[status(thm)],[c_8,c_6,c_1]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_415,plain,
% 3.77/0.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_0,c_58]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3912,plain,
% 3.77/0.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_5,c_120]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_7886,plain,
% 3.77/0.98      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_415,c_3912]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6339,plain,
% 3.77/0.98      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3912,c_58]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2,plain,
% 3.77/0.98      ( k3_xboole_0(X0,X0) = X0 ),
% 3.77/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_465,plain,
% 3.77/0.98      ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_2,c_113]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_466,plain,
% 3.77/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.77/0.98      inference(light_normalisation,[status(thm)],[c_465,c_7]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_897,plain,
% 3.77/0.98      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_466,c_114]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6358,plain,
% 3.77/0.98      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.77/0.98      inference(light_normalisation,[status(thm)],[c_6339,c_309,c_897]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_7909,plain,
% 3.77/0.98      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0 ),
% 3.77/0.98      inference(light_normalisation,[status(thm)],[c_7886,c_6358]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8831,plain,
% 3.77/0.98      ( sK1 = k1_xboole_0 ),
% 3.77/0.98      inference(demodulation,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_8830,c_7,c_309,c_5772,c_7909]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8874,plain,
% 3.77/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_8831,c_605]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8882,plain,
% 3.77/0.98      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_8874,c_5,c_897]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_10,plain,
% 3.77/0.98      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_115,plain,
% 3.77/0.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_10,c_2,c_7]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_117,plain,
% 3.77/0.98      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_xboole_0 ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_115]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(contradiction,plain,
% 3.77/0.98      ( $false ),
% 3.77/0.98      inference(minisat,[status(thm)],[c_8882,c_117]) ).
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  ------                               Statistics
% 3.77/0.98  
% 3.77/0.98  ------ General
% 3.77/0.98  
% 3.77/0.98  abstr_ref_over_cycles:                  0
% 3.77/0.98  abstr_ref_under_cycles:                 0
% 3.77/0.98  gc_basic_clause_elim:                   0
% 3.77/0.98  forced_gc_time:                         0
% 3.77/0.98  parsing_time:                           0.008
% 3.77/0.98  unif_index_cands_time:                  0.
% 3.77/0.98  unif_index_add_time:                    0.
% 3.77/0.98  orderings_time:                         0.
% 3.77/0.98  out_proof_time:                         0.01
% 3.77/0.98  total_time:                             0.426
% 3.77/0.98  num_of_symbols:                         39
% 3.77/0.98  num_of_terms:                           13591
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing
% 3.77/0.98  
% 3.77/0.98  num_of_splits:                          0
% 3.77/0.98  num_of_split_atoms:                     0
% 3.77/0.98  num_of_reused_defs:                     0
% 3.77/0.98  num_eq_ax_congr_red:                    2
% 3.77/0.98  num_of_sem_filtered_clauses:            1
% 3.77/0.98  num_of_subtypes:                        0
% 3.77/0.98  monotx_restored_types:                  0
% 3.77/0.98  sat_num_of_epr_types:                   0
% 3.77/0.98  sat_num_of_non_cyclic_types:            0
% 3.77/0.98  sat_guarded_non_collapsed_types:        0
% 3.77/0.98  num_pure_diseq_elim:                    0
% 3.77/0.98  simp_replaced_by:                       0
% 3.77/0.98  res_preprocessed:                       51
% 3.77/0.98  prep_upred:                             0
% 3.77/0.98  prep_unflattend:                        2
% 3.77/0.98  smt_new_axioms:                         0
% 3.77/0.98  pred_elim_cands:                        1
% 3.77/0.98  pred_elim:                              0
% 3.77/0.98  pred_elim_cl:                           0
% 3.77/0.98  pred_elim_cycles:                       1
% 3.77/0.98  merged_defs:                            0
% 3.77/0.98  merged_defs_ncl:                        0
% 3.77/0.98  bin_hyper_res:                          0
% 3.77/0.98  prep_cycles:                            3
% 3.77/0.98  pred_elim_time:                         0.
% 3.77/0.98  splitting_time:                         0.
% 3.77/0.98  sem_filter_time:                        0.
% 3.77/0.98  monotx_time:                            0.
% 3.77/0.98  subtype_inf_time:                       0.
% 3.77/0.98  
% 3.77/0.98  ------ Problem properties
% 3.77/0.98  
% 3.77/0.98  clauses:                                12
% 3.77/0.98  conjectures:                            1
% 3.77/0.98  epr:                                    0
% 3.77/0.98  horn:                                   11
% 3.77/0.98  ground:                                 1
% 3.77/0.98  unary:                                  10
% 3.77/0.98  binary:                                 2
% 3.77/0.98  lits:                                   14
% 3.77/0.98  lits_eq:                                12
% 3.77/0.98  fd_pure:                                0
% 3.77/0.98  fd_pseudo:                              0
% 3.77/0.98  fd_cond:                                0
% 3.77/0.98  fd_pseudo_cond:                         1
% 3.77/0.98  ac_symbols:                             1
% 3.77/0.98  
% 3.77/0.98  ------ Propositional Solver
% 3.77/0.98  
% 3.77/0.98  prop_solver_calls:                      28
% 3.77/0.98  prop_fast_solver_calls:                 274
% 3.77/0.98  smt_solver_calls:                       0
% 3.77/0.98  smt_fast_solver_calls:                  0
% 3.77/0.98  prop_num_of_clauses:                    2466
% 3.77/0.98  prop_preprocess_simplified:             4971
% 3.77/0.98  prop_fo_subsumed:                       0
% 3.77/0.98  prop_solver_time:                       0.
% 3.77/0.98  smt_solver_time:                        0.
% 3.77/0.98  smt_fast_solver_time:                   0.
% 3.77/0.98  prop_fast_solver_time:                  0.
% 3.77/0.98  prop_unsat_core_time:                   0.
% 3.77/0.98  
% 3.77/0.98  ------ QBF
% 3.77/0.98  
% 3.77/0.98  qbf_q_res:                              0
% 3.77/0.98  qbf_num_tautologies:                    0
% 3.77/0.98  qbf_prep_cycles:                        0
% 3.77/0.98  
% 3.77/0.98  ------ BMC1
% 3.77/0.98  
% 3.77/0.98  bmc1_current_bound:                     -1
% 3.77/0.98  bmc1_last_solved_bound:                 -1
% 3.77/0.98  bmc1_unsat_core_size:                   -1
% 3.77/0.98  bmc1_unsat_core_parents_size:           -1
% 3.77/0.98  bmc1_merge_next_fun:                    0
% 3.77/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.77/0.98  
% 3.77/0.98  ------ Instantiation
% 3.77/0.98  
% 3.77/0.98  inst_num_of_clauses:                    1015
% 3.77/0.98  inst_num_in_passive:                    485
% 3.77/0.98  inst_num_in_active:                     190
% 3.77/0.98  inst_num_in_unprocessed:                342
% 3.77/0.98  inst_num_of_loops:                      340
% 3.77/0.98  inst_num_of_learning_restarts:          0
% 3.77/0.98  inst_num_moves_active_passive:          144
% 3.77/0.98  inst_lit_activity:                      0
% 3.77/0.98  inst_lit_activity_moves:                0
% 3.77/0.98  inst_num_tautologies:                   0
% 3.77/0.98  inst_num_prop_implied:                  0
% 3.77/0.98  inst_num_existing_simplified:           0
% 3.77/0.98  inst_num_eq_res_simplified:             0
% 3.77/0.98  inst_num_child_elim:                    0
% 3.77/0.98  inst_num_of_dismatching_blockings:      829
% 3.77/0.98  inst_num_of_non_proper_insts:           1531
% 3.77/0.98  inst_num_of_duplicates:                 0
% 3.77/0.98  inst_inst_num_from_inst_to_res:         0
% 3.77/0.98  inst_dismatching_checking_time:         0.
% 3.77/0.98  
% 3.77/0.98  ------ Resolution
% 3.77/0.98  
% 3.77/0.98  res_num_of_clauses:                     0
% 3.77/0.98  res_num_in_passive:                     0
% 3.77/0.98  res_num_in_active:                      0
% 3.77/0.98  res_num_of_loops:                       54
% 3.77/0.98  res_forward_subset_subsumed:            138
% 3.77/0.98  res_backward_subset_subsumed:           6
% 3.77/0.98  res_forward_subsumed:                   0
% 3.77/0.98  res_backward_subsumed:                  0
% 3.77/0.98  res_forward_subsumption_resolution:     0
% 3.77/0.98  res_backward_subsumption_resolution:    0
% 3.77/0.98  res_clause_to_clause_subsumption:       4497
% 3.77/0.98  res_orphan_elimination:                 0
% 3.77/0.98  res_tautology_del:                      98
% 3.77/0.98  res_num_eq_res_simplified:              0
% 3.77/0.98  res_num_sel_changes:                    0
% 3.77/0.98  res_moves_from_active_to_pass:          0
% 3.77/0.98  
% 3.77/0.98  ------ Superposition
% 3.77/0.98  
% 3.77/0.98  sup_time_total:                         0.
% 3.77/0.98  sup_time_generating:                    0.
% 3.77/0.98  sup_time_sim_full:                      0.
% 3.77/0.98  sup_time_sim_immed:                     0.
% 3.77/0.98  
% 3.77/0.98  sup_num_of_clauses:                     486
% 3.77/0.98  sup_num_in_active:                      21
% 3.77/0.98  sup_num_in_passive:                     465
% 3.77/0.98  sup_num_of_loops:                       67
% 3.77/0.98  sup_fw_superposition:                   1785
% 3.77/0.98  sup_bw_superposition:                   1016
% 3.77/0.98  sup_immediate_simplified:               960
% 3.77/0.98  sup_given_eliminated:                   4
% 3.77/0.98  comparisons_done:                       0
% 3.77/0.98  comparisons_avoided:                    2
% 3.77/0.98  
% 3.77/0.98  ------ Simplifications
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  sim_fw_subset_subsumed:                 0
% 3.77/0.98  sim_bw_subset_subsumed:                 0
% 3.77/0.98  sim_fw_subsumed:                        91
% 3.77/0.98  sim_bw_subsumed:                        5
% 3.77/0.98  sim_fw_subsumption_res:                 0
% 3.77/0.98  sim_bw_subsumption_res:                 0
% 3.77/0.98  sim_tautology_del:                      0
% 3.77/0.98  sim_eq_tautology_del:                   359
% 3.77/0.98  sim_eq_res_simp:                        0
% 3.77/0.98  sim_fw_demodulated:                     682
% 3.77/0.98  sim_bw_demodulated:                     56
% 3.77/0.98  sim_light_normalised:                   448
% 3.77/0.98  sim_joinable_taut:                      85
% 3.77/0.98  sim_joinable_simp:                      0
% 3.77/0.98  sim_ac_normalised:                      0
% 3.77/0.98  sim_smt_subsumption:                    0
% 3.77/0.98  
%------------------------------------------------------------------------------
