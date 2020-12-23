%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:32 EST 2020

% Result     : Timeout 59.66s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  108 (1533 expanded)
%              Number of clauses        :   53 ( 473 expanded)
%              Number of leaves         :   19 ( 416 expanded)
%              Depth                    :   19
%              Number of atoms          :  116 (1667 expanded)
%              Number of equality atoms :  101 (1476 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f48])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f49,f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f28])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f29,f43])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f18])).

fof(f22,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f19])).

fof(f23,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f42,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f42,f43,f49,f48,f48])).

cnf(c_7,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_130,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_132,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_853,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_130,c_132])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_136,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_131,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_448,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_131])).

cnf(c_854,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_448,c_132])).

cnf(c_138,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_1254,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_854,c_138])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_314,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_669,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_136,c_314])).

cnf(c_673,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_669,c_5])).

cnf(c_697,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_673,c_1])).

cnf(c_1259,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1254,c_697])).

cnf(c_1739,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_136,c_1259])).

cnf(c_38239,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X0,k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X0,k1_xboole_0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(superposition,[status(thm)],[c_853,c_1739])).

cnf(c_38659,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X0,k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X0) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(light_normalisation,[status(thm)],[c_38239,c_697])).

cnf(c_1751,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),X0) = k3_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_1259,c_1259])).

cnf(c_1735,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_138,c_1259])).

cnf(c_37220,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(superposition,[status(thm)],[c_853,c_1735])).

cnf(c_37710,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),X0) = k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_37220,c_697])).

cnf(c_37711,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sP0_iProver_split(X0) ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_37710])).

cnf(c_38660,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_38659,c_1751,c_37711])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_163,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_8])).

cnf(c_223104,plain,
    ( k5_xboole_0(k3_xboole_0(sP0_iProver_split(sK0),sP0_iProver_split(sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_xboole_0(sP0_iProver_split(sK0),sP0_iProver_split(sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_38660,c_163])).

cnf(c_137,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_1740,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_137,c_1259])).

cnf(c_39198,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)),k5_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) ),
    inference(superposition,[status(thm)],[c_853,c_1740])).

cnf(c_39706,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X0)),X1),k5_xboole_0(k3_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X0)),X1)),k5_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X0)),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_39198,c_38660])).

cnf(c_866,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_697,c_137])).

cnf(c_1593,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_854,c_866])).

cnf(c_1620,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1593,c_673])).

cnf(c_1253,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X0))) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_854,c_136])).

cnf(c_1260,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X0))) = X1 ),
    inference(demodulation,[status(thm)],[c_1253,c_697])).

cnf(c_1789,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1620,c_1260])).

cnf(c_1809,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1789,c_697])).

cnf(c_1250,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_854,c_137])).

cnf(c_1261,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1250,c_697])).

cnf(c_1972,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1261,c_1])).

cnf(c_2431,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X0),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1972,c_6])).

cnf(c_6620,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k5_xboole_0(X1,X2)) = k5_xboole_0(k3_xboole_0(X0,X0),X2) ),
    inference(superposition,[status(thm)],[c_2431,c_1261])).

cnf(c_39707,plain,
    ( k3_xboole_0(k3_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X0)),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sP0_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_39706,c_697,c_1809,c_6620])).

cnf(c_223105,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_223104,c_1259,c_39707])).

cnf(c_223106,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_223105])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:53:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 59.66/8.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.66/8.01  
% 59.66/8.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.66/8.01  
% 59.66/8.01  ------  iProver source info
% 59.66/8.01  
% 59.66/8.01  git: date: 2020-06-30 10:37:57 +0100
% 59.66/8.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.66/8.01  git: non_committed_changes: false
% 59.66/8.01  git: last_make_outside_of_git: false
% 59.66/8.01  
% 59.66/8.01  ------ 
% 59.66/8.01  
% 59.66/8.01  ------ Input Options
% 59.66/8.01  
% 59.66/8.01  --out_options                           all
% 59.66/8.01  --tptp_safe_out                         true
% 59.66/8.01  --problem_path                          ""
% 59.66/8.01  --include_path                          ""
% 59.66/8.01  --clausifier                            res/vclausify_rel
% 59.66/8.01  --clausifier_options                    ""
% 59.66/8.01  --stdin                                 false
% 59.66/8.01  --stats_out                             all
% 59.66/8.01  
% 59.66/8.01  ------ General Options
% 59.66/8.01  
% 59.66/8.01  --fof                                   false
% 59.66/8.01  --time_out_real                         305.
% 59.66/8.01  --time_out_virtual                      -1.
% 59.66/8.01  --symbol_type_check                     false
% 59.66/8.01  --clausify_out                          false
% 59.66/8.01  --sig_cnt_out                           false
% 59.66/8.01  --trig_cnt_out                          false
% 59.66/8.01  --trig_cnt_out_tolerance                1.
% 59.66/8.01  --trig_cnt_out_sk_spl                   false
% 59.66/8.01  --abstr_cl_out                          false
% 59.66/8.01  
% 59.66/8.01  ------ Global Options
% 59.66/8.01  
% 59.66/8.01  --schedule                              default
% 59.66/8.01  --add_important_lit                     false
% 59.66/8.01  --prop_solver_per_cl                    1000
% 59.66/8.01  --min_unsat_core                        false
% 59.66/8.01  --soft_assumptions                      false
% 59.66/8.01  --soft_lemma_size                       3
% 59.66/8.01  --prop_impl_unit_size                   0
% 59.66/8.01  --prop_impl_unit                        []
% 59.66/8.01  --share_sel_clauses                     true
% 59.66/8.01  --reset_solvers                         false
% 59.66/8.01  --bc_imp_inh                            [conj_cone]
% 59.66/8.01  --conj_cone_tolerance                   3.
% 59.66/8.01  --extra_neg_conj                        none
% 59.66/8.01  --large_theory_mode                     true
% 59.66/8.01  --prolific_symb_bound                   200
% 59.66/8.01  --lt_threshold                          2000
% 59.66/8.01  --clause_weak_htbl                      true
% 59.66/8.01  --gc_record_bc_elim                     false
% 59.66/8.01  
% 59.66/8.01  ------ Preprocessing Options
% 59.66/8.01  
% 59.66/8.01  --preprocessing_flag                    true
% 59.66/8.01  --time_out_prep_mult                    0.1
% 59.66/8.01  --splitting_mode                        input
% 59.66/8.01  --splitting_grd                         true
% 59.66/8.01  --splitting_cvd                         false
% 59.66/8.01  --splitting_cvd_svl                     false
% 59.66/8.01  --splitting_nvd                         32
% 59.66/8.01  --sub_typing                            true
% 59.66/8.01  --prep_gs_sim                           true
% 59.66/8.01  --prep_unflatten                        true
% 59.66/8.01  --prep_res_sim                          true
% 59.66/8.01  --prep_upred                            true
% 59.66/8.01  --prep_sem_filter                       exhaustive
% 59.66/8.01  --prep_sem_filter_out                   false
% 59.66/8.01  --pred_elim                             true
% 59.66/8.01  --res_sim_input                         true
% 59.66/8.01  --eq_ax_congr_red                       true
% 59.66/8.01  --pure_diseq_elim                       true
% 59.66/8.01  --brand_transform                       false
% 59.66/8.01  --non_eq_to_eq                          false
% 59.66/8.01  --prep_def_merge                        true
% 59.66/8.01  --prep_def_merge_prop_impl              false
% 59.66/8.01  --prep_def_merge_mbd                    true
% 59.66/8.01  --prep_def_merge_tr_red                 false
% 59.66/8.01  --prep_def_merge_tr_cl                  false
% 59.66/8.01  --smt_preprocessing                     true
% 59.66/8.01  --smt_ac_axioms                         fast
% 59.66/8.01  --preprocessed_out                      false
% 59.66/8.01  --preprocessed_stats                    false
% 59.66/8.01  
% 59.66/8.01  ------ Abstraction refinement Options
% 59.66/8.01  
% 59.66/8.01  --abstr_ref                             []
% 59.66/8.01  --abstr_ref_prep                        false
% 59.66/8.01  --abstr_ref_until_sat                   false
% 59.66/8.01  --abstr_ref_sig_restrict                funpre
% 59.66/8.01  --abstr_ref_af_restrict_to_split_sk     false
% 59.66/8.01  --abstr_ref_under                       []
% 59.66/8.01  
% 59.66/8.01  ------ SAT Options
% 59.66/8.01  
% 59.66/8.01  --sat_mode                              false
% 59.66/8.01  --sat_fm_restart_options                ""
% 59.66/8.01  --sat_gr_def                            false
% 59.66/8.01  --sat_epr_types                         true
% 59.66/8.01  --sat_non_cyclic_types                  false
% 59.66/8.01  --sat_finite_models                     false
% 59.66/8.01  --sat_fm_lemmas                         false
% 59.66/8.01  --sat_fm_prep                           false
% 59.66/8.01  --sat_fm_uc_incr                        true
% 59.66/8.01  --sat_out_model                         small
% 59.66/8.01  --sat_out_clauses                       false
% 59.66/8.01  
% 59.66/8.01  ------ QBF Options
% 59.66/8.01  
% 59.66/8.01  --qbf_mode                              false
% 59.66/8.01  --qbf_elim_univ                         false
% 59.66/8.01  --qbf_dom_inst                          none
% 59.66/8.01  --qbf_dom_pre_inst                      false
% 59.66/8.01  --qbf_sk_in                             false
% 59.66/8.01  --qbf_pred_elim                         true
% 59.66/8.01  --qbf_split                             512
% 59.66/8.01  
% 59.66/8.01  ------ BMC1 Options
% 59.66/8.01  
% 59.66/8.01  --bmc1_incremental                      false
% 59.66/8.01  --bmc1_axioms                           reachable_all
% 59.66/8.01  --bmc1_min_bound                        0
% 59.66/8.01  --bmc1_max_bound                        -1
% 59.66/8.01  --bmc1_max_bound_default                -1
% 59.66/8.01  --bmc1_symbol_reachability              true
% 59.66/8.01  --bmc1_property_lemmas                  false
% 59.66/8.01  --bmc1_k_induction                      false
% 59.66/8.01  --bmc1_non_equiv_states                 false
% 59.66/8.01  --bmc1_deadlock                         false
% 59.66/8.01  --bmc1_ucm                              false
% 59.66/8.01  --bmc1_add_unsat_core                   none
% 59.66/8.01  --bmc1_unsat_core_children              false
% 59.66/8.01  --bmc1_unsat_core_extrapolate_axioms    false
% 59.66/8.01  --bmc1_out_stat                         full
% 59.66/8.01  --bmc1_ground_init                      false
% 59.66/8.01  --bmc1_pre_inst_next_state              false
% 59.66/8.01  --bmc1_pre_inst_state                   false
% 59.66/8.01  --bmc1_pre_inst_reach_state             false
% 59.66/8.01  --bmc1_out_unsat_core                   false
% 59.66/8.01  --bmc1_aig_witness_out                  false
% 59.66/8.01  --bmc1_verbose                          false
% 59.66/8.01  --bmc1_dump_clauses_tptp                false
% 59.66/8.01  --bmc1_dump_unsat_core_tptp             false
% 59.66/8.01  --bmc1_dump_file                        -
% 59.66/8.01  --bmc1_ucm_expand_uc_limit              128
% 59.66/8.01  --bmc1_ucm_n_expand_iterations          6
% 59.66/8.01  --bmc1_ucm_extend_mode                  1
% 59.66/8.01  --bmc1_ucm_init_mode                    2
% 59.66/8.01  --bmc1_ucm_cone_mode                    none
% 59.66/8.01  --bmc1_ucm_reduced_relation_type        0
% 59.66/8.01  --bmc1_ucm_relax_model                  4
% 59.66/8.01  --bmc1_ucm_full_tr_after_sat            true
% 59.66/8.01  --bmc1_ucm_expand_neg_assumptions       false
% 59.66/8.01  --bmc1_ucm_layered_model                none
% 59.66/8.01  --bmc1_ucm_max_lemma_size               10
% 59.66/8.01  
% 59.66/8.01  ------ AIG Options
% 59.66/8.01  
% 59.66/8.01  --aig_mode                              false
% 59.66/8.01  
% 59.66/8.01  ------ Instantiation Options
% 59.66/8.01  
% 59.66/8.01  --instantiation_flag                    true
% 59.66/8.01  --inst_sos_flag                         true
% 59.66/8.01  --inst_sos_phase                        true
% 59.66/8.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.66/8.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.66/8.01  --inst_lit_sel_side                     num_symb
% 59.66/8.01  --inst_solver_per_active                1400
% 59.66/8.01  --inst_solver_calls_frac                1.
% 59.66/8.01  --inst_passive_queue_type               priority_queues
% 59.66/8.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.66/8.01  --inst_passive_queues_freq              [25;2]
% 59.66/8.01  --inst_dismatching                      true
% 59.66/8.01  --inst_eager_unprocessed_to_passive     true
% 59.66/8.01  --inst_prop_sim_given                   true
% 59.66/8.01  --inst_prop_sim_new                     false
% 59.66/8.01  --inst_subs_new                         false
% 59.66/8.01  --inst_eq_res_simp                      false
% 59.66/8.01  --inst_subs_given                       false
% 59.66/8.01  --inst_orphan_elimination               true
% 59.66/8.01  --inst_learning_loop_flag               true
% 59.66/8.01  --inst_learning_start                   3000
% 59.66/8.01  --inst_learning_factor                  2
% 59.66/8.01  --inst_start_prop_sim_after_learn       3
% 59.66/8.01  --inst_sel_renew                        solver
% 59.66/8.01  --inst_lit_activity_flag                true
% 59.66/8.01  --inst_restr_to_given                   false
% 59.66/8.01  --inst_activity_threshold               500
% 59.66/8.01  --inst_out_proof                        true
% 59.66/8.01  
% 59.66/8.01  ------ Resolution Options
% 59.66/8.01  
% 59.66/8.01  --resolution_flag                       true
% 59.66/8.01  --res_lit_sel                           adaptive
% 59.66/8.01  --res_lit_sel_side                      none
% 59.66/8.01  --res_ordering                          kbo
% 59.66/8.01  --res_to_prop_solver                    active
% 59.66/8.01  --res_prop_simpl_new                    false
% 59.66/8.01  --res_prop_simpl_given                  true
% 59.66/8.01  --res_passive_queue_type                priority_queues
% 59.66/8.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.66/8.01  --res_passive_queues_freq               [15;5]
% 59.66/8.01  --res_forward_subs                      full
% 59.66/8.01  --res_backward_subs                     full
% 59.66/8.01  --res_forward_subs_resolution           true
% 59.66/8.01  --res_backward_subs_resolution          true
% 59.66/8.01  --res_orphan_elimination                true
% 59.66/8.01  --res_time_limit                        2.
% 59.66/8.01  --res_out_proof                         true
% 59.66/8.01  
% 59.66/8.01  ------ Superposition Options
% 59.66/8.01  
% 59.66/8.01  --superposition_flag                    true
% 59.66/8.01  --sup_passive_queue_type                priority_queues
% 59.66/8.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.66/8.01  --sup_passive_queues_freq               [8;1;4]
% 59.66/8.01  --demod_completeness_check              fast
% 59.66/8.01  --demod_use_ground                      true
% 59.66/8.01  --sup_to_prop_solver                    passive
% 59.66/8.01  --sup_prop_simpl_new                    true
% 59.66/8.01  --sup_prop_simpl_given                  true
% 59.66/8.01  --sup_fun_splitting                     true
% 59.66/8.01  --sup_smt_interval                      50000
% 59.66/8.01  
% 59.66/8.01  ------ Superposition Simplification Setup
% 59.66/8.01  
% 59.66/8.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.66/8.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.66/8.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.66/8.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.66/8.01  --sup_full_triv                         [TrivRules;PropSubs]
% 59.66/8.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.66/8.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.66/8.01  --sup_immed_triv                        [TrivRules]
% 59.66/8.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.66/8.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.66/8.01  --sup_immed_bw_main                     []
% 59.66/8.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.66/8.01  --sup_input_triv                        [Unflattening;TrivRules]
% 59.66/8.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.66/8.01  --sup_input_bw                          []
% 59.66/8.01  
% 59.66/8.01  ------ Combination Options
% 59.66/8.01  
% 59.66/8.01  --comb_res_mult                         3
% 59.66/8.01  --comb_sup_mult                         2
% 59.66/8.01  --comb_inst_mult                        10
% 59.66/8.01  
% 59.66/8.01  ------ Debug Options
% 59.66/8.01  
% 59.66/8.01  --dbg_backtrace                         false
% 59.66/8.01  --dbg_dump_prop_clauses                 false
% 59.66/8.01  --dbg_dump_prop_clauses_file            -
% 59.66/8.01  --dbg_out_stat                          false
% 59.66/8.01  ------ Parsing...
% 59.66/8.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.66/8.01  
% 59.66/8.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 59.66/8.01  
% 59.66/8.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.66/8.01  
% 59.66/8.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.66/8.01  ------ Proving...
% 59.66/8.01  ------ Problem Properties 
% 59.66/8.01  
% 59.66/8.01  
% 59.66/8.01  clauses                                 9
% 59.66/8.01  conjectures                             1
% 59.66/8.01  EPR                                     0
% 59.66/8.01  Horn                                    9
% 59.66/8.01  unary                                   8
% 59.66/8.01  binary                                  1
% 59.66/8.01  lits                                    10
% 59.66/8.01  lits eq                                 7
% 59.66/8.01  fd_pure                                 0
% 59.66/8.01  fd_pseudo                               0
% 59.66/8.01  fd_cond                                 0
% 59.66/8.01  fd_pseudo_cond                          0
% 59.66/8.01  AC symbols                              1
% 59.66/8.01  
% 59.66/8.01  ------ Schedule dynamic 5 is on 
% 59.66/8.01  
% 59.66/8.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.66/8.01  
% 59.66/8.01  
% 59.66/8.01  ------ 
% 59.66/8.01  Current options:
% 59.66/8.01  ------ 
% 59.66/8.01  
% 59.66/8.01  ------ Input Options
% 59.66/8.01  
% 59.66/8.01  --out_options                           all
% 59.66/8.01  --tptp_safe_out                         true
% 59.66/8.01  --problem_path                          ""
% 59.66/8.01  --include_path                          ""
% 59.66/8.01  --clausifier                            res/vclausify_rel
% 59.66/8.01  --clausifier_options                    ""
% 59.66/8.01  --stdin                                 false
% 59.66/8.01  --stats_out                             all
% 59.66/8.01  
% 59.66/8.01  ------ General Options
% 59.66/8.01  
% 59.66/8.01  --fof                                   false
% 59.66/8.01  --time_out_real                         305.
% 59.66/8.01  --time_out_virtual                      -1.
% 59.66/8.01  --symbol_type_check                     false
% 59.66/8.01  --clausify_out                          false
% 59.66/8.01  --sig_cnt_out                           false
% 59.66/8.01  --trig_cnt_out                          false
% 59.66/8.01  --trig_cnt_out_tolerance                1.
% 59.66/8.01  --trig_cnt_out_sk_spl                   false
% 59.66/8.01  --abstr_cl_out                          false
% 59.66/8.01  
% 59.66/8.01  ------ Global Options
% 59.66/8.01  
% 59.66/8.01  --schedule                              default
% 59.66/8.01  --add_important_lit                     false
% 59.66/8.01  --prop_solver_per_cl                    1000
% 59.66/8.01  --min_unsat_core                        false
% 59.66/8.01  --soft_assumptions                      false
% 59.66/8.01  --soft_lemma_size                       3
% 59.66/8.01  --prop_impl_unit_size                   0
% 59.66/8.01  --prop_impl_unit                        []
% 59.66/8.01  --share_sel_clauses                     true
% 59.66/8.01  --reset_solvers                         false
% 59.66/8.01  --bc_imp_inh                            [conj_cone]
% 59.66/8.01  --conj_cone_tolerance                   3.
% 59.66/8.01  --extra_neg_conj                        none
% 59.66/8.01  --large_theory_mode                     true
% 59.66/8.01  --prolific_symb_bound                   200
% 59.66/8.01  --lt_threshold                          2000
% 59.66/8.01  --clause_weak_htbl                      true
% 59.66/8.01  --gc_record_bc_elim                     false
% 59.66/8.01  
% 59.66/8.01  ------ Preprocessing Options
% 59.66/8.01  
% 59.66/8.01  --preprocessing_flag                    true
% 59.66/8.01  --time_out_prep_mult                    0.1
% 59.66/8.01  --splitting_mode                        input
% 59.66/8.01  --splitting_grd                         true
% 59.66/8.01  --splitting_cvd                         false
% 59.66/8.01  --splitting_cvd_svl                     false
% 59.66/8.01  --splitting_nvd                         32
% 59.66/8.01  --sub_typing                            true
% 59.66/8.01  --prep_gs_sim                           true
% 59.66/8.01  --prep_unflatten                        true
% 59.66/8.01  --prep_res_sim                          true
% 59.66/8.01  --prep_upred                            true
% 59.66/8.01  --prep_sem_filter                       exhaustive
% 59.66/8.01  --prep_sem_filter_out                   false
% 59.66/8.01  --pred_elim                             true
% 59.66/8.01  --res_sim_input                         true
% 59.66/8.01  --eq_ax_congr_red                       true
% 59.66/8.01  --pure_diseq_elim                       true
% 59.66/8.01  --brand_transform                       false
% 59.66/8.01  --non_eq_to_eq                          false
% 59.66/8.01  --prep_def_merge                        true
% 59.66/8.01  --prep_def_merge_prop_impl              false
% 59.66/8.01  --prep_def_merge_mbd                    true
% 59.66/8.01  --prep_def_merge_tr_red                 false
% 59.66/8.01  --prep_def_merge_tr_cl                  false
% 59.66/8.01  --smt_preprocessing                     true
% 59.66/8.01  --smt_ac_axioms                         fast
% 59.66/8.01  --preprocessed_out                      false
% 59.66/8.01  --preprocessed_stats                    false
% 59.66/8.01  
% 59.66/8.01  ------ Abstraction refinement Options
% 59.66/8.01  
% 59.66/8.01  --abstr_ref                             []
% 59.66/8.01  --abstr_ref_prep                        false
% 59.66/8.01  --abstr_ref_until_sat                   false
% 59.66/8.01  --abstr_ref_sig_restrict                funpre
% 59.66/8.01  --abstr_ref_af_restrict_to_split_sk     false
% 59.66/8.01  --abstr_ref_under                       []
% 59.66/8.01  
% 59.66/8.01  ------ SAT Options
% 59.66/8.01  
% 59.66/8.01  --sat_mode                              false
% 59.66/8.01  --sat_fm_restart_options                ""
% 59.66/8.01  --sat_gr_def                            false
% 59.66/8.01  --sat_epr_types                         true
% 59.66/8.01  --sat_non_cyclic_types                  false
% 59.66/8.01  --sat_finite_models                     false
% 59.66/8.01  --sat_fm_lemmas                         false
% 59.66/8.01  --sat_fm_prep                           false
% 59.66/8.01  --sat_fm_uc_incr                        true
% 59.66/8.01  --sat_out_model                         small
% 59.66/8.01  --sat_out_clauses                       false
% 59.66/8.01  
% 59.66/8.01  ------ QBF Options
% 59.66/8.01  
% 59.66/8.01  --qbf_mode                              false
% 59.66/8.01  --qbf_elim_univ                         false
% 59.66/8.01  --qbf_dom_inst                          none
% 59.66/8.01  --qbf_dom_pre_inst                      false
% 59.66/8.01  --qbf_sk_in                             false
% 59.66/8.01  --qbf_pred_elim                         true
% 59.66/8.01  --qbf_split                             512
% 59.66/8.01  
% 59.66/8.01  ------ BMC1 Options
% 59.66/8.01  
% 59.66/8.01  --bmc1_incremental                      false
% 59.66/8.01  --bmc1_axioms                           reachable_all
% 59.66/8.01  --bmc1_min_bound                        0
% 59.66/8.01  --bmc1_max_bound                        -1
% 59.66/8.01  --bmc1_max_bound_default                -1
% 59.66/8.01  --bmc1_symbol_reachability              true
% 59.66/8.01  --bmc1_property_lemmas                  false
% 59.66/8.01  --bmc1_k_induction                      false
% 59.66/8.01  --bmc1_non_equiv_states                 false
% 59.66/8.01  --bmc1_deadlock                         false
% 59.66/8.01  --bmc1_ucm                              false
% 59.66/8.01  --bmc1_add_unsat_core                   none
% 59.66/8.01  --bmc1_unsat_core_children              false
% 59.66/8.01  --bmc1_unsat_core_extrapolate_axioms    false
% 59.66/8.01  --bmc1_out_stat                         full
% 59.66/8.01  --bmc1_ground_init                      false
% 59.66/8.01  --bmc1_pre_inst_next_state              false
% 59.66/8.01  --bmc1_pre_inst_state                   false
% 59.66/8.01  --bmc1_pre_inst_reach_state             false
% 59.66/8.01  --bmc1_out_unsat_core                   false
% 59.66/8.01  --bmc1_aig_witness_out                  false
% 59.66/8.01  --bmc1_verbose                          false
% 59.66/8.01  --bmc1_dump_clauses_tptp                false
% 59.66/8.01  --bmc1_dump_unsat_core_tptp             false
% 59.66/8.01  --bmc1_dump_file                        -
% 59.66/8.01  --bmc1_ucm_expand_uc_limit              128
% 59.66/8.01  --bmc1_ucm_n_expand_iterations          6
% 59.66/8.01  --bmc1_ucm_extend_mode                  1
% 59.66/8.01  --bmc1_ucm_init_mode                    2
% 59.66/8.01  --bmc1_ucm_cone_mode                    none
% 59.66/8.01  --bmc1_ucm_reduced_relation_type        0
% 59.66/8.01  --bmc1_ucm_relax_model                  4
% 59.66/8.01  --bmc1_ucm_full_tr_after_sat            true
% 59.66/8.01  --bmc1_ucm_expand_neg_assumptions       false
% 59.66/8.01  --bmc1_ucm_layered_model                none
% 59.66/8.01  --bmc1_ucm_max_lemma_size               10
% 59.66/8.01  
% 59.66/8.01  ------ AIG Options
% 59.66/8.01  
% 59.66/8.01  --aig_mode                              false
% 59.66/8.01  
% 59.66/8.01  ------ Instantiation Options
% 59.66/8.01  
% 59.66/8.01  --instantiation_flag                    true
% 59.66/8.01  --inst_sos_flag                         true
% 59.66/8.01  --inst_sos_phase                        true
% 59.66/8.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.66/8.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.66/8.01  --inst_lit_sel_side                     none
% 59.66/8.01  --inst_solver_per_active                1400
% 59.66/8.01  --inst_solver_calls_frac                1.
% 59.66/8.01  --inst_passive_queue_type               priority_queues
% 59.66/8.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.66/8.01  --inst_passive_queues_freq              [25;2]
% 59.66/8.01  --inst_dismatching                      true
% 59.66/8.01  --inst_eager_unprocessed_to_passive     true
% 59.66/8.01  --inst_prop_sim_given                   true
% 59.66/8.01  --inst_prop_sim_new                     false
% 59.66/8.01  --inst_subs_new                         false
% 59.66/8.01  --inst_eq_res_simp                      false
% 59.66/8.01  --inst_subs_given                       false
% 59.66/8.01  --inst_orphan_elimination               true
% 59.66/8.01  --inst_learning_loop_flag               true
% 59.66/8.01  --inst_learning_start                   3000
% 59.66/8.01  --inst_learning_factor                  2
% 59.66/8.01  --inst_start_prop_sim_after_learn       3
% 59.66/8.01  --inst_sel_renew                        solver
% 59.66/8.01  --inst_lit_activity_flag                true
% 59.66/8.01  --inst_restr_to_given                   false
% 59.66/8.01  --inst_activity_threshold               500
% 59.66/8.01  --inst_out_proof                        true
% 59.66/8.01  
% 59.66/8.01  ------ Resolution Options
% 59.66/8.01  
% 59.66/8.01  --resolution_flag                       false
% 59.66/8.01  --res_lit_sel                           adaptive
% 59.66/8.01  --res_lit_sel_side                      none
% 59.66/8.01  --res_ordering                          kbo
% 59.66/8.01  --res_to_prop_solver                    active
% 59.66/8.01  --res_prop_simpl_new                    false
% 59.66/8.01  --res_prop_simpl_given                  true
% 59.66/8.01  --res_passive_queue_type                priority_queues
% 59.66/8.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.66/8.01  --res_passive_queues_freq               [15;5]
% 59.66/8.01  --res_forward_subs                      full
% 59.66/8.01  --res_backward_subs                     full
% 59.66/8.01  --res_forward_subs_resolution           true
% 59.66/8.01  --res_backward_subs_resolution          true
% 59.66/8.01  --res_orphan_elimination                true
% 59.66/8.01  --res_time_limit                        2.
% 59.66/8.01  --res_out_proof                         true
% 59.66/8.01  
% 59.66/8.01  ------ Superposition Options
% 59.66/8.01  
% 59.66/8.01  --superposition_flag                    true
% 59.66/8.01  --sup_passive_queue_type                priority_queues
% 59.66/8.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.66/8.01  --sup_passive_queues_freq               [8;1;4]
% 59.66/8.01  --demod_completeness_check              fast
% 59.66/8.01  --demod_use_ground                      true
% 59.66/8.01  --sup_to_prop_solver                    passive
% 59.66/8.01  --sup_prop_simpl_new                    true
% 59.66/8.01  --sup_prop_simpl_given                  true
% 59.66/8.01  --sup_fun_splitting                     true
% 59.66/8.01  --sup_smt_interval                      50000
% 59.66/8.01  
% 59.66/8.01  ------ Superposition Simplification Setup
% 59.66/8.01  
% 59.66/8.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.66/8.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.66/8.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.66/8.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.66/8.01  --sup_full_triv                         [TrivRules;PropSubs]
% 59.66/8.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.66/8.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.66/8.01  --sup_immed_triv                        [TrivRules]
% 59.66/8.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.66/8.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.66/8.01  --sup_immed_bw_main                     []
% 59.66/8.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.66/8.01  --sup_input_triv                        [Unflattening;TrivRules]
% 59.66/8.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.66/8.01  --sup_input_bw                          []
% 59.66/8.01  
% 59.66/8.01  ------ Combination Options
% 59.66/8.01  
% 59.66/8.01  --comb_res_mult                         3
% 59.66/8.01  --comb_sup_mult                         2
% 59.66/8.01  --comb_inst_mult                        10
% 59.66/8.01  
% 59.66/8.01  ------ Debug Options
% 59.66/8.01  
% 59.66/8.01  --dbg_backtrace                         false
% 59.66/8.01  --dbg_dump_prop_clauses                 false
% 59.66/8.01  --dbg_dump_prop_clauses_file            -
% 59.66/8.01  --dbg_out_stat                          false
% 59.66/8.01  
% 59.66/8.01  
% 59.66/8.01  
% 59.66/8.01  
% 59.66/8.01  ------ Proving...
% 59.66/8.01  
% 59.66/8.01  
% 59.66/8.01  % SZS status Theorem for theBenchmark.p
% 59.66/8.01  
% 59.66/8.01   Resolution empty clause
% 59.66/8.01  
% 59.66/8.01  % SZS output start CNFRefutation for theBenchmark.p
% 59.66/8.01  
% 59.66/8.01  fof(f17,axiom,(
% 59.66/8.01    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f41,plain,(
% 59.66/8.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 59.66/8.01    inference(cnf_transformation,[],[f17])).
% 59.66/8.01  
% 59.66/8.01  fof(f10,axiom,(
% 59.66/8.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f34,plain,(
% 59.66/8.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f10])).
% 59.66/8.01  
% 59.66/8.01  fof(f49,plain,(
% 59.66/8.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 59.66/8.01    inference(definition_unfolding,[],[f34,f48])).
% 59.66/8.01  
% 59.66/8.01  fof(f11,axiom,(
% 59.66/8.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f35,plain,(
% 59.66/8.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f11])).
% 59.66/8.01  
% 59.66/8.01  fof(f12,axiom,(
% 59.66/8.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f36,plain,(
% 59.66/8.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f12])).
% 59.66/8.01  
% 59.66/8.01  fof(f13,axiom,(
% 59.66/8.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f37,plain,(
% 59.66/8.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f13])).
% 59.66/8.01  
% 59.66/8.01  fof(f14,axiom,(
% 59.66/8.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f38,plain,(
% 59.66/8.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f14])).
% 59.66/8.01  
% 59.66/8.01  fof(f15,axiom,(
% 59.66/8.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f39,plain,(
% 59.66/8.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f15])).
% 59.66/8.01  
% 59.66/8.01  fof(f16,axiom,(
% 59.66/8.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f40,plain,(
% 59.66/8.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f16])).
% 59.66/8.01  
% 59.66/8.01  fof(f44,plain,(
% 59.66/8.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 59.66/8.01    inference(definition_unfolding,[],[f39,f40])).
% 59.66/8.01  
% 59.66/8.01  fof(f45,plain,(
% 59.66/8.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 59.66/8.01    inference(definition_unfolding,[],[f38,f44])).
% 59.66/8.01  
% 59.66/8.01  fof(f46,plain,(
% 59.66/8.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 59.66/8.01    inference(definition_unfolding,[],[f37,f45])).
% 59.66/8.01  
% 59.66/8.01  fof(f47,plain,(
% 59.66/8.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 59.66/8.01    inference(definition_unfolding,[],[f36,f46])).
% 59.66/8.01  
% 59.66/8.01  fof(f48,plain,(
% 59.66/8.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 59.66/8.01    inference(definition_unfolding,[],[f35,f47])).
% 59.66/8.01  
% 59.66/8.01  fof(f54,plain,(
% 59.66/8.01    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 59.66/8.01    inference(definition_unfolding,[],[f41,f49,f48])).
% 59.66/8.01  
% 59.66/8.01  fof(f3,axiom,(
% 59.66/8.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f20,plain,(
% 59.66/8.01    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 59.66/8.01    inference(unused_predicate_definition_removal,[],[f3])).
% 59.66/8.01  
% 59.66/8.01  fof(f21,plain,(
% 59.66/8.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 59.66/8.01    inference(ennf_transformation,[],[f20])).
% 59.66/8.01  
% 59.66/8.01  fof(f27,plain,(
% 59.66/8.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f21])).
% 59.66/8.01  
% 59.66/8.01  fof(f4,axiom,(
% 59.66/8.01    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f28,plain,(
% 59.66/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f4])).
% 59.66/8.01  
% 59.66/8.01  fof(f50,plain,(
% 59.66/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 59.66/8.01    inference(definition_unfolding,[],[f27,f28])).
% 59.66/8.01  
% 59.66/8.01  fof(f8,axiom,(
% 59.66/8.01    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f32,plain,(
% 59.66/8.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f8])).
% 59.66/8.01  
% 59.66/8.01  fof(f2,axiom,(
% 59.66/8.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f26,plain,(
% 59.66/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f2])).
% 59.66/8.01  
% 59.66/8.01  fof(f7,axiom,(
% 59.66/8.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f31,plain,(
% 59.66/8.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.66/8.01    inference(cnf_transformation,[],[f7])).
% 59.66/8.01  
% 59.66/8.01  fof(f53,plain,(
% 59.66/8.01    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 59.66/8.01    inference(definition_unfolding,[],[f31,f28])).
% 59.66/8.01  
% 59.66/8.01  fof(f6,axiom,(
% 59.66/8.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f30,plain,(
% 59.66/8.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f6])).
% 59.66/8.01  
% 59.66/8.01  fof(f52,plain,(
% 59.66/8.01    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 59.66/8.01    inference(definition_unfolding,[],[f30,f28])).
% 59.66/8.01  
% 59.66/8.01  fof(f1,axiom,(
% 59.66/8.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f25,plain,(
% 59.66/8.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f1])).
% 59.66/8.01  
% 59.66/8.01  fof(f5,axiom,(
% 59.66/8.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f29,plain,(
% 59.66/8.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.66/8.01    inference(cnf_transformation,[],[f5])).
% 59.66/8.01  
% 59.66/8.01  fof(f9,axiom,(
% 59.66/8.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f33,plain,(
% 59.66/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 59.66/8.01    inference(cnf_transformation,[],[f9])).
% 59.66/8.01  
% 59.66/8.01  fof(f43,plain,(
% 59.66/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 59.66/8.01    inference(definition_unfolding,[],[f33,f28])).
% 59.66/8.01  
% 59.66/8.01  fof(f51,plain,(
% 59.66/8.01    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 59.66/8.01    inference(definition_unfolding,[],[f29,f43])).
% 59.66/8.01  
% 59.66/8.01  fof(f18,conjecture,(
% 59.66/8.01    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 59.66/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.66/8.01  
% 59.66/8.01  fof(f19,negated_conjecture,(
% 59.66/8.01    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 59.66/8.01    inference(negated_conjecture,[],[f18])).
% 59.66/8.01  
% 59.66/8.01  fof(f22,plain,(
% 59.66/8.01    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)),
% 59.66/8.01    inference(ennf_transformation,[],[f19])).
% 59.66/8.01  
% 59.66/8.01  fof(f23,plain,(
% 59.66/8.01    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 59.66/8.01    introduced(choice_axiom,[])).
% 59.66/8.01  
% 59.66/8.01  fof(f24,plain,(
% 59.66/8.01    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 59.66/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 59.66/8.01  
% 59.66/8.01  fof(f42,plain,(
% 59.66/8.01    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 59.66/8.01    inference(cnf_transformation,[],[f24])).
% 59.66/8.01  
% 59.66/8.01  fof(f55,plain,(
% 59.66/8.01    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 59.66/8.01    inference(definition_unfolding,[],[f42,f43,f49,f48,f48])).
% 59.66/8.01  
% 59.66/8.01  cnf(c_7,plain,
% 59.66/8.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 59.66/8.01      inference(cnf_transformation,[],[f54]) ).
% 59.66/8.01  
% 59.66/8.01  cnf(c_130,plain,
% 59.66/8.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 59.66/8.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 59.66/8.01  
% 59.66/8.01  cnf(c_2,plain,
% 59.66/8.01      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 59.66/8.01      inference(cnf_transformation,[],[f50]) ).
% 59.66/8.01  
% 59.66/8.01  cnf(c_132,plain,
% 59.66/8.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 59.66/8.01      | r1_tarski(X0,X1) != iProver_top ),
% 59.66/8.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 59.66/8.01  
% 59.66/8.01  cnf(c_853,plain,
% 59.66/8.01      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 59.66/8.01      inference(superposition,[status(thm)],[c_130,c_132]) ).
% 59.66/8.01  
% 59.66/8.01  cnf(c_6,plain,
% 59.66/8.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 59.66/8.01      inference(cnf_transformation,[],[f32]) ).
% 59.66/8.01  
% 59.66/8.01  cnf(c_1,plain,
% 59.66/8.01      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 59.66/8.01      inference(cnf_transformation,[],[f26]) ).
% 59.66/8.01  
% 59.66/8.01  cnf(c_136,plain,
% 59.66/8.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_5,plain,
% 59.66/8.02      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 59.66/8.02      inference(cnf_transformation,[],[f53]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_4,plain,
% 59.66/8.02      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 59.66/8.02      inference(cnf_transformation,[],[f52]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_131,plain,
% 59.66/8.02      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 59.66/8.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_448,plain,
% 59.66/8.02      ( r1_tarski(X0,X0) = iProver_top ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_5,c_131]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_854,plain,
% 59.66/8.02      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_448,c_132]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_138,plain,
% 59.66/8.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1254,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_854,c_138]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_0,plain,
% 59.66/8.02      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 59.66/8.02      inference(cnf_transformation,[],[f25]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_3,plain,
% 59.66/8.02      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 59.66/8.02      inference(cnf_transformation,[],[f51]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_314,plain,
% 59.66/8.02      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_669,plain,
% 59.66/8.02      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_136,c_314]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_673,plain,
% 59.66/8.02      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 59.66/8.02      inference(light_normalisation,[status(thm)],[c_669,c_5]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_697,plain,
% 59.66/8.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_673,c_1]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1259,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X1,X0)) = X1 ),
% 59.66/8.02      inference(demodulation,[status(thm)],[c_1254,c_697]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1739,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_136,c_1259]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_38239,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X0,k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X0,k1_xboole_0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_853,c_1739]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_38659,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(X0,k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X0) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 59.66/8.02      inference(light_normalisation,[status(thm)],[c_38239,c_697]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1751,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),X0) = k3_xboole_0(X1,X1) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_1259,c_1259]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1735,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_138,c_1259]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_37220,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_853,c_1735]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_37710,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),X0) = k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 59.66/8.02      inference(light_normalisation,[status(thm)],[c_37220,c_697]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_37711,plain,
% 59.66/8.02      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sP0_iProver_split(X0) ),
% 59.66/8.02      inference(splitting,
% 59.66/8.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 59.66/8.02                [c_37710]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_38660,plain,
% 59.66/8.02      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X0)) ),
% 59.66/8.02      inference(demodulation,[status(thm)],[c_38659,c_1751,c_37711]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_8,negated_conjecture,
% 59.66/8.02      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 59.66/8.02      inference(cnf_transformation,[],[f55]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_163,plain,
% 59.66/8.02      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 59.66/8.02      inference(demodulation,[status(thm)],[c_0,c_8]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_223104,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(sP0_iProver_split(sK0),sP0_iProver_split(sK0)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_xboole_0(sP0_iProver_split(sK0),sP0_iProver_split(sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 59.66/8.02      inference(demodulation,[status(thm)],[c_38660,c_163]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_137,plain,
% 59.66/8.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1740,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_137,c_1259]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_39198,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)),k5_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_853,c_1740]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_39706,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X0)),X1),k5_xboole_0(k3_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X0)),X1)),k5_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X0)),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) ),
% 59.66/8.02      inference(light_normalisation,[status(thm)],[c_39198,c_38660]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_866,plain,
% 59.66/8.02      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_697,c_137]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1593,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(X0,X0),X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_854,c_866]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1620,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(X0,X0),X0) = k1_xboole_0 ),
% 59.66/8.02      inference(demodulation,[status(thm)],[c_1593,c_673]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1253,plain,
% 59.66/8.02      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X0))) = k5_xboole_0(X1,k1_xboole_0) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_854,c_136]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1260,plain,
% 59.66/8.02      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X0))) = X1 ),
% 59.66/8.02      inference(demodulation,[status(thm)],[c_1253,c_697]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1789,plain,
% 59.66/8.02      ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_1620,c_1260]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1809,plain,
% 59.66/8.02      ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = X0 ),
% 59.66/8.02      inference(light_normalisation,[status(thm)],[c_1789,c_697]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1250,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k1_xboole_0) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_854,c_137]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1261,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = X1 ),
% 59.66/8.02      inference(demodulation,[status(thm)],[c_1250,c_697]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_1972,plain,
% 59.66/8.02      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X0)) = X1 ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_1261,c_1]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_2431,plain,
% 59.66/8.02      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X0),X2)) = k5_xboole_0(X1,X2) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_1972,c_6]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_6620,plain,
% 59.66/8.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k5_xboole_0(X1,X2)) = k5_xboole_0(k3_xboole_0(X0,X0),X2) ),
% 59.66/8.02      inference(superposition,[status(thm)],[c_2431,c_1261]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_39707,plain,
% 59.66/8.02      ( k3_xboole_0(k3_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X0)),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sP0_iProver_split(X0) ),
% 59.66/8.02      inference(demodulation,[status(thm)],[c_39706,c_697,c_1809,c_6620]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_223105,plain,
% 59.66/8.02      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 59.66/8.02      inference(demodulation,[status(thm)],[c_223104,c_1259,c_39707]) ).
% 59.66/8.02  
% 59.66/8.02  cnf(c_223106,plain,
% 59.66/8.02      ( $false ),
% 59.66/8.02      inference(equality_resolution_simp,[status(thm)],[c_223105]) ).
% 59.66/8.02  
% 59.66/8.02  
% 59.66/8.02  % SZS output end CNFRefutation for theBenchmark.p
% 59.66/8.02  
% 59.66/8.02  ------                               Statistics
% 59.66/8.02  
% 59.66/8.02  ------ General
% 59.66/8.02  
% 59.66/8.02  abstr_ref_over_cycles:                  0
% 59.66/8.02  abstr_ref_under_cycles:                 0
% 59.66/8.02  gc_basic_clause_elim:                   0
% 59.66/8.02  forced_gc_time:                         0
% 59.66/8.02  parsing_time:                           0.01
% 59.66/8.02  unif_index_cands_time:                  0.
% 59.66/8.02  unif_index_add_time:                    0.
% 59.66/8.02  orderings_time:                         0.
% 59.66/8.02  out_proof_time:                         0.009
% 59.66/8.02  total_time:                             7.267
% 59.66/8.02  num_of_symbols:                         39
% 59.66/8.02  num_of_terms:                           455477
% 59.66/8.02  
% 59.66/8.02  ------ Preprocessing
% 59.66/8.02  
% 59.66/8.02  num_of_splits:                          0
% 59.66/8.02  num_of_split_atoms:                     1
% 59.66/8.02  num_of_reused_defs:                     0
% 59.66/8.02  num_eq_ax_congr_red:                    0
% 59.66/8.02  num_of_sem_filtered_clauses:            1
% 59.66/8.02  num_of_subtypes:                        0
% 59.66/8.02  monotx_restored_types:                  0
% 59.66/8.02  sat_num_of_epr_types:                   0
% 59.66/8.02  sat_num_of_non_cyclic_types:            0
% 59.66/8.02  sat_guarded_non_collapsed_types:        0
% 59.66/8.02  num_pure_diseq_elim:                    0
% 59.66/8.02  simp_replaced_by:                       0
% 59.66/8.02  res_preprocessed:                       40
% 59.66/8.02  prep_upred:                             0
% 59.66/8.02  prep_unflattend:                        4
% 59.66/8.02  smt_new_axioms:                         0
% 59.66/8.02  pred_elim_cands:                        1
% 59.66/8.02  pred_elim:                              0
% 59.66/8.02  pred_elim_cl:                           0
% 59.66/8.02  pred_elim_cycles:                       1
% 59.66/8.02  merged_defs:                            0
% 59.66/8.02  merged_defs_ncl:                        0
% 59.66/8.02  bin_hyper_res:                          0
% 59.66/8.02  prep_cycles:                            3
% 59.66/8.02  pred_elim_time:                         0.
% 59.66/8.02  splitting_time:                         0.
% 59.66/8.02  sem_filter_time:                        0.
% 59.66/8.02  monotx_time:                            0.
% 59.66/8.02  subtype_inf_time:                       0.
% 59.66/8.02  
% 59.66/8.02  ------ Problem properties
% 59.66/8.02  
% 59.66/8.02  clauses:                                9
% 59.66/8.02  conjectures:                            1
% 59.66/8.02  epr:                                    0
% 59.66/8.02  horn:                                   9
% 59.66/8.02  ground:                                 1
% 59.66/8.02  unary:                                  8
% 59.66/8.02  binary:                                 1
% 59.66/8.02  lits:                                   10
% 59.66/8.02  lits_eq:                                7
% 59.66/8.02  fd_pure:                                0
% 59.66/8.02  fd_pseudo:                              0
% 59.66/8.02  fd_cond:                                0
% 59.66/8.02  fd_pseudo_cond:                         0
% 59.66/8.02  ac_symbols:                             1
% 59.66/8.02  
% 59.66/8.02  ------ Propositional Solver
% 59.66/8.02  
% 59.66/8.02  prop_solver_calls:                      31
% 59.66/8.02  prop_fast_solver_calls:                 568
% 59.66/8.02  smt_solver_calls:                       0
% 59.66/8.02  smt_fast_solver_calls:                  0
% 59.66/8.02  prop_num_of_clauses:                    17684
% 59.66/8.02  prop_preprocess_simplified:             20293
% 59.66/8.02  prop_fo_subsumed:                       0
% 59.66/8.02  prop_solver_time:                       0.
% 59.66/8.02  smt_solver_time:                        0.
% 59.66/8.02  smt_fast_solver_time:                   0.
% 59.66/8.02  prop_fast_solver_time:                  0.
% 59.66/8.02  prop_unsat_core_time:                   0.
% 59.66/8.02  
% 59.66/8.02  ------ QBF
% 59.66/8.02  
% 59.66/8.02  qbf_q_res:                              0
% 59.66/8.02  qbf_num_tautologies:                    0
% 59.66/8.02  qbf_prep_cycles:                        0
% 59.66/8.02  
% 59.66/8.02  ------ BMC1
% 59.66/8.02  
% 59.66/8.02  bmc1_current_bound:                     -1
% 59.66/8.02  bmc1_last_solved_bound:                 -1
% 59.66/8.02  bmc1_unsat_core_size:                   -1
% 59.66/8.02  bmc1_unsat_core_parents_size:           -1
% 59.66/8.02  bmc1_merge_next_fun:                    0
% 59.66/8.02  bmc1_unsat_core_clauses_time:           0.
% 59.66/8.02  
% 59.66/8.02  ------ Instantiation
% 59.66/8.02  
% 59.66/8.02  inst_num_of_clauses:                    3677
% 59.66/8.02  inst_num_in_passive:                    1052
% 59.66/8.02  inst_num_in_active:                     1218
% 59.66/8.02  inst_num_in_unprocessed:                1407
% 59.66/8.02  inst_num_of_loops:                      1320
% 59.66/8.02  inst_num_of_learning_restarts:          0
% 59.66/8.02  inst_num_moves_active_passive:          97
% 59.66/8.02  inst_lit_activity:                      0
% 59.66/8.02  inst_lit_activity_moves:                1
% 59.66/8.02  inst_num_tautologies:                   0
% 59.66/8.02  inst_num_prop_implied:                  0
% 59.66/8.02  inst_num_existing_simplified:           0
% 59.66/8.02  inst_num_eq_res_simplified:             0
% 59.66/8.02  inst_num_child_elim:                    0
% 59.66/8.02  inst_num_of_dismatching_blockings:      2869
% 59.66/8.02  inst_num_of_non_proper_insts:           6418
% 59.66/8.02  inst_num_of_duplicates:                 0
% 59.66/8.02  inst_inst_num_from_inst_to_res:         0
% 59.66/8.02  inst_dismatching_checking_time:         0.
% 59.66/8.02  
% 59.66/8.02  ------ Resolution
% 59.66/8.02  
% 59.66/8.02  res_num_of_clauses:                     0
% 59.66/8.02  res_num_in_passive:                     0
% 59.66/8.02  res_num_in_active:                      0
% 59.66/8.02  res_num_of_loops:                       43
% 59.66/8.02  res_forward_subset_subsumed:            2043
% 59.66/8.02  res_backward_subset_subsumed:           2
% 59.66/8.02  res_forward_subsumed:                   0
% 59.66/8.02  res_backward_subsumed:                  0
% 59.66/8.02  res_forward_subsumption_resolution:     0
% 59.66/8.02  res_backward_subsumption_resolution:    0
% 59.66/8.02  res_clause_to_clause_subsumption:       425322
% 59.66/8.02  res_orphan_elimination:                 0
% 59.66/8.02  res_tautology_del:                      513
% 59.66/8.02  res_num_eq_res_simplified:              0
% 59.66/8.02  res_num_sel_changes:                    0
% 59.66/8.02  res_moves_from_active_to_pass:          0
% 59.66/8.02  
% 59.66/8.02  ------ Superposition
% 59.66/8.02  
% 59.66/8.02  sup_time_total:                         0.
% 59.66/8.02  sup_time_generating:                    0.
% 59.66/8.02  sup_time_sim_full:                      0.
% 59.66/8.02  sup_time_sim_immed:                     0.
% 59.66/8.02  
% 59.66/8.02  sup_num_of_clauses:                     9058
% 59.66/8.02  sup_num_in_active:                      237
% 59.66/8.02  sup_num_in_passive:                     8821
% 59.66/8.02  sup_num_of_loops:                       263
% 59.66/8.02  sup_fw_superposition:                   58374
% 59.66/8.02  sup_bw_superposition:                   47909
% 59.66/8.02  sup_immediate_simplified:               69207
% 59.66/8.02  sup_given_eliminated:                   10
% 59.66/8.02  comparisons_done:                       0
% 59.66/8.02  comparisons_avoided:                    0
% 59.66/8.02  
% 59.66/8.02  ------ Simplifications
% 59.66/8.02  
% 59.66/8.02  
% 59.66/8.02  sim_fw_subset_subsumed:                 0
% 59.66/8.02  sim_bw_subset_subsumed:                 0
% 59.66/8.02  sim_fw_subsumed:                        3821
% 59.66/8.02  sim_bw_subsumed:                        42
% 59.66/8.02  sim_fw_subsumption_res:                 0
% 59.66/8.02  sim_bw_subsumption_res:                 0
% 59.66/8.02  sim_tautology_del:                      0
% 59.66/8.02  sim_eq_tautology_del:                   15406
% 59.66/8.02  sim_eq_res_simp:                        0
% 59.66/8.02  sim_fw_demodulated:                     66640
% 59.66/8.02  sim_bw_demodulated:                     513
% 59.66/8.02  sim_light_normalised:                   24450
% 59.66/8.02  sim_joinable_taut:                      1149
% 59.66/8.02  sim_joinable_simp:                      0
% 59.66/8.02  sim_ac_normalised:                      0
% 59.66/8.02  sim_smt_subsumption:                    0
% 59.66/8.02  
%------------------------------------------------------------------------------
