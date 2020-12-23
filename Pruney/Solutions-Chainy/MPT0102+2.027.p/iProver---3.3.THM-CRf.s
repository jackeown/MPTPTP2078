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
% DateTime   : Thu Dec  3 11:25:07 EST 2020

% Result     : Theorem 55.31s
% Output     : CNFRefutation 55.31s
% Verified   : 
% Statistics : Number of formulae       :  258 (51853 expanded)
%              Number of clauses        :  216 (22809 expanded)
%              Number of leaves         :   17 (12786 expanded)
%              Depth                    :   31
%              Number of atoms          :  266 (56537 expanded)
%              Number of equality atoms :  257 (51184 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f38,f25])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f37,f25])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,conjecture,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f22,plain,
    ( ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1)
   => k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f39,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k3_xboole_0(sK0,sK1) ),
    inference(definition_unfolding,[],[f39,f25,f25])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_13,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_68,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_13,c_9,c_0])).

cnf(c_78,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_245,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_78,c_68])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_248,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_245,c_10])).

cnf(c_12,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_152,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_249,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_248,c_152])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_81,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_119,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_81])).

cnf(c_120,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_119,c_81])).

cnf(c_250,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_249,c_120])).

cnf(c_79,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_633,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3,c_79])).

cnf(c_1437,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_250,c_633])).

cnf(c_1490,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1437,c_633])).

cnf(c_6,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4453,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1490,c_6])).

cnf(c_354,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_152,c_10])).

cnf(c_373,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_354,c_81])).

cnf(c_883,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_6,c_373])).

cnf(c_356,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_120,c_10])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_55,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_56,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_55])).

cnf(c_167,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_120,c_56])).

cnf(c_371,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_356,c_120,c_167])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_257,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_152,c_7])).

cnf(c_276,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_257,c_167])).

cnf(c_892,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_276,c_373])).

cnf(c_918,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_892,c_120])).

cnf(c_960,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_918,c_10])).

cnf(c_886,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_56,c_373])).

cnf(c_923,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_886,c_3,c_7])).

cnf(c_905,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k4_xboole_0(X0,X1),X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_373,c_68])).

cnf(c_910,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k4_xboole_0(X0,X1),X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_905,c_56])).

cnf(c_924,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_923,c_910])).

cnf(c_896,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_373,c_250])).

cnf(c_925,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_924,c_896])).

cnf(c_118,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_56,c_5])).

cnf(c_121,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_118,c_3])).

cnf(c_926,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_925,c_121,c_633])).

cnf(c_966,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_960,c_926])).

cnf(c_3277,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_371,c_966])).

cnf(c_4496,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_4453,c_883,c_3277])).

cnf(c_10006,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_68,c_4496])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3299,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,k2_xboole_0(X1,X3))),X1) ),
    inference(superposition,[status(thm)],[c_966,c_8])).

cnf(c_10195,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1))))),X1) = k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_10006,c_7,c_3299])).

cnf(c_10196,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)))),X1) = k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_10195,c_373])).

cnf(c_1028,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_926,c_79])).

cnf(c_10197,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X1)),X1) = k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_10196,c_1028])).

cnf(c_268,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_56])).

cnf(c_465,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_371,c_268])).

cnf(c_894,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_465,c_373])).

cnf(c_916,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_894,c_120])).

cnf(c_2561,plain,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X0),k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_916,c_68])).

cnf(c_1009,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_373,c_926])).

cnf(c_2563,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2561,c_465,c_1009])).

cnf(c_2564,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_2563,c_10,c_81,c_633])).

cnf(c_3337,plain,
    ( k4_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X1),X0) = k4_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_2564,c_3277])).

cnf(c_258,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_56,c_7])).

cnf(c_275,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_258,c_7,c_167])).

cnf(c_1539,plain,
    ( k4_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1009,c_275])).

cnf(c_3372,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3337,c_1539])).

cnf(c_3450,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X1,X0)),k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(X1,X0)))) = k2_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3372,c_68])).

cnf(c_928,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_926,c_896])).

cnf(c_80,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_2637,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k3_xboole_0(X0,X1))) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_928,c_80])).

cnf(c_3456,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_3450,c_81,c_2637])).

cnf(c_229,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_78])).

cnf(c_3503,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3456,c_229])).

cnf(c_3524,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_3503,c_3456])).

cnf(c_10198,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10197,c_3524])).

cnf(c_14228,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_10198,c_4496])).

cnf(c_122,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_890,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_122,c_373])).

cnf(c_124,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_179,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_152,c_68])).

cnf(c_180,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) = k2_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_179,c_152])).

cnf(c_181,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_180,c_1])).

cnf(c_182,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_181,c_81])).

cnf(c_358,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_182,c_10])).

cnf(c_920,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_890,c_124,c_358])).

cnf(c_927,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_926,c_920])).

cnf(c_1059,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X1) = X1 ),
    inference(superposition,[status(thm)],[c_229,c_927])).

cnf(c_3491,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3456,c_1059])).

cnf(c_6916,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_3491,c_10])).

cnf(c_518,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_5,c_122])).

cnf(c_547,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_518,c_122])).

cnf(c_264,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_56])).

cnf(c_3055,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_547,c_264])).

cnf(c_884,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k3_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7,c_373])).

cnf(c_3178,plain,
    ( k3_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3055,c_7,c_884])).

cnf(c_3744,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1009,c_3178])).

cnf(c_5457,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_124,c_124,c_3277])).

cnf(c_5504,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_373,c_5457])).

cnf(c_5593,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_5504,c_926])).

cnf(c_10775,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3744,c_5593])).

cnf(c_10865,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_10775,c_3,c_7])).

cnf(c_14319,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_14228,c_373,c_6916,c_10865])).

cnf(c_10110,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_4496,c_7])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_67,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k3_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_14,c_9,c_0])).

cnf(c_266653,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k3_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_10110,c_67])).

cnf(c_2264,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_373,c_547])).

cnf(c_2311,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2264,c_373])).

cnf(c_329,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_49308,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k3_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_2311,c_329])).

cnf(c_42883,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k3_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_2311,c_8])).

cnf(c_907,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_373,c_8])).

cnf(c_42905,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k3_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_42883,c_907])).

cnf(c_49758,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X2,X0),k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_49308,c_42905])).

cnf(c_904,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_373,c_5])).

cnf(c_929,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_926,c_904])).

cnf(c_265,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_5])).

cnf(c_40745,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_929,c_265])).

cnf(c_49759,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_49758,c_40745])).

cnf(c_321,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_323,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_56,c_8])).

cnf(c_341,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_323,c_3])).

cnf(c_4948,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_341,c_1490])).

cnf(c_632,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_79])).

cnf(c_1342,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(superposition,[status(thm)],[c_79,c_632])).

cnf(c_11,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1081,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_11,c_80])).

cnf(c_130,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_132,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_130,c_5])).

cnf(c_1087,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_132,c_80])).

cnf(c_684,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_132,c_9])).

cnf(c_702,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_684,c_9])).

cnf(c_735,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_229,c_9])).

cnf(c_759,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_735,c_702])).

cnf(c_1152,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_1087,c_632,c_702,c_759])).

cnf(c_1155,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1081,c_1152])).

cnf(c_1399,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1342,c_1155])).

cnf(c_4968,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4948,c_1399,c_1490])).

cnf(c_72549,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3),X1) = k2_xboole_0(k4_xboole_0(X0,X3),X1) ),
    inference(superposition,[status(thm)],[c_321,c_4968])).

cnf(c_328,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_337,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_328,c_5,c_7])).

cnf(c_89842,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X3)),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X3)),k4_xboole_0(X1,k2_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_337,c_8])).

cnf(c_314,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_348,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(demodulation,[status(thm)],[c_314,c_329])).

cnf(c_349,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_348,c_9])).

cnf(c_54090,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X3)),k4_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X3),X0),k4_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_329,c_349])).

cnf(c_89882,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X3,X2),X0),k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_89842,c_54090])).

cnf(c_266654,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_266653,c_49759,c_72549,c_89882])).

cnf(c_5547,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_5457,c_7])).

cnf(c_207336,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_250,c_5547])).

cnf(c_232,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_78])).

cnf(c_293,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9,c_6])).

cnf(c_48219,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_232,c_293])).

cnf(c_669,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_5,c_132])).

cnf(c_709,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_669,c_250])).

cnf(c_243,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_78,c_6])).

cnf(c_28761,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_709,c_243])).

cnf(c_127,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X1)),k3_xboole_0(k2_xboole_0(X0,X1),X1))) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_6,c_68])).

cnf(c_442,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_276,c_5])).

cnf(c_450,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_442,c_3])).

cnf(c_1255,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_450])).

cnf(c_7213,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X1)),X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_127,c_127,c_1059,c_1255])).

cnf(c_4482,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1490,c_80])).

cnf(c_1417,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_633])).

cnf(c_1502,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1417,c_633])).

cnf(c_4527,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7,c_1502])).

cnf(c_7214,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_7213,c_4482,c_4527])).

cnf(c_530,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_122,c_121])).

cnf(c_22051,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_530,c_80])).

cnf(c_28970,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_28761,c_7214,c_22051])).

cnf(c_48583,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_48219,c_28970])).

cnf(c_208572,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_207336,c_3277,c_48583])).

cnf(c_266655,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))) != k3_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_266654,c_208572])).

cnf(c_14255,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_10198,c_132])).

cnf(c_14295,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_14255,c_3524])).

cnf(c_15502,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X0)),k1_xboole_0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3372,c_14295])).

cnf(c_1522,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1009,c_927])).

cnf(c_14512,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_14319,c_1522])).

cnf(c_15615,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_15502,c_14512])).

cnf(c_16358,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_15615,c_78])).

cnf(c_16381,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_16358,c_3])).

cnf(c_37309,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_16381,c_10])).

cnf(c_286,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_5,c_9])).

cnf(c_309,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_286,c_9])).

cnf(c_48855,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_309,c_243])).

cnf(c_242,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_78,c_11])).

cnf(c_48218,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_242,c_293])).

cnf(c_48584,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_48218,c_48583])).

cnf(c_48984,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_48855,c_48584])).

cnf(c_266656,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_266655,c_37309,c_48984])).

cnf(c_436,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_276,c_10])).

cnf(c_456,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_436,c_81])).

cnf(c_290,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_121,c_9])).

cnf(c_1055,plain,
    ( k3_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_78,c_927])).

cnf(c_4083,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_290,c_1055])).

cnf(c_63215,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X3),X2)) ),
    inference(superposition,[status(thm)],[c_456,c_4083])).

cnf(c_498,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_465,c_7])).

cnf(c_511,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_498,c_167])).

cnf(c_14249,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10198,c_6])).

cnf(c_14301,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_14249,c_10865])).

cnf(c_15715,plain,
    ( k4_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X1),k4_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_14301,c_5457])).

cnf(c_15748,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_15715,c_3524])).

cnf(c_17700,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(k3_xboole_0(X0,X2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_511,c_15748])).

cnf(c_17707,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3372,c_15748])).

cnf(c_17864,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_17707,c_14512])).

cnf(c_17868,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_17700,c_17864])).

cnf(c_63479,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k3_xboole_0(X2,X0) ),
    inference(light_normalisation,[status(thm)],[c_63215,c_17868])).

cnf(c_266657,plain,
    ( k3_xboole_0(sK1,sK0) != k3_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_266656,c_63479])).

cnf(c_268042,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_14319,c_266657])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 55.31/7.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.31/7.49  
% 55.31/7.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.31/7.49  
% 55.31/7.49  ------  iProver source info
% 55.31/7.49  
% 55.31/7.49  git: date: 2020-06-30 10:37:57 +0100
% 55.31/7.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.31/7.49  git: non_committed_changes: false
% 55.31/7.49  git: last_make_outside_of_git: false
% 55.31/7.49  
% 55.31/7.49  ------ 
% 55.31/7.49  
% 55.31/7.49  ------ Input Options
% 55.31/7.49  
% 55.31/7.49  --out_options                           all
% 55.31/7.49  --tptp_safe_out                         true
% 55.31/7.49  --problem_path                          ""
% 55.31/7.49  --include_path                          ""
% 55.31/7.49  --clausifier                            res/vclausify_rel
% 55.31/7.49  --clausifier_options                    --mode clausify
% 55.31/7.49  --stdin                                 false
% 55.31/7.49  --stats_out                             all
% 55.31/7.49  
% 55.31/7.49  ------ General Options
% 55.31/7.49  
% 55.31/7.49  --fof                                   false
% 55.31/7.49  --time_out_real                         305.
% 55.31/7.49  --time_out_virtual                      -1.
% 55.31/7.49  --symbol_type_check                     false
% 55.31/7.49  --clausify_out                          false
% 55.31/7.49  --sig_cnt_out                           false
% 55.31/7.49  --trig_cnt_out                          false
% 55.31/7.49  --trig_cnt_out_tolerance                1.
% 55.31/7.49  --trig_cnt_out_sk_spl                   false
% 55.31/7.49  --abstr_cl_out                          false
% 55.31/7.49  
% 55.31/7.49  ------ Global Options
% 55.31/7.49  
% 55.31/7.49  --schedule                              default
% 55.31/7.49  --add_important_lit                     false
% 55.31/7.49  --prop_solver_per_cl                    1000
% 55.31/7.49  --min_unsat_core                        false
% 55.31/7.49  --soft_assumptions                      false
% 55.31/7.49  --soft_lemma_size                       3
% 55.31/7.49  --prop_impl_unit_size                   0
% 55.31/7.49  --prop_impl_unit                        []
% 55.31/7.49  --share_sel_clauses                     true
% 55.31/7.49  --reset_solvers                         false
% 55.31/7.49  --bc_imp_inh                            [conj_cone]
% 55.31/7.49  --conj_cone_tolerance                   3.
% 55.31/7.49  --extra_neg_conj                        none
% 55.31/7.49  --large_theory_mode                     true
% 55.31/7.49  --prolific_symb_bound                   200
% 55.31/7.49  --lt_threshold                          2000
% 55.31/7.49  --clause_weak_htbl                      true
% 55.31/7.49  --gc_record_bc_elim                     false
% 55.31/7.49  
% 55.31/7.49  ------ Preprocessing Options
% 55.31/7.49  
% 55.31/7.49  --preprocessing_flag                    true
% 55.31/7.49  --time_out_prep_mult                    0.1
% 55.31/7.49  --splitting_mode                        input
% 55.31/7.49  --splitting_grd                         true
% 55.31/7.49  --splitting_cvd                         false
% 55.31/7.49  --splitting_cvd_svl                     false
% 55.31/7.49  --splitting_nvd                         32
% 55.31/7.49  --sub_typing                            true
% 55.31/7.49  --prep_gs_sim                           true
% 55.31/7.49  --prep_unflatten                        true
% 55.31/7.49  --prep_res_sim                          true
% 55.31/7.49  --prep_upred                            true
% 55.31/7.49  --prep_sem_filter                       exhaustive
% 55.31/7.49  --prep_sem_filter_out                   false
% 55.31/7.49  --pred_elim                             true
% 55.31/7.49  --res_sim_input                         true
% 55.31/7.49  --eq_ax_congr_red                       true
% 55.31/7.49  --pure_diseq_elim                       true
% 55.31/7.49  --brand_transform                       false
% 55.31/7.49  --non_eq_to_eq                          false
% 55.31/7.49  --prep_def_merge                        true
% 55.31/7.49  --prep_def_merge_prop_impl              false
% 55.31/7.49  --prep_def_merge_mbd                    true
% 55.31/7.49  --prep_def_merge_tr_red                 false
% 55.31/7.49  --prep_def_merge_tr_cl                  false
% 55.31/7.49  --smt_preprocessing                     true
% 55.31/7.49  --smt_ac_axioms                         fast
% 55.31/7.49  --preprocessed_out                      false
% 55.31/7.49  --preprocessed_stats                    false
% 55.31/7.49  
% 55.31/7.49  ------ Abstraction refinement Options
% 55.31/7.49  
% 55.31/7.49  --abstr_ref                             []
% 55.31/7.49  --abstr_ref_prep                        false
% 55.31/7.49  --abstr_ref_until_sat                   false
% 55.31/7.49  --abstr_ref_sig_restrict                funpre
% 55.31/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 55.31/7.49  --abstr_ref_under                       []
% 55.31/7.49  
% 55.31/7.49  ------ SAT Options
% 55.31/7.49  
% 55.31/7.49  --sat_mode                              false
% 55.31/7.49  --sat_fm_restart_options                ""
% 55.31/7.49  --sat_gr_def                            false
% 55.31/7.49  --sat_epr_types                         true
% 55.31/7.49  --sat_non_cyclic_types                  false
% 55.31/7.49  --sat_finite_models                     false
% 55.31/7.49  --sat_fm_lemmas                         false
% 55.31/7.49  --sat_fm_prep                           false
% 55.31/7.49  --sat_fm_uc_incr                        true
% 55.31/7.49  --sat_out_model                         small
% 55.31/7.49  --sat_out_clauses                       false
% 55.31/7.49  
% 55.31/7.49  ------ QBF Options
% 55.31/7.49  
% 55.31/7.49  --qbf_mode                              false
% 55.31/7.49  --qbf_elim_univ                         false
% 55.31/7.49  --qbf_dom_inst                          none
% 55.31/7.49  --qbf_dom_pre_inst                      false
% 55.31/7.49  --qbf_sk_in                             false
% 55.31/7.49  --qbf_pred_elim                         true
% 55.31/7.49  --qbf_split                             512
% 55.31/7.49  
% 55.31/7.49  ------ BMC1 Options
% 55.31/7.49  
% 55.31/7.49  --bmc1_incremental                      false
% 55.31/7.49  --bmc1_axioms                           reachable_all
% 55.31/7.49  --bmc1_min_bound                        0
% 55.31/7.49  --bmc1_max_bound                        -1
% 55.31/7.49  --bmc1_max_bound_default                -1
% 55.31/7.49  --bmc1_symbol_reachability              true
% 55.31/7.49  --bmc1_property_lemmas                  false
% 55.31/7.49  --bmc1_k_induction                      false
% 55.31/7.49  --bmc1_non_equiv_states                 false
% 55.31/7.49  --bmc1_deadlock                         false
% 55.31/7.49  --bmc1_ucm                              false
% 55.31/7.49  --bmc1_add_unsat_core                   none
% 55.31/7.49  --bmc1_unsat_core_children              false
% 55.31/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 55.31/7.49  --bmc1_out_stat                         full
% 55.31/7.49  --bmc1_ground_init                      false
% 55.31/7.49  --bmc1_pre_inst_next_state              false
% 55.31/7.49  --bmc1_pre_inst_state                   false
% 55.31/7.49  --bmc1_pre_inst_reach_state             false
% 55.31/7.49  --bmc1_out_unsat_core                   false
% 55.31/7.49  --bmc1_aig_witness_out                  false
% 55.31/7.49  --bmc1_verbose                          false
% 55.31/7.49  --bmc1_dump_clauses_tptp                false
% 55.31/7.49  --bmc1_dump_unsat_core_tptp             false
% 55.31/7.49  --bmc1_dump_file                        -
% 55.31/7.49  --bmc1_ucm_expand_uc_limit              128
% 55.31/7.49  --bmc1_ucm_n_expand_iterations          6
% 55.31/7.49  --bmc1_ucm_extend_mode                  1
% 55.31/7.49  --bmc1_ucm_init_mode                    2
% 55.31/7.49  --bmc1_ucm_cone_mode                    none
% 55.31/7.49  --bmc1_ucm_reduced_relation_type        0
% 55.31/7.49  --bmc1_ucm_relax_model                  4
% 55.31/7.49  --bmc1_ucm_full_tr_after_sat            true
% 55.31/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 55.31/7.49  --bmc1_ucm_layered_model                none
% 55.31/7.49  --bmc1_ucm_max_lemma_size               10
% 55.31/7.49  
% 55.31/7.49  ------ AIG Options
% 55.31/7.49  
% 55.31/7.49  --aig_mode                              false
% 55.31/7.49  
% 55.31/7.49  ------ Instantiation Options
% 55.31/7.49  
% 55.31/7.49  --instantiation_flag                    true
% 55.31/7.49  --inst_sos_flag                         false
% 55.31/7.49  --inst_sos_phase                        true
% 55.31/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.31/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.31/7.49  --inst_lit_sel_side                     num_symb
% 55.31/7.49  --inst_solver_per_active                1400
% 55.31/7.49  --inst_solver_calls_frac                1.
% 55.31/7.49  --inst_passive_queue_type               priority_queues
% 55.31/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.31/7.49  --inst_passive_queues_freq              [25;2]
% 55.31/7.49  --inst_dismatching                      true
% 55.31/7.49  --inst_eager_unprocessed_to_passive     true
% 55.31/7.49  --inst_prop_sim_given                   true
% 55.31/7.49  --inst_prop_sim_new                     false
% 55.31/7.49  --inst_subs_new                         false
% 55.31/7.49  --inst_eq_res_simp                      false
% 55.31/7.49  --inst_subs_given                       false
% 55.31/7.49  --inst_orphan_elimination               true
% 55.31/7.49  --inst_learning_loop_flag               true
% 55.31/7.49  --inst_learning_start                   3000
% 55.31/7.49  --inst_learning_factor                  2
% 55.31/7.49  --inst_start_prop_sim_after_learn       3
% 55.31/7.49  --inst_sel_renew                        solver
% 55.31/7.49  --inst_lit_activity_flag                true
% 55.31/7.49  --inst_restr_to_given                   false
% 55.31/7.49  --inst_activity_threshold               500
% 55.31/7.49  --inst_out_proof                        true
% 55.31/7.49  
% 55.31/7.49  ------ Resolution Options
% 55.31/7.49  
% 55.31/7.49  --resolution_flag                       true
% 55.31/7.49  --res_lit_sel                           adaptive
% 55.31/7.49  --res_lit_sel_side                      none
% 55.31/7.49  --res_ordering                          kbo
% 55.31/7.49  --res_to_prop_solver                    active
% 55.31/7.49  --res_prop_simpl_new                    false
% 55.31/7.49  --res_prop_simpl_given                  true
% 55.31/7.49  --res_passive_queue_type                priority_queues
% 55.31/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.31/7.49  --res_passive_queues_freq               [15;5]
% 55.31/7.49  --res_forward_subs                      full
% 55.31/7.49  --res_backward_subs                     full
% 55.31/7.49  --res_forward_subs_resolution           true
% 55.31/7.49  --res_backward_subs_resolution          true
% 55.31/7.49  --res_orphan_elimination                true
% 55.31/7.49  --res_time_limit                        2.
% 55.31/7.49  --res_out_proof                         true
% 55.31/7.49  
% 55.31/7.49  ------ Superposition Options
% 55.31/7.49  
% 55.31/7.49  --superposition_flag                    true
% 55.31/7.49  --sup_passive_queue_type                priority_queues
% 55.31/7.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.31/7.49  --sup_passive_queues_freq               [8;1;4]
% 55.31/7.49  --demod_completeness_check              fast
% 55.31/7.49  --demod_use_ground                      true
% 55.31/7.49  --sup_to_prop_solver                    passive
% 55.31/7.49  --sup_prop_simpl_new                    true
% 55.31/7.49  --sup_prop_simpl_given                  true
% 55.31/7.49  --sup_fun_splitting                     false
% 55.31/7.49  --sup_smt_interval                      50000
% 55.31/7.49  
% 55.31/7.49  ------ Superposition Simplification Setup
% 55.31/7.49  
% 55.31/7.49  --sup_indices_passive                   []
% 55.31/7.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.31/7.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.31/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.31/7.49  --sup_full_triv                         [TrivRules;PropSubs]
% 55.31/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.31/7.49  --sup_full_bw                           [BwDemod]
% 55.31/7.49  --sup_immed_triv                        [TrivRules]
% 55.31/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.31/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.31/7.49  --sup_immed_bw_main                     []
% 55.31/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.31/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 55.31/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.31/7.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.31/7.49  
% 55.31/7.49  ------ Combination Options
% 55.31/7.49  
% 55.31/7.49  --comb_res_mult                         3
% 55.31/7.49  --comb_sup_mult                         2
% 55.31/7.49  --comb_inst_mult                        10
% 55.31/7.49  
% 55.31/7.49  ------ Debug Options
% 55.31/7.49  
% 55.31/7.49  --dbg_backtrace                         false
% 55.31/7.49  --dbg_dump_prop_clauses                 false
% 55.31/7.49  --dbg_dump_prop_clauses_file            -
% 55.31/7.49  --dbg_out_stat                          false
% 55.31/7.49  ------ Parsing...
% 55.31/7.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.31/7.49  
% 55.31/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 55.31/7.49  
% 55.31/7.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.31/7.49  
% 55.31/7.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 55.31/7.49  ------ Proving...
% 55.31/7.49  ------ Problem Properties 
% 55.31/7.49  
% 55.31/7.49  
% 55.31/7.49  clauses                                 14
% 55.31/7.49  conjectures                             1
% 55.31/7.49  EPR                                     0
% 55.31/7.49  Horn                                    14
% 55.31/7.49  unary                                   14
% 55.31/7.49  binary                                  0
% 55.31/7.49  lits                                    14
% 55.31/7.49  lits eq                                 14
% 55.31/7.49  fd_pure                                 0
% 55.31/7.49  fd_pseudo                               0
% 55.31/7.49  fd_cond                                 0
% 55.31/7.49  fd_pseudo_cond                          0
% 55.31/7.49  AC symbols                              1
% 55.31/7.49  
% 55.31/7.49  ------ Schedule UEQ
% 55.31/7.49  
% 55.31/7.49  ------ pure equality problem: resolution off 
% 55.31/7.49  
% 55.31/7.49  ------ Option_UEQ Time Limit: Unbounded
% 55.31/7.49  
% 55.31/7.49  
% 55.31/7.49  ------ 
% 55.31/7.49  Current options:
% 55.31/7.49  ------ 
% 55.31/7.49  
% 55.31/7.49  ------ Input Options
% 55.31/7.49  
% 55.31/7.49  --out_options                           all
% 55.31/7.49  --tptp_safe_out                         true
% 55.31/7.49  --problem_path                          ""
% 55.31/7.49  --include_path                          ""
% 55.31/7.49  --clausifier                            res/vclausify_rel
% 55.31/7.49  --clausifier_options                    --mode clausify
% 55.31/7.49  --stdin                                 false
% 55.31/7.49  --stats_out                             all
% 55.31/7.49  
% 55.31/7.49  ------ General Options
% 55.31/7.49  
% 55.31/7.49  --fof                                   false
% 55.31/7.49  --time_out_real                         305.
% 55.31/7.49  --time_out_virtual                      -1.
% 55.31/7.49  --symbol_type_check                     false
% 55.31/7.49  --clausify_out                          false
% 55.31/7.49  --sig_cnt_out                           false
% 55.31/7.49  --trig_cnt_out                          false
% 55.31/7.49  --trig_cnt_out_tolerance                1.
% 55.31/7.49  --trig_cnt_out_sk_spl                   false
% 55.31/7.49  --abstr_cl_out                          false
% 55.31/7.49  
% 55.31/7.49  ------ Global Options
% 55.31/7.49  
% 55.31/7.49  --schedule                              default
% 55.31/7.49  --add_important_lit                     false
% 55.31/7.49  --prop_solver_per_cl                    1000
% 55.31/7.49  --min_unsat_core                        false
% 55.31/7.49  --soft_assumptions                      false
% 55.31/7.49  --soft_lemma_size                       3
% 55.31/7.49  --prop_impl_unit_size                   0
% 55.31/7.49  --prop_impl_unit                        []
% 55.31/7.49  --share_sel_clauses                     true
% 55.31/7.49  --reset_solvers                         false
% 55.31/7.49  --bc_imp_inh                            [conj_cone]
% 55.31/7.49  --conj_cone_tolerance                   3.
% 55.31/7.49  --extra_neg_conj                        none
% 55.31/7.49  --large_theory_mode                     true
% 55.31/7.49  --prolific_symb_bound                   200
% 55.31/7.49  --lt_threshold                          2000
% 55.31/7.49  --clause_weak_htbl                      true
% 55.31/7.49  --gc_record_bc_elim                     false
% 55.31/7.49  
% 55.31/7.49  ------ Preprocessing Options
% 55.31/7.49  
% 55.31/7.49  --preprocessing_flag                    true
% 55.31/7.49  --time_out_prep_mult                    0.1
% 55.31/7.49  --splitting_mode                        input
% 55.31/7.49  --splitting_grd                         true
% 55.31/7.49  --splitting_cvd                         false
% 55.31/7.49  --splitting_cvd_svl                     false
% 55.31/7.49  --splitting_nvd                         32
% 55.31/7.49  --sub_typing                            true
% 55.31/7.49  --prep_gs_sim                           true
% 55.31/7.49  --prep_unflatten                        true
% 55.31/7.49  --prep_res_sim                          true
% 55.31/7.49  --prep_upred                            true
% 55.31/7.49  --prep_sem_filter                       exhaustive
% 55.31/7.49  --prep_sem_filter_out                   false
% 55.31/7.49  --pred_elim                             true
% 55.31/7.49  --res_sim_input                         true
% 55.31/7.49  --eq_ax_congr_red                       true
% 55.31/7.49  --pure_diseq_elim                       true
% 55.31/7.49  --brand_transform                       false
% 55.31/7.49  --non_eq_to_eq                          false
% 55.31/7.49  --prep_def_merge                        true
% 55.31/7.49  --prep_def_merge_prop_impl              false
% 55.31/7.49  --prep_def_merge_mbd                    true
% 55.31/7.49  --prep_def_merge_tr_red                 false
% 55.31/7.49  --prep_def_merge_tr_cl                  false
% 55.31/7.49  --smt_preprocessing                     true
% 55.31/7.49  --smt_ac_axioms                         fast
% 55.31/7.49  --preprocessed_out                      false
% 55.31/7.49  --preprocessed_stats                    false
% 55.31/7.49  
% 55.31/7.49  ------ Abstraction refinement Options
% 55.31/7.49  
% 55.31/7.49  --abstr_ref                             []
% 55.31/7.49  --abstr_ref_prep                        false
% 55.31/7.49  --abstr_ref_until_sat                   false
% 55.31/7.49  --abstr_ref_sig_restrict                funpre
% 55.31/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 55.31/7.49  --abstr_ref_under                       []
% 55.31/7.49  
% 55.31/7.49  ------ SAT Options
% 55.31/7.49  
% 55.31/7.49  --sat_mode                              false
% 55.31/7.49  --sat_fm_restart_options                ""
% 55.31/7.49  --sat_gr_def                            false
% 55.31/7.49  --sat_epr_types                         true
% 55.31/7.49  --sat_non_cyclic_types                  false
% 55.31/7.49  --sat_finite_models                     false
% 55.31/7.49  --sat_fm_lemmas                         false
% 55.31/7.49  --sat_fm_prep                           false
% 55.31/7.49  --sat_fm_uc_incr                        true
% 55.31/7.49  --sat_out_model                         small
% 55.31/7.49  --sat_out_clauses                       false
% 55.31/7.49  
% 55.31/7.49  ------ QBF Options
% 55.31/7.49  
% 55.31/7.49  --qbf_mode                              false
% 55.31/7.49  --qbf_elim_univ                         false
% 55.31/7.49  --qbf_dom_inst                          none
% 55.31/7.49  --qbf_dom_pre_inst                      false
% 55.31/7.49  --qbf_sk_in                             false
% 55.31/7.49  --qbf_pred_elim                         true
% 55.31/7.49  --qbf_split                             512
% 55.31/7.49  
% 55.31/7.49  ------ BMC1 Options
% 55.31/7.49  
% 55.31/7.49  --bmc1_incremental                      false
% 55.31/7.49  --bmc1_axioms                           reachable_all
% 55.31/7.49  --bmc1_min_bound                        0
% 55.31/7.49  --bmc1_max_bound                        -1
% 55.31/7.49  --bmc1_max_bound_default                -1
% 55.31/7.49  --bmc1_symbol_reachability              true
% 55.31/7.49  --bmc1_property_lemmas                  false
% 55.31/7.49  --bmc1_k_induction                      false
% 55.31/7.49  --bmc1_non_equiv_states                 false
% 55.31/7.49  --bmc1_deadlock                         false
% 55.31/7.49  --bmc1_ucm                              false
% 55.31/7.49  --bmc1_add_unsat_core                   none
% 55.31/7.49  --bmc1_unsat_core_children              false
% 55.31/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 55.31/7.49  --bmc1_out_stat                         full
% 55.31/7.49  --bmc1_ground_init                      false
% 55.31/7.49  --bmc1_pre_inst_next_state              false
% 55.31/7.49  --bmc1_pre_inst_state                   false
% 55.31/7.49  --bmc1_pre_inst_reach_state             false
% 55.31/7.49  --bmc1_out_unsat_core                   false
% 55.31/7.49  --bmc1_aig_witness_out                  false
% 55.31/7.49  --bmc1_verbose                          false
% 55.31/7.49  --bmc1_dump_clauses_tptp                false
% 55.31/7.49  --bmc1_dump_unsat_core_tptp             false
% 55.31/7.49  --bmc1_dump_file                        -
% 55.31/7.49  --bmc1_ucm_expand_uc_limit              128
% 55.31/7.49  --bmc1_ucm_n_expand_iterations          6
% 55.31/7.49  --bmc1_ucm_extend_mode                  1
% 55.31/7.49  --bmc1_ucm_init_mode                    2
% 55.31/7.49  --bmc1_ucm_cone_mode                    none
% 55.31/7.49  --bmc1_ucm_reduced_relation_type        0
% 55.31/7.49  --bmc1_ucm_relax_model                  4
% 55.31/7.49  --bmc1_ucm_full_tr_after_sat            true
% 55.31/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 55.31/7.49  --bmc1_ucm_layered_model                none
% 55.31/7.49  --bmc1_ucm_max_lemma_size               10
% 55.31/7.49  
% 55.31/7.49  ------ AIG Options
% 55.31/7.49  
% 55.31/7.49  --aig_mode                              false
% 55.31/7.49  
% 55.31/7.49  ------ Instantiation Options
% 55.31/7.49  
% 55.31/7.49  --instantiation_flag                    false
% 55.31/7.49  --inst_sos_flag                         false
% 55.31/7.49  --inst_sos_phase                        true
% 55.31/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.31/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.31/7.49  --inst_lit_sel_side                     num_symb
% 55.31/7.49  --inst_solver_per_active                1400
% 55.31/7.49  --inst_solver_calls_frac                1.
% 55.31/7.49  --inst_passive_queue_type               priority_queues
% 55.31/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.31/7.49  --inst_passive_queues_freq              [25;2]
% 55.31/7.49  --inst_dismatching                      true
% 55.31/7.49  --inst_eager_unprocessed_to_passive     true
% 55.31/7.49  --inst_prop_sim_given                   true
% 55.31/7.49  --inst_prop_sim_new                     false
% 55.31/7.49  --inst_subs_new                         false
% 55.31/7.49  --inst_eq_res_simp                      false
% 55.31/7.49  --inst_subs_given                       false
% 55.31/7.49  --inst_orphan_elimination               true
% 55.31/7.49  --inst_learning_loop_flag               true
% 55.31/7.49  --inst_learning_start                   3000
% 55.31/7.49  --inst_learning_factor                  2
% 55.31/7.49  --inst_start_prop_sim_after_learn       3
% 55.31/7.49  --inst_sel_renew                        solver
% 55.31/7.49  --inst_lit_activity_flag                true
% 55.31/7.49  --inst_restr_to_given                   false
% 55.31/7.49  --inst_activity_threshold               500
% 55.31/7.49  --inst_out_proof                        true
% 55.31/7.49  
% 55.31/7.49  ------ Resolution Options
% 55.31/7.49  
% 55.31/7.49  --resolution_flag                       false
% 55.31/7.49  --res_lit_sel                           adaptive
% 55.31/7.49  --res_lit_sel_side                      none
% 55.31/7.49  --res_ordering                          kbo
% 55.31/7.49  --res_to_prop_solver                    active
% 55.31/7.49  --res_prop_simpl_new                    false
% 55.31/7.49  --res_prop_simpl_given                  true
% 55.31/7.49  --res_passive_queue_type                priority_queues
% 55.31/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.31/7.49  --res_passive_queues_freq               [15;5]
% 55.31/7.49  --res_forward_subs                      full
% 55.31/7.49  --res_backward_subs                     full
% 55.31/7.49  --res_forward_subs_resolution           true
% 55.31/7.49  --res_backward_subs_resolution          true
% 55.31/7.49  --res_orphan_elimination                true
% 55.31/7.49  --res_time_limit                        2.
% 55.31/7.49  --res_out_proof                         true
% 55.31/7.49  
% 55.31/7.49  ------ Superposition Options
% 55.31/7.49  
% 55.31/7.49  --superposition_flag                    true
% 55.31/7.49  --sup_passive_queue_type                priority_queues
% 55.31/7.49  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.31/7.49  --sup_passive_queues_freq               [8;1;4]
% 55.31/7.49  --demod_completeness_check              fast
% 55.31/7.49  --demod_use_ground                      true
% 55.31/7.49  --sup_to_prop_solver                    active
% 55.31/7.49  --sup_prop_simpl_new                    false
% 55.31/7.49  --sup_prop_simpl_given                  false
% 55.31/7.49  --sup_fun_splitting                     true
% 55.31/7.49  --sup_smt_interval                      10000
% 55.31/7.49  
% 55.31/7.49  ------ Superposition Simplification Setup
% 55.31/7.49  
% 55.31/7.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.31/7.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.31/7.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.31/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.31/7.49  --sup_full_triv                         [TrivRules]
% 55.31/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.31/7.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.31/7.49  --sup_immed_triv                        [TrivRules]
% 55.31/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.31/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.31/7.49  --sup_immed_bw_main                     []
% 55.31/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.31/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 55.31/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.31/7.49  --sup_input_bw                          [BwDemod;BwSubsumption]
% 55.31/7.49  
% 55.31/7.49  ------ Combination Options
% 55.31/7.49  
% 55.31/7.49  --comb_res_mult                         1
% 55.31/7.49  --comb_sup_mult                         1
% 55.31/7.49  --comb_inst_mult                        1000000
% 55.31/7.49  
% 55.31/7.49  ------ Debug Options
% 55.31/7.49  
% 55.31/7.49  --dbg_backtrace                         false
% 55.31/7.49  --dbg_dump_prop_clauses                 false
% 55.31/7.49  --dbg_dump_prop_clauses_file            -
% 55.31/7.49  --dbg_out_stat                          false
% 55.31/7.49  
% 55.31/7.49  
% 55.31/7.49  
% 55.31/7.49  
% 55.31/7.49  ------ Proving...
% 55.31/7.49  
% 55.31/7.49  
% 55.31/7.49  % SZS status Theorem for theBenchmark.p
% 55.31/7.49  
% 55.31/7.49   Resolution empty clause
% 55.31/7.49  
% 55.31/7.49  % SZS output start CNFRefutation for theBenchmark.p
% 55.31/7.49  
% 55.31/7.49  fof(f15,axiom,(
% 55.31/7.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f38,plain,(
% 55.31/7.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 55.31/7.49    inference(cnf_transformation,[],[f15])).
% 55.31/7.49  
% 55.31/7.49  fof(f2,axiom,(
% 55.31/7.49    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f25,plain,(
% 55.31/7.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 55.31/7.49    inference(cnf_transformation,[],[f2])).
% 55.31/7.49  
% 55.31/7.49  fof(f41,plain,(
% 55.31/7.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1))) )),
% 55.31/7.49    inference(definition_unfolding,[],[f38,f25])).
% 55.31/7.49  
% 55.31/7.49  fof(f11,axiom,(
% 55.31/7.49    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f34,plain,(
% 55.31/7.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 55.31/7.49    inference(cnf_transformation,[],[f11])).
% 55.31/7.49  
% 55.31/7.49  fof(f1,axiom,(
% 55.31/7.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f24,plain,(
% 55.31/7.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 55.31/7.49    inference(cnf_transformation,[],[f1])).
% 55.31/7.49  
% 55.31/7.49  fof(f12,axiom,(
% 55.31/7.49    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f35,plain,(
% 55.31/7.49    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 55.31/7.49    inference(cnf_transformation,[],[f12])).
% 55.31/7.49  
% 55.31/7.49  fof(f14,axiom,(
% 55.31/7.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f37,plain,(
% 55.31/7.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 55.31/7.49    inference(cnf_transformation,[],[f14])).
% 55.31/7.49  
% 55.31/7.49  fof(f40,plain,(
% 55.31/7.49    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k1_xboole_0) )),
% 55.31/7.49    inference(definition_unfolding,[],[f37,f25])).
% 55.31/7.49  
% 55.31/7.49  fof(f3,axiom,(
% 55.31/7.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f18,plain,(
% 55.31/7.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 55.31/7.49    inference(rectify,[],[f3])).
% 55.31/7.49  
% 55.31/7.49  fof(f26,plain,(
% 55.31/7.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 55.31/7.49    inference(cnf_transformation,[],[f18])).
% 55.31/7.49  
% 55.31/7.49  fof(f7,axiom,(
% 55.31/7.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f30,plain,(
% 55.31/7.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 55.31/7.49    inference(cnf_transformation,[],[f7])).
% 55.31/7.49  
% 55.31/7.49  fof(f5,axiom,(
% 55.31/7.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f28,plain,(
% 55.31/7.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.31/7.49    inference(cnf_transformation,[],[f5])).
% 55.31/7.49  
% 55.31/7.49  fof(f8,axiom,(
% 55.31/7.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f31,plain,(
% 55.31/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 55.31/7.49    inference(cnf_transformation,[],[f8])).
% 55.31/7.49  
% 55.31/7.49  fof(f4,axiom,(
% 55.31/7.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f19,plain,(
% 55.31/7.49    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 55.31/7.49    inference(unused_predicate_definition_removal,[],[f4])).
% 55.31/7.49  
% 55.31/7.49  fof(f20,plain,(
% 55.31/7.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 55.31/7.49    inference(ennf_transformation,[],[f19])).
% 55.31/7.49  
% 55.31/7.49  fof(f27,plain,(
% 55.31/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 55.31/7.49    inference(cnf_transformation,[],[f20])).
% 55.31/7.49  
% 55.31/7.49  fof(f6,axiom,(
% 55.31/7.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f29,plain,(
% 55.31/7.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 55.31/7.49    inference(cnf_transformation,[],[f6])).
% 55.31/7.49  
% 55.31/7.49  fof(f9,axiom,(
% 55.31/7.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f32,plain,(
% 55.31/7.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 55.31/7.49    inference(cnf_transformation,[],[f9])).
% 55.31/7.49  
% 55.31/7.49  fof(f10,axiom,(
% 55.31/7.49    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f33,plain,(
% 55.31/7.49    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 55.31/7.49    inference(cnf_transformation,[],[f10])).
% 55.31/7.49  
% 55.31/7.49  fof(f16,conjecture,(
% 55.31/7.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f17,negated_conjecture,(
% 55.31/7.49    ~! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 55.31/7.49    inference(negated_conjecture,[],[f16])).
% 55.31/7.49  
% 55.31/7.49  fof(f21,plain,(
% 55.31/7.49    ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1)),
% 55.31/7.49    inference(ennf_transformation,[],[f17])).
% 55.31/7.49  
% 55.31/7.49  fof(f22,plain,(
% 55.31/7.49    ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1) => k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 55.31/7.49    introduced(choice_axiom,[])).
% 55.31/7.49  
% 55.31/7.49  fof(f23,plain,(
% 55.31/7.49    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 55.31/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 55.31/7.49  
% 55.31/7.49  fof(f39,plain,(
% 55.31/7.49    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 55.31/7.49    inference(cnf_transformation,[],[f23])).
% 55.31/7.49  
% 55.31/7.49  fof(f42,plain,(
% 55.31/7.49    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k3_xboole_0(sK0,sK1)),
% 55.31/7.49    inference(definition_unfolding,[],[f39,f25,f25])).
% 55.31/7.49  
% 55.31/7.49  fof(f13,axiom,(
% 55.31/7.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 55.31/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.49  
% 55.31/7.49  fof(f36,plain,(
% 55.31/7.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 55.31/7.49    inference(cnf_transformation,[],[f13])).
% 55.31/7.49  
% 55.31/7.49  cnf(c_13,plain,
% 55.31/7.49      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 55.31/7.49      inference(cnf_transformation,[],[f41]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_9,plain,
% 55.31/7.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(cnf_transformation,[],[f34]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_0,plain,
% 55.31/7.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(cnf_transformation,[],[f24]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_68,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 55.31/7.49      inference(theory_normalisation,[status(thm)],[c_13,c_9,c_0]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_78,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_245,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_78,c_68]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_10,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(cnf_transformation,[],[f35]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_248,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_245,c_10]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_12,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
% 55.31/7.49      inference(cnf_transformation,[],[f40]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1,plain,
% 55.31/7.49      ( k2_xboole_0(X0,X0) = X0 ),
% 55.31/7.49      inference(cnf_transformation,[],[f26]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_152,plain,
% 55.31/7.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_249,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_248,c_152]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_5,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.31/7.49      inference(cnf_transformation,[],[f30]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.31/7.49      inference(cnf_transformation,[],[f28]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_81,plain,
% 55.31/7.49      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_119,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_5,c_81]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_120,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_119,c_81]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_250,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_249,c_120]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_79,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_633,plain,
% 55.31/7.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_3,c_79]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1437,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_250,c_633]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1490,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_1437,c_633]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_6,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 55.31/7.49      inference(cnf_transformation,[],[f31]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_4453,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_1490,c_6]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_354,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_152,c_10]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_373,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_354,c_81]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_883,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_6,c_373]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_356,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_120,c_10]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_2,plain,
% 55.31/7.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 55.31/7.49      inference(cnf_transformation,[],[f27]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_4,plain,
% 55.31/7.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(cnf_transformation,[],[f29]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_55,plain,
% 55.31/7.49      ( X0 != X1
% 55.31/7.49      | k4_xboole_0(X0,X2) != X3
% 55.31/7.49      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 55.31/7.49      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_56,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 55.31/7.49      inference(unflattening,[status(thm)],[c_55]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_167,plain,
% 55.31/7.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_120,c_56]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_371,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_356,c_120,c_167]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_7,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(cnf_transformation,[],[f32]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_257,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_152,c_7]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_276,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_257,c_167]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_892,plain,
% 55.31/7.49      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k1_xboole_0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_276,c_373]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_918,plain,
% 55.31/7.49      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_892,c_120]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_960,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_918,c_10]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_886,plain,
% 55.31/7.49      ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_56,c_373]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_923,plain,
% 55.31/7.49      ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_886,c_3,c_7]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_905,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k4_xboole_0(X0,X1),X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_373,c_68]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_910,plain,
% 55.31/7.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k4_xboole_0(X0,X1),X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_905,c_56]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_924,plain,
% 55.31/7.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_923,c_910]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_896,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_373,c_250]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_925,plain,
% 55.31/7.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_924,c_896]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_118,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_56,c_5]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_121,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_118,c_3]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_926,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_925,c_121,c_633]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_966,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_960,c_926]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3277,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_371,c_966]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_4496,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_4453,c_883,c_3277]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_10006,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_68,c_4496]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_8,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 55.31/7.49      inference(cnf_transformation,[],[f33]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3299,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,k2_xboole_0(X1,X3))),X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_966,c_8]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_10195,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1))))),X1) = k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_10006,c_7,c_3299]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_10196,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)))),X1) = k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_10195,c_373]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1028,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_926,c_79]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_10197,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X1)),X1) = k2_xboole_0(k4_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_10196,c_1028]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_268,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_7,c_56]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_465,plain,
% 55.31/7.49      ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_371,c_268]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_894,plain,
% 55.31/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_465,c_373]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_916,plain,
% 55.31/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_894,c_120]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_2561,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X0),k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_916,c_68]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1009,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_373,c_926]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_2563,plain,
% 55.31/7.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))) = X0 ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_2561,c_465,c_1009]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_2564,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X1)) = X0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_2563,c_10,c_81,c_633]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3337,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X1),X0) = k4_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_2564,c_3277]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_258,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_56,c_7]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_275,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_258,c_7,c_167]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1539,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_1009,c_275]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3372,plain,
% 55.31/7.49      ( k4_xboole_0(k3_xboole_0(X0,X1),X1) = k1_xboole_0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_3337,c_1539]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3450,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X1,X0)),k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(X1,X0)))) = k2_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_3372,c_68]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_928,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_926,c_896]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_80,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_2637,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k3_xboole_0(X0,X1))) = k2_xboole_0(X2,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_928,c_80]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3456,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_3450,c_81,c_2637]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_229,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_1,c_78]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3503,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k3_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_3456,c_229]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3524,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_3503,c_3456]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_10198,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0 ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_10197,c_3524]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_14228,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X1,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_10198,c_4496]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_122,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_890,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_122,c_373]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_124,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_179,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) = k2_xboole_0(X0,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_152,c_68]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_180,plain,
% 55.31/7.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) = k2_xboole_0(X0,X0) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_179,c_152]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_181,plain,
% 55.31/7.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) = X0 ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_180,c_1]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_182,plain,
% 55.31/7.49      ( k3_xboole_0(X0,X0) = X0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_181,c_81]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_358,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_182,c_10]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_920,plain,
% 55.31/7.49      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_890,c_124,c_358]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_927,plain,
% 55.31/7.49      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_926,c_920]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1059,plain,
% 55.31/7.49      ( k3_xboole_0(k2_xboole_0(X0,X1),X1) = X1 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_229,c_927]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3491,plain,
% 55.31/7.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_3456,c_1059]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_6916,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_3491,c_10]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_518,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_5,c_122]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_547,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_518,c_122]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_264,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_7,c_56]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3055,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) = k1_xboole_0 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_547,c_264]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_884,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k3_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_7,c_373]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3178,plain,
% 55.31/7.49      ( k3_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k1_xboole_0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_3055,c_7,c_884]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_3744,plain,
% 55.31/7.49      ( k3_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k1_xboole_0 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_1009,c_3178]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_5457,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_124,c_124,c_3277]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_5504,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_373,c_5457]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_5593,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_5504,c_926]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_10775,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_3744,c_5593]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_10865,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_10775,c_3,c_7]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_14319,plain,
% 55.31/7.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_14228,c_373,c_6916,c_10865]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_10110,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_4496,c_7]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_14,negated_conjecture,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k3_xboole_0(sK0,sK1) ),
% 55.31/7.49      inference(cnf_transformation,[],[f42]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_67,negated_conjecture,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k3_xboole_0(sK0,sK1) ),
% 55.31/7.49      inference(theory_normalisation,[status(thm)],[c_14,c_9,c_0]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_266653,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k3_xboole_0(sK0,sK1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_10110,c_67]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_2264,plain,
% 55.31/7.49      ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_373,c_547]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_2311,plain,
% 55.31/7.49      ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_2264,c_373]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_329,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_49308,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k3_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_2311,c_329]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_42883,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k3_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_2311,c_8]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_907,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_373,c_8]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_42905,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k3_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_42883,c_907]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_49758,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X2,X0),k4_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_49308,c_42905]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_904,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_373,c_5]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_929,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_926,c_904]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_265,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_7,c_5]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_40745,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_929,c_265]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_49759,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_49758,c_40745]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_321,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_323,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_56,c_8]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_341,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_323,c_3]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_4948,plain,
% 55.31/7.49      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_341,c_1490]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_632,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_1,c_79]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1342,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_79,c_632]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_11,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 55.31/7.49      inference(cnf_transformation,[],[f36]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1081,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_11,c_80]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_130,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_132,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_130,c_5]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1087,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_132,c_80]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_684,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_132,c_9]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_702,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_684,c_9]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_735,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_229,c_9]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_759,plain,
% 55.31/7.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_735,c_702]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1152,plain,
% 55.31/7.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_1087,c_632,c_702,c_759]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1155,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_1081,c_1152]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1399,plain,
% 55.31/7.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_1342,c_1155]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_4968,plain,
% 55.31/7.49      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X0,X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_4948,c_1399,c_1490]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_72549,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3),X1) = k2_xboole_0(k4_xboole_0(X0,X3),X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_321,c_4968]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_328,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_337,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_328,c_5,c_7]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_89842,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X3)),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X3)),k4_xboole_0(X1,k2_xboole_0(X3,X2))) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_337,c_8]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_314,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_348,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_314,c_329]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_349,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_348,c_9]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_54090,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X3)),k4_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X3),X0),k4_xboole_0(X2,X3)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_329,c_349]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_89882,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X3,X2),X0),k4_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_89842,c_54090]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_266654,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK1)) != k3_xboole_0(sK0,sK1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_266653,c_49759,c_72549,c_89882]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_5547,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_5457,c_7]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_207336,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_250,c_5547]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_232,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_11,c_78]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_293,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_9,c_6]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_48219,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_232,c_293]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_669,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_5,c_132]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_709,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_669,c_250]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_243,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_78,c_6]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_28761,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_709,c_243]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_127,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X1)),k3_xboole_0(k2_xboole_0(X0,X1),X1))) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_6,c_68]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_442,plain,
% 55.31/7.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_276,c_5]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_450,plain,
% 55.31/7.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_442,c_3]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1255,plain,
% 55.31/7.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_0,c_450]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_7213,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X1)),X1)) = k2_xboole_0(X1,X0) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_127,c_127,c_1059,c_1255]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_4482,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_1490,c_80]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1417,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_5,c_633]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1502,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_1417,c_633]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_4527,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_7,c_1502]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_7214,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_7213,c_4482,c_4527]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_530,plain,
% 55.31/7.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_122,c_121]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_22051,plain,
% 55.31/7.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_530,c_80]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_28970,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_28761,c_7214,c_22051]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_48583,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_48219,c_28970]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_208572,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_207336,c_3277,c_48583]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_266655,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))) != k3_xboole_0(sK0,sK1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_266654,c_208572]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_14255,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_10198,c_132]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_14295,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X1 ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_14255,c_3524]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_15502,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X0)),k1_xboole_0) = k3_xboole_0(X1,X0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_3372,c_14295]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1522,plain,
% 55.31/7.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_1009,c_927]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_14512,plain,
% 55.31/7.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_14319,c_1522]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_15615,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,X0) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_15502,c_14512]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_16358,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_15615,c_78]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_16381,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X2,X1),X0) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_16358,c_3]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_37309,plain,
% 55.31/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X2,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_16381,c_10]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_286,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_5,c_9]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_309,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_286,c_9]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_48855,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_309,c_243]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_242,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_78,c_11]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_48218,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_242,c_293]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_48584,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_48218,c_48583]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_48984,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_48855,c_48584]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_266656,plain,
% 55.31/7.49      ( k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)) != k3_xboole_0(sK0,sK1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_266655,c_37309,c_48984]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_436,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_276,c_10]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_456,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,X2) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_436,c_81]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_290,plain,
% 55.31/7.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_121,c_9]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_1055,plain,
% 55.31/7.49      ( k3_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = X1 ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_78,c_927]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_4083,plain,
% 55.31/7.49      ( k3_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_290,c_1055]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_63215,plain,
% 55.31/7.49      ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X3),X2)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_456,c_4083]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_498,plain,
% 55.31/7.49      ( k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_465,c_7]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_511,plain,
% 55.31/7.49      ( k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_498,c_167]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_14249,plain,
% 55.31/7.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_10198,c_6]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_14301,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_14249,c_10865]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_15715,plain,
% 55.31/7.49      ( k4_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X1),k4_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_14301,c_5457]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_15748,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_15715,c_3524]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_17700,plain,
% 55.31/7.49      ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(k3_xboole_0(X0,X2),k1_xboole_0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_511,c_15748]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_17707,plain,
% 55.31/7.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0) ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_3372,c_15748]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_17864,plain,
% 55.31/7.49      ( k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,X0) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_17707,c_14512]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_17868,plain,
% 55.31/7.49      ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,X0) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_17700,c_17864]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_63479,plain,
% 55.31/7.49      ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k3_xboole_0(X2,X0) ),
% 55.31/7.49      inference(light_normalisation,[status(thm)],[c_63215,c_17868]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_266657,plain,
% 55.31/7.49      ( k3_xboole_0(sK1,sK0) != k3_xboole_0(sK0,sK1) ),
% 55.31/7.49      inference(demodulation,[status(thm)],[c_266656,c_63479]) ).
% 55.31/7.49  
% 55.31/7.49  cnf(c_268042,plain,
% 55.31/7.49      ( $false ),
% 55.31/7.49      inference(superposition,[status(thm)],[c_14319,c_266657]) ).
% 55.31/7.49  
% 55.31/7.49  
% 55.31/7.49  % SZS output end CNFRefutation for theBenchmark.p
% 55.31/7.49  
% 55.31/7.49  ------                               Statistics
% 55.31/7.49  
% 55.31/7.49  ------ General
% 55.31/7.49  
% 55.31/7.49  abstr_ref_over_cycles:                  0
% 55.31/7.49  abstr_ref_under_cycles:                 0
% 55.31/7.49  gc_basic_clause_elim:                   0
% 55.31/7.49  forced_gc_time:                         0
% 55.31/7.49  parsing_time:                           0.008
% 55.31/7.49  unif_index_cands_time:                  0.
% 55.31/7.49  unif_index_add_time:                    0.
% 55.31/7.49  orderings_time:                         0.
% 55.31/7.49  out_proof_time:                         0.011
% 55.31/7.49  total_time:                             6.697
% 55.31/7.49  num_of_symbols:                         38
% 55.31/7.49  num_of_terms:                           360071
% 55.31/7.49  
% 55.31/7.49  ------ Preprocessing
% 55.31/7.49  
% 55.31/7.49  num_of_splits:                          0
% 55.31/7.49  num_of_split_atoms:                     0
% 55.31/7.49  num_of_reused_defs:                     0
% 55.31/7.49  num_eq_ax_congr_red:                    1
% 55.31/7.49  num_of_sem_filtered_clauses:            0
% 55.31/7.49  num_of_subtypes:                        0
% 55.31/7.49  monotx_restored_types:                  0
% 55.31/7.49  sat_num_of_epr_types:                   0
% 55.31/7.49  sat_num_of_non_cyclic_types:            0
% 55.31/7.49  sat_guarded_non_collapsed_types:        0
% 55.31/7.49  num_pure_diseq_elim:                    0
% 55.31/7.49  simp_replaced_by:                       0
% 55.31/7.49  res_preprocessed:                       48
% 55.31/7.49  prep_upred:                             0
% 55.31/7.49  prep_unflattend:                        2
% 55.31/7.49  smt_new_axioms:                         0
% 55.31/7.49  pred_elim_cands:                        0
% 55.31/7.49  pred_elim:                              1
% 55.31/7.49  pred_elim_cl:                           1
% 55.31/7.49  pred_elim_cycles:                       2
% 55.31/7.49  merged_defs:                            0
% 55.31/7.49  merged_defs_ncl:                        0
% 55.31/7.49  bin_hyper_res:                          0
% 55.31/7.49  prep_cycles:                            3
% 55.31/7.49  pred_elim_time:                         0.001
% 55.31/7.49  splitting_time:                         0.
% 55.31/7.49  sem_filter_time:                        0.
% 55.31/7.49  monotx_time:                            0.
% 55.31/7.49  subtype_inf_time:                       0.
% 55.31/7.49  
% 55.31/7.49  ------ Problem properties
% 55.31/7.49  
% 55.31/7.49  clauses:                                14
% 55.31/7.49  conjectures:                            1
% 55.31/7.49  epr:                                    0
% 55.31/7.49  horn:                                   14
% 55.31/7.49  ground:                                 1
% 55.31/7.49  unary:                                  14
% 55.31/7.49  binary:                                 0
% 55.31/7.49  lits:                                   14
% 55.31/7.49  lits_eq:                                14
% 55.31/7.49  fd_pure:                                0
% 55.31/7.49  fd_pseudo:                              0
% 55.31/7.49  fd_cond:                                0
% 55.31/7.49  fd_pseudo_cond:                         0
% 55.31/7.49  ac_symbols:                             1
% 55.31/7.49  
% 55.31/7.49  ------ Propositional Solver
% 55.31/7.49  
% 55.31/7.49  prop_solver_calls:                      17
% 55.31/7.49  prop_fast_solver_calls:                 115
% 55.31/7.49  smt_solver_calls:                       0
% 55.31/7.49  smt_fast_solver_calls:                  0
% 55.31/7.49  prop_num_of_clauses:                    866
% 55.31/7.49  prop_preprocess_simplified:             901
% 55.31/7.49  prop_fo_subsumed:                       0
% 55.31/7.49  prop_solver_time:                       0.
% 55.31/7.49  smt_solver_time:                        0.
% 55.31/7.49  smt_fast_solver_time:                   0.
% 55.31/7.49  prop_fast_solver_time:                  0.
% 55.31/7.49  prop_unsat_core_time:                   0.
% 55.31/7.49  
% 55.31/7.49  ------ QBF
% 55.31/7.49  
% 55.31/7.49  qbf_q_res:                              0
% 55.31/7.49  qbf_num_tautologies:                    0
% 55.31/7.49  qbf_prep_cycles:                        0
% 55.31/7.49  
% 55.31/7.49  ------ BMC1
% 55.31/7.49  
% 55.31/7.49  bmc1_current_bound:                     -1
% 55.31/7.49  bmc1_last_solved_bound:                 -1
% 55.31/7.49  bmc1_unsat_core_size:                   -1
% 55.31/7.49  bmc1_unsat_core_parents_size:           -1
% 55.31/7.49  bmc1_merge_next_fun:                    0
% 55.31/7.49  bmc1_unsat_core_clauses_time:           0.
% 55.31/7.49  
% 55.31/7.49  ------ Instantiation
% 55.31/7.49  
% 55.31/7.49  inst_num_of_clauses:                    0
% 55.31/7.49  inst_num_in_passive:                    0
% 55.31/7.49  inst_num_in_active:                     0
% 55.31/7.49  inst_num_in_unprocessed:                0
% 55.31/7.49  inst_num_of_loops:                      0
% 55.31/7.49  inst_num_of_learning_restarts:          0
% 55.31/7.49  inst_num_moves_active_passive:          0
% 55.31/7.49  inst_lit_activity:                      0
% 55.31/7.49  inst_lit_activity_moves:                0
% 55.31/7.49  inst_num_tautologies:                   0
% 55.31/7.49  inst_num_prop_implied:                  0
% 55.31/7.49  inst_num_existing_simplified:           0
% 55.31/7.49  inst_num_eq_res_simplified:             0
% 55.31/7.49  inst_num_child_elim:                    0
% 55.31/7.49  inst_num_of_dismatching_blockings:      0
% 55.31/7.49  inst_num_of_non_proper_insts:           0
% 55.31/7.49  inst_num_of_duplicates:                 0
% 55.31/7.49  inst_inst_num_from_inst_to_res:         0
% 55.31/7.49  inst_dismatching_checking_time:         0.
% 55.31/7.49  
% 55.31/7.49  ------ Resolution
% 55.31/7.49  
% 55.31/7.49  res_num_of_clauses:                     0
% 55.31/7.49  res_num_in_passive:                     0
% 55.31/7.49  res_num_in_active:                      0
% 55.31/7.49  res_num_of_loops:                       51
% 55.31/7.49  res_forward_subset_subsumed:            0
% 55.31/7.49  res_backward_subset_subsumed:           0
% 55.31/7.49  res_forward_subsumed:                   0
% 55.31/7.49  res_backward_subsumed:                  0
% 55.31/7.49  res_forward_subsumption_resolution:     0
% 55.31/7.49  res_backward_subsumption_resolution:    0
% 55.31/7.49  res_clause_to_clause_subsumption:       633836
% 55.31/7.49  res_orphan_elimination:                 0
% 55.31/7.49  res_tautology_del:                      0
% 55.31/7.49  res_num_eq_res_simplified:              0
% 55.31/7.49  res_num_sel_changes:                    0
% 55.31/7.49  res_moves_from_active_to_pass:          0
% 55.31/7.49  
% 55.31/7.49  ------ Superposition
% 55.31/7.49  
% 55.31/7.49  sup_time_total:                         0.
% 55.31/7.49  sup_time_generating:                    0.
% 55.31/7.49  sup_time_sim_full:                      0.
% 55.31/7.49  sup_time_sim_immed:                     0.
% 55.31/7.49  
% 55.31/7.49  sup_num_of_clauses:                     19825
% 55.31/7.49  sup_num_in_active:                      494
% 55.31/7.49  sup_num_in_passive:                     19331
% 55.31/7.49  sup_num_of_loops:                       537
% 55.31/7.49  sup_fw_superposition:                   102459
% 55.31/7.49  sup_bw_superposition:                   79094
% 55.31/7.49  sup_immediate_simplified:               81294
% 55.31/7.49  sup_given_eliminated:                   5
% 55.31/7.49  comparisons_done:                       0
% 55.31/7.49  comparisons_avoided:                    0
% 55.31/7.49  
% 55.31/7.49  ------ Simplifications
% 55.31/7.49  
% 55.31/7.49  
% 55.31/7.49  sim_fw_subset_subsumed:                 0
% 55.31/7.49  sim_bw_subset_subsumed:                 0
% 55.31/7.49  sim_fw_subsumed:                        11757
% 55.31/7.49  sim_bw_subsumed:                        146
% 55.31/7.49  sim_fw_subsumption_res:                 0
% 55.31/7.49  sim_bw_subsumption_res:                 0
% 55.31/7.49  sim_tautology_del:                      0
% 55.31/7.49  sim_eq_tautology_del:                   23724
% 55.31/7.49  sim_eq_res_simp:                        0
% 55.31/7.49  sim_fw_demodulated:                     49350
% 55.31/7.49  sim_bw_demodulated:                     401
% 55.31/7.49  sim_light_normalised:                   35830
% 55.31/7.49  sim_joinable_taut:                      819
% 55.31/7.49  sim_joinable_simp:                      0
% 55.31/7.49  sim_ac_normalised:                      0
% 55.31/7.49  sim_smt_subsumption:                    0
% 55.31/7.49  
%------------------------------------------------------------------------------
