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
% DateTime   : Thu Dec  3 11:25:07 EST 2020

% Result     : Theorem 11.31s
% Output     : CNFRefutation 11.31s
% Verified   : 
% Statistics : Number of formulae       :  141 (20658 expanded)
%              Number of clauses        :  105 (7620 expanded)
%              Number of leaves         :   14 (5734 expanded)
%              Depth                    :   33
%              Number of atoms          :  142 (20659 expanded)
%              Number of equality atoms :  141 (20658 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f19,f27])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f28,f19,f19,f19,f19])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f19,f27])).

fof(f13,conjecture,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1)
   => k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f30,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f30,f19,f19,f27])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_88,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_3])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_32,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_5,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_58,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_32,c_5])).

cnf(c_43,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_32])).

cnf(c_91,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_43])).

cnf(c_158,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_58,c_91])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_164,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_158,c_6])).

cnf(c_168,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_164,c_91])).

cnf(c_190,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_168])).

cnf(c_212,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_88,c_190])).

cnf(c_242,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_212,c_6])).

cnf(c_245,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_242,c_6,c_91])).

cnf(c_9,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_708,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_245,c_9])).

cnf(c_304,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_9])).

cnf(c_334,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_304,c_2,c_88,c_212])).

cnf(c_716,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_708,c_2,c_334])).

cnf(c_2130,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_716])).

cnf(c_2225,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2130,c_0])).

cnf(c_310,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_168,c_9])).

cnf(c_56,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_323,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_310,c_4,c_56])).

cnf(c_324,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_323,c_32])).

cnf(c_2321,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2225,c_324])).

cnf(c_64,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_76,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_64,c_6])).

cnf(c_5895,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
    inference(superposition,[status(thm)],[c_334,c_76])).

cnf(c_5991,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5895,c_334])).

cnf(c_13396,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X0),X1) ),
    inference(superposition,[status(thm)],[c_2321,c_5991])).

cnf(c_13488,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(k4_xboole_0(X0,X1),X3) ),
    inference(superposition,[status(thm)],[c_5991,c_6])).

cnf(c_2162,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_716,c_0])).

cnf(c_7140,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X3))) ),
    inference(superposition,[status(thm)],[c_2162,c_76])).

cnf(c_7167,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_7140,c_2162])).

cnf(c_13530,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_13488,c_7167])).

cnf(c_13553,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(demodulation,[status(thm)],[c_13396,c_13530])).

cnf(c_298,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_9])).

cnf(c_341,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_298,c_88,c_212])).

cnf(c_342,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_341,c_2])).

cnf(c_308,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_212,c_9])).

cnf(c_327,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_308,c_6,c_32])).

cnf(c_328,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_327,c_2])).

cnf(c_343,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_342,c_328])).

cnf(c_13554,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
    inference(light_normalisation,[status(thm)],[c_13553,c_343])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_20105,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(superposition,[status(thm)],[c_13554,c_8])).

cnf(c_20128,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X1),k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_20105,c_158])).

cnf(c_1669,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_324,c_5])).

cnf(c_1,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_197,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_168,c_1])).

cnf(c_204,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,X1),X0)) ),
    inference(demodulation,[status(thm)],[c_197,c_168])).

cnf(c_205,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_204,c_4,c_56])).

cnf(c_206,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_205,c_32,c_56])).

cnf(c_1688,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1669,c_206])).

cnf(c_2625,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_2321])).

cnf(c_20129,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_20128,c_4,c_32,c_91,c_1688,c_2625])).

cnf(c_21306,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_20129,c_13554])).

cnf(c_21341,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21306,c_158,c_13530])).

cnf(c_22150,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_21341,c_20129])).

cnf(c_2210,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_324,c_2130])).

cnf(c_2247,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(demodulation,[status(thm)],[c_2210,c_2225])).

cnf(c_178,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_88])).

cnf(c_1114,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_178])).

cnf(c_2248,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2247,c_1114])).

cnf(c_2406,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2248,c_0])).

cnf(c_21192,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1688,c_20129])).

cnf(c_21452,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_21192,c_13530])).

cnf(c_2661,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2321,c_0])).

cnf(c_21453,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_21452,c_2661])).

cnf(c_21454,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_21453,c_2,c_190])).

cnf(c_21680,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_21454,c_6])).

cnf(c_21813,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_2406,c_21680])).

cnf(c_165,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_158,c_3])).

cnf(c_167,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_165,c_4])).

cnf(c_67,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_75,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_67,c_6])).

cnf(c_4064,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_167,c_75])).

cnf(c_2198,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2130])).

cnf(c_309,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,X1),X1)),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_190,c_9])).

cnf(c_325,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_309,c_5])).

cnf(c_326,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_325,c_4,c_32])).

cnf(c_2367,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2248,c_326])).

cnf(c_2712,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2198,c_2367])).

cnf(c_2394,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2248,c_2198])).

cnf(c_2427,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2394,c_2406])).

cnf(c_2766,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2712,c_2427])).

cnf(c_4184,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_4064,c_2766])).

cnf(c_21978,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_21680,c_4184])).

cnf(c_22055,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_21813,c_21978])).

cnf(c_22305,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_22150,c_32,c_22055])).

cnf(c_228,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_212])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_31,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_10])).

cnf(c_17982,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_228,c_31])).

cnf(c_5867,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_2406,c_76])).

cnf(c_17983,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_17982,c_2,c_5867])).

cnf(c_21773,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_21680,c_17983])).

cnf(c_33414,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_22305,c_21773])).

cnf(c_33835,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_33414])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.31/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.31/1.99  
% 11.31/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.31/1.99  
% 11.31/1.99  ------  iProver source info
% 11.31/1.99  
% 11.31/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.31/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.31/1.99  git: non_committed_changes: false
% 11.31/1.99  git: last_make_outside_of_git: false
% 11.31/1.99  
% 11.31/1.99  ------ 
% 11.31/1.99  
% 11.31/1.99  ------ Input Options
% 11.31/1.99  
% 11.31/1.99  --out_options                           all
% 11.31/1.99  --tptp_safe_out                         true
% 11.31/1.99  --problem_path                          ""
% 11.31/1.99  --include_path                          ""
% 11.31/1.99  --clausifier                            res/vclausify_rel
% 11.31/1.99  --clausifier_options                    --mode clausify
% 11.31/1.99  --stdin                                 false
% 11.31/1.99  --stats_out                             all
% 11.31/1.99  
% 11.31/1.99  ------ General Options
% 11.31/1.99  
% 11.31/1.99  --fof                                   false
% 11.31/1.99  --time_out_real                         305.
% 11.31/1.99  --time_out_virtual                      -1.
% 11.31/1.99  --symbol_type_check                     false
% 11.31/1.99  --clausify_out                          false
% 11.31/1.99  --sig_cnt_out                           false
% 11.31/1.99  --trig_cnt_out                          false
% 11.31/1.99  --trig_cnt_out_tolerance                1.
% 11.31/1.99  --trig_cnt_out_sk_spl                   false
% 11.31/1.99  --abstr_cl_out                          false
% 11.31/1.99  
% 11.31/1.99  ------ Global Options
% 11.31/1.99  
% 11.31/1.99  --schedule                              default
% 11.31/1.99  --add_important_lit                     false
% 11.31/1.99  --prop_solver_per_cl                    1000
% 11.31/1.99  --min_unsat_core                        false
% 11.31/1.99  --soft_assumptions                      false
% 11.31/1.99  --soft_lemma_size                       3
% 11.31/1.99  --prop_impl_unit_size                   0
% 11.31/1.99  --prop_impl_unit                        []
% 11.31/1.99  --share_sel_clauses                     true
% 11.31/1.99  --reset_solvers                         false
% 11.31/1.99  --bc_imp_inh                            [conj_cone]
% 11.31/1.99  --conj_cone_tolerance                   3.
% 11.31/1.99  --extra_neg_conj                        none
% 11.31/1.99  --large_theory_mode                     true
% 11.31/1.99  --prolific_symb_bound                   200
% 11.31/1.99  --lt_threshold                          2000
% 11.31/1.99  --clause_weak_htbl                      true
% 11.31/1.99  --gc_record_bc_elim                     false
% 11.31/1.99  
% 11.31/1.99  ------ Preprocessing Options
% 11.31/1.99  
% 11.31/1.99  --preprocessing_flag                    true
% 11.31/1.99  --time_out_prep_mult                    0.1
% 11.31/1.99  --splitting_mode                        input
% 11.31/1.99  --splitting_grd                         true
% 11.31/1.99  --splitting_cvd                         false
% 11.31/1.99  --splitting_cvd_svl                     false
% 11.31/1.99  --splitting_nvd                         32
% 11.31/1.99  --sub_typing                            true
% 11.31/1.99  --prep_gs_sim                           true
% 11.31/1.99  --prep_unflatten                        true
% 11.31/1.99  --prep_res_sim                          true
% 11.31/1.99  --prep_upred                            true
% 11.31/1.99  --prep_sem_filter                       exhaustive
% 11.31/1.99  --prep_sem_filter_out                   false
% 11.31/1.99  --pred_elim                             true
% 11.31/1.99  --res_sim_input                         true
% 11.31/1.99  --eq_ax_congr_red                       true
% 11.31/1.99  --pure_diseq_elim                       true
% 11.31/1.99  --brand_transform                       false
% 11.31/1.99  --non_eq_to_eq                          false
% 11.31/1.99  --prep_def_merge                        true
% 11.31/1.99  --prep_def_merge_prop_impl              false
% 11.31/1.99  --prep_def_merge_mbd                    true
% 11.31/1.99  --prep_def_merge_tr_red                 false
% 11.31/1.99  --prep_def_merge_tr_cl                  false
% 11.31/1.99  --smt_preprocessing                     true
% 11.31/1.99  --smt_ac_axioms                         fast
% 11.31/1.99  --preprocessed_out                      false
% 11.31/1.99  --preprocessed_stats                    false
% 11.31/1.99  
% 11.31/1.99  ------ Abstraction refinement Options
% 11.31/1.99  
% 11.31/1.99  --abstr_ref                             []
% 11.31/1.99  --abstr_ref_prep                        false
% 11.31/1.99  --abstr_ref_until_sat                   false
% 11.31/1.99  --abstr_ref_sig_restrict                funpre
% 11.31/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.31/1.99  --abstr_ref_under                       []
% 11.31/1.99  
% 11.31/1.99  ------ SAT Options
% 11.31/1.99  
% 11.31/1.99  --sat_mode                              false
% 11.31/1.99  --sat_fm_restart_options                ""
% 11.31/1.99  --sat_gr_def                            false
% 11.31/1.99  --sat_epr_types                         true
% 11.31/1.99  --sat_non_cyclic_types                  false
% 11.31/1.99  --sat_finite_models                     false
% 11.31/1.99  --sat_fm_lemmas                         false
% 11.31/1.99  --sat_fm_prep                           false
% 11.31/1.99  --sat_fm_uc_incr                        true
% 11.31/1.99  --sat_out_model                         small
% 11.31/1.99  --sat_out_clauses                       false
% 11.31/1.99  
% 11.31/1.99  ------ QBF Options
% 11.31/1.99  
% 11.31/1.99  --qbf_mode                              false
% 11.31/1.99  --qbf_elim_univ                         false
% 11.31/1.99  --qbf_dom_inst                          none
% 11.31/1.99  --qbf_dom_pre_inst                      false
% 11.31/1.99  --qbf_sk_in                             false
% 11.31/1.99  --qbf_pred_elim                         true
% 11.31/1.99  --qbf_split                             512
% 11.31/1.99  
% 11.31/1.99  ------ BMC1 Options
% 11.31/1.99  
% 11.31/1.99  --bmc1_incremental                      false
% 11.31/1.99  --bmc1_axioms                           reachable_all
% 11.31/1.99  --bmc1_min_bound                        0
% 11.31/1.99  --bmc1_max_bound                        -1
% 11.31/1.99  --bmc1_max_bound_default                -1
% 11.31/1.99  --bmc1_symbol_reachability              true
% 11.31/1.99  --bmc1_property_lemmas                  false
% 11.31/1.99  --bmc1_k_induction                      false
% 11.31/1.99  --bmc1_non_equiv_states                 false
% 11.31/1.99  --bmc1_deadlock                         false
% 11.31/1.99  --bmc1_ucm                              false
% 11.31/1.99  --bmc1_add_unsat_core                   none
% 11.31/1.99  --bmc1_unsat_core_children              false
% 11.31/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.31/1.99  --bmc1_out_stat                         full
% 11.31/1.99  --bmc1_ground_init                      false
% 11.31/1.99  --bmc1_pre_inst_next_state              false
% 11.31/1.99  --bmc1_pre_inst_state                   false
% 11.31/1.99  --bmc1_pre_inst_reach_state             false
% 11.31/1.99  --bmc1_out_unsat_core                   false
% 11.31/1.99  --bmc1_aig_witness_out                  false
% 11.31/1.99  --bmc1_verbose                          false
% 11.31/1.99  --bmc1_dump_clauses_tptp                false
% 11.31/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.31/1.99  --bmc1_dump_file                        -
% 11.31/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.31/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.31/1.99  --bmc1_ucm_extend_mode                  1
% 11.31/1.99  --bmc1_ucm_init_mode                    2
% 11.31/1.99  --bmc1_ucm_cone_mode                    none
% 11.31/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.31/1.99  --bmc1_ucm_relax_model                  4
% 11.31/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.31/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.31/1.99  --bmc1_ucm_layered_model                none
% 11.31/1.99  --bmc1_ucm_max_lemma_size               10
% 11.31/1.99  
% 11.31/1.99  ------ AIG Options
% 11.31/1.99  
% 11.31/1.99  --aig_mode                              false
% 11.31/1.99  
% 11.31/1.99  ------ Instantiation Options
% 11.31/1.99  
% 11.31/1.99  --instantiation_flag                    true
% 11.31/1.99  --inst_sos_flag                         false
% 11.31/1.99  --inst_sos_phase                        true
% 11.31/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.31/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.31/1.99  --inst_lit_sel_side                     num_symb
% 11.31/1.99  --inst_solver_per_active                1400
% 11.31/1.99  --inst_solver_calls_frac                1.
% 11.31/1.99  --inst_passive_queue_type               priority_queues
% 11.31/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.31/1.99  --inst_passive_queues_freq              [25;2]
% 11.31/1.99  --inst_dismatching                      true
% 11.31/1.99  --inst_eager_unprocessed_to_passive     true
% 11.31/1.99  --inst_prop_sim_given                   true
% 11.31/1.99  --inst_prop_sim_new                     false
% 11.31/1.99  --inst_subs_new                         false
% 11.31/1.99  --inst_eq_res_simp                      false
% 11.31/1.99  --inst_subs_given                       false
% 11.31/1.99  --inst_orphan_elimination               true
% 11.31/1.99  --inst_learning_loop_flag               true
% 11.31/1.99  --inst_learning_start                   3000
% 11.31/1.99  --inst_learning_factor                  2
% 11.31/1.99  --inst_start_prop_sim_after_learn       3
% 11.31/1.99  --inst_sel_renew                        solver
% 11.31/1.99  --inst_lit_activity_flag                true
% 11.31/1.99  --inst_restr_to_given                   false
% 11.31/1.99  --inst_activity_threshold               500
% 11.31/1.99  --inst_out_proof                        true
% 11.31/1.99  
% 11.31/1.99  ------ Resolution Options
% 11.31/1.99  
% 11.31/1.99  --resolution_flag                       true
% 11.31/1.99  --res_lit_sel                           adaptive
% 11.31/1.99  --res_lit_sel_side                      none
% 11.31/1.99  --res_ordering                          kbo
% 11.31/1.99  --res_to_prop_solver                    active
% 11.31/1.99  --res_prop_simpl_new                    false
% 11.31/1.99  --res_prop_simpl_given                  true
% 11.31/1.99  --res_passive_queue_type                priority_queues
% 11.31/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.31/1.99  --res_passive_queues_freq               [15;5]
% 11.31/1.99  --res_forward_subs                      full
% 11.31/1.99  --res_backward_subs                     full
% 11.31/1.99  --res_forward_subs_resolution           true
% 11.31/1.99  --res_backward_subs_resolution          true
% 11.31/1.99  --res_orphan_elimination                true
% 11.31/1.99  --res_time_limit                        2.
% 11.31/1.99  --res_out_proof                         true
% 11.31/1.99  
% 11.31/1.99  ------ Superposition Options
% 11.31/1.99  
% 11.31/1.99  --superposition_flag                    true
% 11.31/1.99  --sup_passive_queue_type                priority_queues
% 11.31/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.31/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.31/1.99  --demod_completeness_check              fast
% 11.31/1.99  --demod_use_ground                      true
% 11.31/1.99  --sup_to_prop_solver                    passive
% 11.31/1.99  --sup_prop_simpl_new                    true
% 11.31/1.99  --sup_prop_simpl_given                  true
% 11.31/1.99  --sup_fun_splitting                     false
% 11.31/1.99  --sup_smt_interval                      50000
% 11.31/1.99  
% 11.31/1.99  ------ Superposition Simplification Setup
% 11.31/1.99  
% 11.31/1.99  --sup_indices_passive                   []
% 11.31/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.31/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.31/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.31/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.31/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.31/1.99  --sup_full_bw                           [BwDemod]
% 11.31/1.99  --sup_immed_triv                        [TrivRules]
% 11.31/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.31/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.31/1.99  --sup_immed_bw_main                     []
% 11.31/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.31/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.31/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.31/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.31/1.99  
% 11.31/1.99  ------ Combination Options
% 11.31/1.99  
% 11.31/1.99  --comb_res_mult                         3
% 11.31/1.99  --comb_sup_mult                         2
% 11.31/1.99  --comb_inst_mult                        10
% 11.31/1.99  
% 11.31/1.99  ------ Debug Options
% 11.31/1.99  
% 11.31/1.99  --dbg_backtrace                         false
% 11.31/1.99  --dbg_dump_prop_clauses                 false
% 11.31/1.99  --dbg_dump_prop_clauses_file            -
% 11.31/1.99  --dbg_out_stat                          false
% 11.31/1.99  ------ Parsing...
% 11.31/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.31/1.99  
% 11.31/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 11.31/1.99  
% 11.31/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.31/1.99  
% 11.31/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.31/1.99  ------ Proving...
% 11.31/1.99  ------ Problem Properties 
% 11.31/1.99  
% 11.31/1.99  
% 11.31/1.99  clauses                                 11
% 11.31/1.99  conjectures                             1
% 11.31/1.99  EPR                                     0
% 11.31/1.99  Horn                                    11
% 11.31/1.99  unary                                   11
% 11.31/1.99  binary                                  0
% 11.31/1.99  lits                                    11
% 11.31/1.99  lits eq                                 11
% 11.31/1.99  fd_pure                                 0
% 11.31/1.99  fd_pseudo                               0
% 11.31/1.99  fd_cond                                 0
% 11.31/1.99  fd_pseudo_cond                          0
% 11.31/1.99  AC symbols                              0
% 11.31/1.99  
% 11.31/1.99  ------ Schedule UEQ
% 11.31/1.99  
% 11.31/1.99  ------ pure equality problem: resolution off 
% 11.31/1.99  
% 11.31/1.99  ------ Option_UEQ Time Limit: Unbounded
% 11.31/1.99  
% 11.31/1.99  
% 11.31/1.99  ------ 
% 11.31/1.99  Current options:
% 11.31/1.99  ------ 
% 11.31/1.99  
% 11.31/1.99  ------ Input Options
% 11.31/1.99  
% 11.31/1.99  --out_options                           all
% 11.31/1.99  --tptp_safe_out                         true
% 11.31/1.99  --problem_path                          ""
% 11.31/1.99  --include_path                          ""
% 11.31/1.99  --clausifier                            res/vclausify_rel
% 11.31/1.99  --clausifier_options                    --mode clausify
% 11.31/1.99  --stdin                                 false
% 11.31/1.99  --stats_out                             all
% 11.31/1.99  
% 11.31/1.99  ------ General Options
% 11.31/1.99  
% 11.31/1.99  --fof                                   false
% 11.31/1.99  --time_out_real                         305.
% 11.31/1.99  --time_out_virtual                      -1.
% 11.31/1.99  --symbol_type_check                     false
% 11.31/1.99  --clausify_out                          false
% 11.31/1.99  --sig_cnt_out                           false
% 11.31/1.99  --trig_cnt_out                          false
% 11.31/1.99  --trig_cnt_out_tolerance                1.
% 11.31/1.99  --trig_cnt_out_sk_spl                   false
% 11.31/1.99  --abstr_cl_out                          false
% 11.31/1.99  
% 11.31/1.99  ------ Global Options
% 11.31/1.99  
% 11.31/1.99  --schedule                              default
% 11.31/1.99  --add_important_lit                     false
% 11.31/1.99  --prop_solver_per_cl                    1000
% 11.31/1.99  --min_unsat_core                        false
% 11.31/1.99  --soft_assumptions                      false
% 11.31/1.99  --soft_lemma_size                       3
% 11.31/1.99  --prop_impl_unit_size                   0
% 11.31/1.99  --prop_impl_unit                        []
% 11.31/1.99  --share_sel_clauses                     true
% 11.31/1.99  --reset_solvers                         false
% 11.31/1.99  --bc_imp_inh                            [conj_cone]
% 11.31/1.99  --conj_cone_tolerance                   3.
% 11.31/1.99  --extra_neg_conj                        none
% 11.31/1.99  --large_theory_mode                     true
% 11.31/1.99  --prolific_symb_bound                   200
% 11.31/1.99  --lt_threshold                          2000
% 11.31/1.99  --clause_weak_htbl                      true
% 11.31/1.99  --gc_record_bc_elim                     false
% 11.31/1.99  
% 11.31/1.99  ------ Preprocessing Options
% 11.31/1.99  
% 11.31/1.99  --preprocessing_flag                    true
% 11.31/1.99  --time_out_prep_mult                    0.1
% 11.31/1.99  --splitting_mode                        input
% 11.31/1.99  --splitting_grd                         true
% 11.31/1.99  --splitting_cvd                         false
% 11.31/1.99  --splitting_cvd_svl                     false
% 11.31/1.99  --splitting_nvd                         32
% 11.31/1.99  --sub_typing                            true
% 11.31/1.99  --prep_gs_sim                           true
% 11.31/1.99  --prep_unflatten                        true
% 11.31/1.99  --prep_res_sim                          true
% 11.31/1.99  --prep_upred                            true
% 11.31/1.99  --prep_sem_filter                       exhaustive
% 11.31/1.99  --prep_sem_filter_out                   false
% 11.31/1.99  --pred_elim                             true
% 11.31/1.99  --res_sim_input                         true
% 11.31/1.99  --eq_ax_congr_red                       true
% 11.31/1.99  --pure_diseq_elim                       true
% 11.31/1.99  --brand_transform                       false
% 11.31/1.99  --non_eq_to_eq                          false
% 11.31/1.99  --prep_def_merge                        true
% 11.31/1.99  --prep_def_merge_prop_impl              false
% 11.31/1.99  --prep_def_merge_mbd                    true
% 11.31/1.99  --prep_def_merge_tr_red                 false
% 11.31/1.99  --prep_def_merge_tr_cl                  false
% 11.31/1.99  --smt_preprocessing                     true
% 11.31/1.99  --smt_ac_axioms                         fast
% 11.31/1.99  --preprocessed_out                      false
% 11.31/1.99  --preprocessed_stats                    false
% 11.31/1.99  
% 11.31/1.99  ------ Abstraction refinement Options
% 11.31/1.99  
% 11.31/1.99  --abstr_ref                             []
% 11.31/1.99  --abstr_ref_prep                        false
% 11.31/1.99  --abstr_ref_until_sat                   false
% 11.31/1.99  --abstr_ref_sig_restrict                funpre
% 11.31/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.31/1.99  --abstr_ref_under                       []
% 11.31/1.99  
% 11.31/1.99  ------ SAT Options
% 11.31/1.99  
% 11.31/1.99  --sat_mode                              false
% 11.31/1.99  --sat_fm_restart_options                ""
% 11.31/1.99  --sat_gr_def                            false
% 11.31/1.99  --sat_epr_types                         true
% 11.31/1.99  --sat_non_cyclic_types                  false
% 11.31/1.99  --sat_finite_models                     false
% 11.31/1.99  --sat_fm_lemmas                         false
% 11.31/1.99  --sat_fm_prep                           false
% 11.31/1.99  --sat_fm_uc_incr                        true
% 11.31/1.99  --sat_out_model                         small
% 11.31/1.99  --sat_out_clauses                       false
% 11.31/1.99  
% 11.31/1.99  ------ QBF Options
% 11.31/1.99  
% 11.31/1.99  --qbf_mode                              false
% 11.31/1.99  --qbf_elim_univ                         false
% 11.31/1.99  --qbf_dom_inst                          none
% 11.31/1.99  --qbf_dom_pre_inst                      false
% 11.31/1.99  --qbf_sk_in                             false
% 11.31/1.99  --qbf_pred_elim                         true
% 11.31/1.99  --qbf_split                             512
% 11.31/1.99  
% 11.31/1.99  ------ BMC1 Options
% 11.31/1.99  
% 11.31/1.99  --bmc1_incremental                      false
% 11.31/1.99  --bmc1_axioms                           reachable_all
% 11.31/1.99  --bmc1_min_bound                        0
% 11.31/1.99  --bmc1_max_bound                        -1
% 11.31/1.99  --bmc1_max_bound_default                -1
% 11.31/1.99  --bmc1_symbol_reachability              true
% 11.31/1.99  --bmc1_property_lemmas                  false
% 11.31/1.99  --bmc1_k_induction                      false
% 11.31/1.99  --bmc1_non_equiv_states                 false
% 11.31/1.99  --bmc1_deadlock                         false
% 11.31/1.99  --bmc1_ucm                              false
% 11.31/1.99  --bmc1_add_unsat_core                   none
% 11.31/1.99  --bmc1_unsat_core_children              false
% 11.31/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.31/1.99  --bmc1_out_stat                         full
% 11.31/1.99  --bmc1_ground_init                      false
% 11.31/1.99  --bmc1_pre_inst_next_state              false
% 11.31/1.99  --bmc1_pre_inst_state                   false
% 11.31/1.99  --bmc1_pre_inst_reach_state             false
% 11.31/1.99  --bmc1_out_unsat_core                   false
% 11.31/1.99  --bmc1_aig_witness_out                  false
% 11.31/1.99  --bmc1_verbose                          false
% 11.31/1.99  --bmc1_dump_clauses_tptp                false
% 11.31/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.31/1.99  --bmc1_dump_file                        -
% 11.31/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.31/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.31/1.99  --bmc1_ucm_extend_mode                  1
% 11.31/1.99  --bmc1_ucm_init_mode                    2
% 11.31/1.99  --bmc1_ucm_cone_mode                    none
% 11.31/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.31/1.99  --bmc1_ucm_relax_model                  4
% 11.31/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.31/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.31/1.99  --bmc1_ucm_layered_model                none
% 11.31/1.99  --bmc1_ucm_max_lemma_size               10
% 11.31/1.99  
% 11.31/1.99  ------ AIG Options
% 11.31/1.99  
% 11.31/1.99  --aig_mode                              false
% 11.31/1.99  
% 11.31/1.99  ------ Instantiation Options
% 11.31/1.99  
% 11.31/1.99  --instantiation_flag                    false
% 11.31/1.99  --inst_sos_flag                         false
% 11.31/1.99  --inst_sos_phase                        true
% 11.31/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.31/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.31/1.99  --inst_lit_sel_side                     num_symb
% 11.31/1.99  --inst_solver_per_active                1400
% 11.31/1.99  --inst_solver_calls_frac                1.
% 11.31/1.99  --inst_passive_queue_type               priority_queues
% 11.31/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.31/1.99  --inst_passive_queues_freq              [25;2]
% 11.31/1.99  --inst_dismatching                      true
% 11.31/1.99  --inst_eager_unprocessed_to_passive     true
% 11.31/1.99  --inst_prop_sim_given                   true
% 11.31/1.99  --inst_prop_sim_new                     false
% 11.31/1.99  --inst_subs_new                         false
% 11.31/1.99  --inst_eq_res_simp                      false
% 11.31/1.99  --inst_subs_given                       false
% 11.31/1.99  --inst_orphan_elimination               true
% 11.31/1.99  --inst_learning_loop_flag               true
% 11.31/1.99  --inst_learning_start                   3000
% 11.31/1.99  --inst_learning_factor                  2
% 11.31/1.99  --inst_start_prop_sim_after_learn       3
% 11.31/1.99  --inst_sel_renew                        solver
% 11.31/1.99  --inst_lit_activity_flag                true
% 11.31/1.99  --inst_restr_to_given                   false
% 11.31/1.99  --inst_activity_threshold               500
% 11.31/1.99  --inst_out_proof                        true
% 11.31/1.99  
% 11.31/1.99  ------ Resolution Options
% 11.31/1.99  
% 11.31/1.99  --resolution_flag                       false
% 11.31/1.99  --res_lit_sel                           adaptive
% 11.31/1.99  --res_lit_sel_side                      none
% 11.31/1.99  --res_ordering                          kbo
% 11.31/1.99  --res_to_prop_solver                    active
% 11.31/1.99  --res_prop_simpl_new                    false
% 11.31/1.99  --res_prop_simpl_given                  true
% 11.31/1.99  --res_passive_queue_type                priority_queues
% 11.31/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.31/1.99  --res_passive_queues_freq               [15;5]
% 11.31/1.99  --res_forward_subs                      full
% 11.31/1.99  --res_backward_subs                     full
% 11.31/1.99  --res_forward_subs_resolution           true
% 11.31/1.99  --res_backward_subs_resolution          true
% 11.31/1.99  --res_orphan_elimination                true
% 11.31/1.99  --res_time_limit                        2.
% 11.31/1.99  --res_out_proof                         true
% 11.31/1.99  
% 11.31/1.99  ------ Superposition Options
% 11.31/1.99  
% 11.31/1.99  --superposition_flag                    true
% 11.31/1.99  --sup_passive_queue_type                priority_queues
% 11.31/1.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.31/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.31/1.99  --demod_completeness_check              fast
% 11.31/1.99  --demod_use_ground                      true
% 11.31/1.99  --sup_to_prop_solver                    active
% 11.31/1.99  --sup_prop_simpl_new                    false
% 11.31/1.99  --sup_prop_simpl_given                  false
% 11.31/1.99  --sup_fun_splitting                     true
% 11.31/1.99  --sup_smt_interval                      10000
% 11.31/1.99  
% 11.31/1.99  ------ Superposition Simplification Setup
% 11.31/1.99  
% 11.31/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.31/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.31/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.31/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.31/1.99  --sup_full_triv                         [TrivRules]
% 11.31/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.31/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.31/1.99  --sup_immed_triv                        [TrivRules]
% 11.31/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.31/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.31/1.99  --sup_immed_bw_main                     []
% 11.31/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.31/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.31/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.31/1.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 11.31/1.99  
% 11.31/1.99  ------ Combination Options
% 11.31/1.99  
% 11.31/1.99  --comb_res_mult                         1
% 11.31/1.99  --comb_sup_mult                         1
% 11.31/1.99  --comb_inst_mult                        1000000
% 11.31/1.99  
% 11.31/1.99  ------ Debug Options
% 11.31/1.99  
% 11.31/1.99  --dbg_backtrace                         false
% 11.31/1.99  --dbg_dump_prop_clauses                 false
% 11.31/1.99  --dbg_dump_prop_clauses_file            -
% 11.31/1.99  --dbg_out_stat                          false
% 11.31/1.99  
% 11.31/1.99  
% 11.31/1.99  
% 11.31/1.99  
% 11.31/1.99  ------ Proving...
% 11.31/1.99  
% 11.31/1.99  
% 11.31/1.99  % SZS status Theorem for theBenchmark.p
% 11.31/1.99  
% 11.31/1.99   Resolution empty clause
% 11.31/1.99  
% 11.31/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.31/1.99  
% 11.31/1.99  fof(f6,axiom,(
% 11.31/1.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f23,plain,(
% 11.31/1.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.31/1.99    inference(cnf_transformation,[],[f6])).
% 11.31/1.99  
% 11.31/1.99  fof(f9,axiom,(
% 11.31/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f26,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.31/1.99    inference(cnf_transformation,[],[f9])).
% 11.31/1.99  
% 11.31/1.99  fof(f10,axiom,(
% 11.31/1.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f27,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.31/1.99    inference(cnf_transformation,[],[f10])).
% 11.31/1.99  
% 11.31/1.99  fof(f33,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.31/1.99    inference(definition_unfolding,[],[f26,f27])).
% 11.31/1.99  
% 11.31/1.99  fof(f5,axiom,(
% 11.31/1.99    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f22,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 11.31/1.99    inference(cnf_transformation,[],[f5])).
% 11.31/1.99  
% 11.31/1.99  fof(f32,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 11.31/1.99    inference(definition_unfolding,[],[f22,f27])).
% 11.31/1.99  
% 11.31/1.99  fof(f1,axiom,(
% 11.31/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f18,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.31/1.99    inference(cnf_transformation,[],[f1])).
% 11.31/1.99  
% 11.31/1.99  fof(f4,axiom,(
% 11.31/1.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f21,plain,(
% 11.31/1.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.31/1.99    inference(cnf_transformation,[],[f4])).
% 11.31/1.99  
% 11.31/1.99  fof(f7,axiom,(
% 11.31/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f24,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.31/1.99    inference(cnf_transformation,[],[f7])).
% 11.31/1.99  
% 11.31/1.99  fof(f8,axiom,(
% 11.31/1.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f25,plain,(
% 11.31/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.31/1.99    inference(cnf_transformation,[],[f8])).
% 11.31/1.99  
% 11.31/1.99  fof(f12,axiom,(
% 11.31/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f29,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 11.31/1.99    inference(cnf_transformation,[],[f12])).
% 11.31/1.99  
% 11.31/1.99  fof(f2,axiom,(
% 11.31/1.99    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f19,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 11.31/1.99    inference(cnf_transformation,[],[f2])).
% 11.31/1.99  
% 11.31/1.99  fof(f35,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.31/1.99    inference(definition_unfolding,[],[f29,f19,f27])).
% 11.31/1.99  
% 11.31/1.99  fof(f11,axiom,(
% 11.31/1.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f28,plain,(
% 11.31/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.31/1.99    inference(cnf_transformation,[],[f11])).
% 11.31/1.99  
% 11.31/1.99  fof(f34,plain,(
% 11.31/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) )),
% 11.31/1.99    inference(definition_unfolding,[],[f28,f19,f19,f19,f19])).
% 11.31/1.99  
% 11.31/1.99  fof(f3,axiom,(
% 11.31/1.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f20,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 11.31/1.99    inference(cnf_transformation,[],[f3])).
% 11.31/1.99  
% 11.31/1.99  fof(f31,plain,(
% 11.31/1.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.31/1.99    inference(definition_unfolding,[],[f20,f19,f27])).
% 11.31/1.99  
% 11.31/1.99  fof(f13,conjecture,(
% 11.31/1.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.31/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.31/1.99  
% 11.31/1.99  fof(f14,negated_conjecture,(
% 11.31/1.99    ~! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.31/1.99    inference(negated_conjecture,[],[f13])).
% 11.31/1.99  
% 11.31/1.99  fof(f15,plain,(
% 11.31/1.99    ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1)),
% 11.31/1.99    inference(ennf_transformation,[],[f14])).
% 11.31/1.99  
% 11.31/1.99  fof(f16,plain,(
% 11.31/1.99    ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1) => k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 11.31/1.99    introduced(choice_axiom,[])).
% 11.31/1.99  
% 11.31/1.99  fof(f17,plain,(
% 11.31/1.99    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 11.31/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 11.31/1.99  
% 11.31/1.99  fof(f30,plain,(
% 11.31/1.99    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 11.31/1.99    inference(cnf_transformation,[],[f17])).
% 11.31/1.99  
% 11.31/1.99  fof(f36,plain,(
% 11.31/1.99    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 11.31/1.99    inference(definition_unfolding,[],[f30,f19,f19,f27])).
% 11.31/1.99  
% 11.31/1.99  cnf(c_4,plain,
% 11.31/1.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.31/1.99      inference(cnf_transformation,[],[f23]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_7,plain,
% 11.31/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.31/1.99      inference(cnf_transformation,[],[f33]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_3,plain,
% 11.31/1.99      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 11.31/1.99      inference(cnf_transformation,[],[f32]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_88,plain,
% 11.31/1.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_7,c_3]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_0,plain,
% 11.31/1.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.31/1.99      inference(cnf_transformation,[],[f18]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_2,plain,
% 11.31/1.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.31/1.99      inference(cnf_transformation,[],[f21]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_32,plain,
% 11.31/1.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_5,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.31/1.99      inference(cnf_transformation,[],[f24]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_58,plain,
% 11.31/1.99      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_32,c_5]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_43,plain,
% 11.31/1.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_3,c_32]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_91,plain,
% 11.31/1.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_7,c_43]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_158,plain,
% 11.31/1.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.31/1.99      inference(light_normalisation,[status(thm)],[c_58,c_91]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_6,plain,
% 11.31/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.31/1.99      inference(cnf_transformation,[],[f25]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_164,plain,
% 11.31/1.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_158,c_6]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_168,plain,
% 11.31/1.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_164,c_91]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_190,plain,
% 11.31/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_0,c_168]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_212,plain,
% 11.31/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_88,c_190]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_242,plain,
% 11.31/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_212,c_6]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_245,plain,
% 11.31/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_242,c_6,c_91]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_9,plain,
% 11.31/1.99      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 11.31/1.99      inference(cnf_transformation,[],[f35]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_708,plain,
% 11.31/1.99      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_245,c_9]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_304,plain,
% 11.31/1.99      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_7,c_9]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_334,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_304,c_2,c_88,c_212]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_716,plain,
% 11.31/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_708,c_2,c_334]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_2130,plain,
% 11.31/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_4,c_716]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_2225,plain,
% 11.31/1.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_2130,c_0]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_310,plain,
% 11.31/1.99      ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_168,c_9]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_56,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_323,plain,
% 11.31/1.99      ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
% 11.31/1.99      inference(light_normalisation,[status(thm)],[c_310,c_4,c_56]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_324,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_323,c_32]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_2321,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_2225,c_324]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_64,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_76,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_64,c_6]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_5895,plain,
% 11.31/1.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_334,c_76]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_5991,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_5895,c_334]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_13396,plain,
% 11.31/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X0),X1) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_2321,c_5991]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_13488,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(k4_xboole_0(X0,X1),X3) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_5991,c_6]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_2162,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_716,c_0]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_7140,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X3))) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_2162,c_76]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_7167,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_7140,c_2162]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_13530,plain,
% 11.31/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.31/1.99      inference(light_normalisation,[status(thm)],[c_13488,c_7167]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_13553,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_13396,c_13530]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_298,plain,
% 11.31/1.99      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_7,c_9]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_341,plain,
% 11.31/1.99      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(X0,X1)) = X0 ),
% 11.31/1.99      inference(light_normalisation,[status(thm)],[c_298,c_88,c_212]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_342,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_341,c_2]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_308,plain,
% 11.31/1.99      ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_212,c_9]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_327,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_308,c_6,c_32]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_328,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_327,c_2]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_343,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_342,c_328]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_13554,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
% 11.31/1.99      inference(light_normalisation,[status(thm)],[c_13553,c_343]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_8,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) ),
% 11.31/1.99      inference(cnf_transformation,[],[f34]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_20105,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_13554,c_8]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_20128,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X1),k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 11.31/1.99      inference(light_normalisation,[status(thm)],[c_20105,c_158]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_1669,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_324,c_5]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_1,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 11.31/1.99      inference(cnf_transformation,[],[f31]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_197,plain,
% 11.31/1.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X0,k1_xboole_0)) ),
% 11.31/1.99      inference(superposition,[status(thm)],[c_168,c_1]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_204,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,X1),X0)) ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_197,c_168]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_205,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
% 11.31/1.99      inference(light_normalisation,[status(thm)],[c_204,c_4,c_56]) ).
% 11.31/1.99  
% 11.31/1.99  cnf(c_206,plain,
% 11.31/1.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X0) = k4_xboole_0(X1,X0) ),
% 11.31/1.99      inference(demodulation,[status(thm)],[c_205,c_32,c_56]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_1688,plain,
% 11.31/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.31/2.00      inference(light_normalisation,[status(thm)],[c_1669,c_206]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2625,plain,
% 11.31/2.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k4_xboole_0(X0,X1)) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_6,c_2321]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_20129,plain,
% 11.31/2.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 11.31/2.00      inference(demodulation,
% 11.31/2.00                [status(thm)],
% 11.31/2.00                [c_20128,c_4,c_32,c_91,c_1688,c_2625]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_21306,plain,
% 11.31/2.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X1,X1) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_20129,c_13554]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_21341,plain,
% 11.31/2.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_21306,c_158,c_13530]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_22150,plain,
% 11.31/2.00      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_21341,c_20129]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2210,plain,
% 11.31/2.00      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_324,c_2130]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2247,plain,
% 11.31/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_2210,c_2225]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_178,plain,
% 11.31/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_5,c_88]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_1114,plain,
% 11.31/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_0,c_178]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2248,plain,
% 11.31/2.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 11.31/2.00      inference(light_normalisation,[status(thm)],[c_2247,c_1114]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2406,plain,
% 11.31/2.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_2248,c_0]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_21192,plain,
% 11.31/2.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = X0 ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_1688,c_20129]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_21452,plain,
% 11.31/2.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_21192,c_13530]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2661,plain,
% 11.31/2.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_2321,c_0]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_21453,plain,
% 11.31/2.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X1))) = X0 ),
% 11.31/2.00      inference(light_normalisation,[status(thm)],[c_21452,c_2661]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_21454,plain,
% 11.31/2.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_21453,c_2,c_190]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_21680,plain,
% 11.31/2.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_21454,c_6]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_21813,plain,
% 11.31/2.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_2406,c_21680]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_165,plain,
% 11.31/2.00      ( k2_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_158,c_3]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_167,plain,
% 11.31/2.00      ( k2_xboole_0(X0,X0) = X0 ),
% 11.31/2.00      inference(light_normalisation,[status(thm)],[c_165,c_4]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_67,plain,
% 11.31/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_75,plain,
% 11.31/2.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_67,c_6]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_4064,plain,
% 11.31/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_167,c_75]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2198,plain,
% 11.31/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_0,c_2130]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_309,plain,
% 11.31/2.00      ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,X1),X1)),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_190,c_9]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_325,plain,
% 11.31/2.00      ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 11.31/2.00      inference(light_normalisation,[status(thm)],[c_309,c_5]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_326,plain,
% 11.31/2.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_325,c_4,c_32]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2367,plain,
% 11.31/2.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_2248,c_326]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2712,plain,
% 11.31/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_2198,c_2367]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2394,plain,
% 11.31/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_2248,c_2198]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2427,plain,
% 11.31/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_2394,c_2406]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_2766,plain,
% 11.31/2.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.31/2.00      inference(light_normalisation,[status(thm)],[c_2712,c_2427]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_4184,plain,
% 11.31/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_4064,c_2766]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_21978,plain,
% 11.31/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_21680,c_4184]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_22055,plain,
% 11.31/2.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_21813,c_21978]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_22305,plain,
% 11.31/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_22150,c_32,c_22055]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_228,plain,
% 11.31/2.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_1,c_212]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_10,negated_conjecture,
% 11.31/2.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.31/2.00      inference(cnf_transformation,[],[f36]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_31,plain,
% 11.31/2.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_0,c_10]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_17982,plain,
% 11.31/2.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_228,c_31]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_5867,plain,
% 11.31/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
% 11.31/2.00      inference(superposition,[status(thm)],[c_2406,c_76]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_17983,plain,
% 11.31/2.00      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_17982,c_2,c_5867]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_21773,plain,
% 11.31/2.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_21680,c_17983]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_33414,plain,
% 11.31/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.31/2.00      inference(demodulation,[status(thm)],[c_22305,c_21773]) ).
% 11.31/2.00  
% 11.31/2.00  cnf(c_33835,plain,
% 11.31/2.00      ( $false ),
% 11.31/2.00      inference(equality_resolution_simp,[status(thm)],[c_33414]) ).
% 11.31/2.00  
% 11.31/2.00  
% 11.31/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.31/2.00  
% 11.31/2.00  ------                               Statistics
% 11.31/2.00  
% 11.31/2.00  ------ General
% 11.31/2.00  
% 11.31/2.00  abstr_ref_over_cycles:                  0
% 11.31/2.00  abstr_ref_under_cycles:                 0
% 11.31/2.00  gc_basic_clause_elim:                   0
% 11.31/2.00  forced_gc_time:                         0
% 11.31/2.00  parsing_time:                           0.009
% 11.31/2.00  unif_index_cands_time:                  0.
% 11.31/2.00  unif_index_add_time:                    0.
% 11.31/2.00  orderings_time:                         0.
% 11.31/2.00  out_proof_time:                         0.007
% 11.31/2.00  total_time:                             1.183
% 11.31/2.00  num_of_symbols:                         36
% 11.31/2.00  num_of_terms:                           51766
% 11.31/2.00  
% 11.31/2.00  ------ Preprocessing
% 11.31/2.00  
% 11.31/2.00  num_of_splits:                          0
% 11.31/2.00  num_of_split_atoms:                     0
% 11.31/2.00  num_of_reused_defs:                     0
% 11.31/2.00  num_eq_ax_congr_red:                    0
% 11.31/2.00  num_of_sem_filtered_clauses:            0
% 11.31/2.00  num_of_subtypes:                        0
% 11.31/2.00  monotx_restored_types:                  0
% 11.31/2.00  sat_num_of_epr_types:                   0
% 11.31/2.00  sat_num_of_non_cyclic_types:            0
% 11.31/2.00  sat_guarded_non_collapsed_types:        0
% 11.31/2.00  num_pure_diseq_elim:                    0
% 11.31/2.00  simp_replaced_by:                       0
% 11.31/2.00  res_preprocessed:                       26
% 11.31/2.00  prep_upred:                             0
% 11.31/2.00  prep_unflattend:                        0
% 11.31/2.00  smt_new_axioms:                         0
% 11.31/2.00  pred_elim_cands:                        0
% 11.31/2.00  pred_elim:                              0
% 11.31/2.00  pred_elim_cl:                           0
% 11.31/2.00  pred_elim_cycles:                       0
% 11.31/2.00  merged_defs:                            0
% 11.31/2.00  merged_defs_ncl:                        0
% 11.31/2.00  bin_hyper_res:                          0
% 11.31/2.00  prep_cycles:                            2
% 11.31/2.00  pred_elim_time:                         0.
% 11.31/2.00  splitting_time:                         0.
% 11.31/2.00  sem_filter_time:                        0.
% 11.31/2.00  monotx_time:                            0.001
% 11.31/2.00  subtype_inf_time:                       0.
% 11.31/2.00  
% 11.31/2.00  ------ Problem properties
% 11.31/2.00  
% 11.31/2.00  clauses:                                11
% 11.31/2.00  conjectures:                            1
% 11.31/2.00  epr:                                    0
% 11.31/2.00  horn:                                   11
% 11.31/2.00  ground:                                 1
% 11.31/2.00  unary:                                  11
% 11.31/2.00  binary:                                 0
% 11.31/2.00  lits:                                   11
% 11.31/2.00  lits_eq:                                11
% 11.31/2.00  fd_pure:                                0
% 11.31/2.00  fd_pseudo:                              0
% 11.31/2.00  fd_cond:                                0
% 11.31/2.00  fd_pseudo_cond:                         0
% 11.31/2.00  ac_symbols:                             0
% 11.31/2.00  
% 11.31/2.00  ------ Propositional Solver
% 11.31/2.00  
% 11.31/2.00  prop_solver_calls:                      13
% 11.31/2.00  prop_fast_solver_calls:                 64
% 11.31/2.00  smt_solver_calls:                       0
% 11.31/2.00  smt_fast_solver_calls:                  0
% 11.31/2.00  prop_num_of_clauses:                    273
% 11.31/2.00  prop_preprocess_simplified:             428
% 11.31/2.00  prop_fo_subsumed:                       0
% 11.31/2.00  prop_solver_time:                       0.
% 11.31/2.00  smt_solver_time:                        0.
% 11.31/2.00  smt_fast_solver_time:                   0.
% 11.31/2.00  prop_fast_solver_time:                  0.
% 11.31/2.00  prop_unsat_core_time:                   0.
% 11.31/2.00  
% 11.31/2.00  ------ QBF
% 11.31/2.00  
% 11.31/2.00  qbf_q_res:                              0
% 11.31/2.00  qbf_num_tautologies:                    0
% 11.31/2.00  qbf_prep_cycles:                        0
% 11.31/2.00  
% 11.31/2.00  ------ BMC1
% 11.31/2.00  
% 11.31/2.00  bmc1_current_bound:                     -1
% 11.31/2.00  bmc1_last_solved_bound:                 -1
% 11.31/2.00  bmc1_unsat_core_size:                   -1
% 11.31/2.00  bmc1_unsat_core_parents_size:           -1
% 11.31/2.00  bmc1_merge_next_fun:                    0
% 11.31/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.31/2.00  
% 11.31/2.00  ------ Instantiation
% 11.31/2.00  
% 11.31/2.00  inst_num_of_clauses:                    0
% 11.31/2.00  inst_num_in_passive:                    0
% 11.31/2.00  inst_num_in_active:                     0
% 11.31/2.00  inst_num_in_unprocessed:                0
% 11.31/2.00  inst_num_of_loops:                      0
% 11.31/2.00  inst_num_of_learning_restarts:          0
% 11.31/2.00  inst_num_moves_active_passive:          0
% 11.31/2.00  inst_lit_activity:                      0
% 11.31/2.00  inst_lit_activity_moves:                0
% 11.31/2.00  inst_num_tautologies:                   0
% 11.31/2.00  inst_num_prop_implied:                  0
% 11.31/2.00  inst_num_existing_simplified:           0
% 11.31/2.00  inst_num_eq_res_simplified:             0
% 11.31/2.00  inst_num_child_elim:                    0
% 11.31/2.00  inst_num_of_dismatching_blockings:      0
% 11.31/2.00  inst_num_of_non_proper_insts:           0
% 11.31/2.00  inst_num_of_duplicates:                 0
% 11.31/2.00  inst_inst_num_from_inst_to_res:         0
% 11.31/2.00  inst_dismatching_checking_time:         0.
% 11.31/2.00  
% 11.31/2.00  ------ Resolution
% 11.31/2.00  
% 11.31/2.00  res_num_of_clauses:                     0
% 11.31/2.00  res_num_in_passive:                     0
% 11.31/2.00  res_num_in_active:                      0
% 11.31/2.00  res_num_of_loops:                       28
% 11.31/2.00  res_forward_subset_subsumed:            0
% 11.31/2.00  res_backward_subset_subsumed:           0
% 11.31/2.00  res_forward_subsumed:                   0
% 11.31/2.00  res_backward_subsumed:                  0
% 11.31/2.00  res_forward_subsumption_resolution:     0
% 11.31/2.00  res_backward_subsumption_resolution:    0
% 11.31/2.00  res_clause_to_clause_subsumption:       83115
% 11.31/2.00  res_orphan_elimination:                 0
% 11.31/2.00  res_tautology_del:                      0
% 11.31/2.00  res_num_eq_res_simplified:              0
% 11.31/2.00  res_num_sel_changes:                    0
% 11.31/2.00  res_moves_from_active_to_pass:          0
% 11.31/2.00  
% 11.31/2.00  ------ Superposition
% 11.31/2.00  
% 11.31/2.00  sup_time_total:                         0.
% 11.31/2.00  sup_time_generating:                    0.
% 11.31/2.00  sup_time_sim_full:                      0.
% 11.31/2.00  sup_time_sim_immed:                     0.
% 11.31/2.00  
% 11.31/2.00  sup_num_of_clauses:                     3309
% 11.31/2.00  sup_num_in_active:                      124
% 11.31/2.00  sup_num_in_passive:                     3185
% 11.31/2.00  sup_num_of_loops:                       167
% 11.31/2.00  sup_fw_superposition:                   12584
% 11.31/2.00  sup_bw_superposition:                   10617
% 11.31/2.00  sup_immediate_simplified:               9484
% 11.31/2.00  sup_given_eliminated:                   2
% 11.31/2.00  comparisons_done:                       0
% 11.31/2.00  comparisons_avoided:                    0
% 11.31/2.00  
% 11.31/2.00  ------ Simplifications
% 11.31/2.00  
% 11.31/2.00  
% 11.31/2.00  sim_fw_subset_subsumed:                 0
% 11.31/2.00  sim_bw_subset_subsumed:                 0
% 11.31/2.00  sim_fw_subsumed:                        1480
% 11.31/2.00  sim_bw_subsumed:                        24
% 11.31/2.00  sim_fw_subsumption_res:                 0
% 11.31/2.00  sim_bw_subsumption_res:                 0
% 11.31/2.00  sim_tautology_del:                      0
% 11.31/2.00  sim_eq_tautology_del:                   2680
% 11.31/2.00  sim_eq_res_simp:                        0
% 11.31/2.00  sim_fw_demodulated:                     6658
% 11.31/2.00  sim_bw_demodulated:                     93
% 11.31/2.00  sim_light_normalised:                   3762
% 11.31/2.00  sim_joinable_taut:                      0
% 11.31/2.00  sim_joinable_simp:                      0
% 11.31/2.00  sim_ac_normalised:                      0
% 11.31/2.00  sim_smt_subsumption:                    0
% 11.31/2.00  
%------------------------------------------------------------------------------
