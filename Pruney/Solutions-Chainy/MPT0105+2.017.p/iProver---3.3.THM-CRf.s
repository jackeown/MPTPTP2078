%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:14 EST 2020

% Result     : Theorem 11.44s
% Output     : CNFRefutation 11.44s
% Verified   : 
% Statistics : Number of formulae       :  132 (27383 expanded)
%              Number of clauses        :  102 (5726 expanded)
%              Number of leaves         :   10 (8632 expanded)
%              Depth                    :   28
%              Number of atoms          :  133 (27384 expanded)
%              Number of equality atoms :  132 (27383 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f14,f17,f17])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f16,f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f15,f17])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
    inference(definition_unfolding,[],[f19,f23,f23,f23,f23])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(definition_unfolding,[],[f21,f23,f23,f17])).

fof(f9,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1)
   => k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f22,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f22,f23])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_24,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_2])).

cnf(c_46,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_24,c_24])).

cnf(c_886,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1,c_46])).

cnf(c_4,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1063,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),X2))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))))) ),
    inference(superposition,[status(thm)],[c_886,c_4])).

cnf(c_3,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_31,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0)) = k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_32,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_31,c_3])).

cnf(c_68,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_32,c_24])).

cnf(c_69,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_32,c_1])).

cnf(c_71,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_68,c_69])).

cnf(c_1076,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_886,c_71])).

cnf(c_1083,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
    inference(demodulation,[status(thm)],[c_1063,c_1076])).

cnf(c_5,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_249,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_0,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_141,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0))))) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_190,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_141,c_71])).

cnf(c_368,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k2_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_249,c_190])).

cnf(c_398,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_71,c_5])).

cnf(c_140,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))))) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_191,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_140,c_2])).

cnf(c_576,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_191])).

cnf(c_621,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_576])).

cnf(c_648,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_621,c_24,c_398])).

cnf(c_29,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_708,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_648,c_29])).

cnf(c_710,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_708,c_2])).

cnf(c_1084,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_1083,c_368,c_398,c_710])).

cnf(c_1672,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_24,c_1084])).

cnf(c_689,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_648])).

cnf(c_803,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_689,c_29])).

cnf(c_805,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_803,c_710])).

cnf(c_806,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_805,c_24])).

cnf(c_1708,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1672,c_806])).

cnf(c_296,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1))) = k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_362,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_296,c_3])).

cnf(c_6063,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_362])).

cnf(c_167,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_187,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_167,c_24])).

cnf(c_6247,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6063,c_24,c_187])).

cnf(c_6064,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_362])).

cnf(c_6249,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(demodulation,[status(thm)],[c_6247,c_6064])).

cnf(c_6259,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6249,c_2])).

cnf(c_6619,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)))))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1708,c_6259])).

cnf(c_5524,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_1708,c_1])).

cnf(c_6728,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_6619,c_5524])).

cnf(c_890,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) ),
    inference(superposition,[status(thm)],[c_710,c_46])).

cnf(c_705,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_648,c_68])).

cnf(c_1000,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_890,c_705,c_710,c_806])).

cnf(c_1622,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1000,c_806])).

cnf(c_1623,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1622,c_710])).

cnf(c_1597,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[status(thm)],[c_1000,c_2])).

cnf(c_1601,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_1000,c_1])).

cnf(c_857,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_710,c_24])).

cnf(c_1643,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1601,c_806,c_857])).

cnf(c_1646,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) ),
    inference(demodulation,[status(thm)],[c_1597,c_1643])).

cnf(c_6050,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X0),X0),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X0),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X0),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_71,c_362])).

cnf(c_6265,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6050,c_398,c_710,c_1084])).

cnf(c_33,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5,c_2])).

cnf(c_34,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_33,c_5])).

cnf(c_164,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0),k1_xboole_0),k4_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0),k4_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0),k1_xboole_0))) = k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_34,c_0])).

cnf(c_79,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_34,c_3])).

cnf(c_188,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0) = k2_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_164,c_34,c_79])).

cnf(c_6043,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0))),k1_xboole_0),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0))),k1_xboole_0))) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_188,c_362])).

cnf(c_6283,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k1_xboole_0))) = X0 ),
    inference(demodulation,[status(thm)],[c_6043,c_6265])).

cnf(c_6284,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6283,c_806,c_857])).

cnf(c_811,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_710,c_29])).

cnf(c_6285,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_6284,c_806,c_811])).

cnf(c_6729,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6728,c_1623,c_1646,c_6247,c_6265,c_6285])).

cnf(c_810,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_710,c_576])).

cnf(c_2457,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_810,c_1])).

cnf(c_6632,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)))))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2457,c_6259])).

cnf(c_2456,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_810,c_24])).

cnf(c_6105,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k1_xboole_0,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_857,c_362])).

cnf(c_1431,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))))) = k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_857,c_0])).

cnf(c_1468,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0)) = k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1431,c_806,c_810,c_811])).

cnf(c_6207,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6105,c_806,c_810,c_811,c_1468])).

cnf(c_6718,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)))),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)))))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_6632,c_68,c_2456,c_6207])).

cnf(c_6719,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_6718,c_6207])).

cnf(c_6730,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6729,c_6719])).

cnf(c_6734,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6730,c_6729])).

cnf(c_6735,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6734,c_806,c_811])).

cnf(c_913,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_1,c_46])).

cnf(c_7195,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6735,c_913])).

cnf(c_39,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_24])).

cnf(c_49,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_39,c_24])).

cnf(c_1792,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_49,c_71])).

cnf(c_2967,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_1792])).

cnf(c_8236,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_7195,c_2967])).

cnf(c_159,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_10912,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)))) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8236,c_159])).

cnf(c_7313,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_6247])).

cnf(c_7407,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))))) ),
    inference(superposition,[status(thm)],[c_7313,c_4])).

cnf(c_7410,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))) ),
    inference(demodulation,[status(thm)],[c_7407,c_2])).

cnf(c_7411,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_7410,c_24])).

cnf(c_11046,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_10912,c_6285,c_7411])).

cnf(c_6,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_14230,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_11046,c_6])).

cnf(c_14490,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_14230])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:29:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.44/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.44/1.99  
% 11.44/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.44/1.99  
% 11.44/1.99  ------  iProver source info
% 11.44/1.99  
% 11.44/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.44/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.44/1.99  git: non_committed_changes: false
% 11.44/1.99  git: last_make_outside_of_git: false
% 11.44/1.99  
% 11.44/1.99  ------ 
% 11.44/1.99  
% 11.44/1.99  ------ Input Options
% 11.44/1.99  
% 11.44/1.99  --out_options                           all
% 11.44/1.99  --tptp_safe_out                         true
% 11.44/1.99  --problem_path                          ""
% 11.44/1.99  --include_path                          ""
% 11.44/1.99  --clausifier                            res/vclausify_rel
% 11.44/1.99  --clausifier_options                    --mode clausify
% 11.44/1.99  --stdin                                 false
% 11.44/1.99  --stats_out                             all
% 11.44/1.99  
% 11.44/1.99  ------ General Options
% 11.44/1.99  
% 11.44/1.99  --fof                                   false
% 11.44/1.99  --time_out_real                         305.
% 11.44/1.99  --time_out_virtual                      -1.
% 11.44/1.99  --symbol_type_check                     false
% 11.44/1.99  --clausify_out                          false
% 11.44/1.99  --sig_cnt_out                           false
% 11.44/1.99  --trig_cnt_out                          false
% 11.44/1.99  --trig_cnt_out_tolerance                1.
% 11.44/1.99  --trig_cnt_out_sk_spl                   false
% 11.44/1.99  --abstr_cl_out                          false
% 11.44/1.99  
% 11.44/1.99  ------ Global Options
% 11.44/1.99  
% 11.44/1.99  --schedule                              default
% 11.44/1.99  --add_important_lit                     false
% 11.44/1.99  --prop_solver_per_cl                    1000
% 11.44/1.99  --min_unsat_core                        false
% 11.44/1.99  --soft_assumptions                      false
% 11.44/1.99  --soft_lemma_size                       3
% 11.44/1.99  --prop_impl_unit_size                   0
% 11.44/1.99  --prop_impl_unit                        []
% 11.44/1.99  --share_sel_clauses                     true
% 11.44/1.99  --reset_solvers                         false
% 11.44/1.99  --bc_imp_inh                            [conj_cone]
% 11.44/1.99  --conj_cone_tolerance                   3.
% 11.44/1.99  --extra_neg_conj                        none
% 11.44/1.99  --large_theory_mode                     true
% 11.44/1.99  --prolific_symb_bound                   200
% 11.44/1.99  --lt_threshold                          2000
% 11.44/1.99  --clause_weak_htbl                      true
% 11.44/1.99  --gc_record_bc_elim                     false
% 11.44/1.99  
% 11.44/1.99  ------ Preprocessing Options
% 11.44/1.99  
% 11.44/1.99  --preprocessing_flag                    true
% 11.44/1.99  --time_out_prep_mult                    0.1
% 11.44/1.99  --splitting_mode                        input
% 11.44/1.99  --splitting_grd                         true
% 11.44/1.99  --splitting_cvd                         false
% 11.44/1.99  --splitting_cvd_svl                     false
% 11.44/1.99  --splitting_nvd                         32
% 11.44/1.99  --sub_typing                            true
% 11.44/1.99  --prep_gs_sim                           true
% 11.44/1.99  --prep_unflatten                        true
% 11.44/1.99  --prep_res_sim                          true
% 11.44/1.99  --prep_upred                            true
% 11.44/1.99  --prep_sem_filter                       exhaustive
% 11.44/1.99  --prep_sem_filter_out                   false
% 11.44/1.99  --pred_elim                             true
% 11.44/1.99  --res_sim_input                         true
% 11.44/1.99  --eq_ax_congr_red                       true
% 11.44/1.99  --pure_diseq_elim                       true
% 11.44/1.99  --brand_transform                       false
% 11.44/1.99  --non_eq_to_eq                          false
% 11.44/1.99  --prep_def_merge                        true
% 11.44/1.99  --prep_def_merge_prop_impl              false
% 11.44/1.99  --prep_def_merge_mbd                    true
% 11.44/1.99  --prep_def_merge_tr_red                 false
% 11.44/1.99  --prep_def_merge_tr_cl                  false
% 11.44/1.99  --smt_preprocessing                     true
% 11.44/1.99  --smt_ac_axioms                         fast
% 11.44/1.99  --preprocessed_out                      false
% 11.44/1.99  --preprocessed_stats                    false
% 11.44/1.99  
% 11.44/1.99  ------ Abstraction refinement Options
% 11.44/1.99  
% 11.44/1.99  --abstr_ref                             []
% 11.44/1.99  --abstr_ref_prep                        false
% 11.44/1.99  --abstr_ref_until_sat                   false
% 11.44/1.99  --abstr_ref_sig_restrict                funpre
% 11.44/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.44/1.99  --abstr_ref_under                       []
% 11.44/1.99  
% 11.44/1.99  ------ SAT Options
% 11.44/1.99  
% 11.44/1.99  --sat_mode                              false
% 11.44/1.99  --sat_fm_restart_options                ""
% 11.44/1.99  --sat_gr_def                            false
% 11.44/1.99  --sat_epr_types                         true
% 11.44/1.99  --sat_non_cyclic_types                  false
% 11.44/1.99  --sat_finite_models                     false
% 11.44/1.99  --sat_fm_lemmas                         false
% 11.44/1.99  --sat_fm_prep                           false
% 11.44/1.99  --sat_fm_uc_incr                        true
% 11.44/1.99  --sat_out_model                         small
% 11.44/1.99  --sat_out_clauses                       false
% 11.44/1.99  
% 11.44/1.99  ------ QBF Options
% 11.44/1.99  
% 11.44/1.99  --qbf_mode                              false
% 11.44/1.99  --qbf_elim_univ                         false
% 11.44/1.99  --qbf_dom_inst                          none
% 11.44/1.99  --qbf_dom_pre_inst                      false
% 11.44/1.99  --qbf_sk_in                             false
% 11.44/1.99  --qbf_pred_elim                         true
% 11.44/1.99  --qbf_split                             512
% 11.44/1.99  
% 11.44/1.99  ------ BMC1 Options
% 11.44/1.99  
% 11.44/1.99  --bmc1_incremental                      false
% 11.44/1.99  --bmc1_axioms                           reachable_all
% 11.44/1.99  --bmc1_min_bound                        0
% 11.44/1.99  --bmc1_max_bound                        -1
% 11.44/1.99  --bmc1_max_bound_default                -1
% 11.44/1.99  --bmc1_symbol_reachability              true
% 11.44/1.99  --bmc1_property_lemmas                  false
% 11.44/1.99  --bmc1_k_induction                      false
% 11.44/1.99  --bmc1_non_equiv_states                 false
% 11.44/1.99  --bmc1_deadlock                         false
% 11.44/1.99  --bmc1_ucm                              false
% 11.44/1.99  --bmc1_add_unsat_core                   none
% 11.44/1.99  --bmc1_unsat_core_children              false
% 11.44/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.44/1.99  --bmc1_out_stat                         full
% 11.44/1.99  --bmc1_ground_init                      false
% 11.44/1.99  --bmc1_pre_inst_next_state              false
% 11.44/1.99  --bmc1_pre_inst_state                   false
% 11.44/1.99  --bmc1_pre_inst_reach_state             false
% 11.44/1.99  --bmc1_out_unsat_core                   false
% 11.44/1.99  --bmc1_aig_witness_out                  false
% 11.44/1.99  --bmc1_verbose                          false
% 11.44/1.99  --bmc1_dump_clauses_tptp                false
% 11.44/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.44/1.99  --bmc1_dump_file                        -
% 11.44/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.44/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.44/1.99  --bmc1_ucm_extend_mode                  1
% 11.44/1.99  --bmc1_ucm_init_mode                    2
% 11.44/1.99  --bmc1_ucm_cone_mode                    none
% 11.44/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.44/1.99  --bmc1_ucm_relax_model                  4
% 11.44/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.44/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.44/1.99  --bmc1_ucm_layered_model                none
% 11.44/1.99  --bmc1_ucm_max_lemma_size               10
% 11.44/1.99  
% 11.44/1.99  ------ AIG Options
% 11.44/1.99  
% 11.44/1.99  --aig_mode                              false
% 11.44/1.99  
% 11.44/1.99  ------ Instantiation Options
% 11.44/1.99  
% 11.44/1.99  --instantiation_flag                    true
% 11.44/1.99  --inst_sos_flag                         false
% 11.44/1.99  --inst_sos_phase                        true
% 11.44/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.44/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.44/1.99  --inst_lit_sel_side                     num_symb
% 11.44/1.99  --inst_solver_per_active                1400
% 11.44/1.99  --inst_solver_calls_frac                1.
% 11.44/1.99  --inst_passive_queue_type               priority_queues
% 11.44/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.44/1.99  --inst_passive_queues_freq              [25;2]
% 11.44/1.99  --inst_dismatching                      true
% 11.44/1.99  --inst_eager_unprocessed_to_passive     true
% 11.44/1.99  --inst_prop_sim_given                   true
% 11.44/1.99  --inst_prop_sim_new                     false
% 11.44/1.99  --inst_subs_new                         false
% 11.44/1.99  --inst_eq_res_simp                      false
% 11.44/1.99  --inst_subs_given                       false
% 11.44/1.99  --inst_orphan_elimination               true
% 11.44/1.99  --inst_learning_loop_flag               true
% 11.44/1.99  --inst_learning_start                   3000
% 11.44/1.99  --inst_learning_factor                  2
% 11.44/1.99  --inst_start_prop_sim_after_learn       3
% 11.44/1.99  --inst_sel_renew                        solver
% 11.44/1.99  --inst_lit_activity_flag                true
% 11.44/1.99  --inst_restr_to_given                   false
% 11.44/1.99  --inst_activity_threshold               500
% 11.44/1.99  --inst_out_proof                        true
% 11.44/1.99  
% 11.44/1.99  ------ Resolution Options
% 11.44/1.99  
% 11.44/1.99  --resolution_flag                       true
% 11.44/1.99  --res_lit_sel                           adaptive
% 11.44/1.99  --res_lit_sel_side                      none
% 11.44/1.99  --res_ordering                          kbo
% 11.44/1.99  --res_to_prop_solver                    active
% 11.44/1.99  --res_prop_simpl_new                    false
% 11.44/1.99  --res_prop_simpl_given                  true
% 11.44/1.99  --res_passive_queue_type                priority_queues
% 11.44/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.44/1.99  --res_passive_queues_freq               [15;5]
% 11.44/1.99  --res_forward_subs                      full
% 11.44/1.99  --res_backward_subs                     full
% 11.44/1.99  --res_forward_subs_resolution           true
% 11.44/1.99  --res_backward_subs_resolution          true
% 11.44/1.99  --res_orphan_elimination                true
% 11.44/1.99  --res_time_limit                        2.
% 11.44/1.99  --res_out_proof                         true
% 11.44/1.99  
% 11.44/1.99  ------ Superposition Options
% 11.44/1.99  
% 11.44/1.99  --superposition_flag                    true
% 11.44/1.99  --sup_passive_queue_type                priority_queues
% 11.44/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.44/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.44/1.99  --demod_completeness_check              fast
% 11.44/1.99  --demod_use_ground                      true
% 11.44/1.99  --sup_to_prop_solver                    passive
% 11.44/1.99  --sup_prop_simpl_new                    true
% 11.44/1.99  --sup_prop_simpl_given                  true
% 11.44/1.99  --sup_fun_splitting                     false
% 11.44/1.99  --sup_smt_interval                      50000
% 11.44/1.99  
% 11.44/1.99  ------ Superposition Simplification Setup
% 11.44/1.99  
% 11.44/1.99  --sup_indices_passive                   []
% 11.44/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.44/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/1.99  --sup_full_bw                           [BwDemod]
% 11.44/1.99  --sup_immed_triv                        [TrivRules]
% 11.44/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.44/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/1.99  --sup_immed_bw_main                     []
% 11.44/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.44/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.44/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.44/1.99  
% 11.44/1.99  ------ Combination Options
% 11.44/1.99  
% 11.44/1.99  --comb_res_mult                         3
% 11.44/1.99  --comb_sup_mult                         2
% 11.44/1.99  --comb_inst_mult                        10
% 11.44/1.99  
% 11.44/1.99  ------ Debug Options
% 11.44/1.99  
% 11.44/1.99  --dbg_backtrace                         false
% 11.44/1.99  --dbg_dump_prop_clauses                 false
% 11.44/1.99  --dbg_dump_prop_clauses_file            -
% 11.44/1.99  --dbg_out_stat                          false
% 11.44/1.99  ------ Parsing...
% 11.44/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.44/1.99  
% 11.44/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 11.44/1.99  
% 11.44/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.44/1.99  
% 11.44/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.44/1.99  ------ Proving...
% 11.44/1.99  ------ Problem Properties 
% 11.44/1.99  
% 11.44/1.99  
% 11.44/1.99  clauses                                 7
% 11.44/1.99  conjectures                             1
% 11.44/1.99  EPR                                     0
% 11.44/1.99  Horn                                    7
% 11.44/1.99  unary                                   7
% 11.44/1.99  binary                                  0
% 11.44/1.99  lits                                    7
% 11.44/1.99  lits eq                                 7
% 11.44/1.99  fd_pure                                 0
% 11.44/1.99  fd_pseudo                               0
% 11.44/1.99  fd_cond                                 0
% 11.44/1.99  fd_pseudo_cond                          0
% 11.44/1.99  AC symbols                              0
% 11.44/1.99  
% 11.44/1.99  ------ Schedule UEQ
% 11.44/1.99  
% 11.44/1.99  ------ pure equality problem: resolution off 
% 11.44/1.99  
% 11.44/1.99  ------ Option_UEQ Time Limit: Unbounded
% 11.44/1.99  
% 11.44/1.99  
% 11.44/1.99  ------ 
% 11.44/1.99  Current options:
% 11.44/1.99  ------ 
% 11.44/1.99  
% 11.44/1.99  ------ Input Options
% 11.44/1.99  
% 11.44/1.99  --out_options                           all
% 11.44/1.99  --tptp_safe_out                         true
% 11.44/1.99  --problem_path                          ""
% 11.44/1.99  --include_path                          ""
% 11.44/1.99  --clausifier                            res/vclausify_rel
% 11.44/1.99  --clausifier_options                    --mode clausify
% 11.44/1.99  --stdin                                 false
% 11.44/1.99  --stats_out                             all
% 11.44/1.99  
% 11.44/1.99  ------ General Options
% 11.44/1.99  
% 11.44/1.99  --fof                                   false
% 11.44/1.99  --time_out_real                         305.
% 11.44/1.99  --time_out_virtual                      -1.
% 11.44/1.99  --symbol_type_check                     false
% 11.44/1.99  --clausify_out                          false
% 11.44/1.99  --sig_cnt_out                           false
% 11.44/1.99  --trig_cnt_out                          false
% 11.44/1.99  --trig_cnt_out_tolerance                1.
% 11.44/1.99  --trig_cnt_out_sk_spl                   false
% 11.44/1.99  --abstr_cl_out                          false
% 11.44/1.99  
% 11.44/1.99  ------ Global Options
% 11.44/1.99  
% 11.44/1.99  --schedule                              default
% 11.44/1.99  --add_important_lit                     false
% 11.44/1.99  --prop_solver_per_cl                    1000
% 11.44/1.99  --min_unsat_core                        false
% 11.44/1.99  --soft_assumptions                      false
% 11.44/1.99  --soft_lemma_size                       3
% 11.44/1.99  --prop_impl_unit_size                   0
% 11.44/1.99  --prop_impl_unit                        []
% 11.44/1.99  --share_sel_clauses                     true
% 11.44/1.99  --reset_solvers                         false
% 11.44/1.99  --bc_imp_inh                            [conj_cone]
% 11.44/1.99  --conj_cone_tolerance                   3.
% 11.44/1.99  --extra_neg_conj                        none
% 11.44/1.99  --large_theory_mode                     true
% 11.44/1.99  --prolific_symb_bound                   200
% 11.44/1.99  --lt_threshold                          2000
% 11.44/1.99  --clause_weak_htbl                      true
% 11.44/1.99  --gc_record_bc_elim                     false
% 11.44/1.99  
% 11.44/1.99  ------ Preprocessing Options
% 11.44/1.99  
% 11.44/1.99  --preprocessing_flag                    true
% 11.44/1.99  --time_out_prep_mult                    0.1
% 11.44/1.99  --splitting_mode                        input
% 11.44/1.99  --splitting_grd                         true
% 11.44/1.99  --splitting_cvd                         false
% 11.44/1.99  --splitting_cvd_svl                     false
% 11.44/1.99  --splitting_nvd                         32
% 11.44/1.99  --sub_typing                            true
% 11.44/1.99  --prep_gs_sim                           true
% 11.44/1.99  --prep_unflatten                        true
% 11.44/1.99  --prep_res_sim                          true
% 11.44/1.99  --prep_upred                            true
% 11.44/1.99  --prep_sem_filter                       exhaustive
% 11.44/1.99  --prep_sem_filter_out                   false
% 11.44/1.99  --pred_elim                             true
% 11.44/1.99  --res_sim_input                         true
% 11.44/1.99  --eq_ax_congr_red                       true
% 11.44/1.99  --pure_diseq_elim                       true
% 11.44/1.99  --brand_transform                       false
% 11.44/1.99  --non_eq_to_eq                          false
% 11.44/1.99  --prep_def_merge                        true
% 11.44/1.99  --prep_def_merge_prop_impl              false
% 11.44/1.99  --prep_def_merge_mbd                    true
% 11.44/1.99  --prep_def_merge_tr_red                 false
% 11.44/1.99  --prep_def_merge_tr_cl                  false
% 11.44/1.99  --smt_preprocessing                     true
% 11.44/1.99  --smt_ac_axioms                         fast
% 11.44/1.99  --preprocessed_out                      false
% 11.44/1.99  --preprocessed_stats                    false
% 11.44/1.99  
% 11.44/1.99  ------ Abstraction refinement Options
% 11.44/1.99  
% 11.44/1.99  --abstr_ref                             []
% 11.44/1.99  --abstr_ref_prep                        false
% 11.44/1.99  --abstr_ref_until_sat                   false
% 11.44/1.99  --abstr_ref_sig_restrict                funpre
% 11.44/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.44/1.99  --abstr_ref_under                       []
% 11.44/1.99  
% 11.44/1.99  ------ SAT Options
% 11.44/1.99  
% 11.44/1.99  --sat_mode                              false
% 11.44/1.99  --sat_fm_restart_options                ""
% 11.44/1.99  --sat_gr_def                            false
% 11.44/1.99  --sat_epr_types                         true
% 11.44/1.99  --sat_non_cyclic_types                  false
% 11.44/1.99  --sat_finite_models                     false
% 11.44/1.99  --sat_fm_lemmas                         false
% 11.44/1.99  --sat_fm_prep                           false
% 11.44/1.99  --sat_fm_uc_incr                        true
% 11.44/1.99  --sat_out_model                         small
% 11.44/1.99  --sat_out_clauses                       false
% 11.44/1.99  
% 11.44/1.99  ------ QBF Options
% 11.44/1.99  
% 11.44/1.99  --qbf_mode                              false
% 11.44/1.99  --qbf_elim_univ                         false
% 11.44/1.99  --qbf_dom_inst                          none
% 11.44/1.99  --qbf_dom_pre_inst                      false
% 11.44/1.99  --qbf_sk_in                             false
% 11.44/1.99  --qbf_pred_elim                         true
% 11.44/1.99  --qbf_split                             512
% 11.44/1.99  
% 11.44/1.99  ------ BMC1 Options
% 11.44/1.99  
% 11.44/1.99  --bmc1_incremental                      false
% 11.44/1.99  --bmc1_axioms                           reachable_all
% 11.44/1.99  --bmc1_min_bound                        0
% 11.44/1.99  --bmc1_max_bound                        -1
% 11.44/1.99  --bmc1_max_bound_default                -1
% 11.44/1.99  --bmc1_symbol_reachability              true
% 11.44/1.99  --bmc1_property_lemmas                  false
% 11.44/1.99  --bmc1_k_induction                      false
% 11.44/1.99  --bmc1_non_equiv_states                 false
% 11.44/1.99  --bmc1_deadlock                         false
% 11.44/1.99  --bmc1_ucm                              false
% 11.44/1.99  --bmc1_add_unsat_core                   none
% 11.44/1.99  --bmc1_unsat_core_children              false
% 11.44/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.44/1.99  --bmc1_out_stat                         full
% 11.44/1.99  --bmc1_ground_init                      false
% 11.44/1.99  --bmc1_pre_inst_next_state              false
% 11.44/1.99  --bmc1_pre_inst_state                   false
% 11.44/1.99  --bmc1_pre_inst_reach_state             false
% 11.44/1.99  --bmc1_out_unsat_core                   false
% 11.44/1.99  --bmc1_aig_witness_out                  false
% 11.44/1.99  --bmc1_verbose                          false
% 11.44/1.99  --bmc1_dump_clauses_tptp                false
% 11.44/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.44/1.99  --bmc1_dump_file                        -
% 11.44/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.44/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.44/1.99  --bmc1_ucm_extend_mode                  1
% 11.44/1.99  --bmc1_ucm_init_mode                    2
% 11.44/1.99  --bmc1_ucm_cone_mode                    none
% 11.44/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.44/1.99  --bmc1_ucm_relax_model                  4
% 11.44/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.44/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.44/1.99  --bmc1_ucm_layered_model                none
% 11.44/1.99  --bmc1_ucm_max_lemma_size               10
% 11.44/1.99  
% 11.44/1.99  ------ AIG Options
% 11.44/1.99  
% 11.44/1.99  --aig_mode                              false
% 11.44/1.99  
% 11.44/1.99  ------ Instantiation Options
% 11.44/1.99  
% 11.44/1.99  --instantiation_flag                    false
% 11.44/1.99  --inst_sos_flag                         false
% 11.44/1.99  --inst_sos_phase                        true
% 11.44/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.44/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.44/1.99  --inst_lit_sel_side                     num_symb
% 11.44/1.99  --inst_solver_per_active                1400
% 11.44/1.99  --inst_solver_calls_frac                1.
% 11.44/1.99  --inst_passive_queue_type               priority_queues
% 11.44/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.44/1.99  --inst_passive_queues_freq              [25;2]
% 11.44/1.99  --inst_dismatching                      true
% 11.44/1.99  --inst_eager_unprocessed_to_passive     true
% 11.44/1.99  --inst_prop_sim_given                   true
% 11.44/1.99  --inst_prop_sim_new                     false
% 11.44/1.99  --inst_subs_new                         false
% 11.44/1.99  --inst_eq_res_simp                      false
% 11.44/1.99  --inst_subs_given                       false
% 11.44/1.99  --inst_orphan_elimination               true
% 11.44/1.99  --inst_learning_loop_flag               true
% 11.44/1.99  --inst_learning_start                   3000
% 11.44/1.99  --inst_learning_factor                  2
% 11.44/1.99  --inst_start_prop_sim_after_learn       3
% 11.44/1.99  --inst_sel_renew                        solver
% 11.44/1.99  --inst_lit_activity_flag                true
% 11.44/1.99  --inst_restr_to_given                   false
% 11.44/1.99  --inst_activity_threshold               500
% 11.44/1.99  --inst_out_proof                        true
% 11.44/1.99  
% 11.44/1.99  ------ Resolution Options
% 11.44/1.99  
% 11.44/1.99  --resolution_flag                       false
% 11.44/1.99  --res_lit_sel                           adaptive
% 11.44/1.99  --res_lit_sel_side                      none
% 11.44/1.99  --res_ordering                          kbo
% 11.44/1.99  --res_to_prop_solver                    active
% 11.44/1.99  --res_prop_simpl_new                    false
% 11.44/1.99  --res_prop_simpl_given                  true
% 11.44/1.99  --res_passive_queue_type                priority_queues
% 11.44/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.44/1.99  --res_passive_queues_freq               [15;5]
% 11.44/1.99  --res_forward_subs                      full
% 11.44/1.99  --res_backward_subs                     full
% 11.44/1.99  --res_forward_subs_resolution           true
% 11.44/1.99  --res_backward_subs_resolution          true
% 11.44/1.99  --res_orphan_elimination                true
% 11.44/1.99  --res_time_limit                        2.
% 11.44/1.99  --res_out_proof                         true
% 11.44/1.99  
% 11.44/1.99  ------ Superposition Options
% 11.44/1.99  
% 11.44/1.99  --superposition_flag                    true
% 11.44/1.99  --sup_passive_queue_type                priority_queues
% 11.44/1.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.44/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.44/1.99  --demod_completeness_check              fast
% 11.44/1.99  --demod_use_ground                      true
% 11.44/1.99  --sup_to_prop_solver                    active
% 11.44/1.99  --sup_prop_simpl_new                    false
% 11.44/1.99  --sup_prop_simpl_given                  false
% 11.44/1.99  --sup_fun_splitting                     true
% 11.44/1.99  --sup_smt_interval                      10000
% 11.44/1.99  
% 11.44/1.99  ------ Superposition Simplification Setup
% 11.44/1.99  
% 11.44/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.44/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.44/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.44/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/1.99  --sup_full_triv                         [TrivRules]
% 11.44/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.44/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.44/1.99  --sup_immed_triv                        [TrivRules]
% 11.44/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.44/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.44/1.99  --sup_immed_bw_main                     []
% 11.44/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.44/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.44/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.44/1.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 11.44/1.99  
% 11.44/1.99  ------ Combination Options
% 11.44/1.99  
% 11.44/1.99  --comb_res_mult                         1
% 11.44/1.99  --comb_sup_mult                         1
% 11.44/1.99  --comb_inst_mult                        1000000
% 11.44/1.99  
% 11.44/1.99  ------ Debug Options
% 11.44/1.99  
% 11.44/1.99  --dbg_backtrace                         false
% 11.44/1.99  --dbg_dump_prop_clauses                 false
% 11.44/1.99  --dbg_dump_prop_clauses_file            -
% 11.44/1.99  --dbg_out_stat                          false
% 11.44/1.99  
% 11.44/1.99  
% 11.44/1.99  
% 11.44/1.99  
% 11.44/1.99  ------ Proving...
% 11.44/1.99  
% 11.44/1.99  
% 11.44/1.99  % SZS status Theorem for theBenchmark.p
% 11.44/1.99  
% 11.44/1.99   Resolution empty clause
% 11.44/1.99  
% 11.44/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.44/1.99  
% 11.44/1.99  fof(f1,axiom,(
% 11.44/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.44/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/1.99  
% 11.44/1.99  fof(f14,plain,(
% 11.44/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.44/1.99    inference(cnf_transformation,[],[f1])).
% 11.44/1.99  
% 11.44/1.99  fof(f4,axiom,(
% 11.44/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.44/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/1.99  
% 11.44/1.99  fof(f17,plain,(
% 11.44/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.44/1.99    inference(cnf_transformation,[],[f4])).
% 11.44/1.99  
% 11.44/1.99  fof(f25,plain,(
% 11.44/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.44/1.99    inference(definition_unfolding,[],[f14,f17,f17])).
% 11.44/1.99  
% 11.44/1.99  fof(f3,axiom,(
% 11.44/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.44/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/1.99  
% 11.44/1.99  fof(f16,plain,(
% 11.44/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.44/1.99    inference(cnf_transformation,[],[f3])).
% 11.44/1.99  
% 11.44/1.99  fof(f26,plain,(
% 11.44/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.44/1.99    inference(definition_unfolding,[],[f16,f17])).
% 11.44/1.99  
% 11.44/1.99  fof(f6,axiom,(
% 11.44/1.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.44/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/1.99  
% 11.44/1.99  fof(f19,plain,(
% 11.44/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.44/1.99    inference(cnf_transformation,[],[f6])).
% 11.44/1.99  
% 11.44/1.99  fof(f2,axiom,(
% 11.44/1.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.44/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/1.99  
% 11.44/1.99  fof(f15,plain,(
% 11.44/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 11.44/1.99    inference(cnf_transformation,[],[f2])).
% 11.44/1.99  
% 11.44/1.99  fof(f23,plain,(
% 11.44/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.44/1.99    inference(definition_unfolding,[],[f15,f17])).
% 11.44/1.99  
% 11.44/1.99  fof(f28,plain,(
% 11.44/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2)))) )),
% 11.44/1.99    inference(definition_unfolding,[],[f19,f23,f23,f23,f23])).
% 11.44/1.99  
% 11.44/1.99  fof(f5,axiom,(
% 11.44/1.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.44/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/1.99  
% 11.44/1.99  fof(f18,plain,(
% 11.44/1.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.44/1.99    inference(cnf_transformation,[],[f5])).
% 11.44/1.99  
% 11.44/1.99  fof(f27,plain,(
% 11.44/1.99    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0) )),
% 11.44/1.99    inference(definition_unfolding,[],[f18,f23])).
% 11.44/1.99  
% 11.44/1.99  fof(f7,axiom,(
% 11.44/1.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.44/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/1.99  
% 11.44/1.99  fof(f20,plain,(
% 11.44/1.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.44/1.99    inference(cnf_transformation,[],[f7])).
% 11.44/1.99  
% 11.44/1.99  fof(f29,plain,(
% 11.44/1.99    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k1_xboole_0) )),
% 11.44/1.99    inference(definition_unfolding,[],[f20,f23])).
% 11.44/1.99  
% 11.44/1.99  fof(f8,axiom,(
% 11.44/1.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 11.44/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/1.99  
% 11.44/1.99  fof(f21,plain,(
% 11.44/1.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 11.44/1.99    inference(cnf_transformation,[],[f8])).
% 11.44/1.99  
% 11.44/1.99  fof(f24,plain,(
% 11.44/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) )),
% 11.44/1.99    inference(definition_unfolding,[],[f21,f23,f23,f17])).
% 11.44/1.99  
% 11.44/1.99  fof(f9,conjecture,(
% 11.44/1.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.44/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/1.99  
% 11.44/1.99  fof(f10,negated_conjecture,(
% 11.44/1.99    ~! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.44/1.99    inference(negated_conjecture,[],[f9])).
% 11.44/1.99  
% 11.44/1.99  fof(f11,plain,(
% 11.44/1.99    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1)),
% 11.44/1.99    inference(ennf_transformation,[],[f10])).
% 11.44/1.99  
% 11.44/1.99  fof(f12,plain,(
% 11.44/1.99    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1) => k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 11.44/1.99    introduced(choice_axiom,[])).
% 11.44/1.99  
% 11.44/1.99  fof(f13,plain,(
% 11.44/1.99    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 11.44/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 11.44/1.99  
% 11.44/1.99  fof(f22,plain,(
% 11.44/1.99    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 11.44/1.99    inference(cnf_transformation,[],[f13])).
% 11.44/1.99  
% 11.44/1.99  fof(f30,plain,(
% 11.44/1.99    k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))))),
% 11.44/1.99    inference(definition_unfolding,[],[f22,f23])).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1,plain,
% 11.44/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.44/1.99      inference(cnf_transformation,[],[f25]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_2,plain,
% 11.44/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.44/1.99      inference(cnf_transformation,[],[f26]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_24,plain,
% 11.44/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_2]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_46,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_24,c_24]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_886,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_46]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_4,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
% 11.44/1.99      inference(cnf_transformation,[],[f28]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1063,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))),X2))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))))) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_886,c_4]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_3,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
% 11.44/1.99      inference(cnf_transformation,[],[f27]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_31,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0)) = k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_32,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0)) = X0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_31,c_3]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_68,plain,
% 11.44/1.99      ( k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_32,c_24]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_69,plain,
% 11.44/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0))) = X0 ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_32,c_1]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_71,plain,
% 11.44/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_68,c_69]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1076,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_886,c_71]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1083,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_1063,c_1076]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_5,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k1_xboole_0 ),
% 11.44/1.99      inference(cnf_transformation,[],[f29]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_249,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_0,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k2_xboole_0(X0,X1) ),
% 11.44/1.99      inference(cnf_transformation,[],[f24]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_141,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0))))) = k2_xboole_0(X0,X0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_190,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(X0,X0) ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_141,c_71]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_368,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k2_xboole_0(X1,X1) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_249,c_190]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_398,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k1_xboole_0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_71,c_5]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_140,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))))) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_191,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_140,c_2]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_576,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_191]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_621,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_576]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_648,plain,
% 11.44/1.99      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k1_xboole_0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_621,c_24,c_398]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_29,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_708,plain,
% 11.44/1.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_648,c_29]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_710,plain,
% 11.44/1.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_708,c_2]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1084,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,X0) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_1083,c_368,c_398,c_710]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1672,plain,
% 11.44/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k1_xboole_0,X0)) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_24,c_1084]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_689,plain,
% 11.44/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_648]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_803,plain,
% 11.44/1.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_689,c_29]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_805,plain,
% 11.44/1.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_803,c_710]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_806,plain,
% 11.44/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_805,c_24]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1708,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_1672,c_806]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_296,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1))) = k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_362,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1))) = X0 ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_296,c_3]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6063,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X0,X1)))) = X0 ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_362]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_167,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_187,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_167,c_24]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6247,plain,
% 11.44/1.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_6063,c_24,c_187]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6064,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_2,c_362]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6249,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_6247,c_6064]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6259,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_6249,c_2]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6619,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)))))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1708,c_6259]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_5524,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1708,c_1]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6728,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_6619,c_5524]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_890,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_710,c_46]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_705,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_648,c_68]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1000,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_890,c_705,c_710,c_806]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1622,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1000,c_806]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1623,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_1622,c_710]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1597,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1000,c_2]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1601,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1000,c_1]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_857,plain,
% 11.44/1.99      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_710,c_24]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1643,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_1601,c_806,c_857]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1646,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_1597,c_1643]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6050,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X0),X0),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X0),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X0),X0))) = X0 ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_71,c_362]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6265,plain,
% 11.44/1.99      ( k2_xboole_0(X0,X0) = X0 ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_6050,c_398,c_710,c_1084]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_33,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0)) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_5,c_2]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_34,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0)) = k1_xboole_0 ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_33,c_5]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_164,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0),k1_xboole_0),k4_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0),k4_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0),k1_xboole_0))) = k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_34,c_0]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_79,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0) = k2_xboole_0(X0,X0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_34,c_3]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_188,plain,
% 11.44/1.99      ( k2_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0) = k2_xboole_0(X0,X0) ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_164,c_34,c_79]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6043,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0))),k1_xboole_0),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0))),k1_xboole_0))) = k2_xboole_0(X0,X0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_188,c_362]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6283,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k1_xboole_0))) = X0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_6043,c_6265]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6284,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = X0 ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_6283,c_806,c_857]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_811,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_710,c_29]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6285,plain,
% 11.44/1.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_6284,c_806,c_811]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6729,plain,
% 11.44/1.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.44/1.99      inference(demodulation,
% 11.44/1.99                [status(thm)],
% 11.44/1.99                [c_6728,c_1623,c_1646,c_6247,c_6265,c_6285]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_810,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_710,c_576]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_2457,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_810,c_1]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6632,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0)))))) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_2457,c_6259]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_2456,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k2_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_810,c_24]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6105,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k1_xboole_0,X0)))) = X0 ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_857,c_362]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1431,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))))) = k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_857,c_0]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1468,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0)) = k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_1431,c_806,c_810,c_811]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6207,plain,
% 11.44/1.99      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.44/1.99      inference(light_normalisation,
% 11.44/1.99                [status(thm)],
% 11.44/1.99                [c_6105,c_806,c_810,c_811,c_1468]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6718,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)))),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)))))) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.44/1.99      inference(light_normalisation,[status(thm)],[c_6632,c_68,c_2456,c_6207]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6719,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)))) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_6718,c_6207]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6730,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)))) = k1_xboole_0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_6729,c_6719]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6734,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0))) = k1_xboole_0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_6730,c_6729]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6735,plain,
% 11.44/1.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_6734,c_806,c_811]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_913,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_46]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_7195,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_6735,c_913]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_39,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_24]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_49,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_39,c_24]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_1792,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_49,c_71]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_2967,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_1792]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_8236,plain,
% 11.44/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_7195,c_2967]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_159,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k2_xboole_0(X0,X1) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_10912,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)))) = k2_xboole_0(X0,X1) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_8236,c_159]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_7313,plain,
% 11.44/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_1,c_6247]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_7407,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))))) ),
% 11.44/1.99      inference(superposition,[status(thm)],[c_7313,c_4]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_7410,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_7407,c_2]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_7411,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_7410,c_24]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_11046,plain,
% 11.44/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_10912,c_6285,c_7411]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_6,negated_conjecture,
% 11.44/1.99      ( k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
% 11.44/1.99      inference(cnf_transformation,[],[f30]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_14230,plain,
% 11.44/1.99      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 11.44/1.99      inference(demodulation,[status(thm)],[c_11046,c_6]) ).
% 11.44/1.99  
% 11.44/1.99  cnf(c_14490,plain,
% 11.44/1.99      ( $false ),
% 11.44/1.99      inference(equality_resolution_simp,[status(thm)],[c_14230]) ).
% 11.44/1.99  
% 11.44/1.99  
% 11.44/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.44/1.99  
% 11.44/1.99  ------                               Statistics
% 11.44/1.99  
% 11.44/1.99  ------ General
% 11.44/1.99  
% 11.44/1.99  abstr_ref_over_cycles:                  0
% 11.44/1.99  abstr_ref_under_cycles:                 0
% 11.44/1.99  gc_basic_clause_elim:                   0
% 11.44/1.99  forced_gc_time:                         0
% 11.44/1.99  parsing_time:                           0.007
% 11.44/1.99  unif_index_cands_time:                  0.
% 11.44/1.99  unif_index_add_time:                    0.
% 11.44/1.99  orderings_time:                         0.
% 11.44/1.99  out_proof_time:                         0.016
% 11.44/1.99  total_time:                             1.062
% 11.44/1.99  num_of_symbols:                         36
% 11.44/1.99  num_of_terms:                           21143
% 11.44/1.99  
% 11.44/1.99  ------ Preprocessing
% 11.44/1.99  
% 11.44/1.99  num_of_splits:                          0
% 11.44/1.99  num_of_split_atoms:                     0
% 11.44/1.99  num_of_reused_defs:                     0
% 11.44/1.99  num_eq_ax_congr_red:                    0
% 11.44/1.99  num_of_sem_filtered_clauses:            0
% 11.44/1.99  num_of_subtypes:                        0
% 11.44/1.99  monotx_restored_types:                  0
% 11.44/1.99  sat_num_of_epr_types:                   0
% 11.44/1.99  sat_num_of_non_cyclic_types:            0
% 11.44/1.99  sat_guarded_non_collapsed_types:        0
% 11.44/1.99  num_pure_diseq_elim:                    0
% 11.44/1.99  simp_replaced_by:                       0
% 11.44/1.99  res_preprocessed:                       18
% 11.44/1.99  prep_upred:                             0
% 11.44/1.99  prep_unflattend:                        0
% 11.44/1.99  smt_new_axioms:                         0
% 11.44/1.99  pred_elim_cands:                        0
% 11.44/1.99  pred_elim:                              0
% 11.44/1.99  pred_elim_cl:                           0
% 11.44/1.99  pred_elim_cycles:                       0
% 11.44/1.99  merged_defs:                            0
% 11.44/1.99  merged_defs_ncl:                        0
% 11.44/1.99  bin_hyper_res:                          0
% 11.44/1.99  prep_cycles:                            2
% 11.44/1.99  pred_elim_time:                         0.
% 11.44/1.99  splitting_time:                         0.
% 11.44/1.99  sem_filter_time:                        0.
% 11.44/1.99  monotx_time:                            0.
% 11.44/1.99  subtype_inf_time:                       0.
% 11.44/1.99  
% 11.44/1.99  ------ Problem properties
% 11.44/1.99  
% 11.44/1.99  clauses:                                7
% 11.44/1.99  conjectures:                            1
% 11.44/1.99  epr:                                    0
% 11.44/1.99  horn:                                   7
% 11.44/1.99  ground:                                 1
% 11.44/1.99  unary:                                  7
% 11.44/1.99  binary:                                 0
% 11.44/1.99  lits:                                   7
% 11.44/1.99  lits_eq:                                7
% 11.44/1.99  fd_pure:                                0
% 11.44/1.99  fd_pseudo:                              0
% 11.44/1.99  fd_cond:                                0
% 11.44/1.99  fd_pseudo_cond:                         0
% 11.44/1.99  ac_symbols:                             0
% 11.44/1.99  
% 11.44/1.99  ------ Propositional Solver
% 11.44/1.99  
% 11.44/1.99  prop_solver_calls:                      13
% 11.44/1.99  prop_fast_solver_calls:                 48
% 11.44/1.99  smt_solver_calls:                       0
% 11.44/1.99  smt_fast_solver_calls:                  0
% 11.44/1.99  prop_num_of_clauses:                    201
% 11.44/1.99  prop_preprocess_simplified:             269
% 11.44/1.99  prop_fo_subsumed:                       0
% 11.44/1.99  prop_solver_time:                       0.
% 11.44/1.99  smt_solver_time:                        0.
% 11.44/1.99  smt_fast_solver_time:                   0.
% 11.44/1.99  prop_fast_solver_time:                  0.
% 11.44/1.99  prop_unsat_core_time:                   0.
% 11.44/1.99  
% 11.44/1.99  ------ QBF
% 11.44/1.99  
% 11.44/1.99  qbf_q_res:                              0
% 11.44/1.99  qbf_num_tautologies:                    0
% 11.44/1.99  qbf_prep_cycles:                        0
% 11.44/1.99  
% 11.44/1.99  ------ BMC1
% 11.44/1.99  
% 11.44/1.99  bmc1_current_bound:                     -1
% 11.44/1.99  bmc1_last_solved_bound:                 -1
% 11.44/1.99  bmc1_unsat_core_size:                   -1
% 11.44/1.99  bmc1_unsat_core_parents_size:           -1
% 11.44/1.99  bmc1_merge_next_fun:                    0
% 11.44/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.44/1.99  
% 11.44/1.99  ------ Instantiation
% 11.44/1.99  
% 11.44/1.99  inst_num_of_clauses:                    0
% 11.44/1.99  inst_num_in_passive:                    0
% 11.44/1.99  inst_num_in_active:                     0
% 11.44/1.99  inst_num_in_unprocessed:                0
% 11.44/1.99  inst_num_of_loops:                      0
% 11.44/1.99  inst_num_of_learning_restarts:          0
% 11.44/1.99  inst_num_moves_active_passive:          0
% 11.44/1.99  inst_lit_activity:                      0
% 11.44/1.99  inst_lit_activity_moves:                0
% 11.44/1.99  inst_num_tautologies:                   0
% 11.44/1.99  inst_num_prop_implied:                  0
% 11.44/1.99  inst_num_existing_simplified:           0
% 11.44/1.99  inst_num_eq_res_simplified:             0
% 11.44/1.99  inst_num_child_elim:                    0
% 11.44/1.99  inst_num_of_dismatching_blockings:      0
% 11.44/1.99  inst_num_of_non_proper_insts:           0
% 11.44/1.99  inst_num_of_duplicates:                 0
% 11.44/1.99  inst_inst_num_from_inst_to_res:         0
% 11.44/1.99  inst_dismatching_checking_time:         0.
% 11.44/1.99  
% 11.44/1.99  ------ Resolution
% 11.44/1.99  
% 11.44/1.99  res_num_of_clauses:                     0
% 11.44/1.99  res_num_in_passive:                     0
% 11.44/1.99  res_num_in_active:                      0
% 11.44/1.99  res_num_of_loops:                       20
% 11.44/1.99  res_forward_subset_subsumed:            0
% 11.44/1.99  res_backward_subset_subsumed:           0
% 11.44/1.99  res_forward_subsumed:                   0
% 11.44/1.99  res_backward_subsumed:                  0
% 11.44/1.99  res_forward_subsumption_resolution:     0
% 11.44/1.99  res_backward_subsumption_resolution:    0
% 11.44/1.99  res_clause_to_clause_subsumption:       19495
% 11.44/1.99  res_orphan_elimination:                 0
% 11.44/1.99  res_tautology_del:                      0
% 11.44/1.99  res_num_eq_res_simplified:              0
% 11.44/1.99  res_num_sel_changes:                    0
% 11.44/1.99  res_moves_from_active_to_pass:          0
% 11.44/1.99  
% 11.44/1.99  ------ Superposition
% 11.44/1.99  
% 11.44/1.99  sup_time_total:                         0.
% 11.44/1.99  sup_time_generating:                    0.
% 11.44/1.99  sup_time_sim_full:                      0.
% 11.44/1.99  sup_time_sim_immed:                     0.
% 11.44/1.99  
% 11.44/1.99  sup_num_of_clauses:                     1284
% 11.44/1.99  sup_num_in_active:                      45
% 11.44/1.99  sup_num_in_passive:                     1239
% 11.44/1.99  sup_num_of_loops:                       111
% 11.44/1.99  sup_fw_superposition:                   5297
% 11.44/1.99  sup_bw_superposition:                   4628
% 11.44/1.99  sup_immediate_simplified:               3822
% 11.44/1.99  sup_given_eliminated:                   2
% 11.44/1.99  comparisons_done:                       0
% 11.44/1.99  comparisons_avoided:                    0
% 11.44/1.99  
% 11.44/1.99  ------ Simplifications
% 11.44/1.99  
% 11.44/1.99  
% 11.44/1.99  sim_fw_subset_subsumed:                 0
% 11.44/1.99  sim_bw_subset_subsumed:                 0
% 11.44/1.99  sim_fw_subsumed:                        249
% 11.44/1.99  sim_bw_subsumed:                        43
% 11.44/1.99  sim_fw_subsumption_res:                 0
% 11.44/1.99  sim_bw_subsumption_res:                 0
% 11.44/1.99  sim_tautology_del:                      0
% 11.44/1.99  sim_eq_tautology_del:                   1821
% 11.44/1.99  sim_eq_res_simp:                        0
% 11.44/1.99  sim_fw_demodulated:                     2091
% 11.44/1.99  sim_bw_demodulated:                     167
% 11.44/1.99  sim_light_normalised:                   2206
% 11.44/1.99  sim_joinable_taut:                      0
% 11.44/1.99  sim_joinable_simp:                      0
% 11.44/1.99  sim_ac_normalised:                      0
% 11.44/1.99  sim_smt_subsumption:                    0
% 11.44/1.99  
%------------------------------------------------------------------------------
