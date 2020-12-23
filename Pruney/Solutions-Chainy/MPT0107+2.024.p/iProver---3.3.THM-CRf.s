%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:22 EST 2020

% Result     : Theorem 7.96s
% Output     : CNFRefutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :  110 (46227 expanded)
%              Number of clauses        :   85 (16166 expanded)
%              Number of leaves         :    9 (13221 expanded)
%              Depth                    :   38
%              Number of atoms          :  111 (46228 expanded)
%              Number of equality atoms :  110 (46227 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f30,f30])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f30,f26])).

fof(f9,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f17])).

fof(f32,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(definition_unfolding,[],[f32,f26,f30])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_977,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_979,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_977,c_9])).

cnf(c_0,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_955,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_0,c_9])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1001,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_10,c_9])).

cnf(c_1008,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1001,c_9])).

cnf(c_1645,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X0)))) = k4_xboole_0(X0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_955,c_1008])).

cnf(c_2870,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_979,c_1645])).

cnf(c_2949,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_2870,c_10])).

cnf(c_3134,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_2949,c_9])).

cnf(c_975,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_9,c_9])).

cnf(c_984,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_975,c_9])).

cnf(c_3160,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_3134,c_9,c_984])).

cnf(c_3229,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3160,c_984])).

cnf(c_995,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_10])).

cnf(c_1038,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_995,c_9])).

cnf(c_1048,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1038,c_9])).

cnf(c_1774,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_995,c_1048])).

cnf(c_1775,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_1048])).

cnf(c_1866,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1775,c_995])).

cnf(c_1867,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_1866,c_9])).

cnf(c_1869,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1774,c_1867])).

cnf(c_4070,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_3229,c_1869])).

cnf(c_4369,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0)),k4_xboole_0(X0,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_4070,c_955])).

cnf(c_1033,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_995])).

cnf(c_1059,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_1033,c_9])).

cnf(c_3626,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1059,c_10])).

cnf(c_3649,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3626,c_10])).

cnf(c_4377,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_4070,c_3649])).

cnf(c_4378,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X0,X0),X0) ),
    inference(demodulation,[status(thm)],[c_4377,c_4070])).

cnf(c_3115,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_2949,c_1645])).

cnf(c_4380,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_4378,c_3115])).

cnf(c_4398,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4369,c_4380])).

cnf(c_3138,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2949,c_955])).

cnf(c_4400,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_4398,c_2949,c_3138])).

cnf(c_8,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1393,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,X0),X0)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_995,c_8])).

cnf(c_1464,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_1393,c_9,c_955])).

cnf(c_4646,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_4400,c_1464])).

cnf(c_5412,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X0))))) = k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_4646,c_979])).

cnf(c_5414,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_5412,c_3229,c_3649])).

cnf(c_5599,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_5414,c_955])).

cnf(c_5613,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),X0)) ),
    inference(superposition,[status(thm)],[c_5414,c_1059])).

cnf(c_5615,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5613,c_4400,c_5414])).

cnf(c_5639,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k2_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5599,c_5615])).

cnf(c_5641,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_5639,c_3138])).

cnf(c_5712,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)))) = k4_xboole_0(k2_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_5641,c_3649])).

cnf(c_5721,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_5712,c_4400,c_5414])).

cnf(c_5795,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X0))) = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_5721,c_1])).

cnf(c_5833,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_5795,c_2949,c_4646])).

cnf(c_5941,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5833,c_979])).

cnf(c_1031,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_995])).

cnf(c_1061,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_1031,c_995])).

cnf(c_1063,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_1061,c_9])).

cnf(c_1090,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1063,c_9])).

cnf(c_5958,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_5941,c_1090,c_3649])).

cnf(c_971,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_1255,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_971,c_9])).

cnf(c_7192,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5958,c_1255])).

cnf(c_976,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_18682,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7192,c_976])).

cnf(c_1035,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_995,c_995])).

cnf(c_1053,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) ),
    inference(demodulation,[status(thm)],[c_1035,c_9])).

cnf(c_18715,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(demodulation,[status(thm)],[c_18682,c_9,c_1053])).

cnf(c_7197,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_5958,c_1048])).

cnf(c_7203,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7197,c_995])).

cnf(c_18716,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_18715,c_1090,c_7203])).

cnf(c_19450,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_18716,c_1255])).

cnf(c_11,negated_conjecture,
    ( k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_962,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),sK1))) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_11,c_9,c_10])).

cnf(c_22435,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK1))) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_19450,c_962])).

cnf(c_5778,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_5721,c_955])).

cnf(c_5876,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k2_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5778,c_5833])).

cnf(c_5794,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_5721,c_9])).

cnf(c_5836,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_5794,c_9])).

cnf(c_5877,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k2_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_5876,c_5836])).

cnf(c_5879,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_5877,c_2949,c_5641])).

cnf(c_7188,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5958,c_5879])).

cnf(c_7223,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7188,c_5958])).

cnf(c_7225,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7223,c_1063])).

cnf(c_22439,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_22435,c_7225])).

cnf(c_22440,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_22439])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.96/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.96/1.50  
% 7.96/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.96/1.50  
% 7.96/1.50  ------  iProver source info
% 7.96/1.50  
% 7.96/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.96/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.96/1.50  git: non_committed_changes: false
% 7.96/1.50  git: last_make_outside_of_git: false
% 7.96/1.50  
% 7.96/1.50  ------ 
% 7.96/1.50  ------ Parsing...
% 7.96/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.50  ------ Proving...
% 7.96/1.50  ------ Problem Properties 
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  clauses                                 12
% 7.96/1.50  conjectures                             2
% 7.96/1.50  EPR                                     0
% 7.96/1.50  Horn                                    8
% 7.96/1.50  unary                                   6
% 7.96/1.50  binary                                  2
% 7.96/1.50  lits                                    23
% 7.96/1.50  lits eq                                 9
% 7.96/1.50  fd_pure                                 0
% 7.96/1.50  fd_pseudo                               0
% 7.96/1.50  fd_cond                                 0
% 7.96/1.50  fd_pseudo_cond                          3
% 7.96/1.50  AC symbols                              0
% 7.96/1.50  
% 7.96/1.50  ------ Input Options Time Limit: Unbounded
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing...
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.96/1.50  Current options:
% 7.96/1.50  ------ 
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  ------ Proving...
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.50  
% 7.96/1.50  ------ Proving...
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.50  
% 7.96/1.50  ------ Proving...
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.50  
% 7.96/1.50  ------ Proving...
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  % SZS status Theorem for theBenchmark.p
% 7.96/1.50  
% 7.96/1.50   Resolution empty clause
% 7.96/1.50  
% 7.96/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.96/1.50  
% 7.96/1.50  fof(f5,axiom,(
% 7.96/1.50    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.96/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f28,plain,(
% 7.96/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f5])).
% 7.96/1.50  
% 7.96/1.50  fof(f1,axiom,(
% 7.96/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.96/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f19,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f1])).
% 7.96/1.50  
% 7.96/1.50  fof(f7,axiom,(
% 7.96/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.96/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f30,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.96/1.50    inference(cnf_transformation,[],[f7])).
% 7.96/1.50  
% 7.96/1.50  fof(f34,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f19,f30,f30])).
% 7.96/1.50  
% 7.96/1.50  fof(f8,axiom,(
% 7.96/1.50    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.96/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f31,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f8])).
% 7.96/1.50  
% 7.96/1.50  fof(f3,axiom,(
% 7.96/1.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 7.96/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f26,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 7.96/1.50    inference(cnf_transformation,[],[f3])).
% 7.96/1.50  
% 7.96/1.50  fof(f33,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f31,f26])).
% 7.96/1.50  
% 7.96/1.50  fof(f6,axiom,(
% 7.96/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.96/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f29,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.96/1.50    inference(cnf_transformation,[],[f6])).
% 7.96/1.50  
% 7.96/1.50  fof(f36,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f29,f30])).
% 7.96/1.50  
% 7.96/1.50  fof(f4,axiom,(
% 7.96/1.50    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 7.96/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f27,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f4])).
% 7.96/1.50  
% 7.96/1.50  fof(f35,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f27,f30,f26])).
% 7.96/1.50  
% 7.96/1.50  fof(f9,conjecture,(
% 7.96/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.96/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f10,negated_conjecture,(
% 7.96/1.50    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.96/1.50    inference(negated_conjecture,[],[f9])).
% 7.96/1.50  
% 7.96/1.50  fof(f11,plain,(
% 7.96/1.50    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.96/1.50    inference(ennf_transformation,[],[f10])).
% 7.96/1.50  
% 7.96/1.50  fof(f17,plain,(
% 7.96/1.50    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 7.96/1.50    introduced(choice_axiom,[])).
% 7.96/1.50  
% 7.96/1.50  fof(f18,plain,(
% 7.96/1.50    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 7.96/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f17])).
% 7.96/1.50  
% 7.96/1.50  fof(f32,plain,(
% 7.96/1.50    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 7.96/1.50    inference(cnf_transformation,[],[f18])).
% 7.96/1.50  
% 7.96/1.50  fof(f37,plain,(
% 7.96/1.50    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),
% 7.96/1.50    inference(definition_unfolding,[],[f32,f26,f30])).
% 7.96/1.50  
% 7.96/1.50  cnf(c_9,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.96/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.96/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_977,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_979,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_977,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_0,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(X0,X1) ),
% 7.96/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_955,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,X1) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_0,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_10,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1001,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_10,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1008,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_1001,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1645,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X0)))) = k4_xboole_0(X0,k2_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_955,c_1008]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2870,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,k2_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_979,c_1645]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2949,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_2870,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3134,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_2949,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_975,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_9,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_984,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_975,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3160,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3134,c_9,c_984]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3229,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3160,c_984]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_995,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1038,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_995,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1048,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_1038,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1774,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_995,c_1048]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1775,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1,c_1048]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1866,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_1775,c_995]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1867,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_1866,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1869,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_1774,c_1867]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4070,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3229,c_1869]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4369,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0)),k4_xboole_0(X0,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_4070,c_955]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1033,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_9,c_995]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1059,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_1033,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3626,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1059,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3649,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_3626,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4377,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X0,X0),X0) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_4070,c_3649]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4378,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X0,X0),X0) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_4377,c_4070]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3115,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X0) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_2949,c_1645]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4380,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_4378,c_3115]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4398,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_4369,c_4380]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3138,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_2949,c_955]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4400,plain,
% 7.96/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_4398,c_2949,c_3138]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_8,plain,
% 7.96/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 7.96/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1393,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,X0),X0)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_995,c_8]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1464,plain,
% 7.96/1.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_1393,c_9,c_955]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4646,plain,
% 7.96/1.50      ( k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_4400,c_1464]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5412,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X0))))) = k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_4646,c_979]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5414,plain,
% 7.96/1.50      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_5412,c_3229,c_3649]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5599,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k2_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_5414,c_955]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5613,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_5414,c_1059]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5615,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_5613,c_4400,c_5414]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5639,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k2_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_5599,c_5615]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5641,plain,
% 7.96/1.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_5639,c_3138]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5712,plain,
% 7.96/1.50      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)))) = k4_xboole_0(k2_xboole_0(X0,X0),X0) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_5641,c_3649]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5721,plain,
% 7.96/1.50      ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_5712,c_4400,c_5414]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5795,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X0))) = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_5721,c_1]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5833,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_5795,c_2949,c_4646]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5941,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_5833,c_979]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1031,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1,c_995]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1061,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_1031,c_995]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1063,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_1061,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1090,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1063,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5958,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_5941,c_1090,c_3649]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_971,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1255,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_971,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_7192,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_5958,c_1255]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_976,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_18682,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_7192,c_976]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1035,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_995,c_995]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1053,plain,
% 7.96/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_1035,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_18715,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X0)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_18682,c_9,c_1053]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_7197,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_5958,c_1048]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_7203,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_7197,c_995]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_18716,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_18715,c_1090,c_7203]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_19450,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_18716,c_1255]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_11,negated_conjecture,
% 7.96/1.50      ( k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
% 7.96/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_962,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),sK1))) != k4_xboole_0(sK1,sK2) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_11,c_9,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_22435,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK1))) != k4_xboole_0(sK1,sK2) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_19450,c_962]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5778,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k2_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_5721,c_955]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5876,plain,
% 7.96/1.50      ( k2_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k2_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_5778,c_5833]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5794,plain,
% 7.96/1.50      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_5721,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5836,plain,
% 7.96/1.50      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_5794,c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5877,plain,
% 7.96/1.50      ( k2_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k2_xboole_0(X0,X0)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_5876,c_5836]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5879,plain,
% 7.96/1.50      ( k2_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_5877,c_2949,c_5641]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_7188,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_5958,c_5879]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_7223,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_7188,c_5958]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_7225,plain,
% 7.96/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_7223,c_1063]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_22439,plain,
% 7.96/1.50      ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_22435,c_7225]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_22440,plain,
% 7.96/1.50      ( $false ),
% 7.96/1.50      inference(equality_resolution_simp,[status(thm)],[c_22439]) ).
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.96/1.50  
% 7.96/1.50  ------                               Statistics
% 7.96/1.50  
% 7.96/1.50  ------ Selected
% 7.96/1.50  
% 7.96/1.50  total_time:                             0.949
% 7.96/1.50  
%------------------------------------------------------------------------------
