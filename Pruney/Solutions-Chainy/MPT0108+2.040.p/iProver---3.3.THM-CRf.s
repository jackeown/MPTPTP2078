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
% DateTime   : Thu Dec  3 11:25:34 EST 2020

% Result     : Theorem 50.93s
% Output     : CNFRefutation 50.93s
% Verified   : 
% Statistics : Number of formulae       :  206 (315709 expanded)
%              Number of clauses        :  168 (75561 expanded)
%              Number of leaves         :   13 (101384 expanded)
%              Depth                    :   46
%              Number of atoms          :  207 (315710 expanded)
%              Number of equality atoms :  206 (315709 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f24,f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f25,f24,f24])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f22,f28,f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f26,f28,f24])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f19,f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f21,f24,f24,f24,f24])).

fof(f12,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f13])).

fof(f16,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f29,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
    inference(definition_unfolding,[],[f29,f28,f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f23,f28,f28])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_112,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_35,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_30,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_6,c_4])).

cnf(c_47,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_30,c_0])).

cnf(c_59,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_47,c_47])).

cnf(c_242,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_59,c_1])).

cnf(c_250,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,X1) ),
    inference(light_normalisation,[status(thm)],[c_242,c_47])).

cnf(c_800,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_250,c_6])).

cnf(c_812,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_800,c_250])).

cnf(c_115,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_47,c_6])).

cnf(c_322,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_115])).

cnf(c_813,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_812,c_47,c_322])).

cnf(c_814,plain,
    ( k4_xboole_0(X0,X0) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_813])).

cnf(c_58,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_47,c_0])).

cnf(c_823,plain,
    ( k5_xboole_0(X0,X0) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_814,c_58])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_930,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_823,c_8])).

cnf(c_66,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_58,c_8])).

cnf(c_821,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(sP0_iProver_split,X1) ),
    inference(demodulation,[status(thm)],[c_814,c_66])).

cnf(c_7,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_157,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_7,c_47])).

cnf(c_171,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_47,c_157])).

cnf(c_822,plain,
    ( k5_xboole_0(sP0_iProver_split,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_814,c_171])).

cnf(c_826,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_821,c_822])).

cnf(c_1090,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_930,c_826])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_824,plain,
    ( k5_xboole_0(X0,sP0_iProver_split) = X0 ),
    inference(demodulation,[status(thm)],[c_814,c_2])).

cnf(c_1098,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1090,c_824])).

cnf(c_1056,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_8,c_826])).

cnf(c_1446,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_1098,c_1056])).

cnf(c_1492,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_35,c_1446])).

cnf(c_10620,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X0),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_112,c_1492])).

cnf(c_609,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_322])).

cnf(c_687,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_609,c_322])).

cnf(c_837,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_800,c_687])).

cnf(c_838,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_837,c_47,c_322,c_814])).

cnf(c_10948,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_10620,c_6,c_822,c_838])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_31,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_3,c_6])).

cnf(c_172,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_31,c_157])).

cnf(c_174,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_172,c_31])).

cnf(c_175,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_174,c_115])).

cnf(c_161280,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10948,c_175])).

cnf(c_1448,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1098,c_826])).

cnf(c_1124,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,sP0_iProver_split)) = X1 ),
    inference(superposition,[status(thm)],[c_823,c_1056])).

cnf(c_1140,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(light_normalisation,[status(thm)],[c_1124,c_824])).

cnf(c_1462,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
    inference(superposition,[status(thm)],[c_8,c_1140])).

cnf(c_1936,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X2,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1448,c_1462])).

cnf(c_2029,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X0)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_1936,c_8])).

cnf(c_2331,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_822,c_2029])).

cnf(c_2478,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,sP0_iProver_split)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_2331,c_1056])).

cnf(c_2514,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_2478,c_824])).

cnf(c_161467,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X3) ),
    inference(superposition,[status(thm)],[c_175,c_2514])).

cnf(c_161794,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = sP5_iProver_split(X0,X1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_161467])).

cnf(c_162038,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = sP5_iProver_split(X0,X1) ),
    inference(demodulation,[status(thm)],[c_161280,c_161794])).

cnf(c_9,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_170899,plain,
    ( k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),sP5_iProver_split(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_162038,c_9])).

cnf(c_159,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_157])).

cnf(c_635,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_322,c_159])).

cnf(c_225,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_171,c_8])).

cnf(c_519,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_6,c_225])).

cnf(c_298,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),X2) ),
    inference(superposition,[status(thm)],[c_6,c_66])).

cnf(c_553,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_519,c_47,c_66,c_298,c_322])).

cnf(c_38,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_554,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(light_normalisation,[status(thm)],[c_553,c_38])).

cnf(c_660,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X1,X0))) = X1 ),
    inference(demodulation,[status(thm)],[c_635,c_6,c_554])).

cnf(c_661,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = X1 ),
    inference(demodulation,[status(thm)],[c_660,c_47])).

cnf(c_2782,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_661,c_1140])).

cnf(c_1439,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_159,c_1098])).

cnf(c_2495,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2331,c_1098])).

cnf(c_6268,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP0_iProver_split) = k5_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1439,c_2495])).

cnf(c_5,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_872,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k5_xboole_0(sP0_iProver_split,k4_xboole_0(k4_xboole_0(X1,X0),sP0_iProver_split)) ),
    inference(superposition,[status(thm)],[c_814,c_5])).

cnf(c_882,plain,
    ( k4_xboole_0(X0,sP0_iProver_split) = X0 ),
    inference(superposition,[status(thm)],[c_814,c_47])).

cnf(c_906,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k5_xboole_0(sP0_iProver_split,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_872,c_882])).

cnf(c_907,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_906,c_822])).

cnf(c_3873,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_907,c_35])).

cnf(c_885,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_814,c_5])).

cnf(c_781,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_250,c_159])).

cnf(c_783,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_250,c_59])).

cnf(c_851,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_783,c_814])).

cnf(c_852,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_781,c_851])).

cnf(c_330,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_59,c_115])).

cnf(c_361,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_330,c_59,c_250])).

cnf(c_853,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_852,c_361])).

cnf(c_894,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_885,c_853])).

cnf(c_3738,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_59,c_894])).

cnf(c_3808,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3738,c_47])).

cnf(c_3895,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_3873,c_823,c_3808])).

cnf(c_3946,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_5,c_3895])).

cnf(c_7587,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),X2)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_115,c_3946])).

cnf(c_7725,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X0,X2)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_7587,c_6,c_157])).

cnf(c_10080,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_7725,c_6])).

cnf(c_10288,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP0_iProver_split)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_3946,c_10080])).

cnf(c_2430,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_8,c_2331])).

cnf(c_3102,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),sP0_iProver_split) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_823,c_2430])).

cnf(c_67,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_58,c_8])).

cnf(c_802,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_250,c_5])).

cnf(c_834,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(k5_xboole_0(X0,sP0_iProver_split),X1) ),
    inference(light_normalisation,[status(thm)],[c_802,c_814])).

cnf(c_835,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split) = k4_xboole_0(k5_xboole_0(X0,sP0_iProver_split),X1) ),
    inference(demodulation,[status(thm)],[c_834,c_814])).

cnf(c_2648,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_2495])).

cnf(c_3233,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split),k5_xboole_0(X0,X1)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_3102,c_67,c_835,c_2648])).

cnf(c_3234,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_3233,c_2495])).

cnf(c_342,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_115,c_0])).

cnf(c_3325,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_3234,c_342])).

cnf(c_3374,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) = k4_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) ),
    inference(demodulation,[status(thm)],[c_3325,c_3234])).

cnf(c_3375,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) = k5_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3374,c_2495])).

cnf(c_7569,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sP0_iProver_split),k5_xboole_0(k4_xboole_0(X1,X0),X0)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_3375,c_3946])).

cnf(c_7732,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X0)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_7569,c_882])).

cnf(c_8030,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X2,X0),X0)) = k5_xboole_0(sP0_iProver_split,k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X0),X0)),sP0_iProver_split)) ),
    inference(superposition,[status(thm)],[c_7732,c_5])).

cnf(c_129,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_47])).

cnf(c_803,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X1)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_250,c_129])).

cnf(c_644,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_322,c_31])).

cnf(c_85,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_47,c_31])).

cnf(c_105,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) ),
    inference(demodulation,[status(thm)],[c_85,c_6,c_47])).

cnf(c_653,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) ),
    inference(light_normalisation,[status(thm)],[c_644,c_105])).

cnf(c_654,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_653,c_129])).

cnf(c_831,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X2)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_803,c_654])).

cnf(c_832,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_831,c_814])).

cnf(c_8093,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X2,X0),X0)) = k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X0),X0)) ),
    inference(demodulation,[status(thm)],[c_8030,c_822,c_832])).

cnf(c_11206,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),X1)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_10288,c_3375,c_8093])).

cnf(c_11571,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),sP0_iProver_split),X0) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) ),
    inference(superposition,[status(thm)],[c_11206,c_894])).

cnf(c_11612,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_11571,c_894,c_2495])).

cnf(c_11576,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,sP0_iProver_split)) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) ),
    inference(superposition,[status(thm)],[c_11206,c_35])).

cnf(c_11609,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_11576,c_882])).

cnf(c_11614,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_11612,c_11609])).

cnf(c_39576,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(X0,X2)) = k5_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_11614,c_8])).

cnf(c_162348,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),sP0_iProver_split)) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6268,c_39576])).

cnf(c_3732,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_47,c_894])).

cnf(c_3814,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3732,c_59])).

cnf(c_468,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_159,c_8])).

cnf(c_32340,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X0))),k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X0),X0),X2) ),
    inference(superposition,[status(thm)],[c_3814,c_468])).

cnf(c_32493,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X2) = k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(light_normalisation,[status(thm)],[c_32340,c_882,c_7732])).

cnf(c_163277,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X1),sP0_iProver_split)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_162348,c_554,c_32493])).

cnf(c_163278,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,sP0_iProver_split),X1)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_163277,c_835])).

cnf(c_11507,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X0),X1),k4_xboole_0(X0,X1))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_1439,c_11206])).

cnf(c_1445,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1098,c_1056])).

cnf(c_8180,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(X3,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2029,c_1445])).

cnf(c_1434,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_8,c_1098])).

cnf(c_1800,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1448,c_1434])).

cnf(c_1449,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1098,c_8])).

cnf(c_1904,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(superposition,[status(thm)],[c_1449,c_1449])).

cnf(c_2486,plain,
    ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2331,c_1446])).

cnf(c_2554,plain,
    ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_2486])).

cnf(c_4690,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,sP0_iProver_split)) = k5_xboole_0(sP0_iProver_split,k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_2554,c_2554])).

cnf(c_4757,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,sP0_iProver_split)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X3,X2)) ),
    inference(demodulation,[status(thm)],[c_4690,c_2554])).

cnf(c_4758,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X3)),X2) ),
    inference(demodulation,[status(thm)],[c_4757,c_824])).

cnf(c_8378,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_8180,c_1800,c_1904,c_4758])).

cnf(c_11665,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_11507,c_8378])).

cnf(c_3770,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_894,c_322])).

cnf(c_1438,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_157,c_1098])).

cnf(c_6119,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_894,c_1438])).

cnf(c_6200,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_6119,c_894])).

cnf(c_11666,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_11665,c_3770,c_6200])).

cnf(c_11991,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X2,k4_xboole_0(X0,X2))) = k4_xboole_0(X1,k4_xboole_0(X1,sP0_iProver_split)) ),
    inference(superposition,[status(thm)],[c_11666,c_112])).

cnf(c_12019,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X2,k4_xboole_0(X0,X2))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_11991,c_6,c_814,c_882])).

cnf(c_17120,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X2,k4_xboole_0(X1,X2))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_1,c_12019])).

cnf(c_22206,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),sP0_iProver_split)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_17120,c_35])).

cnf(c_22275,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,sP0_iProver_split))))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_22206,c_6,c_8378])).

cnf(c_22276,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_22275,c_882])).

cnf(c_163279,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_163278,c_342,c_824,c_22276])).

cnf(c_163280,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP5_iProver_split(X2,X1)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_163279,c_162038])).

cnf(c_170916,plain,
    ( k5_xboole_0(sK1,sK0) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_170899,c_2782,c_163280])).

cnf(c_174084,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_170916])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:02:39 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 50.93/6.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.93/6.98  
% 50.93/6.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 50.93/6.98  
% 50.93/6.98  ------  iProver source info
% 50.93/6.98  
% 50.93/6.98  git: date: 2020-06-30 10:37:57 +0100
% 50.93/6.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 50.93/6.98  git: non_committed_changes: false
% 50.93/6.98  git: last_make_outside_of_git: false
% 50.93/6.98  
% 50.93/6.98  ------ 
% 50.93/6.98  
% 50.93/6.98  ------ Input Options
% 50.93/6.98  
% 50.93/6.98  --out_options                           all
% 50.93/6.98  --tptp_safe_out                         true
% 50.93/6.98  --problem_path                          ""
% 50.93/6.98  --include_path                          ""
% 50.93/6.98  --clausifier                            res/vclausify_rel
% 50.93/6.98  --clausifier_options                    --mode clausify
% 50.93/6.98  --stdin                                 false
% 50.93/6.98  --stats_out                             all
% 50.93/6.98  
% 50.93/6.98  ------ General Options
% 50.93/6.98  
% 50.93/6.98  --fof                                   false
% 50.93/6.98  --time_out_real                         305.
% 50.93/6.98  --time_out_virtual                      -1.
% 50.93/6.98  --symbol_type_check                     false
% 50.93/6.98  --clausify_out                          false
% 50.93/6.98  --sig_cnt_out                           false
% 50.93/6.98  --trig_cnt_out                          false
% 50.93/6.98  --trig_cnt_out_tolerance                1.
% 50.93/6.98  --trig_cnt_out_sk_spl                   false
% 50.93/6.98  --abstr_cl_out                          false
% 50.93/6.98  
% 50.93/6.98  ------ Global Options
% 50.93/6.98  
% 50.93/6.98  --schedule                              default
% 50.93/6.98  --add_important_lit                     false
% 50.93/6.98  --prop_solver_per_cl                    1000
% 50.93/6.98  --min_unsat_core                        false
% 50.93/6.98  --soft_assumptions                      false
% 50.93/6.98  --soft_lemma_size                       3
% 50.93/6.98  --prop_impl_unit_size                   0
% 50.93/6.98  --prop_impl_unit                        []
% 50.93/6.98  --share_sel_clauses                     true
% 50.93/6.98  --reset_solvers                         false
% 50.93/6.98  --bc_imp_inh                            [conj_cone]
% 50.93/6.98  --conj_cone_tolerance                   3.
% 50.93/6.98  --extra_neg_conj                        none
% 50.93/6.98  --large_theory_mode                     true
% 50.93/6.98  --prolific_symb_bound                   200
% 50.93/6.98  --lt_threshold                          2000
% 50.93/6.98  --clause_weak_htbl                      true
% 50.93/6.98  --gc_record_bc_elim                     false
% 50.93/6.98  
% 50.93/6.98  ------ Preprocessing Options
% 50.93/6.98  
% 50.93/6.98  --preprocessing_flag                    true
% 50.93/6.98  --time_out_prep_mult                    0.1
% 50.93/6.98  --splitting_mode                        input
% 50.93/6.98  --splitting_grd                         true
% 50.93/6.98  --splitting_cvd                         false
% 50.93/6.98  --splitting_cvd_svl                     false
% 50.93/6.98  --splitting_nvd                         32
% 50.93/6.98  --sub_typing                            true
% 50.93/6.98  --prep_gs_sim                           true
% 50.93/6.98  --prep_unflatten                        true
% 50.93/6.98  --prep_res_sim                          true
% 50.93/6.98  --prep_upred                            true
% 50.93/6.98  --prep_sem_filter                       exhaustive
% 50.93/6.98  --prep_sem_filter_out                   false
% 50.93/6.98  --pred_elim                             true
% 50.93/6.98  --res_sim_input                         true
% 50.93/6.98  --eq_ax_congr_red                       true
% 50.93/6.98  --pure_diseq_elim                       true
% 50.93/6.98  --brand_transform                       false
% 50.93/6.98  --non_eq_to_eq                          false
% 50.93/6.98  --prep_def_merge                        true
% 50.93/6.98  --prep_def_merge_prop_impl              false
% 50.93/6.98  --prep_def_merge_mbd                    true
% 50.93/6.98  --prep_def_merge_tr_red                 false
% 50.93/6.98  --prep_def_merge_tr_cl                  false
% 50.93/6.98  --smt_preprocessing                     true
% 50.93/6.98  --smt_ac_axioms                         fast
% 50.93/6.98  --preprocessed_out                      false
% 50.93/6.98  --preprocessed_stats                    false
% 50.93/6.98  
% 50.93/6.98  ------ Abstraction refinement Options
% 50.93/6.98  
% 50.93/6.98  --abstr_ref                             []
% 50.93/6.98  --abstr_ref_prep                        false
% 50.93/6.98  --abstr_ref_until_sat                   false
% 50.93/6.98  --abstr_ref_sig_restrict                funpre
% 50.93/6.98  --abstr_ref_af_restrict_to_split_sk     false
% 50.93/6.98  --abstr_ref_under                       []
% 50.93/6.98  
% 50.93/6.98  ------ SAT Options
% 50.93/6.98  
% 50.93/6.98  --sat_mode                              false
% 50.93/6.98  --sat_fm_restart_options                ""
% 50.93/6.98  --sat_gr_def                            false
% 50.93/6.98  --sat_epr_types                         true
% 50.93/6.98  --sat_non_cyclic_types                  false
% 50.93/6.98  --sat_finite_models                     false
% 50.93/6.98  --sat_fm_lemmas                         false
% 50.93/6.98  --sat_fm_prep                           false
% 50.93/6.98  --sat_fm_uc_incr                        true
% 50.93/6.98  --sat_out_model                         small
% 50.93/6.98  --sat_out_clauses                       false
% 50.93/6.98  
% 50.93/6.98  ------ QBF Options
% 50.93/6.98  
% 50.93/6.98  --qbf_mode                              false
% 50.93/6.98  --qbf_elim_univ                         false
% 50.93/6.98  --qbf_dom_inst                          none
% 50.93/6.98  --qbf_dom_pre_inst                      false
% 50.93/6.98  --qbf_sk_in                             false
% 50.93/6.98  --qbf_pred_elim                         true
% 50.93/6.98  --qbf_split                             512
% 50.93/6.98  
% 50.93/6.98  ------ BMC1 Options
% 50.93/6.98  
% 50.93/6.98  --bmc1_incremental                      false
% 50.93/6.98  --bmc1_axioms                           reachable_all
% 50.93/6.98  --bmc1_min_bound                        0
% 50.93/6.98  --bmc1_max_bound                        -1
% 50.93/6.98  --bmc1_max_bound_default                -1
% 50.93/6.98  --bmc1_symbol_reachability              true
% 50.93/6.98  --bmc1_property_lemmas                  false
% 50.93/6.98  --bmc1_k_induction                      false
% 50.93/6.98  --bmc1_non_equiv_states                 false
% 50.93/6.98  --bmc1_deadlock                         false
% 50.93/6.98  --bmc1_ucm                              false
% 50.93/6.98  --bmc1_add_unsat_core                   none
% 50.93/6.98  --bmc1_unsat_core_children              false
% 50.93/6.98  --bmc1_unsat_core_extrapolate_axioms    false
% 50.93/6.98  --bmc1_out_stat                         full
% 50.93/6.98  --bmc1_ground_init                      false
% 50.93/6.98  --bmc1_pre_inst_next_state              false
% 50.93/6.98  --bmc1_pre_inst_state                   false
% 50.93/6.98  --bmc1_pre_inst_reach_state             false
% 50.93/6.98  --bmc1_out_unsat_core                   false
% 50.93/6.98  --bmc1_aig_witness_out                  false
% 50.93/6.98  --bmc1_verbose                          false
% 50.93/6.98  --bmc1_dump_clauses_tptp                false
% 50.93/6.98  --bmc1_dump_unsat_core_tptp             false
% 50.93/6.98  --bmc1_dump_file                        -
% 50.93/6.98  --bmc1_ucm_expand_uc_limit              128
% 50.93/6.98  --bmc1_ucm_n_expand_iterations          6
% 50.93/6.98  --bmc1_ucm_extend_mode                  1
% 50.93/6.98  --bmc1_ucm_init_mode                    2
% 50.93/6.98  --bmc1_ucm_cone_mode                    none
% 50.93/6.98  --bmc1_ucm_reduced_relation_type        0
% 50.93/6.98  --bmc1_ucm_relax_model                  4
% 50.93/6.98  --bmc1_ucm_full_tr_after_sat            true
% 50.93/6.98  --bmc1_ucm_expand_neg_assumptions       false
% 50.93/6.98  --bmc1_ucm_layered_model                none
% 50.93/6.98  --bmc1_ucm_max_lemma_size               10
% 50.93/6.98  
% 50.93/6.98  ------ AIG Options
% 50.93/6.98  
% 50.93/6.98  --aig_mode                              false
% 50.93/6.98  
% 50.93/6.98  ------ Instantiation Options
% 50.93/6.98  
% 50.93/6.98  --instantiation_flag                    true
% 50.93/6.98  --inst_sos_flag                         false
% 50.93/6.98  --inst_sos_phase                        true
% 50.93/6.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 50.93/6.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 50.93/6.98  --inst_lit_sel_side                     num_symb
% 50.93/6.98  --inst_solver_per_active                1400
% 50.93/6.98  --inst_solver_calls_frac                1.
% 50.93/6.98  --inst_passive_queue_type               priority_queues
% 50.93/6.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 50.93/6.98  --inst_passive_queues_freq              [25;2]
% 50.93/6.98  --inst_dismatching                      true
% 50.93/6.98  --inst_eager_unprocessed_to_passive     true
% 50.93/6.98  --inst_prop_sim_given                   true
% 50.93/6.98  --inst_prop_sim_new                     false
% 50.93/6.98  --inst_subs_new                         false
% 50.93/6.98  --inst_eq_res_simp                      false
% 50.93/6.98  --inst_subs_given                       false
% 50.93/6.98  --inst_orphan_elimination               true
% 50.93/6.98  --inst_learning_loop_flag               true
% 50.93/6.98  --inst_learning_start                   3000
% 50.93/6.98  --inst_learning_factor                  2
% 50.93/6.98  --inst_start_prop_sim_after_learn       3
% 50.93/6.98  --inst_sel_renew                        solver
% 50.93/6.98  --inst_lit_activity_flag                true
% 50.93/6.98  --inst_restr_to_given                   false
% 50.93/6.98  --inst_activity_threshold               500
% 50.93/6.98  --inst_out_proof                        true
% 50.93/6.98  
% 50.93/6.98  ------ Resolution Options
% 50.93/6.98  
% 50.93/6.98  --resolution_flag                       true
% 50.93/6.98  --res_lit_sel                           adaptive
% 50.93/6.98  --res_lit_sel_side                      none
% 50.93/6.98  --res_ordering                          kbo
% 50.93/6.98  --res_to_prop_solver                    active
% 50.93/6.98  --res_prop_simpl_new                    false
% 50.93/6.98  --res_prop_simpl_given                  true
% 50.93/6.98  --res_passive_queue_type                priority_queues
% 50.93/6.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 50.93/6.98  --res_passive_queues_freq               [15;5]
% 50.93/6.98  --res_forward_subs                      full
% 50.93/6.98  --res_backward_subs                     full
% 50.93/6.98  --res_forward_subs_resolution           true
% 50.93/6.98  --res_backward_subs_resolution          true
% 50.93/6.98  --res_orphan_elimination                true
% 50.93/6.98  --res_time_limit                        2.
% 50.93/6.98  --res_out_proof                         true
% 50.93/6.98  
% 50.93/6.98  ------ Superposition Options
% 50.93/6.98  
% 50.93/6.98  --superposition_flag                    true
% 50.93/6.98  --sup_passive_queue_type                priority_queues
% 50.93/6.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 50.93/6.98  --sup_passive_queues_freq               [8;1;4]
% 50.93/6.98  --demod_completeness_check              fast
% 50.93/6.98  --demod_use_ground                      true
% 50.93/6.98  --sup_to_prop_solver                    passive
% 50.93/6.98  --sup_prop_simpl_new                    true
% 50.93/6.98  --sup_prop_simpl_given                  true
% 50.93/6.98  --sup_fun_splitting                     false
% 50.93/6.98  --sup_smt_interval                      50000
% 50.93/6.98  
% 50.93/6.98  ------ Superposition Simplification Setup
% 50.93/6.98  
% 50.93/6.98  --sup_indices_passive                   []
% 50.93/6.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.93/6.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.93/6.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.93/6.98  --sup_full_triv                         [TrivRules;PropSubs]
% 50.93/6.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.93/6.98  --sup_full_bw                           [BwDemod]
% 50.93/6.98  --sup_immed_triv                        [TrivRules]
% 50.93/6.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 50.93/6.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.93/6.98  --sup_immed_bw_main                     []
% 50.93/6.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.93/6.98  --sup_input_triv                        [Unflattening;TrivRules]
% 50.93/6.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.93/6.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.93/6.98  
% 50.93/6.98  ------ Combination Options
% 50.93/6.98  
% 50.93/6.98  --comb_res_mult                         3
% 50.93/6.98  --comb_sup_mult                         2
% 50.93/6.98  --comb_inst_mult                        10
% 50.93/6.98  
% 50.93/6.98  ------ Debug Options
% 50.93/6.98  
% 50.93/6.98  --dbg_backtrace                         false
% 50.93/6.98  --dbg_dump_prop_clauses                 false
% 50.93/6.98  --dbg_dump_prop_clauses_file            -
% 50.93/6.98  --dbg_out_stat                          false
% 50.93/6.98  ------ Parsing...
% 50.93/6.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 50.93/6.98  
% 50.93/6.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 50.93/6.98  
% 50.93/6.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 50.93/6.98  
% 50.93/6.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 50.93/6.98  ------ Proving...
% 50.93/6.98  ------ Problem Properties 
% 50.93/6.98  
% 50.93/6.98  
% 50.93/6.98  clauses                                 10
% 50.93/6.98  conjectures                             1
% 50.93/6.98  EPR                                     0
% 50.93/6.98  Horn                                    10
% 50.93/6.98  unary                                   10
% 50.93/6.98  binary                                  0
% 50.93/6.98  lits                                    10
% 50.93/6.98  lits eq                                 10
% 50.93/6.98  fd_pure                                 0
% 50.93/6.98  fd_pseudo                               0
% 50.93/6.98  fd_cond                                 0
% 50.93/6.98  fd_pseudo_cond                          0
% 50.93/6.98  AC symbols                              0
% 50.93/6.98  
% 50.93/6.98  ------ Schedule UEQ
% 50.93/6.98  
% 50.93/6.98  ------ pure equality problem: resolution off 
% 50.93/6.98  
% 50.93/6.98  ------ Option_UEQ Time Limit: Unbounded
% 50.93/6.98  
% 50.93/6.98  
% 50.93/6.98  ------ 
% 50.93/6.98  Current options:
% 50.93/6.98  ------ 
% 50.93/6.98  
% 50.93/6.98  ------ Input Options
% 50.93/6.98  
% 50.93/6.98  --out_options                           all
% 50.93/6.98  --tptp_safe_out                         true
% 50.93/6.98  --problem_path                          ""
% 50.93/6.98  --include_path                          ""
% 50.93/6.98  --clausifier                            res/vclausify_rel
% 50.93/6.98  --clausifier_options                    --mode clausify
% 50.93/6.98  --stdin                                 false
% 50.93/6.98  --stats_out                             all
% 50.93/6.98  
% 50.93/6.98  ------ General Options
% 50.93/6.98  
% 50.93/6.98  --fof                                   false
% 50.93/6.98  --time_out_real                         305.
% 50.93/6.98  --time_out_virtual                      -1.
% 50.93/6.98  --symbol_type_check                     false
% 50.93/6.98  --clausify_out                          false
% 50.93/6.98  --sig_cnt_out                           false
% 50.93/6.98  --trig_cnt_out                          false
% 50.93/6.98  --trig_cnt_out_tolerance                1.
% 50.93/6.98  --trig_cnt_out_sk_spl                   false
% 50.93/6.98  --abstr_cl_out                          false
% 50.93/6.98  
% 50.93/6.98  ------ Global Options
% 50.93/6.98  
% 50.93/6.98  --schedule                              default
% 50.93/6.98  --add_important_lit                     false
% 50.93/6.98  --prop_solver_per_cl                    1000
% 50.93/6.98  --min_unsat_core                        false
% 50.93/6.98  --soft_assumptions                      false
% 50.93/6.98  --soft_lemma_size                       3
% 50.93/6.98  --prop_impl_unit_size                   0
% 50.93/6.98  --prop_impl_unit                        []
% 50.93/6.98  --share_sel_clauses                     true
% 50.93/6.98  --reset_solvers                         false
% 50.93/6.98  --bc_imp_inh                            [conj_cone]
% 50.93/6.98  --conj_cone_tolerance                   3.
% 50.93/6.98  --extra_neg_conj                        none
% 50.93/6.98  --large_theory_mode                     true
% 50.93/6.98  --prolific_symb_bound                   200
% 50.93/6.98  --lt_threshold                          2000
% 50.93/6.98  --clause_weak_htbl                      true
% 50.93/6.98  --gc_record_bc_elim                     false
% 50.93/6.98  
% 50.93/6.98  ------ Preprocessing Options
% 50.93/6.98  
% 50.93/6.98  --preprocessing_flag                    true
% 50.93/6.98  --time_out_prep_mult                    0.1
% 50.93/6.98  --splitting_mode                        input
% 50.93/6.98  --splitting_grd                         true
% 50.93/6.98  --splitting_cvd                         false
% 50.93/6.98  --splitting_cvd_svl                     false
% 50.93/6.98  --splitting_nvd                         32
% 50.93/6.98  --sub_typing                            true
% 50.93/6.98  --prep_gs_sim                           true
% 50.93/6.98  --prep_unflatten                        true
% 50.93/6.98  --prep_res_sim                          true
% 50.93/6.98  --prep_upred                            true
% 50.93/6.98  --prep_sem_filter                       exhaustive
% 50.93/6.98  --prep_sem_filter_out                   false
% 50.93/6.98  --pred_elim                             true
% 50.93/6.98  --res_sim_input                         true
% 50.93/6.98  --eq_ax_congr_red                       true
% 50.93/6.98  --pure_diseq_elim                       true
% 50.93/6.98  --brand_transform                       false
% 50.93/6.98  --non_eq_to_eq                          false
% 50.93/6.98  --prep_def_merge                        true
% 50.93/6.98  --prep_def_merge_prop_impl              false
% 50.93/6.98  --prep_def_merge_mbd                    true
% 50.93/6.98  --prep_def_merge_tr_red                 false
% 50.93/6.98  --prep_def_merge_tr_cl                  false
% 50.93/6.98  --smt_preprocessing                     true
% 50.93/6.98  --smt_ac_axioms                         fast
% 50.93/6.98  --preprocessed_out                      false
% 50.93/6.98  --preprocessed_stats                    false
% 50.93/6.98  
% 50.93/6.98  ------ Abstraction refinement Options
% 50.93/6.98  
% 50.93/6.98  --abstr_ref                             []
% 50.93/6.98  --abstr_ref_prep                        false
% 50.93/6.98  --abstr_ref_until_sat                   false
% 50.93/6.98  --abstr_ref_sig_restrict                funpre
% 50.93/6.98  --abstr_ref_af_restrict_to_split_sk     false
% 50.93/6.98  --abstr_ref_under                       []
% 50.93/6.98  
% 50.93/6.98  ------ SAT Options
% 50.93/6.98  
% 50.93/6.98  --sat_mode                              false
% 50.93/6.98  --sat_fm_restart_options                ""
% 50.93/6.98  --sat_gr_def                            false
% 50.93/6.98  --sat_epr_types                         true
% 50.93/6.98  --sat_non_cyclic_types                  false
% 50.93/6.98  --sat_finite_models                     false
% 50.93/6.98  --sat_fm_lemmas                         false
% 50.93/6.98  --sat_fm_prep                           false
% 50.93/6.98  --sat_fm_uc_incr                        true
% 50.93/6.98  --sat_out_model                         small
% 50.93/6.98  --sat_out_clauses                       false
% 50.93/6.98  
% 50.93/6.98  ------ QBF Options
% 50.93/6.98  
% 50.93/6.98  --qbf_mode                              false
% 50.93/6.98  --qbf_elim_univ                         false
% 50.93/6.98  --qbf_dom_inst                          none
% 50.93/6.98  --qbf_dom_pre_inst                      false
% 50.93/6.98  --qbf_sk_in                             false
% 50.93/6.98  --qbf_pred_elim                         true
% 50.93/6.98  --qbf_split                             512
% 50.93/6.98  
% 50.93/6.98  ------ BMC1 Options
% 50.93/6.98  
% 50.93/6.98  --bmc1_incremental                      false
% 50.93/6.98  --bmc1_axioms                           reachable_all
% 50.93/6.98  --bmc1_min_bound                        0
% 50.93/6.98  --bmc1_max_bound                        -1
% 50.93/6.98  --bmc1_max_bound_default                -1
% 50.93/6.98  --bmc1_symbol_reachability              true
% 50.93/6.98  --bmc1_property_lemmas                  false
% 50.93/6.98  --bmc1_k_induction                      false
% 50.93/6.98  --bmc1_non_equiv_states                 false
% 50.93/6.98  --bmc1_deadlock                         false
% 50.93/6.98  --bmc1_ucm                              false
% 50.93/6.98  --bmc1_add_unsat_core                   none
% 50.93/6.98  --bmc1_unsat_core_children              false
% 50.93/6.98  --bmc1_unsat_core_extrapolate_axioms    false
% 50.93/6.98  --bmc1_out_stat                         full
% 50.93/6.98  --bmc1_ground_init                      false
% 50.93/6.98  --bmc1_pre_inst_next_state              false
% 50.93/6.98  --bmc1_pre_inst_state                   false
% 50.93/6.98  --bmc1_pre_inst_reach_state             false
% 50.93/6.98  --bmc1_out_unsat_core                   false
% 50.93/6.98  --bmc1_aig_witness_out                  false
% 50.93/6.98  --bmc1_verbose                          false
% 50.93/6.98  --bmc1_dump_clauses_tptp                false
% 50.93/6.98  --bmc1_dump_unsat_core_tptp             false
% 50.93/6.98  --bmc1_dump_file                        -
% 50.93/6.98  --bmc1_ucm_expand_uc_limit              128
% 50.93/6.98  --bmc1_ucm_n_expand_iterations          6
% 50.93/6.98  --bmc1_ucm_extend_mode                  1
% 50.93/6.98  --bmc1_ucm_init_mode                    2
% 50.93/6.98  --bmc1_ucm_cone_mode                    none
% 50.93/6.98  --bmc1_ucm_reduced_relation_type        0
% 50.93/6.98  --bmc1_ucm_relax_model                  4
% 50.93/6.98  --bmc1_ucm_full_tr_after_sat            true
% 50.93/6.98  --bmc1_ucm_expand_neg_assumptions       false
% 50.93/6.98  --bmc1_ucm_layered_model                none
% 50.93/6.98  --bmc1_ucm_max_lemma_size               10
% 50.93/6.98  
% 50.93/6.98  ------ AIG Options
% 50.93/6.98  
% 50.93/6.98  --aig_mode                              false
% 50.93/6.98  
% 50.93/6.98  ------ Instantiation Options
% 50.93/6.98  
% 50.93/6.98  --instantiation_flag                    false
% 50.93/6.98  --inst_sos_flag                         false
% 50.93/6.98  --inst_sos_phase                        true
% 50.93/6.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 50.93/6.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 50.93/6.98  --inst_lit_sel_side                     num_symb
% 50.93/6.98  --inst_solver_per_active                1400
% 50.93/6.98  --inst_solver_calls_frac                1.
% 50.93/6.98  --inst_passive_queue_type               priority_queues
% 50.93/6.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 50.93/6.98  --inst_passive_queues_freq              [25;2]
% 50.93/6.98  --inst_dismatching                      true
% 50.93/6.98  --inst_eager_unprocessed_to_passive     true
% 50.93/6.98  --inst_prop_sim_given                   true
% 50.93/6.98  --inst_prop_sim_new                     false
% 50.93/6.98  --inst_subs_new                         false
% 50.93/6.98  --inst_eq_res_simp                      false
% 50.93/6.98  --inst_subs_given                       false
% 50.93/6.98  --inst_orphan_elimination               true
% 50.93/6.98  --inst_learning_loop_flag               true
% 50.93/6.98  --inst_learning_start                   3000
% 50.93/6.98  --inst_learning_factor                  2
% 50.93/6.98  --inst_start_prop_sim_after_learn       3
% 50.93/6.98  --inst_sel_renew                        solver
% 50.93/6.98  --inst_lit_activity_flag                true
% 50.93/6.98  --inst_restr_to_given                   false
% 50.93/6.98  --inst_activity_threshold               500
% 50.93/6.98  --inst_out_proof                        true
% 50.93/6.98  
% 50.93/6.98  ------ Resolution Options
% 50.93/6.98  
% 50.93/6.98  --resolution_flag                       false
% 50.93/6.98  --res_lit_sel                           adaptive
% 50.93/6.98  --res_lit_sel_side                      none
% 50.93/6.98  --res_ordering                          kbo
% 50.93/6.98  --res_to_prop_solver                    active
% 50.93/6.98  --res_prop_simpl_new                    false
% 50.93/6.98  --res_prop_simpl_given                  true
% 50.93/6.98  --res_passive_queue_type                priority_queues
% 50.93/6.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 50.93/6.98  --res_passive_queues_freq               [15;5]
% 50.93/6.98  --res_forward_subs                      full
% 50.93/6.98  --res_backward_subs                     full
% 50.93/6.98  --res_forward_subs_resolution           true
% 50.93/6.98  --res_backward_subs_resolution          true
% 50.93/6.98  --res_orphan_elimination                true
% 50.93/6.98  --res_time_limit                        2.
% 50.93/6.98  --res_out_proof                         true
% 50.93/6.98  
% 50.93/6.98  ------ Superposition Options
% 50.93/6.98  
% 50.93/6.98  --superposition_flag                    true
% 50.93/6.98  --sup_passive_queue_type                priority_queues
% 50.93/6.98  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 50.93/6.98  --sup_passive_queues_freq               [8;1;4]
% 50.93/6.98  --demod_completeness_check              fast
% 50.93/6.98  --demod_use_ground                      true
% 50.93/6.98  --sup_to_prop_solver                    active
% 50.93/6.98  --sup_prop_simpl_new                    false
% 50.93/6.98  --sup_prop_simpl_given                  false
% 50.93/6.98  --sup_fun_splitting                     true
% 50.93/6.98  --sup_smt_interval                      10000
% 50.93/6.98  
% 50.93/6.98  ------ Superposition Simplification Setup
% 50.93/6.98  
% 50.93/6.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 50.93/6.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 50.93/6.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 50.93/6.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.93/6.98  --sup_full_triv                         [TrivRules]
% 50.93/6.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 50.93/6.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 50.93/6.98  --sup_immed_triv                        [TrivRules]
% 50.93/6.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 50.93/6.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 50.93/6.98  --sup_immed_bw_main                     []
% 50.93/6.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 50.93/6.98  --sup_input_triv                        [Unflattening;TrivRules]
% 50.93/6.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 50.93/6.98  --sup_input_bw                          [BwDemod;BwSubsumption]
% 50.93/6.98  
% 50.93/6.98  ------ Combination Options
% 50.93/6.98  
% 50.93/6.98  --comb_res_mult                         1
% 50.93/6.98  --comb_sup_mult                         1
% 50.93/6.98  --comb_inst_mult                        1000000
% 50.93/6.98  
% 50.93/6.98  ------ Debug Options
% 50.93/6.98  
% 50.93/6.98  --dbg_backtrace                         false
% 50.93/6.98  --dbg_dump_prop_clauses                 false
% 50.93/6.98  --dbg_dump_prop_clauses_file            -
% 50.93/6.98  --dbg_out_stat                          false
% 50.93/6.98  
% 50.93/6.98  
% 50.93/6.98  
% 50.93/6.98  
% 50.93/6.98  ------ Proving...
% 50.93/6.98  
% 50.93/6.98  
% 50.93/6.98  % SZS status Theorem for theBenchmark.p
% 50.93/6.98  
% 50.93/6.98   Resolution empty clause
% 50.93/6.98  
% 50.93/6.98  % SZS output start CNFRefutation for theBenchmark.p
% 50.93/6.98  
% 50.93/6.98  fof(f1,axiom,(
% 50.93/6.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f18,plain,(
% 50.93/6.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 50.93/6.98    inference(cnf_transformation,[],[f1])).
% 50.93/6.98  
% 50.93/6.98  fof(f7,axiom,(
% 50.93/6.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f24,plain,(
% 50.93/6.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 50.93/6.98    inference(cnf_transformation,[],[f7])).
% 50.93/6.98  
% 50.93/6.98  fof(f31,plain,(
% 50.93/6.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 50.93/6.98    inference(definition_unfolding,[],[f18,f24,f24])).
% 50.93/6.98  
% 50.93/6.98  fof(f8,axiom,(
% 50.93/6.98    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f25,plain,(
% 50.93/6.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 50.93/6.98    inference(cnf_transformation,[],[f8])).
% 50.93/6.98  
% 50.93/6.98  fof(f36,plain,(
% 50.93/6.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 50.93/6.98    inference(definition_unfolding,[],[f25,f24,f24])).
% 50.93/6.98  
% 50.93/6.98  fof(f3,axiom,(
% 50.93/6.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f20,plain,(
% 50.93/6.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 50.93/6.98    inference(cnf_transformation,[],[f3])).
% 50.93/6.98  
% 50.93/6.98  fof(f30,plain,(
% 50.93/6.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 50.93/6.98    inference(definition_unfolding,[],[f20,f24])).
% 50.93/6.98  
% 50.93/6.98  fof(f5,axiom,(
% 50.93/6.98    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f22,plain,(
% 50.93/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 50.93/6.98    inference(cnf_transformation,[],[f5])).
% 50.93/6.98  
% 50.93/6.98  fof(f11,axiom,(
% 50.93/6.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f28,plain,(
% 50.93/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 50.93/6.98    inference(cnf_transformation,[],[f11])).
% 50.93/6.98  
% 50.93/6.98  fof(f34,plain,(
% 50.93/6.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 50.93/6.98    inference(definition_unfolding,[],[f22,f28,f24])).
% 50.93/6.98  
% 50.93/6.98  fof(f10,axiom,(
% 50.93/6.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f27,plain,(
% 50.93/6.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 50.93/6.98    inference(cnf_transformation,[],[f10])).
% 50.93/6.98  
% 50.93/6.98  fof(f9,axiom,(
% 50.93/6.98    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f26,plain,(
% 50.93/6.98    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 50.93/6.98    inference(cnf_transformation,[],[f9])).
% 50.93/6.98  
% 50.93/6.98  fof(f37,plain,(
% 50.93/6.98    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 50.93/6.98    inference(definition_unfolding,[],[f26,f28,f24])).
% 50.93/6.98  
% 50.93/6.98  fof(f2,axiom,(
% 50.93/6.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f14,plain,(
% 50.93/6.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 50.93/6.98    inference(rectify,[],[f2])).
% 50.93/6.98  
% 50.93/6.98  fof(f19,plain,(
% 50.93/6.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 50.93/6.98    inference(cnf_transformation,[],[f14])).
% 50.93/6.98  
% 50.93/6.98  fof(f32,plain,(
% 50.93/6.98    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 50.93/6.98    inference(definition_unfolding,[],[f19,f28])).
% 50.93/6.98  
% 50.93/6.98  fof(f4,axiom,(
% 50.93/6.98    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f21,plain,(
% 50.93/6.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 50.93/6.98    inference(cnf_transformation,[],[f4])).
% 50.93/6.98  
% 50.93/6.98  fof(f33,plain,(
% 50.93/6.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 50.93/6.98    inference(definition_unfolding,[],[f21,f24,f24,f24,f24])).
% 50.93/6.98  
% 50.93/6.98  fof(f12,conjecture,(
% 50.93/6.98    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f13,negated_conjecture,(
% 50.93/6.98    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 50.93/6.98    inference(negated_conjecture,[],[f12])).
% 50.93/6.98  
% 50.93/6.98  fof(f15,plain,(
% 50.93/6.98    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)),
% 50.93/6.98    inference(ennf_transformation,[],[f13])).
% 50.93/6.98  
% 50.93/6.98  fof(f16,plain,(
% 50.93/6.98    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 50.93/6.98    introduced(choice_axiom,[])).
% 50.93/6.98  
% 50.93/6.98  fof(f17,plain,(
% 50.93/6.98    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 50.93/6.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 50.93/6.98  
% 50.93/6.98  fof(f29,plain,(
% 50.93/6.98    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 50.93/6.98    inference(cnf_transformation,[],[f17])).
% 50.93/6.98  
% 50.93/6.98  fof(f38,plain,(
% 50.93/6.98    k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1)),
% 50.93/6.98    inference(definition_unfolding,[],[f29,f28,f24])).
% 50.93/6.98  
% 50.93/6.98  fof(f6,axiom,(
% 50.93/6.98    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 50.93/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 50.93/6.98  
% 50.93/6.98  fof(f23,plain,(
% 50.93/6.98    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 50.93/6.98    inference(cnf_transformation,[],[f6])).
% 50.93/6.98  
% 50.93/6.98  fof(f35,plain,(
% 50.93/6.98    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) )),
% 50.93/6.98    inference(definition_unfolding,[],[f23,f28,f28])).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 50.93/6.98      inference(cnf_transformation,[],[f31]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_6,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 50.93/6.98      inference(cnf_transformation,[],[f36]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_112,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_0,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(cnf_transformation,[],[f30]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_35,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_4,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
% 50.93/6.98      inference(cnf_transformation,[],[f34]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_30,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_6,c_4]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_47,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_30,c_0]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_59,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_47,c_47]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_242,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_59,c_1]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_250,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,X1) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_242,c_47]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_800,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_250,c_6]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_812,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(X1,X1) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_800,c_250]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_115,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_47,c_6]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_322,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1,c_115]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_813,plain,
% 50.93/6.98      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_812,c_47,c_322]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_814,plain,
% 50.93/6.98      ( k4_xboole_0(X0,X0) = sP0_iProver_split ),
% 50.93/6.98      inference(splitting,
% 50.93/6.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 50.93/6.98                [c_813]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_58,plain,
% 50.93/6.98      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_47,c_0]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_823,plain,
% 50.93/6.98      ( k5_xboole_0(X0,X0) = sP0_iProver_split ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_814,c_58]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_8,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 50.93/6.98      inference(cnf_transformation,[],[f27]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_930,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = sP0_iProver_split ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_823,c_8]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_66,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_58,c_8]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_821,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(sP0_iProver_split,X1) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_814,c_66]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_7,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
% 50.93/6.98      inference(cnf_transformation,[],[f37]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_157,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_7,c_47]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_171,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_47,c_157]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_822,plain,
% 50.93/6.98      ( k5_xboole_0(sP0_iProver_split,X0) = X0 ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_814,c_171]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_826,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_821,c_822]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1090,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,sP0_iProver_split) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_930,c_826]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_2,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 50.93/6.98      inference(cnf_transformation,[],[f32]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_824,plain,
% 50.93/6.98      ( k5_xboole_0(X0,sP0_iProver_split) = X0 ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_814,c_2]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1098,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_1090,c_824]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1056,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_8,c_826]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1446,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1098,c_1056]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1492,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_35,c_1446]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_10620,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X0),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_112,c_1492]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_609,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1,c_322]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_687,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_609,c_322]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_837,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_800,c_687]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_838,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = sP0_iProver_split ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_837,c_47,c_322,c_814]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_10948,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_10620,c_6,c_822,c_838]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 50.93/6.98      inference(cnf_transformation,[],[f33]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_31,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_3,c_6]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_172,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_31,c_157]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_174,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_172,c_31]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_175,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_174,c_115]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_161280,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_10948,c_175]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1448,plain,
% 50.93/6.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1098,c_826]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1124,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,sP0_iProver_split)) = X1 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_823,c_1056]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1140,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_1124,c_824]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1462,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_8,c_1140]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1936,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X2,X0)) = X1 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1448,c_1462]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_2029,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X0)) = X1 ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_1936,c_8]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_2331,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = sP0_iProver_split ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_822,c_2029]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_2478,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,sP0_iProver_split)) = k5_xboole_0(X2,X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_2331,c_1056]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_2514,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_2478,c_824]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_161467,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X3) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_175,c_2514]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_161794,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = sP5_iProver_split(X0,X1) ),
% 50.93/6.98      inference(splitting,
% 50.93/6.98                [splitting(split),new_symbols(definition,[])],
% 50.93/6.98                [c_161467]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_162038,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = sP5_iProver_split(X0,X1) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_161280,c_161794]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_9,negated_conjecture,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
% 50.93/6.98      inference(cnf_transformation,[],[f38]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_170899,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),sP5_iProver_split(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_162038,c_9]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_159,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1,c_157]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_635,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)),k4_xboole_0(X1,X0)) = X1 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_322,c_159]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_225,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_171,c_8]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_519,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_6,c_225]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_298,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),X2) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_6,c_66]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_553,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_519,c_47,c_66,c_298,c_322]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_38,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_554,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_553,c_38]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_660,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))),k4_xboole_0(X1,X0))) = X1 ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_635,c_6,c_554]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_661,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = X1 ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_660,c_47]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_2782,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X1,X0) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_661,c_1140]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1439,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_159,c_1098]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_2495,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) = k5_xboole_0(X1,X0) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_2331,c_1098]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_6268,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP0_iProver_split) = k5_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1439,c_2495]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_5,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
% 50.93/6.98      inference(cnf_transformation,[],[f35]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_872,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k5_xboole_0(sP0_iProver_split,k4_xboole_0(k4_xboole_0(X1,X0),sP0_iProver_split)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_814,c_5]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_882,plain,
% 50.93/6.98      ( k4_xboole_0(X0,sP0_iProver_split) = X0 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_814,c_47]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_906,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k5_xboole_0(sP0_iProver_split,k4_xboole_0(X1,X0)) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_872,c_882]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_907,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_906,c_822]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3873,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_907,c_35]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_885,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_814,c_5]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_781,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_250,c_159]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_783,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_250,c_59]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_851,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_783,c_814]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_852,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_781,c_851]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_330,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_59,c_115]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_361,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_330,c_59,c_250]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_853,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_852,c_361]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_894,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_885,c_853]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3738,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_59,c_894]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3808,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_3738,c_47]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3895,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP0_iProver_split ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_3873,c_823,c_3808]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3946,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)) = sP0_iProver_split ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_5,c_3895]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_7587,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),X2)) = sP0_iProver_split ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_115,c_3946]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_7725,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X0,X2)) = sP0_iProver_split ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_7587,c_6,c_157]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_10080,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) = sP0_iProver_split ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_7725,c_6]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_10288,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP0_iProver_split)) = sP0_iProver_split ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_3946,c_10080]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_2430,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = sP0_iProver_split ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_8,c_2331]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3102,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),sP0_iProver_split) = sP0_iProver_split ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_823,c_2430]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_67,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_58,c_8]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_802,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X0)),X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_250,c_5]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_834,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(k5_xboole_0(X0,sP0_iProver_split),X1) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_802,c_814]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_835,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split) = k4_xboole_0(k5_xboole_0(X0,sP0_iProver_split),X1) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_834,c_814]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_2648,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_8,c_2495]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3233,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split),k5_xboole_0(X0,X1)) = sP0_iProver_split ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_3102,c_67,c_835,c_2648]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3234,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = sP0_iProver_split ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_3233,c_2495]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_342,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_115,c_0]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3325,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_3234,c_342]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3374,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) = k4_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_3325,c_3234]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3375,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) = k5_xboole_0(X1,X0) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_3374,c_2495]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_7569,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,sP0_iProver_split),k5_xboole_0(k4_xboole_0(X1,X0),X0)) = sP0_iProver_split ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_3375,c_3946]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_7732,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X0)) = sP0_iProver_split ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_7569,c_882]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_8030,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X2,X0),X0)) = k5_xboole_0(sP0_iProver_split,k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X0),X0)),sP0_iProver_split)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_7732,c_5]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_129,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_6,c_47]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_803,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X1)))) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_250,c_129]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_644,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_322,c_31]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_85,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_47,c_31]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_105,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_85,c_6,c_47]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_653,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_644,c_105]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_654,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(X0,X0) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_653,c_129]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_831,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X2)) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_803,c_654]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_832,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_831,c_814]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_8093,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X2,X0),X0)) = k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X0),X0)) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_8030,c_822,c_832]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_11206,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),X1)) = sP0_iProver_split ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_10288,c_3375,c_8093]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_11571,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),sP0_iProver_split),X0) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_11206,c_894]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_11612,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) = k4_xboole_0(X1,X0) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_11571,c_894,c_2495]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_11576,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,sP0_iProver_split)) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_11206,c_35]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_11609,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_11576,c_882]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_11614,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X0) = k4_xboole_0(X1,X0) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_11612,c_11609]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_39576,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(X0,X2)) = k5_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_11614,c_8]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_162348,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),sP0_iProver_split)) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X2)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_6268,c_39576]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3732,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_47,c_894]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3814,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X1) = k4_xboole_0(X0,X1) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_3732,c_59]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_468,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_159,c_8]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_32340,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X0))),k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X0),X0),X2) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_3814,c_468]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_32493,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X2) = k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X0,X1),X2)) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_32340,c_882,c_7732]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_163277,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X1),sP0_iProver_split)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_162348,c_554,c_32493]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_163278,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,sP0_iProver_split),X1)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_163277,c_835]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_11507,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X0),X1),k4_xboole_0(X0,X1))) = sP0_iProver_split ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1439,c_11206]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1445,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1098,c_1056]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_8180,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(X3,k5_xboole_0(X2,X1)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_2029,c_1445]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1434,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_8,c_1098]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1800,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1448,c_1434]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1449,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1098,c_8]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1904,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1449,c_1449]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_2486,plain,
% 50.93/6.98      ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_2331,c_1446]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_2554,plain,
% 50.93/6.98      ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_8,c_2486]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_4690,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,sP0_iProver_split)) = k5_xboole_0(sP0_iProver_split,k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X0,X1)))) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_2554,c_2554]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_4757,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,sP0_iProver_split)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X3,X2)) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_4690,c_2554]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_4758,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X3)),X2) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_4757,c_824]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_8378,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_8180,c_1800,c_1904,c_4758]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_11665,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = sP0_iProver_split ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_11507,c_8378]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_3770,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_894,c_322]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_1438,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_157,c_1098]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_6119,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_894,c_1438]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_6200,plain,
% 50.93/6.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 50.93/6.98      inference(light_normalisation,[status(thm)],[c_6119,c_894]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_11666,plain,
% 50.93/6.98      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = sP0_iProver_split ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_11665,c_3770,c_6200]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_11991,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X2,k4_xboole_0(X0,X2))) = k4_xboole_0(X1,k4_xboole_0(X1,sP0_iProver_split)) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_11666,c_112]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_12019,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X2,k4_xboole_0(X0,X2))) = sP0_iProver_split ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_11991,c_6,c_814,c_882]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_17120,plain,
% 50.93/6.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X2,k4_xboole_0(X1,X2))) = sP0_iProver_split ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_1,c_12019]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_22206,plain,
% 50.93/6.98      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),sP0_iProver_split)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 50.93/6.98      inference(superposition,[status(thm)],[c_17120,c_35]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_22275,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,sP0_iProver_split))))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_22206,c_6,c_8378]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_22276,plain,
% 50.93/6.98      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_22275,c_882]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_163279,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_163278,c_342,c_824,c_22276]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_163280,plain,
% 50.93/6.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP5_iProver_split(X2,X1)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_163279,c_162038]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_170916,plain,
% 50.93/6.98      ( k5_xboole_0(sK1,sK0) != k5_xboole_0(sK0,sK1) ),
% 50.93/6.98      inference(demodulation,[status(thm)],[c_170899,c_2782,c_163280]) ).
% 50.93/6.98  
% 50.93/6.98  cnf(c_174084,plain,
% 50.93/6.98      ( $false ),
% 50.93/6.98      inference(theory_normalisation,[status(thm)],[c_170916]) ).
% 50.93/6.98  
% 50.93/6.98  
% 50.93/6.98  % SZS output end CNFRefutation for theBenchmark.p
% 50.93/6.98  
% 50.93/6.98  ------                               Statistics
% 50.93/6.98  
% 50.93/6.98  ------ General
% 50.93/6.98  
% 50.93/6.98  abstr_ref_over_cycles:                  0
% 50.93/6.98  abstr_ref_under_cycles:                 0
% 50.93/6.98  gc_basic_clause_elim:                   0
% 50.93/6.98  forced_gc_time:                         0
% 50.93/6.98  parsing_time:                           0.008
% 50.93/6.98  unif_index_cands_time:                  0.
% 50.93/6.98  unif_index_add_time:                    0.
% 50.93/6.98  orderings_time:                         0.
% 50.93/6.98  out_proof_time:                         0.011
% 50.93/6.98  total_time:                             6.141
% 50.93/6.98  num_of_symbols:                         41
% 50.93/6.98  num_of_terms:                           415319
% 50.93/6.98  
% 50.93/6.98  ------ Preprocessing
% 50.93/6.98  
% 50.93/6.98  num_of_splits:                          0
% 50.93/6.98  num_of_split_atoms:                     6
% 50.93/6.98  num_of_reused_defs:                     6
% 50.93/6.98  num_eq_ax_congr_red:                    0
% 50.93/6.98  num_of_sem_filtered_clauses:            0
% 50.93/6.98  num_of_subtypes:                        0
% 50.93/6.98  monotx_restored_types:                  0
% 50.93/6.98  sat_num_of_epr_types:                   0
% 50.93/6.98  sat_num_of_non_cyclic_types:            0
% 50.93/6.98  sat_guarded_non_collapsed_types:        0
% 50.93/6.98  num_pure_diseq_elim:                    0
% 50.93/6.98  simp_replaced_by:                       0
% 50.93/6.98  res_preprocessed:                       24
% 50.93/6.98  prep_upred:                             0
% 50.93/6.98  prep_unflattend:                        0
% 50.93/6.98  smt_new_axioms:                         0
% 50.93/6.98  pred_elim_cands:                        0
% 50.93/6.98  pred_elim:                              0
% 50.93/6.98  pred_elim_cl:                           0
% 50.93/6.98  pred_elim_cycles:                       0
% 50.93/6.98  merged_defs:                            0
% 50.93/6.98  merged_defs_ncl:                        0
% 50.93/6.98  bin_hyper_res:                          0
% 50.93/6.98  prep_cycles:                            2
% 50.93/6.98  pred_elim_time:                         0.
% 50.93/6.98  splitting_time:                         0.
% 50.93/6.98  sem_filter_time:                        0.
% 50.93/6.98  monotx_time:                            0.
% 50.93/6.98  subtype_inf_time:                       0.
% 50.93/6.98  
% 50.93/6.98  ------ Problem properties
% 50.93/6.98  
% 50.93/6.98  clauses:                                10
% 50.93/6.98  conjectures:                            1
% 50.93/6.98  epr:                                    0
% 50.93/6.98  horn:                                   10
% 50.93/6.98  ground:                                 1
% 50.93/6.98  unary:                                  10
% 50.93/6.98  binary:                                 0
% 50.93/6.98  lits:                                   10
% 50.93/6.98  lits_eq:                                10
% 50.93/6.98  fd_pure:                                0
% 50.93/6.98  fd_pseudo:                              0
% 50.93/6.98  fd_cond:                                0
% 50.93/6.98  fd_pseudo_cond:                         0
% 50.93/6.98  ac_symbols:                             1
% 50.93/6.98  
% 50.93/6.98  ------ Propositional Solver
% 50.93/6.98  
% 50.93/6.98  prop_solver_calls:                      13
% 50.93/6.98  prop_fast_solver_calls:                 60
% 50.93/6.98  smt_solver_calls:                       0
% 50.93/6.98  smt_fast_solver_calls:                  0
% 50.93/6.98  prop_num_of_clauses:                    511
% 50.93/6.98  prop_preprocess_simplified:             440
% 50.93/6.98  prop_fo_subsumed:                       0
% 50.93/6.98  prop_solver_time:                       0.
% 50.93/6.98  smt_solver_time:                        0.
% 50.93/6.98  smt_fast_solver_time:                   0.
% 50.93/6.98  prop_fast_solver_time:                  0.
% 50.93/6.98  prop_unsat_core_time:                   0.
% 50.93/6.98  
% 50.93/6.98  ------ QBF
% 50.93/6.98  
% 50.93/6.98  qbf_q_res:                              0
% 50.93/6.98  qbf_num_tautologies:                    0
% 50.93/6.98  qbf_prep_cycles:                        0
% 50.93/6.98  
% 50.93/6.98  ------ BMC1
% 50.93/6.98  
% 50.93/6.98  bmc1_current_bound:                     -1
% 50.93/6.98  bmc1_last_solved_bound:                 -1
% 50.93/6.98  bmc1_unsat_core_size:                   -1
% 50.93/6.98  bmc1_unsat_core_parents_size:           -1
% 50.93/6.98  bmc1_merge_next_fun:                    0
% 50.93/6.98  bmc1_unsat_core_clauses_time:           0.
% 50.93/6.98  
% 50.93/6.98  ------ Instantiation
% 50.93/6.98  
% 50.93/6.98  inst_num_of_clauses:                    0
% 50.93/6.98  inst_num_in_passive:                    0
% 50.93/6.98  inst_num_in_active:                     0
% 50.93/6.98  inst_num_in_unprocessed:                0
% 50.93/6.98  inst_num_of_loops:                      0
% 50.93/6.98  inst_num_of_learning_restarts:          0
% 50.93/6.98  inst_num_moves_active_passive:          0
% 50.93/6.98  inst_lit_activity:                      0
% 50.93/6.98  inst_lit_activity_moves:                0
% 50.93/6.98  inst_num_tautologies:                   0
% 50.93/6.98  inst_num_prop_implied:                  0
% 50.93/6.98  inst_num_existing_simplified:           0
% 50.93/6.98  inst_num_eq_res_simplified:             0
% 50.93/6.98  inst_num_child_elim:                    0
% 50.93/6.98  inst_num_of_dismatching_blockings:      0
% 50.93/6.98  inst_num_of_non_proper_insts:           0
% 50.93/6.98  inst_num_of_duplicates:                 0
% 50.93/6.98  inst_inst_num_from_inst_to_res:         0
% 50.93/6.98  inst_dismatching_checking_time:         0.
% 50.93/6.98  
% 50.93/6.98  ------ Resolution
% 50.93/6.98  
% 50.93/6.98  res_num_of_clauses:                     0
% 50.93/6.98  res_num_in_passive:                     0
% 50.93/6.98  res_num_in_active:                      0
% 50.93/6.98  res_num_of_loops:                       26
% 50.93/6.98  res_forward_subset_subsumed:            0
% 50.93/6.98  res_backward_subset_subsumed:           0
% 50.93/6.98  res_forward_subsumed:                   0
% 50.93/6.98  res_backward_subsumed:                  0
% 50.93/6.98  res_forward_subsumption_resolution:     0
% 50.93/6.98  res_backward_subsumption_resolution:    0
% 50.93/6.98  res_clause_to_clause_subsumption:       561666
% 50.93/6.98  res_orphan_elimination:                 0
% 50.93/6.98  res_tautology_del:                      0
% 50.93/6.98  res_num_eq_res_simplified:              0
% 50.93/6.98  res_num_sel_changes:                    0
% 50.93/6.98  res_moves_from_active_to_pass:          0
% 50.93/6.98  
% 50.93/6.98  ------ Superposition
% 50.93/6.98  
% 50.93/6.98  sup_time_total:                         0.
% 50.93/6.98  sup_time_generating:                    0.
% 50.93/6.98  sup_time_sim_full:                      0.
% 50.93/6.98  sup_time_sim_immed:                     0.
% 50.93/6.98  
% 50.93/6.98  sup_num_of_clauses:                     12839
% 50.93/6.98  sup_num_in_active:                      185
% 50.93/6.98  sup_num_in_passive:                     12654
% 50.93/6.98  sup_num_of_loops:                       306
% 50.93/6.98  sup_fw_superposition:                   47923
% 50.93/6.98  sup_bw_superposition:                   41751
% 50.93/6.98  sup_immediate_simplified:               57094
% 50.93/6.98  sup_given_eliminated:                   21
% 50.93/6.98  comparisons_done:                       0
% 50.93/6.98  comparisons_avoided:                    0
% 50.93/6.98  
% 50.93/6.98  ------ Simplifications
% 50.93/6.98  
% 50.93/6.98  
% 50.93/6.98  sim_fw_subset_subsumed:                 0
% 50.93/6.98  sim_bw_subset_subsumed:                 0
% 50.93/6.98  sim_fw_subsumed:                        4243
% 50.93/6.98  sim_bw_subsumed:                        136
% 50.93/6.98  sim_fw_subsumption_res:                 0
% 50.93/6.98  sim_bw_subsumption_res:                 0
% 50.93/6.98  sim_tautology_del:                      0
% 50.93/6.98  sim_eq_tautology_del:                   17706
% 50.93/6.98  sim_eq_res_simp:                        0
% 50.93/6.98  sim_fw_demodulated:                     59912
% 50.93/6.98  sim_bw_demodulated:                     1014
% 50.93/6.98  sim_light_normalised:                   22728
% 50.93/6.98  sim_joinable_taut:                      550
% 50.93/6.98  sim_joinable_simp:                      1
% 50.93/6.98  sim_ac_normalised:                      0
% 50.93/6.98  sim_smt_subsumption:                    0
% 50.93/6.98  
%------------------------------------------------------------------------------
