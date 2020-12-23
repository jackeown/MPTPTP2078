%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 (1170 expanded)
%              Number of leaves         :   15 ( 379 expanded)
%              Depth                    :   29
%              Number of atoms          :   96 (1185 expanded)
%              Number of equality atoms :   86 (1155 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f319])).

fof(f319,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f313,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f313,plain,(
    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f311,f34])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f311,plain,(
    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f47,f269])).

fof(f269,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f262,f219])).

fof(f219,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f127,f197])).

fof(f197,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(forward_demodulation,[],[f194,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f194,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f188,f36])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f188,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f155,f187])).

fof(f187,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)))) ),
    inference(forward_demodulation,[],[f186,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f186,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0))) ),
    inference(forward_demodulation,[],[f170,f35])).

fof(f170,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),X0)) ),
    inference(superposition,[],[f35,f162])).

fof(f162,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f154,f30])).

fof(f154,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f74,f51])).

fof(f51,plain,(
    k1_xboole_0 = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f49,f36])).

fof(f49,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f48,f36])).

fof(f48,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f43,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f25,f26,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f25,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) ),
    inference(forward_demodulation,[],[f73,f35])).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) ),
    inference(superposition,[],[f35,f70])).

fof(f70,plain,(
    k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f63,f30])).

fof(f63,plain,(
    k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f55,f31])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f35,f49])).

fof(f155,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f74,f60])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0))) ),
    inference(forward_demodulation,[],[f59,f35])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) ),
    inference(superposition,[],[f35,f51])).

fof(f127,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f126,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f126,plain,(
    r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f123,f31])).

fof(f123,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f46,f119])).

fof(f119,plain,(
    k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f116,f39])).

fof(f116,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) ),
    inference(superposition,[],[f46,f108])).

fof(f108,plain,(
    k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f101,f36])).

fof(f101,plain,(
    k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) ),
    inference(forward_demodulation,[],[f91,f30])).

fof(f91,plain,(
    k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f60,f31])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f37,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f262,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f217,f259])).

fof(f259,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f258,f31])).

fof(f258,plain,(
    sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f257,f217])).

fof(f257,plain,(
    sK1 = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f222,f197])).

fof(f222,plain,(
    k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f179,f197])).

fof(f179,plain,(
    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f111,f172])).

fof(f172,plain,(
    k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f81,f171])).

fof(f171,plain,(
    k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f169,f30])).

fof(f169,plain,(
    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(superposition,[],[f60,f162])).

fof(f81,plain,(
    k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f75,f30])).

fof(f75,plain,(
    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)) ),
    inference(superposition,[],[f58,f51])).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0))) ),
    inference(forward_demodulation,[],[f57,f35])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),X0)) ),
    inference(superposition,[],[f35,f50])).

fof(f50,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f49,f35])).

fof(f111,plain,(
    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f55,f101])).

fof(f217,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f121,f197])).

fof(f121,plain,(
    k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f119,f33])).

fof(f47,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f28,f42,f32,f42,f42])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:18:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (26619)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (26621)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (26643)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.51  % (26635)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (26623)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (26624)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (26627)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (26638)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (26632)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (26640)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (26620)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (26646)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (26623)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f320,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f319])).
% 0.22/0.54  fof(f319,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0),
% 0.22/0.54    inference(superposition,[],[f313,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.54  fof(f313,plain,(
% 0.22/0.54    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.54    inference(forward_demodulation,[],[f311,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.54    inference(rectify,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.54  fof(f311,plain,(
% 0.22/0.54    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),
% 0.22/0.54    inference(superposition,[],[f47,f269])).
% 0.22/0.54  fof(f269,plain,(
% 0.22/0.54    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f262,f219])).
% 0.22/0.54  fof(f219,plain,(
% 0.22/0.54    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.54    inference(backward_demodulation,[],[f127,f197])).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = X3) )),
% 0.22/0.54    inference(forward_demodulation,[],[f194,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k1_xboole_0))) )),
% 0.22/0.54    inference(superposition,[],[f188,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 0.22/0.54    inference(backward_demodulation,[],[f155,f187])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0))))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f186,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f170,f35])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),X0))) )),
% 0.22/0.54    inference(superposition,[],[f35,f162])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.22/0.54    inference(forward_demodulation,[],[f154,f30])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.22/0.54    inference(superposition,[],[f74,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    k1_xboole_0 = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(superposition,[],[f49,f36])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(forward_demodulation,[],[f48,f36])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(forward_demodulation,[],[f43,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.22/0.54    inference(definition_unfolding,[],[f25,f26,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f38,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.54    inference(ennf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.54    inference(negated_conjecture,[],[f20])).
% 0.22/0.54  fof(f20,conjecture,(
% 0.22/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f73,f35])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0))) )),
% 0.22/0.54    inference(superposition,[],[f35,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(forward_demodulation,[],[f63,f30])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(superposition,[],[f55,f31])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(superposition,[],[f35,f49])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 0.22/0.54    inference(superposition,[],[f74,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f59,f35])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0))) )),
% 0.22/0.54    inference(superposition,[],[f35,f51])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f126,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(forward_demodulation,[],[f123,f31])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    r1_tarski(k5_xboole_0(k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(superposition,[],[f46,f119])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f116,f39])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    r1_tarski(k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)),
% 0.22/0.54    inference(superposition,[],[f46,f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.54    inference(superposition,[],[f101,f36])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f91,f30])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k1_xboole_0))),
% 0.22/0.54    inference(superposition,[],[f60,f31])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f37,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.54  fof(f262,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.54    inference(backward_demodulation,[],[f217,f259])).
% 0.22/0.54  fof(f259,plain,(
% 0.22/0.54    k1_xboole_0 = sK1),
% 0.22/0.54    inference(forward_demodulation,[],[f258,f31])).
% 0.22/0.54  fof(f258,plain,(
% 0.22/0.54    sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.54    inference(forward_demodulation,[],[f257,f217])).
% 0.22/0.54  fof(f257,plain,(
% 0.22/0.54    sK1 = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.54    inference(forward_demodulation,[],[f222,f197])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,sK1)),
% 0.22/0.54    inference(backward_demodulation,[],[f179,f197])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(backward_demodulation,[],[f111,f172])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.54    inference(backward_demodulation,[],[f81,f171])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(forward_demodulation,[],[f169,f30])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 0.22/0.54    inference(superposition,[],[f60,f162])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(forward_demodulation,[],[f75,f30])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0))),
% 0.22/0.54    inference(superposition,[],[f58,f51])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f57,f35])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),X0))) )),
% 0.22/0.54    inference(superposition,[],[f35,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.22/0.54    inference(superposition,[],[f49,f35])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(superposition,[],[f55,f101])).
% 0.22/0.54  fof(f217,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.54    inference(backward_demodulation,[],[f121,f197])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(superposition,[],[f119,f33])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) )),
% 0.22/0.54    inference(equality_resolution,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f42,f32,f42,f42])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (26623)------------------------------
% 0.22/0.54  % (26623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26623)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (26623)Memory used [KB]: 6396
% 0.22/0.54  % (26623)Time elapsed: 0.132 s
% 0.22/0.54  % (26623)------------------------------
% 0.22/0.54  % (26623)------------------------------
% 0.22/0.55  % (26645)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (26642)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (26642)Refutation not found, incomplete strategy% (26642)------------------------------
% 0.22/0.55  % (26642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26642)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26642)Memory used [KB]: 1663
% 0.22/0.55  % (26642)Time elapsed: 0.138 s
% 0.22/0.55  % (26642)------------------------------
% 0.22/0.55  % (26642)------------------------------
% 0.22/0.55  % (26625)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (26647)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (26639)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (26634)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (26622)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (26634)Refutation not found, incomplete strategy% (26634)------------------------------
% 0.22/0.55  % (26634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26634)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26634)Memory used [KB]: 6140
% 0.22/0.55  % (26634)Time elapsed: 0.003 s
% 0.22/0.55  % (26634)------------------------------
% 0.22/0.55  % (26634)------------------------------
% 0.22/0.55  % (26628)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (26636)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (26631)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (26636)Refutation not found, incomplete strategy% (26636)------------------------------
% 0.22/0.55  % (26636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26636)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26636)Memory used [KB]: 10618
% 0.22/0.55  % (26636)Time elapsed: 0.140 s
% 0.22/0.55  % (26636)------------------------------
% 0.22/0.55  % (26636)------------------------------
% 0.22/0.56  % (26630)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (26648)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (26629)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (26629)Refutation not found, incomplete strategy% (26629)------------------------------
% 0.22/0.56  % (26629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26629)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26629)Memory used [KB]: 10618
% 0.22/0.56  % (26629)Time elapsed: 0.150 s
% 0.22/0.56  % (26629)------------------------------
% 0.22/0.56  % (26629)------------------------------
% 0.22/0.56  % (26618)Success in time 0.195 s
%------------------------------------------------------------------------------
