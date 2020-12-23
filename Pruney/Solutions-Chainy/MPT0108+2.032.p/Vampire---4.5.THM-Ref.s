%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:22 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   83 (1911 expanded)
%              Number of leaves         :   14 ( 586 expanded)
%              Depth                    :   23
%              Number of atoms          :   91 (2272 expanded)
%              Number of equality atoms :   69 (1679 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8079,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8078,f7311])).

fof(f7311,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,X8)),X8) ),
    inference(superposition,[],[f7225,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f7225,plain,(
    ! [X2,X1] : k5_xboole_0(k5_xboole_0(X1,X2),X2) = X1 ),
    inference(superposition,[],[f7083,f6694])).

fof(f6694,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(backward_demodulation,[],[f5883,f6674])).

fof(f6674,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,X8) = X8 ),
    inference(forward_demodulation,[],[f6586,f24])).

fof(f24,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f6586,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,k1_xboole_0) ),
    inference(superposition,[],[f5883,f5677])).

fof(f5677,plain,(
    ! [X25] : k1_xboole_0 = k5_xboole_0(X25,X25) ),
    inference(backward_demodulation,[],[f4836,f5631])).

fof(f5631,plain,(
    ! [X72] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X72,X72),k5_xboole_0(X72,k5_xboole_0(X72,X72))) ),
    inference(superposition,[],[f4767,f4922])).

fof(f4922,plain,(
    ! [X60] : k3_xboole_0(X60,k5_xboole_0(X60,k5_xboole_0(X60,X60))) = X60 ),
    inference(forward_demodulation,[],[f4754,f24])).

fof(f4754,plain,(
    ! [X60] : k3_xboole_0(X60,k5_xboole_0(X60,k5_xboole_0(k5_xboole_0(X60,X60),k1_xboole_0))) = X60 ),
    inference(superposition,[],[f38,f689])).

fof(f689,plain,(
    ! [X20] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X20,X20),X20) ),
    inference(forward_demodulation,[],[f676,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f676,plain,(
    ! [X20] : k3_xboole_0(k5_xboole_0(X20,X20),X20) = k3_xboole_0(k5_xboole_0(X20,X20),k1_xboole_0) ),
    inference(superposition,[],[f308,f609])).

fof(f609,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f310,f85])).

fof(f85,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f73,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f31,f25])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f310,plain,(
    ! [X8,X7] : k1_xboole_0 = k3_xboole_0(X7,k3_xboole_0(X8,k5_xboole_0(X7,X8))) ),
    inference(superposition,[],[f35,f76])).

fof(f76,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f308,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f35,f73])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f4767,plain,(
    ! [X4,X3] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X3)),X3) ),
    inference(superposition,[],[f311,f38])).

fof(f311,plain,(
    ! [X10,X9] : k1_xboole_0 = k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9))) ),
    inference(superposition,[],[f35,f77])).

fof(f77,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(resolution,[],[f32,f61])).

fof(f61,plain,(
    ! [X2,X1] : r1_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f28,f26])).

fof(f4836,plain,(
    ! [X25] : k5_xboole_0(X25,X25) = k3_xboole_0(k5_xboole_0(X25,X25),k5_xboole_0(X25,k5_xboole_0(X25,X25))) ),
    inference(forward_demodulation,[],[f4835,f24])).

fof(f4835,plain,(
    ! [X25] : k5_xboole_0(X25,X25) = k3_xboole_0(k5_xboole_0(X25,X25),k5_xboole_0(X25,k5_xboole_0(X25,k5_xboole_0(X25,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f4736,f33])).

fof(f4736,plain,(
    ! [X25] : k5_xboole_0(X25,X25) = k3_xboole_0(k5_xboole_0(X25,X25),k5_xboole_0(k5_xboole_0(X25,X25),k5_xboole_0(X25,k1_xboole_0))) ),
    inference(superposition,[],[f38,f609])).

fof(f5883,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f33,f5677])).

fof(f7083,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f7051,f24])).

fof(f7051,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f6694,f5881])).

fof(f5881,plain,(
    ! [X2,X3] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f5677,f33])).

fof(f8078,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f42,f8046])).

fof(f8046,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(resolution,[],[f7288,f31])).

fof(f7288,plain,(
    ! [X24,X23] : r1_tarski(X23,k5_xboole_0(X24,k5_xboole_0(X23,k3_xboole_0(X24,X23)))) ),
    inference(backward_demodulation,[],[f6638,f7245])).

fof(f7245,plain,(
    ! [X28,X29] : k5_xboole_0(X28,X29) = k5_xboole_0(X29,X28) ),
    inference(superposition,[],[f6694,f7083])).

fof(f6638,plain,(
    ! [X24,X23] : r1_tarski(X23,k5_xboole_0(X24,k5_xboole_0(k3_xboole_0(X24,X23),X23))) ),
    inference(backward_demodulation,[],[f5925,f6637])).

fof(f6637,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f6585,f242])).

fof(f242,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f33,f24])).

fof(f6585,plain,(
    ! [X6,X7] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(k1_xboole_0,X7)) ),
    inference(superposition,[],[f5883,f5883])).

fof(f5925,plain,(
    ! [X24,X23] : r1_tarski(X23,k5_xboole_0(k1_xboole_0,k5_xboole_0(X24,k5_xboole_0(k3_xboole_0(X24,X23),X23)))) ),
    inference(backward_demodulation,[],[f5202,f5883])).

fof(f5202,plain,(
    ! [X24,X23] : r1_tarski(X23,k5_xboole_0(X23,k5_xboole_0(X23,k5_xboole_0(X24,k5_xboole_0(k3_xboole_0(X24,X23),X23))))) ),
    inference(forward_demodulation,[],[f5201,f33])).

fof(f5201,plain,(
    ! [X24,X23] : r1_tarski(X23,k5_xboole_0(X23,k5_xboole_0(X23,k5_xboole_0(k5_xboole_0(X24,k3_xboole_0(X24,X23)),X23)))) ),
    inference(forward_demodulation,[],[f5171,f33])).

fof(f5171,plain,(
    ! [X24,X23] : r1_tarski(X23,k5_xboole_0(X23,k5_xboole_0(k5_xboole_0(X23,k5_xboole_0(X24,k3_xboole_0(X24,X23))),X23))) ),
    inference(superposition,[],[f5067,f38])).

fof(f5067,plain,(
    ! [X2,X1] : r1_tarski(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) ),
    inference(superposition,[],[f4771,f26])).

fof(f4771,plain,(
    ! [X17,X16] : r1_tarski(X16,k5_xboole_0(X16,k5_xboole_0(X17,k3_xboole_0(X17,X16)))) ),
    inference(superposition,[],[f48,f38])).

fof(f48,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f25,f26])).

fof(f42,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f41,f35])).

fof(f41,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f40,f26])).

fof(f40,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f37,f26])).

fof(f37,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f22,f30,f36])).

fof(f22,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:08:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (23697)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.45  % (23697)Refutation not found, incomplete strategy% (23697)------------------------------
% 0.22/0.45  % (23697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (23697)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.45  
% 0.22/0.45  % (23697)Memory used [KB]: 10618
% 0.22/0.45  % (23697)Time elapsed: 0.003 s
% 0.22/0.45  % (23697)------------------------------
% 0.22/0.45  % (23697)------------------------------
% 0.22/0.48  % (23689)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (23695)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (23698)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (23691)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (23690)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (23696)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (23703)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (23700)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (23699)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (23686)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (23688)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.52  % (23701)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (23693)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.53  % (23694)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.54  % (23687)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.54  % (23692)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (23702)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.96/0.61  % (23700)Refutation found. Thanks to Tanya!
% 1.96/0.61  % SZS status Theorem for theBenchmark
% 1.96/0.61  % SZS output start Proof for theBenchmark
% 1.96/0.61  fof(f8079,plain,(
% 1.96/0.61    $false),
% 1.96/0.61    inference(subsumption_resolution,[],[f8078,f7311])).
% 1.96/0.61  fof(f7311,plain,(
% 1.96/0.61    ( ! [X6,X8,X7] : (k5_xboole_0(X6,X7) = k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,X8)),X8)) )),
% 1.96/0.61    inference(superposition,[],[f7225,f33])).
% 1.96/0.61  fof(f33,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f12])).
% 1.96/0.61  fof(f12,axiom,(
% 1.96/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.96/0.61  fof(f7225,plain,(
% 1.96/0.61    ( ! [X2,X1] : (k5_xboole_0(k5_xboole_0(X1,X2),X2) = X1) )),
% 1.96/0.61    inference(superposition,[],[f7083,f6694])).
% 1.96/0.61  fof(f6694,plain,(
% 1.96/0.61    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) )),
% 1.96/0.61    inference(backward_demodulation,[],[f5883,f6674])).
% 1.96/0.61  fof(f6674,plain,(
% 1.96/0.61    ( ! [X8] : (k5_xboole_0(k1_xboole_0,X8) = X8) )),
% 1.96/0.61    inference(forward_demodulation,[],[f6586,f24])).
% 1.96/0.61  fof(f24,plain,(
% 1.96/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.96/0.61    inference(cnf_transformation,[],[f11])).
% 1.96/0.61  fof(f11,axiom,(
% 1.96/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.96/0.61  fof(f6586,plain,(
% 1.96/0.61    ( ! [X8] : (k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,k1_xboole_0)) )),
% 1.96/0.61    inference(superposition,[],[f5883,f5677])).
% 1.96/0.61  fof(f5677,plain,(
% 1.96/0.61    ( ! [X25] : (k1_xboole_0 = k5_xboole_0(X25,X25)) )),
% 1.96/0.61    inference(backward_demodulation,[],[f4836,f5631])).
% 1.96/0.61  fof(f5631,plain,(
% 1.96/0.61    ( ! [X72] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X72,X72),k5_xboole_0(X72,k5_xboole_0(X72,X72)))) )),
% 1.96/0.61    inference(superposition,[],[f4767,f4922])).
% 1.96/0.61  fof(f4922,plain,(
% 1.96/0.61    ( ! [X60] : (k3_xboole_0(X60,k5_xboole_0(X60,k5_xboole_0(X60,X60))) = X60) )),
% 1.96/0.61    inference(forward_demodulation,[],[f4754,f24])).
% 1.96/0.61  fof(f4754,plain,(
% 1.96/0.61    ( ! [X60] : (k3_xboole_0(X60,k5_xboole_0(X60,k5_xboole_0(k5_xboole_0(X60,X60),k1_xboole_0))) = X60) )),
% 1.96/0.61    inference(superposition,[],[f38,f689])).
% 1.96/0.61  fof(f689,plain,(
% 1.96/0.61    ( ! [X20] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X20,X20),X20)) )),
% 1.96/0.61    inference(forward_demodulation,[],[f676,f23])).
% 1.96/0.61  fof(f23,plain,(
% 1.96/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f9])).
% 1.96/0.61  fof(f9,axiom,(
% 1.96/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.96/0.61  fof(f676,plain,(
% 1.96/0.61    ( ! [X20] : (k3_xboole_0(k5_xboole_0(X20,X20),X20) = k3_xboole_0(k5_xboole_0(X20,X20),k1_xboole_0)) )),
% 1.96/0.61    inference(superposition,[],[f308,f609])).
% 1.96/0.61  fof(f609,plain,(
% 1.96/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X0,X0))) )),
% 1.96/0.61    inference(superposition,[],[f310,f85])).
% 1.96/0.61  fof(f85,plain,(
% 1.96/0.61    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 1.96/0.61    inference(superposition,[],[f73,f26])).
% 1.96/0.61  fof(f26,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f1])).
% 1.96/0.61  fof(f1,axiom,(
% 1.96/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.96/0.61  fof(f73,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 1.96/0.61    inference(resolution,[],[f31,f25])).
% 1.96/0.61  fof(f25,plain,(
% 1.96/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.96/0.61    inference(cnf_transformation,[],[f6])).
% 1.96/0.61  fof(f6,axiom,(
% 1.96/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.96/0.61  fof(f31,plain,(
% 1.96/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.96/0.61    inference(cnf_transformation,[],[f18])).
% 1.96/0.61  fof(f18,plain,(
% 1.96/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.96/0.61    inference(ennf_transformation,[],[f8])).
% 1.96/0.61  fof(f8,axiom,(
% 1.96/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.96/0.61  fof(f310,plain,(
% 1.96/0.61    ( ! [X8,X7] : (k1_xboole_0 = k3_xboole_0(X7,k3_xboole_0(X8,k5_xboole_0(X7,X8)))) )),
% 1.96/0.61    inference(superposition,[],[f35,f76])).
% 1.96/0.61  fof(f76,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.96/0.61    inference(resolution,[],[f32,f28])).
% 1.96/0.61  fof(f28,plain,(
% 1.96/0.61    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f3])).
% 1.96/0.61  fof(f3,axiom,(
% 1.96/0.61    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.96/0.61  fof(f32,plain,(
% 1.96/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.96/0.61    inference(cnf_transformation,[],[f19])).
% 1.96/0.61  fof(f19,plain,(
% 1.96/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 1.96/0.61    inference(ennf_transformation,[],[f16])).
% 1.96/0.61  fof(f16,plain,(
% 1.96/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.96/0.61    inference(unused_predicate_definition_removal,[],[f2])).
% 1.96/0.61  fof(f2,axiom,(
% 1.96/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.96/0.61  fof(f35,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f5])).
% 1.96/0.61  fof(f5,axiom,(
% 1.96/0.61    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.96/0.61  fof(f308,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 1.96/0.61    inference(superposition,[],[f35,f73])).
% 1.96/0.61  fof(f38,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 1.96/0.61    inference(definition_unfolding,[],[f27,f36])).
% 1.96/0.61  fof(f36,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.96/0.61    inference(definition_unfolding,[],[f29,f30])).
% 1.96/0.61  fof(f30,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f4])).
% 1.96/0.61  fof(f4,axiom,(
% 1.96/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.96/0.61  fof(f29,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f13])).
% 1.96/0.61  fof(f13,axiom,(
% 1.96/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.96/0.61  fof(f27,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.96/0.61    inference(cnf_transformation,[],[f7])).
% 1.96/0.61  fof(f7,axiom,(
% 1.96/0.61    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.96/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.96/0.61  fof(f4767,plain,(
% 1.96/0.61    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X3)),X3)) )),
% 1.96/0.61    inference(superposition,[],[f311,f38])).
% 1.96/0.62  fof(f311,plain,(
% 1.96/0.62    ( ! [X10,X9] : (k1_xboole_0 = k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9)))) )),
% 1.96/0.62    inference(superposition,[],[f35,f77])).
% 1.96/0.62  fof(f77,plain,(
% 1.96/0.62    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 1.96/0.62    inference(resolution,[],[f32,f61])).
% 1.96/0.62  fof(f61,plain,(
% 1.96/0.62    ( ! [X2,X1] : (r1_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X1,X2))) )),
% 1.96/0.62    inference(superposition,[],[f28,f26])).
% 1.96/0.62  fof(f4836,plain,(
% 1.96/0.62    ( ! [X25] : (k5_xboole_0(X25,X25) = k3_xboole_0(k5_xboole_0(X25,X25),k5_xboole_0(X25,k5_xboole_0(X25,X25)))) )),
% 1.96/0.62    inference(forward_demodulation,[],[f4835,f24])).
% 1.96/0.62  fof(f4835,plain,(
% 1.96/0.62    ( ! [X25] : (k5_xboole_0(X25,X25) = k3_xboole_0(k5_xboole_0(X25,X25),k5_xboole_0(X25,k5_xboole_0(X25,k5_xboole_0(X25,k1_xboole_0))))) )),
% 1.96/0.62    inference(forward_demodulation,[],[f4736,f33])).
% 1.96/0.62  fof(f4736,plain,(
% 1.96/0.62    ( ! [X25] : (k5_xboole_0(X25,X25) = k3_xboole_0(k5_xboole_0(X25,X25),k5_xboole_0(k5_xboole_0(X25,X25),k5_xboole_0(X25,k1_xboole_0)))) )),
% 1.96/0.62    inference(superposition,[],[f38,f609])).
% 1.96/0.62  fof(f5883,plain,(
% 1.96/0.62    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2))) )),
% 1.96/0.62    inference(superposition,[],[f33,f5677])).
% 1.96/0.62  fof(f7083,plain,(
% 1.96/0.62    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.96/0.62    inference(forward_demodulation,[],[f7051,f24])).
% 1.96/0.62  fof(f7051,plain,(
% 1.96/0.62    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.96/0.62    inference(superposition,[],[f6694,f5881])).
% 1.96/0.62  fof(f5881,plain,(
% 1.96/0.62    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 1.96/0.62    inference(superposition,[],[f5677,f33])).
% 1.96/0.62  fof(f8078,plain,(
% 1.96/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))),
% 1.96/0.62    inference(backward_demodulation,[],[f42,f8046])).
% 1.96/0.62  fof(f8046,plain,(
% 1.96/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0) )),
% 1.96/0.62    inference(resolution,[],[f7288,f31])).
% 1.96/0.62  fof(f7288,plain,(
% 1.96/0.62    ( ! [X24,X23] : (r1_tarski(X23,k5_xboole_0(X24,k5_xboole_0(X23,k3_xboole_0(X24,X23))))) )),
% 1.96/0.62    inference(backward_demodulation,[],[f6638,f7245])).
% 1.96/0.62  fof(f7245,plain,(
% 1.96/0.62    ( ! [X28,X29] : (k5_xboole_0(X28,X29) = k5_xboole_0(X29,X28)) )),
% 1.96/0.62    inference(superposition,[],[f6694,f7083])).
% 1.96/0.62  fof(f6638,plain,(
% 1.96/0.62    ( ! [X24,X23] : (r1_tarski(X23,k5_xboole_0(X24,k5_xboole_0(k3_xboole_0(X24,X23),X23)))) )),
% 1.96/0.62    inference(backward_demodulation,[],[f5925,f6637])).
% 1.96/0.62  fof(f6637,plain,(
% 1.96/0.62    ( ! [X6,X7] : (k5_xboole_0(X6,X7) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,X7))) )),
% 1.96/0.62    inference(forward_demodulation,[],[f6585,f242])).
% 1.96/0.62  fof(f242,plain,(
% 1.96/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 1.96/0.62    inference(superposition,[],[f33,f24])).
% 1.96/0.62  fof(f6585,plain,(
% 1.96/0.62    ( ! [X6,X7] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(k1_xboole_0,X7))) )),
% 1.96/0.62    inference(superposition,[],[f5883,f5883])).
% 1.96/0.62  fof(f5925,plain,(
% 1.96/0.62    ( ! [X24,X23] : (r1_tarski(X23,k5_xboole_0(k1_xboole_0,k5_xboole_0(X24,k5_xboole_0(k3_xboole_0(X24,X23),X23))))) )),
% 1.96/0.62    inference(backward_demodulation,[],[f5202,f5883])).
% 1.96/0.62  fof(f5202,plain,(
% 1.96/0.62    ( ! [X24,X23] : (r1_tarski(X23,k5_xboole_0(X23,k5_xboole_0(X23,k5_xboole_0(X24,k5_xboole_0(k3_xboole_0(X24,X23),X23)))))) )),
% 1.96/0.62    inference(forward_demodulation,[],[f5201,f33])).
% 1.96/0.62  fof(f5201,plain,(
% 1.96/0.62    ( ! [X24,X23] : (r1_tarski(X23,k5_xboole_0(X23,k5_xboole_0(X23,k5_xboole_0(k5_xboole_0(X24,k3_xboole_0(X24,X23)),X23))))) )),
% 1.96/0.62    inference(forward_demodulation,[],[f5171,f33])).
% 1.96/0.62  fof(f5171,plain,(
% 1.96/0.62    ( ! [X24,X23] : (r1_tarski(X23,k5_xboole_0(X23,k5_xboole_0(k5_xboole_0(X23,k5_xboole_0(X24,k3_xboole_0(X24,X23))),X23)))) )),
% 1.96/0.62    inference(superposition,[],[f5067,f38])).
% 1.96/0.62  fof(f5067,plain,(
% 1.96/0.62    ( ! [X2,X1] : (r1_tarski(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))))) )),
% 1.96/0.62    inference(superposition,[],[f4771,f26])).
% 1.96/0.62  fof(f4771,plain,(
% 1.96/0.62    ( ! [X17,X16] : (r1_tarski(X16,k5_xboole_0(X16,k5_xboole_0(X17,k3_xboole_0(X17,X16))))) )),
% 1.96/0.62    inference(superposition,[],[f48,f38])).
% 1.96/0.62  fof(f48,plain,(
% 1.96/0.62    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 1.96/0.62    inference(superposition,[],[f25,f26])).
% 1.96/0.62  fof(f42,plain,(
% 1.96/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 1.96/0.62    inference(backward_demodulation,[],[f41,f35])).
% 1.96/0.62  fof(f41,plain,(
% 1.96/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 1.96/0.62    inference(forward_demodulation,[],[f40,f26])).
% 1.96/0.62  fof(f40,plain,(
% 1.96/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 1.96/0.62    inference(backward_demodulation,[],[f37,f26])).
% 1.96/0.62  fof(f37,plain,(
% 1.96/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 1.96/0.62    inference(definition_unfolding,[],[f22,f30,f36])).
% 1.96/0.62  fof(f22,plain,(
% 1.96/0.62    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.96/0.62    inference(cnf_transformation,[],[f21])).
% 1.96/0.62  fof(f21,plain,(
% 1.96/0.62    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.96/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20])).
% 1.96/0.62  fof(f20,plain,(
% 1.96/0.62    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.96/0.62    introduced(choice_axiom,[])).
% 1.96/0.62  fof(f17,plain,(
% 1.96/0.62    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.96/0.62    inference(ennf_transformation,[],[f15])).
% 1.96/0.62  fof(f15,negated_conjecture,(
% 1.96/0.62    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.96/0.62    inference(negated_conjecture,[],[f14])).
% 1.96/0.62  fof(f14,conjecture,(
% 1.96/0.62    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 1.96/0.62  % SZS output end Proof for theBenchmark
% 1.96/0.62  % (23700)------------------------------
% 1.96/0.62  % (23700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.62  % (23700)Termination reason: Refutation
% 1.96/0.62  
% 1.96/0.62  % (23700)Memory used [KB]: 9978
% 1.96/0.62  % (23700)Time elapsed: 0.186 s
% 1.96/0.62  % (23700)------------------------------
% 1.96/0.62  % (23700)------------------------------
% 1.96/0.62  % (23685)Success in time 0.251 s
%------------------------------------------------------------------------------
