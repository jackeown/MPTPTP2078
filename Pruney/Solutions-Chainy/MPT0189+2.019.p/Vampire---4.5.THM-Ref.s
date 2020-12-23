%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:20 EST 2020

% Result     : Theorem 52.54s
% Output     : Refutation 52.54s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 150 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :   78 ( 151 expanded)
%              Number of equality atoms :   77 ( 150 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43203,plain,(
    $false ),
    inference(subsumption_resolution,[],[f43144,f66])).

fof(f66,plain,(
    ! [X14,X12,X13,X11] : k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12) ),
    inference(superposition,[],[f32,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f43144,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1) ),
    inference(superposition,[],[f22,f42024])).

fof(f42024,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X8,X9,X10,X11) = k2_enumset1(X9,X10,X11,X8) ),
    inference(superposition,[],[f42016,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42016,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X3,X2) = k2_enumset1(X1,X3,X2,X0) ),
    inference(forward_demodulation,[],[f42005,f41881])).

fof(f41881,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f41857,f33])).

fof(f41857,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(superposition,[],[f27186,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f31,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27186,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f27181,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f27181,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f1114,f33])).

fof(f1114,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f1113,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f1113,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(superposition,[],[f136,f34])).

fof(f136,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(forward_demodulation,[],[f135,f36])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f135,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(superposition,[],[f38,f35])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f42005,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X3,X2) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) ),
    inference(superposition,[],[f41976,f23])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41976,plain,(
    ! [X6,X8,X7,X5,X9] : k2_xboole_0(k1_enumset1(X5,X6,X7),k2_tarski(X8,X9)) = k3_enumset1(X8,X9,X5,X7,X6) ),
    inference(backward_demodulation,[],[f28508,f41975])).

fof(f41975,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X7,X6,X8,X8,X9) = k3_enumset1(X8,X9,X5,X6,X7) ),
    inference(forward_demodulation,[],[f41964,f27177])).

fof(f27177,plain,(
    ! [X21,X19,X17,X20,X18] : k2_xboole_0(k2_tarski(X17,X18),k1_enumset1(X19,X20,X21)) = k3_enumset1(X17,X18,X19,X20,X21) ),
    inference(forward_demodulation,[],[f27168,f34])).

fof(f27168,plain,(
    ! [X21,X19,X17,X20,X18] : k4_enumset1(X17,X17,X18,X19,X20,X21) = k2_xboole_0(k2_tarski(X17,X18),k1_enumset1(X19,X20,X21)) ),
    inference(superposition,[],[f971,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f77,f26])).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f77,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X3,X5,X4) ),
    inference(superposition,[],[f61,f29])).

fof(f971,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_enumset1(X3,X4,X5)) ),
    inference(forward_demodulation,[],[f953,f35])).

fof(f953,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_enumset1(X3,X4,X5)) ),
    inference(superposition,[],[f122,f61])).

fof(f122,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(forward_demodulation,[],[f117,f36])).

fof(f117,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f37,f33])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(f41964,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X7,X6,X8,X8,X9) = k2_xboole_0(k2_tarski(X8,X9),k1_enumset1(X5,X6,X7)) ),
    inference(superposition,[],[f27169,f2193])).

fof(f2193,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f2019,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f2019,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f1866,f25])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1866,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X3,X2) ),
    inference(forward_demodulation,[],[f1808,f28])).

fof(f1808,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),X2) = k5_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f178,f154])).

fof(f154,plain,(
    ! [X10,X11,X9] : k5_xboole_0(k4_xboole_0(X9,X10),X11) = k5_xboole_0(k3_xboole_0(X10,X9),k5_xboole_0(X9,X11)) ),
    inference(superposition,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f27,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f30,f25])).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f178,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(X8,X6)) ),
    inference(superposition,[],[f49,f27])).

fof(f49,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f30,f25])).

fof(f27169,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X4,X3),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f971,f26])).

fof(f28508,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X6,X7,X8,X8,X9) = k2_xboole_0(k1_enumset1(X5,X6,X7),k2_tarski(X8,X9)) ),
    inference(forward_demodulation,[],[f28483,f29])).

fof(f28483,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X6,X7,X8,X8,X9) = k2_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_tarski(X8,X9)) ),
    inference(superposition,[],[f967,f35])).

fof(f967,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X2,X3,X4,X5,X0,X0,X1) = k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f122,f26])).

fof(f22,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:33:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (6090)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (6084)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (6087)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (6091)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (6093)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (6089)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (6098)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (6095)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (6096)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (6095)Refutation not found, incomplete strategy% (6095)------------------------------
% 0.21/0.48  % (6095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6095)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (6095)Memory used [KB]: 10618
% 0.21/0.48  % (6095)Time elapsed: 0.071 s
% 0.21/0.48  % (6095)------------------------------
% 0.21/0.48  % (6095)------------------------------
% 0.21/0.48  % (6086)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (6085)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (6101)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (6099)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (6094)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (6100)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (6092)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (6097)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (6088)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 5.23/1.05  % (6088)Time limit reached!
% 5.23/1.05  % (6088)------------------------------
% 5.23/1.05  % (6088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.23/1.05  % (6088)Termination reason: Time limit
% 5.23/1.05  % (6088)Termination phase: Saturation
% 5.23/1.05  
% 5.23/1.05  % (6088)Memory used [KB]: 14967
% 5.23/1.05  % (6088)Time elapsed: 0.600 s
% 5.23/1.05  % (6088)------------------------------
% 5.23/1.05  % (6088)------------------------------
% 12.94/2.00  % (6090)Time limit reached!
% 12.94/2.00  % (6090)------------------------------
% 12.94/2.00  % (6090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.94/2.00  % (6090)Termination reason: Time limit
% 12.94/2.00  
% 12.94/2.00  % (6090)Memory used [KB]: 36204
% 12.94/2.00  % (6090)Time elapsed: 1.581 s
% 12.94/2.00  % (6090)------------------------------
% 12.94/2.00  % (6090)------------------------------
% 12.94/2.03  % (6089)Time limit reached!
% 12.94/2.03  % (6089)------------------------------
% 12.94/2.03  % (6089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.94/2.03  % (6089)Termination reason: Time limit
% 12.94/2.03  % (6089)Termination phase: Saturation
% 12.94/2.03  
% 12.94/2.03  % (6089)Memory used [KB]: 38250
% 12.94/2.03  % (6089)Time elapsed: 1.500 s
% 12.94/2.03  % (6089)------------------------------
% 12.94/2.03  % (6089)------------------------------
% 14.81/2.27  % (6086)Time limit reached!
% 14.81/2.27  % (6086)------------------------------
% 14.81/2.27  % (6086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.81/2.28  % (6086)Termination reason: Time limit
% 14.81/2.28  
% 14.81/2.28  % (6086)Memory used [KB]: 38123
% 14.81/2.28  % (6086)Time elapsed: 1.852 s
% 14.81/2.28  % (6086)------------------------------
% 14.81/2.28  % (6086)------------------------------
% 17.78/2.61  % (6096)Time limit reached!
% 17.78/2.61  % (6096)------------------------------
% 17.78/2.61  % (6096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.78/2.61  % (6096)Termination reason: Time limit
% 17.78/2.61  % (6096)Termination phase: Saturation
% 17.78/2.61  
% 17.78/2.61  % (6096)Memory used [KB]: 36715
% 17.78/2.61  % (6096)Time elapsed: 2.200 s
% 17.78/2.61  % (6096)------------------------------
% 17.78/2.61  % (6096)------------------------------
% 52.54/6.97  % (6087)Refutation found. Thanks to Tanya!
% 52.54/6.97  % SZS status Theorem for theBenchmark
% 52.54/6.97  % SZS output start Proof for theBenchmark
% 52.54/6.97  fof(f43203,plain,(
% 52.54/6.97    $false),
% 52.54/6.97    inference(subsumption_resolution,[],[f43144,f66])).
% 52.54/6.97  fof(f66,plain,(
% 52.54/6.97    ( ! [X14,X12,X13,X11] : (k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12)) )),
% 52.54/6.97    inference(superposition,[],[f32,f31])).
% 52.54/6.97  fof(f31,plain,(
% 52.54/6.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 52.54/6.97    inference(cnf_transformation,[],[f6])).
% 52.54/6.97  fof(f6,axiom,(
% 52.54/6.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 52.54/6.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 52.54/6.97  fof(f32,plain,(
% 52.54/6.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 52.54/6.97    inference(cnf_transformation,[],[f7])).
% 52.54/6.97  fof(f7,axiom,(
% 52.54/6.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 52.54/6.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 52.54/6.97  fof(f43144,plain,(
% 52.54/6.97    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1)),
% 52.54/6.97    inference(superposition,[],[f22,f42024])).
% 52.54/6.97  fof(f42024,plain,(
% 52.54/6.97    ( ! [X10,X8,X11,X9] : (k2_enumset1(X8,X9,X10,X11) = k2_enumset1(X9,X10,X11,X8)) )),
% 52.54/6.97    inference(superposition,[],[f42016,f33])).
% 52.54/6.97  fof(f33,plain,(
% 52.54/6.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 52.54/6.97    inference(cnf_transformation,[],[f13])).
% 52.54/6.97  fof(f13,axiom,(
% 52.54/6.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 52.54/6.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 52.54/6.97  fof(f42016,plain,(
% 52.54/6.97    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X3,X2) = k2_enumset1(X1,X3,X2,X0)) )),
% 52.54/6.97    inference(forward_demodulation,[],[f42005,f41881])).
% 52.54/6.97  fof(f41881,plain,(
% 52.54/6.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 52.54/6.97    inference(forward_demodulation,[],[f41857,f33])).
% 52.54/6.97  fof(f41857,plain,(
% 52.54/6.97    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 52.54/6.97    inference(superposition,[],[f27186,f61])).
% 52.54/6.97  fof(f61,plain,(
% 52.54/6.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 52.54/6.97    inference(superposition,[],[f31,f29])).
% 52.54/6.97  fof(f29,plain,(
% 52.54/6.97    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 52.54/6.97    inference(cnf_transformation,[],[f12])).
% 52.54/6.97  fof(f12,axiom,(
% 52.54/6.97    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 52.54/6.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 52.54/6.97  fof(f27186,plain,(
% 52.54/6.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 52.54/6.97    inference(forward_demodulation,[],[f27181,f34])).
% 52.54/6.97  fof(f34,plain,(
% 52.54/6.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 52.54/6.97    inference(cnf_transformation,[],[f14])).
% 52.54/6.97  fof(f14,axiom,(
% 52.54/6.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 52.54/6.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 52.54/6.97  fof(f27181,plain,(
% 52.54/6.97    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 52.54/6.97    inference(superposition,[],[f1114,f33])).
% 52.54/6.97  fof(f1114,plain,(
% 52.54/6.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 52.54/6.97    inference(forward_demodulation,[],[f1113,f35])).
% 52.54/6.97  fof(f35,plain,(
% 52.54/6.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 52.54/6.97    inference(cnf_transformation,[],[f15])).
% 52.54/6.97  fof(f15,axiom,(
% 52.54/6.97    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 52.54/6.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 52.54/6.97  fof(f1113,plain,(
% 52.54/6.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 52.54/6.97    inference(superposition,[],[f136,f34])).
% 52.54/6.97  fof(f136,plain,(
% 52.54/6.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 52.54/6.97    inference(forward_demodulation,[],[f135,f36])).
% 52.54/6.97  fof(f36,plain,(
% 52.54/6.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 52.54/6.97    inference(cnf_transformation,[],[f16])).
% 52.54/6.97  fof(f16,axiom,(
% 52.54/6.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 52.54/6.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 52.54/6.97  fof(f135,plain,(
% 52.54/6.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 52.54/6.97    inference(superposition,[],[f38,f35])).
% 52.54/6.97  fof(f38,plain,(
% 52.54/6.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 52.54/6.97    inference(cnf_transformation,[],[f9])).
% 52.54/6.97  fof(f9,axiom,(
% 52.54/6.97    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 52.54/6.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 52.54/6.97  fof(f42005,plain,(
% 52.54/6.97    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X3,X2) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) )),
% 52.54/6.97    inference(superposition,[],[f41976,f23])).
% 52.54/6.97  fof(f23,plain,(
% 52.54/6.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 52.54/6.97    inference(cnf_transformation,[],[f10])).
% 52.54/6.97  fof(f10,axiom,(
% 52.54/6.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 52.54/6.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 52.54/6.97  fof(f41976,plain,(
% 52.54/6.97    ( ! [X6,X8,X7,X5,X9] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k2_tarski(X8,X9)) = k3_enumset1(X8,X9,X5,X7,X6)) )),
% 52.54/6.97    inference(backward_demodulation,[],[f28508,f41975])).
% 52.54/6.97  fof(f41975,plain,(
% 52.54/6.97    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X7,X6,X8,X8,X9) = k3_enumset1(X8,X9,X5,X6,X7)) )),
% 52.54/6.97    inference(forward_demodulation,[],[f41964,f27177])).
% 52.54/6.97  fof(f27177,plain,(
% 52.54/6.97    ( ! [X21,X19,X17,X20,X18] : (k2_xboole_0(k2_tarski(X17,X18),k1_enumset1(X19,X20,X21)) = k3_enumset1(X17,X18,X19,X20,X21)) )),
% 52.54/6.97    inference(forward_demodulation,[],[f27168,f34])).
% 52.54/6.97  fof(f27168,plain,(
% 52.54/6.97    ( ! [X21,X19,X17,X20,X18] : (k4_enumset1(X17,X17,X18,X19,X20,X21) = k2_xboole_0(k2_tarski(X17,X18),k1_enumset1(X19,X20,X21))) )),
% 52.54/6.97    inference(superposition,[],[f971,f87])).
% 52.54/6.97  fof(f87,plain,(
% 52.54/6.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 52.54/6.97    inference(superposition,[],[f77,f26])).
% 52.54/6.98  fof(f26,plain,(
% 52.54/6.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 52.54/6.98    inference(cnf_transformation,[],[f11])).
% 52.54/6.98  fof(f11,axiom,(
% 52.54/6.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 52.54/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 52.54/6.98  fof(f77,plain,(
% 52.54/6.98    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X3,X5,X4)) )),
% 52.54/6.98    inference(superposition,[],[f61,f29])).
% 52.54/6.98  fof(f971,plain,(
% 52.54/6.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_enumset1(X3,X4,X5))) )),
% 52.54/6.98    inference(forward_demodulation,[],[f953,f35])).
% 52.54/6.98  fof(f953,plain,(
% 52.54/6.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_enumset1(X3,X4,X5))) )),
% 52.54/6.98    inference(superposition,[],[f122,f61])).
% 52.54/6.98  fof(f122,plain,(
% 52.54/6.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 52.54/6.98    inference(forward_demodulation,[],[f117,f36])).
% 52.54/6.98  fof(f117,plain,(
% 52.54/6.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 52.54/6.98    inference(superposition,[],[f37,f33])).
% 52.54/6.98  fof(f37,plain,(
% 52.54/6.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 52.54/6.98    inference(cnf_transformation,[],[f8])).
% 52.54/6.98  fof(f8,axiom,(
% 52.54/6.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 52.54/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).
% 52.54/6.98  fof(f41964,plain,(
% 52.54/6.98    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X7,X6,X8,X8,X9) = k2_xboole_0(k2_tarski(X8,X9),k1_enumset1(X5,X6,X7))) )),
% 52.54/6.98    inference(superposition,[],[f27169,f2193])).
% 52.54/6.98  fof(f2193,plain,(
% 52.54/6.98    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 52.54/6.98    inference(superposition,[],[f2019,f28])).
% 52.54/6.98  fof(f28,plain,(
% 52.54/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 52.54/6.98    inference(cnf_transformation,[],[f5])).
% 52.54/6.98  fof(f5,axiom,(
% 52.54/6.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 52.54/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 52.54/6.98  fof(f2019,plain,(
% 52.54/6.98    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 52.54/6.98    inference(superposition,[],[f1866,f25])).
% 52.54/6.98  fof(f25,plain,(
% 52.54/6.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 52.54/6.98    inference(cnf_transformation,[],[f2])).
% 52.54/6.98  fof(f2,axiom,(
% 52.54/6.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 52.54/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 52.54/6.98  fof(f1866,plain,(
% 52.54/6.98    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X3,X2)) )),
% 52.54/6.98    inference(forward_demodulation,[],[f1808,f28])).
% 52.54/6.98  fof(f1808,plain,(
% 52.54/6.98    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),X2) = k5_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 52.54/6.98    inference(superposition,[],[f178,f154])).
% 52.54/6.98  fof(f154,plain,(
% 52.54/6.98    ( ! [X10,X11,X9] : (k5_xboole_0(k4_xboole_0(X9,X10),X11) = k5_xboole_0(k3_xboole_0(X10,X9),k5_xboole_0(X9,X11))) )),
% 52.54/6.98    inference(superposition,[],[f43,f39])).
% 52.54/6.98  fof(f39,plain,(
% 52.54/6.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 52.54/6.98    inference(superposition,[],[f27,f24])).
% 52.54/6.98  fof(f24,plain,(
% 52.54/6.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 52.54/6.98    inference(cnf_transformation,[],[f1])).
% 52.54/6.98  fof(f1,axiom,(
% 52.54/6.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 52.54/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 52.54/6.98  fof(f27,plain,(
% 52.54/6.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 52.54/6.98    inference(cnf_transformation,[],[f3])).
% 52.54/6.98  fof(f3,axiom,(
% 52.54/6.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 52.54/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 52.54/6.98  fof(f43,plain,(
% 52.54/6.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) )),
% 52.54/6.98    inference(superposition,[],[f30,f25])).
% 52.54/6.98  fof(f30,plain,(
% 52.54/6.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 52.54/6.98    inference(cnf_transformation,[],[f4])).
% 52.54/6.98  fof(f4,axiom,(
% 52.54/6.98    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 52.54/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 52.54/6.98  fof(f178,plain,(
% 52.54/6.98    ( ! [X6,X8,X7] : (k5_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(X8,X6))) )),
% 52.54/6.98    inference(superposition,[],[f49,f27])).
% 52.54/6.98  fof(f49,plain,(
% 52.54/6.98    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 52.54/6.98    inference(superposition,[],[f30,f25])).
% 52.54/6.98  fof(f27169,plain,(
% 52.54/6.98    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X4,X3),k2_tarski(X0,X1))) )),
% 52.54/6.98    inference(superposition,[],[f971,f26])).
% 52.54/6.98  fof(f28508,plain,(
% 52.54/6.98    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X6,X7,X8,X8,X9) = k2_xboole_0(k1_enumset1(X5,X6,X7),k2_tarski(X8,X9))) )),
% 52.54/6.98    inference(forward_demodulation,[],[f28483,f29])).
% 52.54/6.98  fof(f28483,plain,(
% 52.54/6.98    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X6,X7,X8,X8,X9) = k2_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_tarski(X8,X9))) )),
% 52.54/6.98    inference(superposition,[],[f967,f35])).
% 52.54/6.98  fof(f967,plain,(
% 52.54/6.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X2,X3,X4,X5,X0,X0,X1) = k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_tarski(X0,X1))) )),
% 52.54/6.98    inference(superposition,[],[f122,f26])).
% 52.54/6.98  fof(f22,plain,(
% 52.54/6.98    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 52.54/6.98    inference(cnf_transformation,[],[f21])).
% 52.54/6.98  fof(f21,plain,(
% 52.54/6.98    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 52.54/6.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f20])).
% 52.54/6.98  fof(f20,plain,(
% 52.54/6.98    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 52.54/6.98    introduced(choice_axiom,[])).
% 52.54/6.98  fof(f19,plain,(
% 52.54/6.98    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 52.54/6.98    inference(ennf_transformation,[],[f18])).
% 52.54/6.98  fof(f18,negated_conjecture,(
% 52.54/6.98    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 52.54/6.98    inference(negated_conjecture,[],[f17])).
% 52.54/6.98  fof(f17,conjecture,(
% 52.54/6.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 52.54/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
% 52.54/6.98  % SZS output end Proof for theBenchmark
% 52.54/6.98  % (6087)------------------------------
% 52.54/6.98  % (6087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 52.54/6.98  % (6087)Termination reason: Refutation
% 52.54/6.98  
% 52.54/6.98  % (6087)Memory used [KB]: 131255
% 52.54/6.98  % (6087)Time elapsed: 6.548 s
% 52.54/6.98  % (6087)------------------------------
% 52.54/6.98  % (6087)------------------------------
% 52.54/6.98  % (6083)Success in time 6.624 s
%------------------------------------------------------------------------------
