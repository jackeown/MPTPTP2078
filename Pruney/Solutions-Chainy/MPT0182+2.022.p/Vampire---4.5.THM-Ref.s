%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:12 EST 2020

% Result     : Theorem 49.82s
% Output     : Refutation 49.82s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 141 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :   74 ( 142 expanded)
%              Number of equality atoms :   73 ( 141 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41898,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41890,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(f41890,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(superposition,[],[f21,f41588])).

fof(f41588,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4) ),
    inference(superposition,[],[f40511,f40278])).

fof(f40278,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0) ),
    inference(forward_demodulation,[],[f40266,f22079])).

fof(f22079,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(forward_demodulation,[],[f22076,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22076,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(superposition,[],[f22065,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f22065,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3) ),
    inference(forward_demodulation,[],[f22062,f31])).

fof(f22062,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3) ),
    inference(superposition,[],[f16929,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f16929,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(forward_demodulation,[],[f16927,f32])).

fof(f16927,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(superposition,[],[f1467,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f1467,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5) ),
    inference(forward_demodulation,[],[f1465,f33])).

fof(f1465,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5) ),
    inference(superposition,[],[f507,f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f507,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k5_enumset1(X1,X2,X3,X4,X5,X6,X0) ),
    inference(backward_demodulation,[],[f389,f506])).

fof(f506,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(forward_demodulation,[],[f505,f34])).

fof(f505,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(superposition,[],[f36,f33])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f389,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)) ),
    inference(superposition,[],[f35,f22])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(f40266,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f39735,f22])).

fof(f39735,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f39719,f31])).

fof(f39719,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f22074,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22074,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f22068,f32])).

fof(f22068,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f1582,f29])).

fof(f1582,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f1580,f33])).

fof(f1580,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f390,f31])).

fof(f390,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(forward_demodulation,[],[f388,f34])).

fof(f388,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f35,f32])).

fof(f40511,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) ),
    inference(superposition,[],[f40277,f1885])).

fof(f1885,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f1706,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1706,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f1673,f24])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1673,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X3,X2) ),
    inference(forward_demodulation,[],[f1615,f27])).

fof(f1615,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),X2) = k5_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f94,f70])).

fof(f70,plain,(
    ! [X10,X11,X9] : k5_xboole_0(k4_xboole_0(X9,X10),X11) = k5_xboole_0(k3_xboole_0(X10,X9),k5_xboole_0(X9,X11)) ),
    inference(superposition,[],[f49,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f30,f24])).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f94,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(X8,X6)) ),
    inference(superposition,[],[f55,f26])).

fof(f55,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f30,f24])).

fof(f40277,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f40265,f29])).

fof(f40265,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f39735,f22])).

fof(f21,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:55:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (1576)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (1586)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (1577)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (1590)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (1579)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (1589)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (1581)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (1593)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (1588)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (1587)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (1585)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (1587)Refutation not found, incomplete strategy% (1587)------------------------------
% 0.21/0.51  % (1587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1587)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1587)Memory used [KB]: 10618
% 0.21/0.51  % (1587)Time elapsed: 0.096 s
% 0.21/0.51  % (1587)------------------------------
% 0.21/0.51  % (1587)------------------------------
% 0.21/0.52  % (1580)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (1582)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (1578)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (1592)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.53  % (1591)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.54  % (1584)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.54  % (1583)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 5.67/1.09  % (1580)Time limit reached!
% 5.67/1.09  % (1580)------------------------------
% 5.67/1.09  % (1580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.67/1.09  % (1580)Termination reason: Time limit
% 5.67/1.09  % (1580)Termination phase: Saturation
% 5.67/1.09  
% 5.67/1.09  % (1580)Memory used [KB]: 14711
% 5.67/1.09  % (1580)Time elapsed: 0.600 s
% 5.67/1.09  % (1580)------------------------------
% 5.67/1.09  % (1580)------------------------------
% 11.77/1.92  % (1582)Time limit reached!
% 11.77/1.92  % (1582)------------------------------
% 11.77/1.92  % (1582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.53/1.94  % (1582)Termination reason: Time limit
% 12.53/1.94  
% 12.53/1.94  % (1582)Memory used [KB]: 25841
% 12.53/1.94  % (1582)Time elapsed: 1.506 s
% 12.53/1.94  % (1582)------------------------------
% 12.53/1.94  % (1582)------------------------------
% 12.53/1.95  % (1581)Time limit reached!
% 12.53/1.95  % (1581)------------------------------
% 12.53/1.95  % (1581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.53/1.95  % (1581)Termination reason: Time limit
% 12.53/1.95  % (1581)Termination phase: Saturation
% 12.53/1.95  
% 12.53/1.95  % (1581)Memory used [KB]: 40937
% 12.53/1.95  % (1581)Time elapsed: 1.500 s
% 12.53/1.95  % (1581)------------------------------
% 12.53/1.95  % (1581)------------------------------
% 14.92/2.27  % (1578)Time limit reached!
% 14.92/2.27  % (1578)------------------------------
% 14.92/2.27  % (1578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.92/2.27  % (1578)Termination reason: Time limit
% 14.92/2.27  % (1578)Termination phase: Saturation
% 14.92/2.27  
% 14.92/2.27  % (1578)Memory used [KB]: 38378
% 14.92/2.27  % (1578)Time elapsed: 1.800 s
% 14.92/2.27  % (1578)------------------------------
% 14.92/2.27  % (1578)------------------------------
% 17.87/2.65  % (1588)Time limit reached!
% 17.87/2.65  % (1588)------------------------------
% 17.87/2.65  % (1588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.87/2.65  % (1588)Termination reason: Time limit
% 17.87/2.65  
% 17.87/2.65  % (1588)Memory used [KB]: 37739
% 17.87/2.65  % (1588)Time elapsed: 2.236 s
% 17.87/2.65  % (1588)------------------------------
% 17.87/2.65  % (1588)------------------------------
% 49.82/6.60  % (1579)Refutation found. Thanks to Tanya!
% 49.82/6.60  % SZS status Theorem for theBenchmark
% 49.82/6.60  % SZS output start Proof for theBenchmark
% 49.82/6.60  fof(f41898,plain,(
% 49.82/6.60    $false),
% 49.82/6.60    inference(subsumption_resolution,[],[f41890,f28])).
% 49.82/6.60  fof(f28,plain,(
% 49.82/6.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 49.82/6.60    inference(cnf_transformation,[],[f15])).
% 49.82/6.60  fof(f15,axiom,(
% 49.82/6.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
% 49.82/6.60  fof(f41890,plain,(
% 49.82/6.60    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 49.82/6.60    inference(superposition,[],[f21,f41588])).
% 49.82/6.60  fof(f41588,plain,(
% 49.82/6.60    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)) )),
% 49.82/6.60    inference(superposition,[],[f40511,f40278])).
% 49.82/6.60  fof(f40278,plain,(
% 49.82/6.60    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0)) )),
% 49.82/6.60    inference(forward_demodulation,[],[f40266,f22079])).
% 49.82/6.60  fof(f22079,plain,(
% 49.82/6.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 49.82/6.60    inference(forward_demodulation,[],[f22076,f29])).
% 49.82/6.60  fof(f29,plain,(
% 49.82/6.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 49.82/6.60    inference(cnf_transformation,[],[f10])).
% 49.82/6.60  fof(f10,axiom,(
% 49.82/6.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 49.82/6.60  fof(f22076,plain,(
% 49.82/6.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 49.82/6.60    inference(superposition,[],[f22065,f31])).
% 49.82/6.60  fof(f31,plain,(
% 49.82/6.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 49.82/6.60    inference(cnf_transformation,[],[f11])).
% 49.82/6.60  fof(f11,axiom,(
% 49.82/6.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 49.82/6.60  fof(f22065,plain,(
% 49.82/6.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) )),
% 49.82/6.60    inference(forward_demodulation,[],[f22062,f31])).
% 49.82/6.60  fof(f22062,plain,(
% 49.82/6.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) )),
% 49.82/6.60    inference(superposition,[],[f16929,f32])).
% 49.82/6.60  fof(f32,plain,(
% 49.82/6.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 49.82/6.60    inference(cnf_transformation,[],[f12])).
% 49.82/6.60  fof(f12,axiom,(
% 49.82/6.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 49.82/6.60  fof(f16929,plain,(
% 49.82/6.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 49.82/6.60    inference(forward_demodulation,[],[f16927,f32])).
% 49.82/6.60  fof(f16927,plain,(
% 49.82/6.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 49.82/6.60    inference(superposition,[],[f1467,f33])).
% 49.82/6.60  fof(f33,plain,(
% 49.82/6.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 49.82/6.60    inference(cnf_transformation,[],[f13])).
% 49.82/6.60  fof(f13,axiom,(
% 49.82/6.60    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 49.82/6.60  fof(f1467,plain,(
% 49.82/6.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5)) )),
% 49.82/6.60    inference(forward_demodulation,[],[f1465,f33])).
% 49.82/6.60  fof(f1465,plain,(
% 49.82/6.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5)) )),
% 49.82/6.60    inference(superposition,[],[f507,f34])).
% 49.82/6.60  fof(f34,plain,(
% 49.82/6.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 49.82/6.60    inference(cnf_transformation,[],[f14])).
% 49.82/6.60  fof(f14,axiom,(
% 49.82/6.60    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 49.82/6.60  fof(f507,plain,(
% 49.82/6.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k5_enumset1(X1,X2,X3,X4,X5,X6,X0)) )),
% 49.82/6.60    inference(backward_demodulation,[],[f389,f506])).
% 49.82/6.60  fof(f506,plain,(
% 49.82/6.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 49.82/6.60    inference(forward_demodulation,[],[f505,f34])).
% 49.82/6.60  fof(f505,plain,(
% 49.82/6.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 49.82/6.60    inference(superposition,[],[f36,f33])).
% 49.82/6.60  fof(f36,plain,(
% 49.82/6.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 49.82/6.60    inference(cnf_transformation,[],[f7])).
% 49.82/6.60  fof(f7,axiom,(
% 49.82/6.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 49.82/6.60  fof(f389,plain,(
% 49.82/6.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) )),
% 49.82/6.60    inference(superposition,[],[f35,f22])).
% 49.82/6.60  fof(f22,plain,(
% 49.82/6.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 49.82/6.60    inference(cnf_transformation,[],[f8])).
% 49.82/6.60  fof(f8,axiom,(
% 49.82/6.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 49.82/6.60  fof(f35,plain,(
% 49.82/6.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 49.82/6.60    inference(cnf_transformation,[],[f6])).
% 49.82/6.60  fof(f6,axiom,(
% 49.82/6.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 49.82/6.60  fof(f40266,plain,(
% 49.82/6.60    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 49.82/6.60    inference(superposition,[],[f39735,f22])).
% 49.82/6.60  fof(f39735,plain,(
% 49.82/6.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 49.82/6.60    inference(forward_demodulation,[],[f39719,f31])).
% 49.82/6.60  fof(f39719,plain,(
% 49.82/6.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 49.82/6.60    inference(superposition,[],[f22074,f25])).
% 49.82/6.60  fof(f25,plain,(
% 49.82/6.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 49.82/6.60    inference(cnf_transformation,[],[f9])).
% 49.82/6.60  fof(f9,axiom,(
% 49.82/6.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 49.82/6.60  fof(f22074,plain,(
% 49.82/6.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 49.82/6.60    inference(forward_demodulation,[],[f22068,f32])).
% 49.82/6.60  fof(f22068,plain,(
% 49.82/6.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 49.82/6.60    inference(superposition,[],[f1582,f29])).
% 49.82/6.60  fof(f1582,plain,(
% 49.82/6.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 49.82/6.60    inference(forward_demodulation,[],[f1580,f33])).
% 49.82/6.60  fof(f1580,plain,(
% 49.82/6.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 49.82/6.60    inference(superposition,[],[f390,f31])).
% 49.82/6.60  fof(f390,plain,(
% 49.82/6.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 49.82/6.60    inference(forward_demodulation,[],[f388,f34])).
% 49.82/6.60  fof(f388,plain,(
% 49.82/6.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 49.82/6.60    inference(superposition,[],[f35,f32])).
% 49.82/6.60  fof(f40511,plain,(
% 49.82/6.60    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3))) )),
% 49.82/6.60    inference(superposition,[],[f40277,f1885])).
% 49.82/6.60  fof(f1885,plain,(
% 49.82/6.60    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 49.82/6.60    inference(superposition,[],[f1706,f27])).
% 49.82/6.60  fof(f27,plain,(
% 49.82/6.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 49.82/6.60    inference(cnf_transformation,[],[f5])).
% 49.82/6.60  fof(f5,axiom,(
% 49.82/6.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 49.82/6.60  fof(f1706,plain,(
% 49.82/6.60    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 49.82/6.60    inference(superposition,[],[f1673,f24])).
% 49.82/6.60  fof(f24,plain,(
% 49.82/6.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 49.82/6.60    inference(cnf_transformation,[],[f2])).
% 49.82/6.60  fof(f2,axiom,(
% 49.82/6.60    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 49.82/6.60  fof(f1673,plain,(
% 49.82/6.60    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X3,X2)) )),
% 49.82/6.60    inference(forward_demodulation,[],[f1615,f27])).
% 49.82/6.60  fof(f1615,plain,(
% 49.82/6.60    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),X2) = k5_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 49.82/6.60    inference(superposition,[],[f94,f70])).
% 49.82/6.60  fof(f70,plain,(
% 49.82/6.60    ( ! [X10,X11,X9] : (k5_xboole_0(k4_xboole_0(X9,X10),X11) = k5_xboole_0(k3_xboole_0(X10,X9),k5_xboole_0(X9,X11))) )),
% 49.82/6.60    inference(superposition,[],[f49,f37])).
% 49.82/6.60  fof(f37,plain,(
% 49.82/6.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 49.82/6.60    inference(superposition,[],[f26,f23])).
% 49.82/6.60  fof(f23,plain,(
% 49.82/6.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 49.82/6.60    inference(cnf_transformation,[],[f1])).
% 49.82/6.60  fof(f1,axiom,(
% 49.82/6.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 49.82/6.60  fof(f26,plain,(
% 49.82/6.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 49.82/6.60    inference(cnf_transformation,[],[f3])).
% 49.82/6.60  fof(f3,axiom,(
% 49.82/6.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 49.82/6.60  fof(f49,plain,(
% 49.82/6.60    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) )),
% 49.82/6.60    inference(superposition,[],[f30,f24])).
% 49.82/6.60  fof(f30,plain,(
% 49.82/6.60    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 49.82/6.60    inference(cnf_transformation,[],[f4])).
% 49.82/6.60  fof(f4,axiom,(
% 49.82/6.60    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 49.82/6.60  fof(f94,plain,(
% 49.82/6.60    ( ! [X6,X8,X7] : (k5_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(X8,X6))) )),
% 49.82/6.60    inference(superposition,[],[f55,f26])).
% 49.82/6.60  fof(f55,plain,(
% 49.82/6.60    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 49.82/6.60    inference(superposition,[],[f30,f24])).
% 49.82/6.60  fof(f40277,plain,(
% 49.82/6.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 49.82/6.60    inference(forward_demodulation,[],[f40265,f29])).
% 49.82/6.60  fof(f40265,plain,(
% 49.82/6.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 49.82/6.60    inference(superposition,[],[f39735,f22])).
% 49.82/6.60  fof(f21,plain,(
% 49.82/6.60    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 49.82/6.60    inference(cnf_transformation,[],[f20])).
% 49.82/6.60  fof(f20,plain,(
% 49.82/6.60    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 49.82/6.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 49.82/6.60  fof(f19,plain,(
% 49.82/6.60    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 49.82/6.60    introduced(choice_axiom,[])).
% 49.82/6.60  fof(f18,plain,(
% 49.82/6.60    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)),
% 49.82/6.60    inference(ennf_transformation,[],[f17])).
% 49.82/6.60  fof(f17,negated_conjecture,(
% 49.82/6.60    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 49.82/6.60    inference(negated_conjecture,[],[f16])).
% 49.82/6.60  fof(f16,conjecture,(
% 49.82/6.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 49.82/6.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).
% 49.82/6.60  % SZS output end Proof for theBenchmark
% 49.82/6.60  % (1579)------------------------------
% 49.82/6.60  % (1579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 49.82/6.60  % (1579)Termination reason: Refutation
% 49.82/6.60  
% 49.82/6.60  % (1579)Memory used [KB]: 129976
% 49.82/6.60  % (1579)Time elapsed: 6.183 s
% 49.82/6.60  % (1579)------------------------------
% 49.82/6.60  % (1579)------------------------------
% 49.82/6.61  % (1575)Success in time 6.253 s
%------------------------------------------------------------------------------
