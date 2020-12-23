%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:05 EST 2020

% Result     : Theorem 14.19s
% Output     : Refutation 14.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 412 expanded)
%              Number of leaves         :   10 ( 137 expanded)
%              Depth                    :   15
%              Number of atoms          :   68 ( 413 expanded)
%              Number of equality atoms :   67 ( 412 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70320,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f70308])).

fof(f70308,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(superposition,[],[f69936,f48397])).

fof(f48397,plain,(
    ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X9,X8) = k3_enumset1(X6,X7,X5,X8,X9) ),
    inference(superposition,[],[f2291,f2282])).

fof(f2282,plain,(
    ! [X24,X23,X21,X25,X22] : k3_enumset1(X21,X22,X23,X24,X25) = k2_xboole_0(k1_enumset1(X23,X21,X22),k2_tarski(X24,X25)) ),
    inference(superposition,[],[f30,f100])).

fof(f100,plain,(
    ! [X4,X5,X3] : k1_enumset1(X5,X3,X4) = k1_enumset1(X3,X4,X5) ),
    inference(superposition,[],[f69,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f69,plain,(
    ! [X8,X7,X9] : k2_xboole_0(k2_tarski(X8,X9),k1_tarski(X7)) = k1_enumset1(X7,X8,X9) ),
    inference(superposition,[],[f25,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f2291,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X2,X3,X4,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f30,f39])).

fof(f39,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    inference(superposition,[],[f31,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f31,plain,(
    ! [X2,X3] : k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) = k2_tarski(X2,X3) ),
    inference(superposition,[],[f21,f19])).

fof(f69936,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK2,sK0,sK1,sK4,sK3) ),
    inference(superposition,[],[f69668,f65592])).

fof(f65592,plain,(
    ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X9,X7,X8) = k3_enumset1(X5,X7,X6,X8,X9) ),
    inference(superposition,[],[f1018,f3056])).

fof(f3056,plain,(
    ! [X76,X74,X72,X75,X73] : k3_enumset1(X76,X72,X73,X74,X75) = k2_xboole_0(k1_tarski(X76),k2_enumset1(X73,X72,X74,X75)) ),
    inference(superposition,[],[f29,f2446])).

fof(f2446,plain,(
    ! [X66,X64,X67,X65] : k2_enumset1(X64,X65,X66,X67) = k2_enumset1(X65,X64,X66,X67) ),
    inference(superposition,[],[f2302,f2301])).

fof(f2301,plain,(
    ! [X14,X12,X15,X13] : k3_enumset1(X12,X13,X12,X14,X15) = k2_enumset1(X13,X12,X14,X15) ),
    inference(backward_demodulation,[],[f2280,f2300])).

fof(f2300,plain,(
    ! [X59,X57,X58,X56] : k2_xboole_0(k2_tarski(X56,X57),k2_tarski(X58,X59)) = k2_enumset1(X56,X57,X58,X59) ),
    inference(forward_demodulation,[],[f2289,f550])).

fof(f550,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X3,X0,X1,X2) = k3_enumset1(X3,X0,X0,X1,X2) ),
    inference(forward_demodulation,[],[f535,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f535,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f29,f406])).

fof(f406,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(superposition,[],[f28,f74])).

fof(f74,plain,(
    ! [X8,X7,X9] : k1_enumset1(X7,X8,X9) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X7,X8,X9)) ),
    inference(superposition,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f2289,plain,(
    ! [X59,X57,X58,X56] : k3_enumset1(X56,X57,X57,X58,X59) = k2_xboole_0(k2_tarski(X56,X57),k2_tarski(X58,X59)) ),
    inference(superposition,[],[f30,f109])).

fof(f109,plain,(
    ! [X2,X3] : k2_tarski(X3,X2) = k1_enumset1(X3,X2,X2) ),
    inference(superposition,[],[f100,f68])).

fof(f68,plain,(
    ! [X2,X3] : k2_tarski(X3,X2) = k1_enumset1(X2,X3,X2) ),
    inference(superposition,[],[f25,f43])).

fof(f43,plain,(
    ! [X2,X3] : k2_tarski(X3,X2) = k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X2)) ),
    inference(superposition,[],[f23,f31])).

fof(f2280,plain,(
    ! [X14,X12,X15,X13] : k3_enumset1(X12,X13,X12,X14,X15) = k2_xboole_0(k2_tarski(X13,X12),k2_tarski(X14,X15)) ),
    inference(superposition,[],[f30,f68])).

fof(f2302,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X8,X9,X10,X11) = k3_enumset1(X8,X9,X8,X10,X11) ),
    inference(backward_demodulation,[],[f2279,f2300])).

fof(f2279,plain,(
    ! [X10,X8,X11,X9] : k3_enumset1(X8,X9,X8,X10,X11) = k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)) ),
    inference(superposition,[],[f30,f108])).

fof(f108,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f100,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[],[f25,f38])).

fof(f38,plain,(
    ! [X6,X7] : k2_tarski(X6,X7) = k2_xboole_0(k1_tarski(X6),k2_tarski(X6,X7)) ),
    inference(superposition,[],[f23,f21])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f1018,plain,(
    ! [X45,X43,X41,X44,X42] : k3_enumset1(X45,X41,X42,X43,X44) = k2_xboole_0(k1_tarski(X45),k2_enumset1(X41,X43,X44,X42)) ),
    inference(superposition,[],[f29,f946])).

fof(f946,plain,(
    ! [X26,X24,X23,X25] : k2_enumset1(X23,X24,X26,X25) = k2_enumset1(X23,X26,X25,X24) ),
    inference(superposition,[],[f881,f555])).

fof(f555,plain,(
    ! [X23,X21,X22,X20] : k2_enumset1(X23,X20,X22,X21) = k3_enumset1(X23,X20,X21,X22,X22) ),
    inference(forward_demodulation,[],[f540,f28])).

fof(f540,plain,(
    ! [X23,X21,X22,X20] : k3_enumset1(X23,X20,X21,X22,X22) = k2_xboole_0(k1_tarski(X23),k1_enumset1(X20,X22,X21)) ),
    inference(superposition,[],[f29,f424])).

fof(f424,plain,(
    ! [X47,X48,X49] : k2_enumset1(X49,X47,X48,X48) = k1_enumset1(X49,X48,X47) ),
    inference(forward_demodulation,[],[f405,f25])).

fof(f405,plain,(
    ! [X47,X48,X49] : k2_enumset1(X49,X47,X48,X48) = k2_xboole_0(k1_tarski(X49),k2_tarski(X48,X47)) ),
    inference(superposition,[],[f28,f111])).

fof(f111,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f100,f67])).

fof(f881,plain,(
    ! [X28,X26,X29,X27] : k3_enumset1(X29,X26,X27,X28,X28) = k2_enumset1(X29,X28,X27,X26) ),
    inference(forward_demodulation,[],[f872,f28])).

fof(f872,plain,(
    ! [X28,X26,X29,X27] : k3_enumset1(X29,X26,X27,X28,X28) = k2_xboole_0(k1_tarski(X29),k1_enumset1(X28,X27,X26)) ),
    inference(superposition,[],[f29,f817])).

fof(f817,plain,(
    ! [X47,X48,X49] : k2_enumset1(X49,X47,X48,X48) = k1_enumset1(X48,X47,X49) ),
    inference(forward_demodulation,[],[f804,f26])).

fof(f804,plain,(
    ! [X47,X48,X49] : k2_enumset1(X49,X47,X48,X48) = k2_xboole_0(k2_tarski(X48,X47),k1_tarski(X49)) ),
    inference(superposition,[],[f409,f111])).

fof(f409,plain,(
    ! [X14,X15,X13,X16] : k2_xboole_0(k1_enumset1(X14,X15,X16),k1_tarski(X13)) = k2_enumset1(X13,X14,X15,X16) ),
    inference(superposition,[],[f28,f19])).

fof(f69668,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK2,sK1,sK3,sK0,sK4) ),
    inference(superposition,[],[f55100,f65592])).

fof(f55100,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK2,sK3,sK4,sK1,sK0) ),
    inference(superposition,[],[f18,f11142])).

fof(f11142,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X2,X3,X4,X0,X1) = k2_xboole_0(k2_tarski(X1,X0),k1_enumset1(X2,X3,X4)) ),
    inference(superposition,[],[f2293,f39])).

fof(f2293,plain,(
    ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k2_tarski(X8,X9),k1_enumset1(X5,X6,X7)) ),
    inference(superposition,[],[f30,f19])).

fof(f18,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:02:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.41  % (5947)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.45  % (5949)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.45  % (5946)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (5944)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.47  % (5955)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.47  % (5955)Refutation not found, incomplete strategy% (5955)------------------------------
% 0.19/0.47  % (5955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (5955)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (5955)Memory used [KB]: 10618
% 0.19/0.47  % (5955)Time elapsed: 0.061 s
% 0.19/0.47  % (5955)------------------------------
% 0.19/0.47  % (5955)------------------------------
% 0.19/0.47  % (5952)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.47  % (5958)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.47  % (5954)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.48  % (5953)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.48  % (5956)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.48  % (5959)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.48  % (5951)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.49  % (5945)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.49  % (5960)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.49  % (5961)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.50  % (5948)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.51  % (5957)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.51  % (5950)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 5.29/1.04  % (5948)Time limit reached!
% 5.29/1.04  % (5948)------------------------------
% 5.29/1.04  % (5948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.29/1.04  % (5948)Termination reason: Time limit
% 5.29/1.04  
% 5.29/1.04  % (5948)Memory used [KB]: 17526
% 5.29/1.04  % (5948)Time elapsed: 0.643 s
% 5.29/1.04  % (5948)------------------------------
% 5.29/1.04  % (5948)------------------------------
% 12.54/1.93  % (5949)Time limit reached!
% 12.54/1.93  % (5949)------------------------------
% 12.54/1.93  % (5949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/1.93  % (5949)Termination reason: Time limit
% 12.54/1.93  % (5949)Termination phase: Saturation
% 12.54/1.93  
% 12.54/1.93  % (5949)Memory used [KB]: 55137
% 12.54/1.93  % (5949)Time elapsed: 1.500 s
% 12.54/1.93  % (5949)------------------------------
% 12.54/1.93  % (5949)------------------------------
% 12.54/1.94  % (5950)Time limit reached!
% 12.54/1.94  % (5950)------------------------------
% 12.54/1.94  % (5950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/1.94  % (5950)Termination reason: Time limit
% 12.54/1.94  % (5950)Termination phase: Saturation
% 12.54/1.94  
% 12.54/1.94  % (5950)Memory used [KB]: 38634
% 12.54/1.94  % (5950)Time elapsed: 1.500 s
% 12.54/1.94  % (5950)------------------------------
% 12.54/1.94  % (5950)------------------------------
% 14.19/2.16  % (5960)Refutation found. Thanks to Tanya!
% 14.19/2.16  % SZS status Theorem for theBenchmark
% 14.19/2.16  % SZS output start Proof for theBenchmark
% 14.19/2.16  fof(f70320,plain,(
% 14.19/2.16    $false),
% 14.19/2.16    inference(trivial_inequality_removal,[],[f70308])).
% 14.19/2.16  fof(f70308,plain,(
% 14.19/2.16    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)),
% 14.19/2.16    inference(superposition,[],[f69936,f48397])).
% 14.19/2.16  fof(f48397,plain,(
% 14.19/2.16    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X9,X8) = k3_enumset1(X6,X7,X5,X8,X9)) )),
% 14.19/2.16    inference(superposition,[],[f2291,f2282])).
% 14.19/2.16  fof(f2282,plain,(
% 14.19/2.16    ( ! [X24,X23,X21,X25,X22] : (k3_enumset1(X21,X22,X23,X24,X25) = k2_xboole_0(k1_enumset1(X23,X21,X22),k2_tarski(X24,X25))) )),
% 14.19/2.16    inference(superposition,[],[f30,f100])).
% 14.19/2.16  fof(f100,plain,(
% 14.19/2.16    ( ! [X4,X5,X3] : (k1_enumset1(X5,X3,X4) = k1_enumset1(X3,X4,X5)) )),
% 14.19/2.16    inference(superposition,[],[f69,f26])).
% 14.19/2.16  fof(f26,plain,(
% 14.19/2.16    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 14.19/2.16    inference(cnf_transformation,[],[f10])).
% 14.19/2.16  fof(f10,axiom,(
% 14.19/2.16    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 14.19/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 14.19/2.16  fof(f69,plain,(
% 14.19/2.16    ( ! [X8,X7,X9] : (k2_xboole_0(k2_tarski(X8,X9),k1_tarski(X7)) = k1_enumset1(X7,X8,X9)) )),
% 14.19/2.16    inference(superposition,[],[f25,f19])).
% 14.19/2.16  fof(f19,plain,(
% 14.19/2.16    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 14.19/2.16    inference(cnf_transformation,[],[f1])).
% 14.19/2.16  fof(f1,axiom,(
% 14.19/2.16    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 14.19/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 14.19/2.16  fof(f25,plain,(
% 14.19/2.16    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 14.19/2.16    inference(cnf_transformation,[],[f9])).
% 14.19/2.16  fof(f9,axiom,(
% 14.19/2.16    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 14.19/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 14.19/2.16  fof(f30,plain,(
% 14.19/2.16    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 14.19/2.16    inference(cnf_transformation,[],[f7])).
% 14.19/2.16  fof(f7,axiom,(
% 14.19/2.16    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 14.19/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).
% 14.19/2.16  fof(f2291,plain,(
% 14.19/2.16    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X2,X3,X4,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X1,X0))) )),
% 14.19/2.16    inference(superposition,[],[f30,f39])).
% 14.19/2.16  fof(f39,plain,(
% 14.19/2.16    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) )),
% 14.19/2.16    inference(superposition,[],[f31,f21])).
% 14.19/2.16  fof(f21,plain,(
% 14.19/2.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 14.19/2.16    inference(cnf_transformation,[],[f8])).
% 14.19/2.16  fof(f8,axiom,(
% 14.19/2.16    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 14.19/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 14.19/2.16  fof(f31,plain,(
% 14.19/2.16    ( ! [X2,X3] : (k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) = k2_tarski(X2,X3)) )),
% 14.19/2.16    inference(superposition,[],[f21,f19])).
% 14.19/2.16  fof(f69936,plain,(
% 14.19/2.16    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK2,sK0,sK1,sK4,sK3)),
% 14.19/2.16    inference(superposition,[],[f69668,f65592])).
% 14.19/2.16  fof(f65592,plain,(
% 14.19/2.16    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X9,X7,X8) = k3_enumset1(X5,X7,X6,X8,X9)) )),
% 14.19/2.16    inference(superposition,[],[f1018,f3056])).
% 14.19/2.16  fof(f3056,plain,(
% 14.19/2.16    ( ! [X76,X74,X72,X75,X73] : (k3_enumset1(X76,X72,X73,X74,X75) = k2_xboole_0(k1_tarski(X76),k2_enumset1(X73,X72,X74,X75))) )),
% 14.19/2.16    inference(superposition,[],[f29,f2446])).
% 14.19/2.16  fof(f2446,plain,(
% 14.19/2.16    ( ! [X66,X64,X67,X65] : (k2_enumset1(X64,X65,X66,X67) = k2_enumset1(X65,X64,X66,X67)) )),
% 14.19/2.16    inference(superposition,[],[f2302,f2301])).
% 14.19/2.16  fof(f2301,plain,(
% 14.19/2.16    ( ! [X14,X12,X15,X13] : (k3_enumset1(X12,X13,X12,X14,X15) = k2_enumset1(X13,X12,X14,X15)) )),
% 14.19/2.16    inference(backward_demodulation,[],[f2280,f2300])).
% 14.19/2.16  fof(f2300,plain,(
% 14.19/2.16    ( ! [X59,X57,X58,X56] : (k2_xboole_0(k2_tarski(X56,X57),k2_tarski(X58,X59)) = k2_enumset1(X56,X57,X58,X59)) )),
% 14.19/2.16    inference(forward_demodulation,[],[f2289,f550])).
% 14.19/2.16  fof(f550,plain,(
% 14.19/2.16    ( ! [X2,X0,X3,X1] : (k2_enumset1(X3,X0,X1,X2) = k3_enumset1(X3,X0,X0,X1,X2)) )),
% 14.19/2.16    inference(forward_demodulation,[],[f535,f28])).
% 14.19/2.16  fof(f28,plain,(
% 14.19/2.16    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 14.19/2.16    inference(cnf_transformation,[],[f11])).
% 14.19/2.16  fof(f11,axiom,(
% 14.19/2.16    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 14.19/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 14.19/2.16  fof(f535,plain,(
% 14.19/2.16    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 14.19/2.16    inference(superposition,[],[f29,f406])).
% 14.19/2.16  fof(f406,plain,(
% 14.19/2.16    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 14.19/2.16    inference(superposition,[],[f28,f74])).
% 14.19/2.16  fof(f74,plain,(
% 14.19/2.16    ( ! [X8,X7,X9] : (k1_enumset1(X7,X8,X9) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X7,X8,X9))) )),
% 14.19/2.16    inference(superposition,[],[f23,f25])).
% 14.19/2.16  fof(f23,plain,(
% 14.19/2.16    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 14.19/2.16    inference(cnf_transformation,[],[f3])).
% 14.19/2.16  fof(f3,axiom,(
% 14.19/2.16    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 14.19/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 14.19/2.16  fof(f2289,plain,(
% 14.19/2.16    ( ! [X59,X57,X58,X56] : (k3_enumset1(X56,X57,X57,X58,X59) = k2_xboole_0(k2_tarski(X56,X57),k2_tarski(X58,X59))) )),
% 14.19/2.16    inference(superposition,[],[f30,f109])).
% 14.19/2.16  fof(f109,plain,(
% 14.19/2.16    ( ! [X2,X3] : (k2_tarski(X3,X2) = k1_enumset1(X3,X2,X2)) )),
% 14.19/2.16    inference(superposition,[],[f100,f68])).
% 14.19/2.16  fof(f68,plain,(
% 14.19/2.16    ( ! [X2,X3] : (k2_tarski(X3,X2) = k1_enumset1(X2,X3,X2)) )),
% 14.19/2.16    inference(superposition,[],[f25,f43])).
% 14.19/2.16  fof(f43,plain,(
% 14.19/2.16    ( ! [X2,X3] : (k2_tarski(X3,X2) = k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X2))) )),
% 14.19/2.16    inference(superposition,[],[f23,f31])).
% 14.19/2.16  fof(f2280,plain,(
% 14.19/2.16    ( ! [X14,X12,X15,X13] : (k3_enumset1(X12,X13,X12,X14,X15) = k2_xboole_0(k2_tarski(X13,X12),k2_tarski(X14,X15))) )),
% 14.19/2.16    inference(superposition,[],[f30,f68])).
% 14.19/2.16  fof(f2302,plain,(
% 14.19/2.16    ( ! [X10,X8,X11,X9] : (k2_enumset1(X8,X9,X10,X11) = k3_enumset1(X8,X9,X8,X10,X11)) )),
% 14.19/2.16    inference(backward_demodulation,[],[f2279,f2300])).
% 14.19/2.16  fof(f2279,plain,(
% 14.19/2.16    ( ! [X10,X8,X11,X9] : (k3_enumset1(X8,X9,X8,X10,X11) = k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11))) )),
% 14.19/2.16    inference(superposition,[],[f30,f108])).
% 14.19/2.16  fof(f108,plain,(
% 14.19/2.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 14.19/2.16    inference(superposition,[],[f100,f67])).
% 14.19/2.16  fof(f67,plain,(
% 14.19/2.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 14.19/2.16    inference(superposition,[],[f25,f38])).
% 14.19/2.16  fof(f38,plain,(
% 14.19/2.16    ( ! [X6,X7] : (k2_tarski(X6,X7) = k2_xboole_0(k1_tarski(X6),k2_tarski(X6,X7))) )),
% 14.19/2.16    inference(superposition,[],[f23,f21])).
% 14.19/2.16  fof(f29,plain,(
% 14.19/2.16    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 14.19/2.16    inference(cnf_transformation,[],[f12])).
% 14.19/2.16  fof(f12,axiom,(
% 14.19/2.16    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 14.19/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 14.19/2.16  fof(f1018,plain,(
% 14.19/2.16    ( ! [X45,X43,X41,X44,X42] : (k3_enumset1(X45,X41,X42,X43,X44) = k2_xboole_0(k1_tarski(X45),k2_enumset1(X41,X43,X44,X42))) )),
% 14.19/2.16    inference(superposition,[],[f29,f946])).
% 14.19/2.16  fof(f946,plain,(
% 14.19/2.16    ( ! [X26,X24,X23,X25] : (k2_enumset1(X23,X24,X26,X25) = k2_enumset1(X23,X26,X25,X24)) )),
% 14.19/2.16    inference(superposition,[],[f881,f555])).
% 14.19/2.16  fof(f555,plain,(
% 14.19/2.16    ( ! [X23,X21,X22,X20] : (k2_enumset1(X23,X20,X22,X21) = k3_enumset1(X23,X20,X21,X22,X22)) )),
% 14.19/2.16    inference(forward_demodulation,[],[f540,f28])).
% 14.19/2.16  fof(f540,plain,(
% 14.19/2.16    ( ! [X23,X21,X22,X20] : (k3_enumset1(X23,X20,X21,X22,X22) = k2_xboole_0(k1_tarski(X23),k1_enumset1(X20,X22,X21))) )),
% 14.19/2.16    inference(superposition,[],[f29,f424])).
% 14.19/2.16  fof(f424,plain,(
% 14.19/2.16    ( ! [X47,X48,X49] : (k2_enumset1(X49,X47,X48,X48) = k1_enumset1(X49,X48,X47)) )),
% 14.19/2.16    inference(forward_demodulation,[],[f405,f25])).
% 14.19/2.16  fof(f405,plain,(
% 14.19/2.16    ( ! [X47,X48,X49] : (k2_enumset1(X49,X47,X48,X48) = k2_xboole_0(k1_tarski(X49),k2_tarski(X48,X47))) )),
% 14.19/2.16    inference(superposition,[],[f28,f111])).
% 14.19/2.16  fof(f111,plain,(
% 14.19/2.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 14.19/2.16    inference(superposition,[],[f100,f67])).
% 14.19/2.16  fof(f881,plain,(
% 14.19/2.16    ( ! [X28,X26,X29,X27] : (k3_enumset1(X29,X26,X27,X28,X28) = k2_enumset1(X29,X28,X27,X26)) )),
% 14.19/2.16    inference(forward_demodulation,[],[f872,f28])).
% 14.19/2.16  fof(f872,plain,(
% 14.19/2.16    ( ! [X28,X26,X29,X27] : (k3_enumset1(X29,X26,X27,X28,X28) = k2_xboole_0(k1_tarski(X29),k1_enumset1(X28,X27,X26))) )),
% 14.19/2.16    inference(superposition,[],[f29,f817])).
% 14.19/2.16  fof(f817,plain,(
% 14.19/2.16    ( ! [X47,X48,X49] : (k2_enumset1(X49,X47,X48,X48) = k1_enumset1(X48,X47,X49)) )),
% 14.19/2.16    inference(forward_demodulation,[],[f804,f26])).
% 14.19/2.16  fof(f804,plain,(
% 14.19/2.16    ( ! [X47,X48,X49] : (k2_enumset1(X49,X47,X48,X48) = k2_xboole_0(k2_tarski(X48,X47),k1_tarski(X49))) )),
% 14.19/2.16    inference(superposition,[],[f409,f111])).
% 14.19/2.16  fof(f409,plain,(
% 14.19/2.16    ( ! [X14,X15,X13,X16] : (k2_xboole_0(k1_enumset1(X14,X15,X16),k1_tarski(X13)) = k2_enumset1(X13,X14,X15,X16)) )),
% 14.19/2.16    inference(superposition,[],[f28,f19])).
% 14.19/2.16  fof(f69668,plain,(
% 14.19/2.16    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK2,sK1,sK3,sK0,sK4)),
% 14.19/2.16    inference(superposition,[],[f55100,f65592])).
% 14.19/2.16  fof(f55100,plain,(
% 14.19/2.16    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK2,sK3,sK4,sK1,sK0)),
% 14.19/2.16    inference(superposition,[],[f18,f11142])).
% 14.19/2.16  fof(f11142,plain,(
% 14.19/2.16    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X2,X3,X4,X0,X1) = k2_xboole_0(k2_tarski(X1,X0),k1_enumset1(X2,X3,X4))) )),
% 14.19/2.16    inference(superposition,[],[f2293,f39])).
% 14.19/2.16  fof(f2293,plain,(
% 14.19/2.16    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k2_tarski(X8,X9),k1_enumset1(X5,X6,X7))) )),
% 14.19/2.16    inference(superposition,[],[f30,f19])).
% 14.19/2.16  fof(f18,plain,(
% 14.19/2.16    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4))),
% 14.19/2.16    inference(cnf_transformation,[],[f17])).
% 14.19/2.16  fof(f17,plain,(
% 14.19/2.16    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4))),
% 14.19/2.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 14.19/2.16  fof(f16,plain,(
% 14.19/2.16    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4))),
% 14.19/2.16    introduced(choice_axiom,[])).
% 14.19/2.16  fof(f15,plain,(
% 14.19/2.16    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 14.19/2.16    inference(ennf_transformation,[],[f14])).
% 14.19/2.16  fof(f14,negated_conjecture,(
% 14.19/2.16    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 14.19/2.16    inference(negated_conjecture,[],[f13])).
% 14.19/2.16  fof(f13,conjecture,(
% 14.19/2.16    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 14.19/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 14.19/2.16  % SZS output end Proof for theBenchmark
% 14.19/2.16  % (5960)------------------------------
% 14.19/2.16  % (5960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.19/2.16  % (5960)Termination reason: Refutation
% 14.19/2.16  
% 14.19/2.16  % (5960)Memory used [KB]: 24818
% 14.19/2.16  % (5960)Time elapsed: 1.755 s
% 14.19/2.16  % (5960)------------------------------
% 14.19/2.16  % (5960)------------------------------
% 14.19/2.17  % (5943)Success in time 1.819 s
%------------------------------------------------------------------------------
